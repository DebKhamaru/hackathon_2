#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <memory>
#include <functional>
#include <stdexcept>
#include <algorithm>
#include <cmath>
#include <ctime>
#include <random>
#include <iomanip>
#include <climits>
#include <cassert>
#include <set>


using namespace std;

// FORWARD DECLARATIONS

struct JSVal; using JV = shared_ptr<JSVal>;
struct Env;   using EP = shared_ptr<Env>;
struct Node;  using NP = shared_ptr<Node>;

// NUMBER → STRING  (matches JavaScript's Number.prototype.toString)

static string numToStr(double n) {
    if (isnan(n))  return "NaN";
    if (isinf(n))  return n > 0 ? "Infinity" : "-Infinity";
    if (n == 0.0)  return "0";
    // Whole-number fast path
    if (n == trunc(n) && fabs(n) < 1e15) {
        ostringstream oss; oss << fixed << setprecision(0) << n;
        return oss.str();
    }
    // General case: up to 17 significant digits, trimmed
    ostringstream oss;
    oss << setprecision(17) << n;
    string s = oss.str();
    // Remove trailing zeros after decimal point
    if (s.find('.') != string::npos && s.find('e') == string::npos) {
        size_t last = s.find_last_not_of('0');
        if (last != string::npos && s[last] == '.') s = s.substr(0, last);
        else if (last != string::npos)              s = s.substr(0, last + 1);
    }
    return s;
}

static double parseNumStr(const string& raw) {
    if (raw.empty()) return 0;
    // Trim whitespace
    size_t a = raw.find_first_not_of(" \t\n\r\f\v");
    size_t b = raw.find_last_not_of(" \t\n\r\f\v");
    if (a == string::npos) return 0;
    string t = raw.substr(a, b - a + 1);
    if (t.empty())   return 0;
    if (t == "Infinity" || t == "+Infinity") return numeric_limits<double>::infinity();
    if (t == "-Infinity") return -numeric_limits<double>::infinity();
    // Hex
    if (t.size() > 2 && t[0] == '0' && (t[1] == 'x' || t[1] == 'X')) {
        try { return (double)stoull(t, nullptr, 16); } catch (...) {}
        return numeric_limits<double>::quiet_NaN();
    }
    try {
        size_t pos;
        double d = stod(t, &pos);
        if (pos == t.size()) return d;
    } catch (...) {}
    return numeric_limits<double>::quiet_NaN();
}

// TOKEN TYPES

enum class TT {
    NUM,STR,BOOL,NIL,UNDEF,TMPL,ID,
    LET,CONST,VAR,FN,RET,IF,ELSE,WHILE,FOR,DO,
    SWITCH,CASE,DFL,BREAK,CONT,NEW,TYPEOF,VOID,THIS,
    OF,IN,THROW,TRY,CATCH,FINALLY,CLASS,EXTENDS,
    PLUS,MINUS,STAR,SL,MOD,POW,
    EQ,EQ2,EQ3,NE1,NE2,LT,GT,LE,GE,
    AND,OR,NOT,NULLISH,QUES,
    PLUSA,MINUSA,STARA,SLA,MODA,
    INC,DEC,ARROW,SPREAD,
    BAND,BOR,BXOR,BNOT,SHL,SHR,USHR,
    LP,RP,LB,RB,LA,RA,
    COMMA,SEMI,DOT,COLON,EOFT
};

struct Tok { TT t; string v; int ln; };

// LEXER

class Lexer {
    string src; size_t p = 0; int ln = 1;
    char c()  const { return p < src.size() ? src[p]     : 0; }
    char pk(int n=1) const { return (p+n) < src.size() ? src[p+n] : 0; }
    char a() { char ch = src[p++]; if (ch=='\n') ln++; return ch; }

    void ws() {
        while (p < src.size()) {
            if (isspace(c())) { a(); continue; }
            if (c()=='/' && pk()=='/') { while (p<src.size()&&c()!='\n') a(); continue; }
            if (c()=='/' && pk()=='*') {
                a(); a();
                while (p<src.size() && !(c()=='*'&&pk()=='/')) a();
                if (p<src.size()) { a(); a(); }
                continue;
            }
            break;
        }
    }

    Tok readNum() {
        string s;
        if (c()=='0' && (pk()=='x'||pk()=='X')) {
            s+=a(); s+=a();
            while (p<src.size() && isxdigit(c())) s+=a();
        } else {
            while (p<src.size() && (isdigit(c())||c()=='.')) s+=a();
            if (p<src.size() && (c()=='e'||c()=='E')) {
                s+=a();
                if (p<src.size()&&(c()=='+'||c()=='-')) s+=a();
                while (p<src.size()&&isdigit(c())) s+=a();
            }
        }
        return {TT::NUM, s, ln};
    }

    Tok readStr(char d) {
        a(); string s;
        while (p<src.size() && c()!=d) {
            if (c()=='\\') {
                a(); char e=a();
                switch(e) {
                    case 'n': s+='\n'; break; case 't': s+='\t'; break;
                    case 'r': s+='\r'; break; case '\\': s+='\\'; break;
                    case '\'': s+='\''; break; case '"': s+='"'; break;
                    case '`': s+='`'; break; case '0': s+='\0'; break;
                    case 'u': {
                        string h;
                        if (p<src.size()&&c()=='{') {
                            a(); while(p<src.size()&&c()!='}') h+=a(); a();
                        } else {
                            for(int i=0;i<4&&p<src.size();i++) h+=a();
                        }
                        try { unsigned cp=(unsigned)stoul(h,nullptr,16);
                            if(cp<128) s+=(char)cp;
                            else { s+=(char)(0xC0|(cp>>6)); s+=(char)(0x80|(cp&0x3F)); }
                        } catch(...) {}
                        break;
                    }
                    default: s+=e; break;
                }
            } else s+=a();
        }
        if (p<src.size()) a();
        return {TT::STR, s, ln};
    }

    Tok readTmpl() {
        a(); string s;
        while (p<src.size() && c()!='`') {
            if (c()=='\\') {
                a(); char e=a();
                switch(e) {
                    case 'n': s+='\n'; break; case 't': s+='\t'; break;
                    case 'r': s+='\r'; break; default: s+=e; break;
                }
            } else if (c()=='$' && pk()=='{') {
                s+="${"; a(); a(); int d=1;
                while (p<src.size()&&d>0) {
                    char ch=a();
                    if(ch=='{') d++;
                    else if(ch=='}'){d--;if(d==0){s+='}';break;}}
                    s+=ch;
                }
            } else s+=a();
        }
        if (p<src.size()) a();
        return {TT::TMPL, s, ln};
    }

    Tok readId() {
        string s;
        while (p<src.size()&&(isalnum(c())||c()=='_'||c()=='$')) s+=a();
        static const unordered_map<string,TT> kw={
            {"let",TT::LET},{"const",TT::CONST},{"var",TT::VAR},{"function",TT::FN},
            {"return",TT::RET},{"if",TT::IF},{"else",TT::ELSE},{"while",TT::WHILE},
            {"for",TT::FOR},{"do",TT::DO},{"switch",TT::SWITCH},{"case",TT::CASE},
            {"default",TT::DFL},{"break",TT::BREAK},{"continue",TT::CONT},
            {"new",TT::NEW},{"typeof",TT::TYPEOF},{"void",TT::VOID},{"this",TT::THIS},
            {"of",TT::OF},{"in",TT::IN},{"throw",TT::THROW},{"try",TT::TRY},
            {"catch",TT::CATCH},{"finally",TT::FINALLY},{"class",TT::CLASS},{"extends",TT::EXTENDS},
            {"true",TT::BOOL},{"false",TT::BOOL},{"null",TT::NIL},{"undefined",TT::UNDEF},
        };
        auto it=kw.find(s); if(it!=kw.end()) return {it->second, s, ln};
        return {TT::ID, s, ln};
    }

public:
    Lexer(string s) : src(move(s)) {}

    vector<Tok> tokenize() {
        vector<Tok> r;
        while (true) {
            ws();
            if (p>=src.size()) { r.push_back({TT::EOFT,"",ln}); break; }
            int l=ln; char ch=c();
            if (isdigit(ch)||(ch=='.'&&isdigit(pk()))) { r.push_back(readNum()); continue; }
            if (ch=='"'||ch=='\'') { r.push_back(readStr(ch)); continue; }
            if (ch=='`')  { r.push_back(readTmpl()); continue; }
            if (isalpha(ch)||ch=='_'||ch=='$') { r.push_back(readId()); continue; }
            a();
            switch(ch) {
                case '+': if(c()=='+'){a();r.push_back({TT::INC,"++",l});}else if(c()=='='){a();r.push_back({TT::PLUSA,"+=",l});}else r.push_back({TT::PLUS,"+",l}); break;
                case '-': if(c()=='-'){a();r.push_back({TT::DEC,"--",l});}else if(c()=='='){a();r.push_back({TT::MINUSA,"-=",l});}else r.push_back({TT::MINUS,"-",l}); break;
                case '*': if(c()=='*'){a();r.push_back({TT::POW,"**",l});}else if(c()=='='){a();r.push_back({TT::STARA,"*=",l});}else r.push_back({TT::STAR,"*",l}); break;
                case '/': if(c()=='='){a();r.push_back({TT::SLA,"/=",l});}else r.push_back({TT::SL,"/",l}); break;
                case '%': if(c()=='='){a();r.push_back({TT::MODA,"%=",l});}else r.push_back({TT::MOD,"%",l}); break;
                case '=': if(c()=='='){a();if(c()=='='){a();r.push_back({TT::EQ3,"===",l});}else r.push_back({TT::EQ2,"==",l});}else if(c()=='>'){a();r.push_back({TT::ARROW,"=>",l});}else r.push_back({TT::EQ,"=",l}); break;
                case '!': if(c()=='='){a();if(c()=='='){a();r.push_back({TT::NE2,"!==",l});}else r.push_back({TT::NE1,"!=",l});}else r.push_back({TT::NOT,"!",l}); break;
                case '<': if(c()=='='){a();r.push_back({TT::LE,"<=",l});}else if(c()=='<'){a();r.push_back({TT::SHL,"<<",l});}else r.push_back({TT::LT,"<",l}); break;
                case '>': if(c()=='='){a();r.push_back({TT::GE,">=",l});}else if(c()=='>'){a();if(c()=='>'){a();r.push_back({TT::USHR,">>>",l});}else r.push_back({TT::SHR,">>",l});}else r.push_back({TT::GT,">",l}); break;
                case '&': if(c()=='&'){a();r.push_back({TT::AND,"&&",l});}else r.push_back({TT::BAND,"&",l}); break;
                case '|': if(c()=='|'){a();r.push_back({TT::OR,"||",l});}else r.push_back({TT::BOR,"|",l}); break;
                case '^': r.push_back({TT::BXOR,"^",l}); break;
                case '~': r.push_back({TT::BNOT,"~",l}); break;
                case '?': if(c()=='?'){a();r.push_back({TT::NULLISH,"??",l});}else r.push_back({TT::QUES,"?",l}); break;
                case '.': if(c()=='.'&&pk()=='.'){a();a();r.push_back({TT::SPREAD,"...",l});}else r.push_back({TT::DOT,".",l}); break;
                case '(': r.push_back({TT::LP,"(",l}); break;
                case ')': r.push_back({TT::RP,")",l}); break;
                case '{': r.push_back({TT::LB,"{",l}); break;
                case '}': r.push_back({TT::RB,"}",l}); break;
                case '[': r.push_back({TT::LA,"[",l}); break;
                case ']': r.push_back({TT::RA,"]",l}); break;
                case ',': r.push_back({TT::COMMA,",",l}); break;
                case ';': r.push_back({TT::SEMI,";",l}); break;
                case ':': r.push_back({TT::COLON,":",l}); break;
                default: break;
            }
        }
        return r;
    }
};


// AST NODE TYPES

enum class NT {
    Prog, Block,
    VDecl, FDecl, Ret, Brk, Ctn, Throw, Try,
    If, While, For, ForOf, ForIn, DoWhile, Switch, SCase,
    ExprS,
    Lit, Id, ArrL, ObjL, FnEx, Arrow,
    Asn, Bin, Un, Upd, Log, Cond,
    Call, New_, Mem, Idx, Spread, Tmpl, Typeof,
};

struct Node {
    NT      type;
    string  str, sval;        // str = name/operator/discriminator; sval = string-literal text
    double  num   = 0;
    bool    flag  = false;    // bool-literal / prefix-flag / isConst
    bool    isConst=false, hasRest=false, isDefault=false, computed=false;
    string  restParam;
    vector<NP>               ch;
    vector<pair<string,NP>>  props;   // object-literal properties
    vector<string>           params;
    Node(NT t) : type(t) {}
};
static NP mkN(NT t) { return make_shared<Node>(t); }

// JS VALUE

enum class JT { Undef, Null, Bool, Num, Str, Obj, Arr, Fn };

struct JsFn {
    string        name;
    vector<string> params;
    bool          hasRest  = false;
    string        restParam;
    NP            body;       // nullptr → native
    EP            closure;
    bool          isArrow   = false;
    bool          isNative  = false;
    function<JV(vector<JV>, JV, EP)> native;
};

struct JSVal {
    JT     type  = JT::Undef;
    bool   b     = false;
    double n     = 0;
    string s;
    shared_ptr<map<string,JV>> props;
    shared_ptr<vector<JV>>     arr;
    shared_ptr<JsFn>           fn;
    shared_ptr<vector<string>> keys;    // insertion-order key list

    bool truthy() const {
        switch (type) {
            case JT::Undef: case JT::Null: return false;
            case JT::Bool:  return b;
            case JT::Num:   return n != 0.0 && !isnan(n);
            case JT::Str:   return !s.empty();
            default:        return true;
        }
    }

    // ── factories 
    static JV undef() { return make_shared<JSVal>(); }
    static JV null_() { auto v=make_shared<JSVal>(); v->type=JT::Null; return v; }
    static JV bl(bool b_) {
        auto v=make_shared<JSVal>(); v->type=JT::Bool; v->b=b_; return v;
    }
    static JV nm(double n_) {
        auto v=make_shared<JSVal>(); v->type=JT::Num; v->n=n_; return v;
    }
    static JV st(string s_) {
        auto v=make_shared<JSVal>(); v->type=JT::Str; v->s=move(s_); return v;
    }
    static JV ob() {
        auto v=make_shared<JSVal>(); v->type=JT::Obj;
        v->props=make_shared<map<string,JV>>();
        v->keys=make_shared<vector<string>>();
        return v;
    }
    static JV ar() {
        auto v=make_shared<JSVal>(); v->type=JT::Arr;
        v->arr=make_shared<vector<JV>>();
        v->props=make_shared<map<string,JV>>();
        v->keys=make_shared<vector<string>>();
        return v;
    }
    static JV fn_(shared_ptr<JsFn> f) {
        auto v=make_shared<JSVal>(); v->type=JT::Fn; v->fn=f; return v;
    }

    // ── property helpers ───────────────────────────────────────
    void setProp(const string& k, JV val) {
        if (!props) { props=make_shared<map<string,JV>>(); keys=make_shared<vector<string>>(); }
        if (!props->count(k)) keys->push_back(k);
        (*props)[k] = val;
    }
    JV getProp(const string& k) const {
        if (props && props->count(k)) return (*props)[k];
        return JSVal::undef();
    }
    bool hasProp(const string& k) const {
        return props && props->count(k);
    }
    void delProp(const string& k) {
        if (!props) return;
        props->erase(k);
        if (keys) keys->erase(remove(keys->begin(),keys->end(),k),keys->end());
    }
};

// VALUE CONVERSIONS (declared before use)

static string jsStr(JV v);
static double jsNum(JV v);

static string arrToStr(JV v) {
    if (!v||!v->arr) return "";
    string r;
    for (size_t i=0;i<v->arr->size();i++) {
        if (i) r+=',';
        auto& e=(*v->arr)[i];
        if (e&&e->type!=JT::Null&&e->type!=JT::Undef) r+=jsStr(e);
    }
    return r;
}

static string jsStr(JV v) {
    if (!v) return "undefined";
    switch(v->type) {
        case JT::Undef: return "undefined";
        case JT::Null:  return "null";
        case JT::Bool:  return v->b ? "true" : "false";
        case JT::Num:   return numToStr(v->n);
        case JT::Str:   return v->s;
        case JT::Arr:   return arrToStr(v);
        case JT::Fn:    return "[object Function]";
        case JT::Obj: {
            if (v->hasProp("__isDate__")) {
                // Return a readable date string
                if (v->hasProp("__ms__")) {
                    double ms = jsNum(v->getProp("__ms__"));
                    time_t t=(time_t)(ms/1000);
                    char buf[64];
                    struct tm* ti=gmtime(&t);
                    strftime(buf,sizeof(buf),"%Y-%m-%dT%H:%M:%S.000Z",ti);
                    return buf;
                }
            }
            return "[object Object]";
        }
    }
    return "undefined";
}

static double jsNum(JV v) {
    if (!v) return numeric_limits<double>::quiet_NaN();
    switch(v->type) {
        case JT::Undef: return numeric_limits<double>::quiet_NaN();
        case JT::Null:  return 0;
        case JT::Bool:  return v->b ? 1.0 : 0.0;
        case JT::Num:   return v->n;
        case JT::Str:   return parseNumStr(v->s);
        case JT::Arr:
            if (!v->arr||v->arr->empty()) return 0;
            if (v->arr->size()==1) return jsNum((*v->arr)[0]);
            return numeric_limits<double>::quiet_NaN();
        default: return numeric_limits<double>::quiet_NaN();
    }
}

static bool jsBool(JV v) { return v && v->truthy(); }

static bool jsAbstractEq(JV a, JV b) {
    if (!a) a=JSVal::undef(); if (!b) b=JSVal::undef();
    if (a->type==b->type) {
        if (a->type==JT::Undef||a->type==JT::Null) return true;
        if (a->type==JT::Num)  { if(isnan(a->n)||isnan(b->n)) return false; return a->n==b->n; }
        if (a->type==JT::Str)  return a->s==b->s;
        if (a->type==JT::Bool) return a->b==b->b;
        return a.get()==b.get();
    }
    if ((a->type==JT::Null&&b->type==JT::Undef)||(a->type==JT::Undef&&b->type==JT::Null)) return true;
    if (a->type==JT::Num&&b->type==JT::Str) return a->n==jsNum(b);
    if (a->type==JT::Str&&b->type==JT::Num) return jsNum(a)==b->n;
    if (a->type==JT::Bool) return jsAbstractEq(JSVal::nm(a->b?1:0),b);
    if (b->type==JT::Bool) return jsAbstractEq(a,JSVal::nm(b->b?1:0));
    return false;
}

static bool jsStrictEq(JV a, JV b) {
    if (!a) a=JSVal::undef(); if (!b) b=JSVal::undef();
    if (a->type!=b->type) return false;
    switch(a->type) {
        case JT::Undef: case JT::Null: return true;
        case JT::Bool: return a->b==b->b;
        case JT::Num:  if(isnan(a->n)||isnan(b->n)) return false; return a->n==b->n;
        case JT::Str:  return a->s==b->s;
        default:       return a.get()==b.get();
    }
}

// ENVIRONMENT
struct Env {
    unordered_map<string,JV>   vars;
    unordered_map<string,bool> consts;
    EP parent;
    Env(EP p=nullptr) : parent(p) {}

    JV get(const string& name) const {
        auto it=vars.find(name);
        if (it!=vars.end()) return it->second;
        if (parent) return parent->get(name);
        return JSVal::undef();
    }
    Env* owner(const string& name) {
        if (vars.count(name)) return this;
        if (parent) return parent->owner(name);
        return nullptr;
    }
    void set(const string& name, JV val) {
        Env* o=owner(name);
        if (o) {
            if (o->consts.count(name)&&o->consts[name])
                throw runtime_error("Assignment to constant variable '"+name+"'.");
            o->vars[name]=val;
        } else {
            vars[name]=val;
        }
    }
    void def(const string& name, JV val, bool isC=false) {
        vars[name]=val; consts[name]=isC;
    }
};
static EP mkEnv(EP p=nullptr) { return make_shared<Env>(p); }

// 
// PARSER

class Parser {
    vector<Tok> toks; size_t p=0;

    Tok& cur()          { return toks[p]; }
    Tok& pk2(int n=1)   { size_t i=min(p+n,toks.size()-1); return toks[i]; }
    bool is(TT t)       { return cur().t==t; }
    bool isAny(initializer_list<TT> ts) { for(auto t:ts) if(is(t)) return true; return false; }
    Tok  eat(TT t)      {
        if(!is(t)) throw runtime_error("Parse error: expected token but got '"+cur().v+"' at line "+to_string(cur().ln));
        return toks[p++];
    }
    Tok  adv()          { return toks[p++]; }
    bool match(TT t)    { if(is(t)){p++;return true;} return false; }
    void skipSemi()     { while(match(TT::SEMI)){} }

    // ─── Statements ───────────────────────────────────────────

    NP parseBlock() {
        auto n=mkN(NT::Block); eat(TT::LB);
        while(!is(TT::RB)&&!is(TT::EOFT)) { auto s=parseStmt(); if(s) n->ch.push_back(s); }
        eat(TT::RB); return n;
    }

    NP parseStmt() {
        while(match(TT::SEMI)){}
        if(is(TT::EOFT)||is(TT::RB)) return nullptr;
        if(isAny({TT::LET,TT::CONST,TT::VAR})) return parseVarDecl();
        if(is(TT::FN)&&pk2().t==TT::ID) return parseFnDecl();
        if(is(TT::RET))   return parseRet();
        if(is(TT::BREAK)) { adv(); skipSemi(); return mkN(NT::Brk); }
        if(is(TT::CONT))  { adv(); skipSemi(); return mkN(NT::Ctn); }
        if(is(TT::THROW)) return parseThrow();
        if(is(TT::TRY))   return parseTry();
        if(is(TT::IF))    return parseIf();
        if(is(TT::WHILE)) return parseWhile();
        if(is(TT::FOR))   return parseFor();
        if(is(TT::DO))    return parseDoWhile();
        if(is(TT::SWITCH))return parseSwitch();
        if(is(TT::CLASS)) return parseClass();
        if(is(TT::LB))    return parseBlock();
        // Expression statement
        auto n=mkN(NT::ExprS);
        n->ch.push_back(parseExpr());
        skipSemi(); return n;
    }

    NP parseVarDecl(bool noSemi=false) {
        bool isC=is(TT::CONST); adv();
        auto decl=mkN(NT::VDecl); decl->isConst=isC;
        do {
            NP sub;
            if (is(TT::LA)) {
                // Array destructuring
                sub=mkN(NT::VDecl); sub->str="[d]"; sub->isConst=isC; adv();
                while(!is(TT::RA)&&!is(TT::EOFT)) {
                    if(is(TT::SPREAD)){adv();sub->hasRest=true;sub->restParam=eat(TT::ID).v;break;}
                    if(is(TT::COMMA)){sub->params.push_back("");adv();continue;}
                    if(is(TT::ID)) sub->params.push_back(adv().v);
                    else break;
                    if(!match(TT::COMMA)) break;
                }
                eat(TT::RA);
                if(match(TT::EQ)) sub->ch.push_back(parseAssign());
            } else if (is(TT::LB)) {
                // Object destructuring
                sub=mkN(NT::VDecl); sub->str="{d}"; sub->isConst=isC; adv();
                while(!is(TT::RB)&&!is(TT::EOFT)) {
                    if(is(TT::SPREAD)){adv();sub->restParam=eat(TT::ID).v;sub->hasRest=true;break;}
                    string key;
                    if(is(TT::ID)||is(TT::STR)||is(TT::NUM)) key=adv().v;
                    else { adv(); break; }
                    if(match(TT::COLON)){
                        string nm2=eat(TT::ID).v;
                        sub->params.push_back(key+":"+nm2);
                    } else {
                        sub->params.push_back(key);
                    }
                    if(match(TT::EQ)) parseAssign(); // skip default
                    if(!match(TT::COMMA)) break;
                }
                eat(TT::RB);
                if(match(TT::EQ)) sub->ch.push_back(parseAssign());
            } else {
                sub=mkN(NT::VDecl); sub->str=eat(TT::ID).v; sub->isConst=isC;
                if(match(TT::EQ)) sub->ch.push_back(parseAssign());
            }
            decl->ch.push_back(sub);
        } while(match(TT::COMMA));
        if(!noSemi) skipSemi();
        return decl;
    }

    NP parseFnDecl() {
        eat(TT::FN);
        string name=eat(TT::ID).v;
        auto n=mkN(NT::FDecl); n->str=name;
        parseParamList(n.get());
        n->ch.push_back(parseBlock());
        return n;
    }

    void parseParamList(Node* n) {
        eat(TT::LP);
        while(!is(TT::RP)&&!is(TT::EOFT)) {
            if(is(TT::SPREAD)){adv();n->hasRest=true;n->restParam=eat(TT::ID).v;break;}
            if(is(TT::LB)||is(TT::LA)) {
                // destructuring param – use placeholder name
                string ph="__dp"+to_string(n->params.size())+"__";
                n->params.push_back(ph);
                int d=1; TT cl=(is(TT::LB))?TT::RB:TT::RA;
                TT op=cur().t; adv();
                while(d>0&&!is(TT::EOFT)){
                    if(is(op)) d++; else if(is(cl)) d--;
                    if(d>0) adv(); else adv();
                }
            } else {
                n->params.push_back(eat(TT::ID).v);
            }
            if(match(TT::EQ)) parseAssign(); // skip default value
            if(!match(TT::COMMA)) break;
        }
        eat(TT::RP);
    }

    NP parseRet() {
        eat(TT::RET); auto n=mkN(NT::Ret);
        if(!is(TT::SEMI)&&!is(TT::RB)&&!is(TT::EOFT))
            n->ch.push_back(parseExpr());
        skipSemi(); return n;
    }

    NP parseThrow() {
        eat(TT::THROW); auto n=mkN(NT::Throw);
        n->ch.push_back(parseExpr());
        skipSemi(); return n;
    }

    NP parseTry() {
        eat(TT::TRY); auto n=mkN(NT::Try);
        n->ch.push_back(parseBlock()); // [0]=try body
        if(match(TT::CATCH)) {
            if(match(TT::LP)) { n->str=eat(TT::ID).v; eat(TT::RP); }
            n->ch.push_back(parseBlock()); // [1]=catch body
        } else n->ch.push_back(nullptr);
        if(match(TT::FINALLY)) n->ch.push_back(parseBlock()); // [2]=finally
        else n->ch.push_back(nullptr);
        return n;
    }

    NP parseIf() {
        eat(TT::IF); eat(TT::LP); auto cond=parseExpr(); eat(TT::RP);
        auto n=mkN(NT::If);
        n->ch.push_back(cond);
        n->ch.push_back(parseStmt());
        if(match(TT::ELSE)) n->ch.push_back(parseStmt());
        else n->ch.push_back(nullptr);
        return n;
    }

    NP parseWhile() {
        eat(TT::WHILE); eat(TT::LP); auto cond=parseExpr(); eat(TT::RP);
        auto n=mkN(NT::While); n->ch.push_back(cond); n->ch.push_back(parseStmt());
        return n;
    }

    NP parseFor() {
        eat(TT::FOR); eat(TT::LP);
        // Detect for-of / for-in via look-ahead
        size_t saved=p; bool isOf=false,isIn=false,declared=false; string ivar;
        if(isAny({TT::LET,TT::CONST,TT::VAR})){adv();declared=true;}
        if(is(TT::ID)){ivar=adv().v; if(is(TT::OF))isOf=true; else if(is(TT::IN))isIn=true;}
        if(isOf||isIn) {
            adv(); auto iter=parseExpr(); eat(TT::RP);
            auto body=parseStmt();
            auto n=mkN(isOf?NT::ForOf:NT::ForIn); n->str=ivar; n->flag=declared;
            n->ch.push_back(iter); n->ch.push_back(body); return n;
        }
        p=saved;
        auto n=mkN(NT::For);
        if(!is(TT::SEMI)){
            if(isAny({TT::LET,TT::CONST,TT::VAR})) n->ch.push_back(parseVarDecl(true));
            else { auto es=mkN(NT::ExprS); es->ch.push_back(parseExpr()); n->ch.push_back(es); }
        } else n->ch.push_back(nullptr);
        eat(TT::SEMI);
        if(!is(TT::SEMI)) n->ch.push_back(parseExpr()); else n->ch.push_back(nullptr);
        eat(TT::SEMI);
        if(!is(TT::RP)) n->ch.push_back(parseExpr()); else n->ch.push_back(nullptr);
        eat(TT::RP); n->ch.push_back(parseStmt()); return n;
    }

    NP parseDoWhile() {
        eat(TT::DO); auto n=mkN(NT::DoWhile); n->ch.push_back(parseStmt());
        eat(TT::WHILE); eat(TT::LP); n->ch.push_back(parseExpr()); eat(TT::RP);
        skipSemi(); return n;
    }

    NP parseSwitch() {
        eat(TT::SWITCH); eat(TT::LP); auto disc=parseExpr(); eat(TT::RP); eat(TT::LB);
        auto n=mkN(NT::Switch); n->ch.push_back(disc);
        while(!is(TT::RB)&&!is(TT::EOFT)) {
            auto sc=mkN(NT::SCase);
            if(match(TT::CASE)){sc->ch.push_back(parseExpr());eat(TT::COLON);}
            else {eat(TT::DFL);eat(TT::COLON);sc->isDefault=true;sc->ch.push_back(nullptr);}
            while(!is(TT::CASE)&&!is(TT::DFL)&&!is(TT::RB)&&!is(TT::EOFT)){
                auto s=parseStmt(); if(s) sc->ch.push_back(s);
            }
            n->ch.push_back(sc);
        }
        eat(TT::RB); return n;
    }

    NP parseClass() {
        eat(TT::CLASS);
        string name=is(TT::ID)?adv().v:"";
        string superName="";
        if(match(TT::EXTENDS)&&is(TT::ID)) superName=adv().v;
        eat(TT::LB);
        NP ctorNode=nullptr;
        vector<pair<string,NP>> methods;
        vector<pair<string,NP>> staticMethods;
        while(!is(TT::RB)&&!is(TT::EOFT)){
            bool isStatic=false;
            if(is(TT::ID)&&cur().v=="static"){adv();isStatic=true;}
            if(is(TT::SEMI)){adv();continue;}
            string mname;
            if(is(TT::ID)||is(TT::STR)) mname=adv().v;
            else if(is(TT::NUM)) mname=adv().v;
            else {skipSemi();continue;}
            if(is(TT::LP)) {
                auto fn=mkN(NT::FnEx); fn->str=mname;
                parseParamList(fn.get());
                fn->ch.push_back(parseBlock());
                if(mname=="constructor") ctorNode=fn;
                else if(isStatic) staticMethods.push_back({mname,fn});
                else methods.push_back({mname,fn});
            } else {
                // Property
                if(match(TT::EQ)) parseAssign();
                skipSemi();
            }
        }
        eat(TT::RB);
        // Build a VDecl that holds a constructor FnExpr with prototype methods
        auto vd=mkN(NT::VDecl); vd->str=name;
        NP fn;
        if(ctorNode){ fn=ctorNode; fn->str=name; }
        else { fn=mkN(NT::FnEx); fn->str=name; fn->ch.push_back(mkN(NT::Block)); }
        // Store methods in fn->props so the interpreter can attach them
        fn->props=methods;
        if(!superName.empty()) fn->sval=superName; // super class name
        vd->ch.push_back(fn);
        return vd;
    }

    // ─── Expressions ──────────────────────────────────────────

    NP parseExpr() {
        auto e=parseAssign();
        // Sequence expressions (rare outside for-init) – ignore for simplicity
        return e;
    }

    NP parseAssign() {
        auto lhs=parseCond();
        static const set<TT> ops={TT::EQ,TT::PLUSA,TT::MINUSA,TT::STARA,TT::SLA,TT::MODA};
        if(ops.count(cur().t)){
            string op=adv().v; auto rhs=parseAssign();
            auto n=mkN(NT::Asn); n->str=op; n->ch.push_back(lhs); n->ch.push_back(rhs);
            return n;
        }
        return lhs;
    }

    NP parseCond() {
        auto c=parseNullCoal();
        if(match(TT::QUES)){
            auto t=parseAssign(); eat(TT::COLON); auto f=parseAssign();
            auto n=mkN(NT::Cond); n->ch={c,t,f}; return n;
        }
        return c;
    }

    NP parseNullCoal(){
        auto lhs=parseOr();
        while(is(TT::NULLISH)){adv();auto rhs=parseOr();auto n=mkN(NT::Log);n->str="??";n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseOr(){
        auto lhs=parseAnd();
        while(is(TT::OR)){adv();auto rhs=parseAnd();auto n=mkN(NT::Log);n->str="||";n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseAnd(){
        auto lhs=parseBitOr();
        while(is(TT::AND)){adv();auto rhs=parseBitOr();auto n=mkN(NT::Log);n->str="&&";n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseBitOr(){
        auto lhs=parseBitXor();
        while(is(TT::BOR)){string op=adv().v;auto rhs=parseBitXor();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseBitXor(){
        auto lhs=parseBitAnd();
        while(is(TT::BXOR)){string op=adv().v;auto rhs=parseBitAnd();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseBitAnd(){
        auto lhs=parseEq();
        while(is(TT::BAND)){string op=adv().v;auto rhs=parseEq();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseEq(){
        auto lhs=parseRel();
        while(isAny({TT::EQ2,TT::EQ3,TT::NE1,TT::NE2})){string op=adv().v;auto rhs=parseRel();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseRel(){
        auto lhs=parseShift();
        while(isAny({TT::LT,TT::GT,TT::LE,TT::GE,TT::IN})){string op=adv().v;auto rhs=parseShift();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseShift(){
        auto lhs=parseAdd();
        while(isAny({TT::SHL,TT::SHR,TT::USHR})){string op=adv().v;auto rhs=parseAdd();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseAdd(){
        auto lhs=parseMul();
        while(isAny({TT::PLUS,TT::MINUS})){string op=adv().v;auto rhs=parseMul();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parseMul(){
        auto lhs=parsePow();
        while(isAny({TT::STAR,TT::SL,TT::MOD})){string op=adv().v;auto rhs=parsePow();auto n=mkN(NT::Bin);n->str=op;n->ch={lhs,rhs};lhs=n;}
        return lhs;
    }
    NP parsePow(){
        auto base=parseUnary();
        if(is(TT::POW)){adv();auto exp=parsePow();auto n=mkN(NT::Bin);n->str="**";n->ch={base,exp};return n;}
        return base;
    }
    NP parseUnary(){
        if(is(TT::NOT)){adv();auto n=mkN(NT::Un);n->str="!";n->ch.push_back(parseUnary());return n;}
        if(is(TT::MINUS)){adv();auto n=mkN(NT::Un);n->str="-";n->ch.push_back(parseUnary());return n;}
        if(is(TT::PLUS)){adv();auto n=mkN(NT::Un);n->str="+";n->ch.push_back(parseUnary());return n;}
        if(is(TT::BNOT)){adv();auto n=mkN(NT::Un);n->str="~";n->ch.push_back(parseUnary());return n;}
        if(is(TT::TYPEOF)){adv();auto n=mkN(NT::Typeof);n->ch.push_back(parseUnary());return n;}
        if(is(TT::VOID)){adv();auto n=mkN(NT::Un);n->str="void";n->ch.push_back(parseUnary());return n;}
        if(is(TT::INC)){adv();auto n=mkN(NT::Upd);n->str="++";n->flag=true;n->ch.push_back(parseUnary());return n;}
        if(is(TT::DEC)){adv();auto n=mkN(NT::Upd);n->str="--";n->flag=true;n->ch.push_back(parseUnary());return n;}
        if(is(TT::NEW)) return parseNew();
        return parsePostfix();
    }
    NP parseNew(){
        eat(TT::NEW); auto n=mkN(NT::New_);
        if(is(TT::NEW)) n->ch.push_back(parseNew());
        else {
            auto callee=parsePrimaryNoCall();
            // Allow member access before args
            while(is(TT::DOT)||is(TT::LA)) {
                if(match(TT::DOT)){string pr=(is(TT::ID)||isAny({TT::LET,TT::CONST,TT::VAR,TT::FN,TT::RET,TT::IF,TT::ELSE,TT::TYPEOF}))?adv().v:adv().v;auto m=mkN(NT::Mem);m->str=pr;m->ch.push_back(callee);callee=m;}
                else{eat(TT::LA);auto idx=mkN(NT::Idx);idx->ch.push_back(callee);idx->ch.push_back(parseExpr());eat(TT::RA);callee=idx;}
            }
            n->ch.push_back(callee);
        }
        if(is(TT::LP)){eat(TT::LP);while(!is(TT::RP)&&!is(TT::EOFT)){if(is(TT::SPREAD)){adv();auto s=mkN(NT::Spread);s->ch.push_back(parseAssign());n->ch.push_back(s);}else n->ch.push_back(parseAssign());if(!match(TT::COMMA))break;}eat(TT::RP);}
        return n;
    }
    NP parsePostfix(){
        auto e=parseCallExpr();
        if(is(TT::INC)){adv();auto n=mkN(NT::Upd);n->str="++";n->flag=false;n->ch.push_back(e);return n;}
        if(is(TT::DEC)){adv();auto n=mkN(NT::Upd);n->str="--";n->flag=false;n->ch.push_back(e);return n;}
        return e;
    }
    NP parseCallExpr(){
        auto callee=parsePrimary();
        while(true){
            if(is(TT::DOT)){
                adv(); string prop=adv().v;
                auto m=mkN(NT::Mem); m->str=prop; m->ch.push_back(callee); callee=m;
            } else if(is(TT::LA)){
                eat(TT::LA); auto idx=mkN(NT::Idx); idx->ch.push_back(callee);
                idx->ch.push_back(parseExpr()); eat(TT::RA); callee=idx;
            } else if(is(TT::LP)){
                eat(TT::LP); auto call=mkN(NT::Call); call->ch.push_back(callee);
                while(!is(TT::RP)&&!is(TT::EOFT)){
                    if(is(TT::SPREAD)){adv();auto s=mkN(NT::Spread);s->ch.push_back(parseAssign());call->ch.push_back(s);}
                    else call->ch.push_back(parseAssign());
                    if(!match(TT::COMMA)) break;
                }
                eat(TT::RP); callee=call;
            } else break;
        }
        return callee;
    }

    NP parsePrimaryNoCall() {
        // Like parsePrimary but no call/member chaining
        if(is(TT::FN)){adv();auto n=mkN(NT::FnEx);if(is(TT::ID))n->str=adv().v;parseParamList(n.get());n->ch.push_back(parseBlock());return n;}
        if(is(TT::ID)){auto n=mkN(NT::Id);n->str=adv().v;return n;}
        return parsePrimary();
    }

    NP parsePrimary() {
        // Arrow: id => ...
        if(is(TT::ID)&&pk2().t==TT::ARROW){
            string pn=adv().v; adv();
            auto n=mkN(NT::Arrow); n->params.push_back(pn);
            if(is(TT::LB)) n->ch.push_back(parseBlock());
            else {
                // Wrap expr-body in Block containing Ret
                auto body=mkN(NT::Ret); body->ch.push_back(parseAssign());
                auto blk=mkN(NT::Block); blk->ch.push_back(body);
                n->ch.push_back(blk);
            }
            return n;
        }
        if(is(TT::NUM)){
            auto n=mkN(NT::Lit); n->str="num"; n->sval=cur().v;
            string sv=cur().v; adv();
            if(sv.size()>2&&sv[0]=='0'&&(sv[1]=='x'||sv[1]=='X')) n->num=(double)stoull(sv,nullptr,16);
            else n->num=stod(sv);
            return n;
        }
        if(is(TT::STR)){auto n=mkN(NT::Lit);n->str="str";n->sval=adv().v;return n;}
        if(is(TT::BOOL)){auto n=mkN(NT::Lit);n->str="bool";n->flag=(cur().v=="true");adv();return n;}
        if(is(TT::NIL)) {adv();auto n=mkN(NT::Lit);n->str="null";return n;}
        if(is(TT::UNDEF)){adv();auto n=mkN(NT::Lit);n->str="undef";return n;}
        if(is(TT::TMPL)){auto n=mkN(NT::Tmpl);n->sval=adv().v;return n;}
        if(is(TT::THIS)){adv();auto n=mkN(NT::Id);n->str="this";return n;}
        if(is(TT::FN)){
            adv(); auto n=mkN(NT::FnEx);
            if(is(TT::ID)) n->str=adv().v;
            parseParamList(n.get());
            n->ch.push_back(parseBlock());
            return n;
        }
        if(is(TT::LP)){
            adv();
            // Look for ) => pattern (arrow function)
            size_t scanP=p; int depth=1; bool couldArrow=true;
            while(scanP<toks.size()&&depth>0){
                if(toks[scanP].t==TT::LP) depth++;
                else if(toks[scanP].t==TT::RP){depth--;if(depth==0){scanP++;break;}}
                else if(toks[scanP].t==TT::SEMI||toks[scanP].t==TT::LB){couldArrow=false;break;}
                scanP++;
            }
            if(couldArrow&&scanP<toks.size()&&toks[scanP].t==TT::ARROW){
                // Parse as arrow function
                auto n=mkN(NT::Arrow);
                while(!is(TT::RP)&&!is(TT::EOFT)){
                    if(is(TT::SPREAD)){adv();n->hasRest=true;n->restParam=eat(TT::ID).v;break;}
                    n->params.push_back(eat(TT::ID).v);
                    if(match(TT::EQ)) parseAssign(); // skip default
                    if(!match(TT::COMMA)) break;
                }
                eat(TT::RP); eat(TT::ARROW);
                if(is(TT::LB)) n->ch.push_back(parseBlock());
                else {
                    auto body=mkN(NT::Ret); body->ch.push_back(parseAssign());
                    auto blk=mkN(NT::Block); blk->ch.push_back(body);
                    n->ch.push_back(blk);
                }
                return n;
            }
            auto e=parseExpr(); eat(TT::RP); return e;
        }
        if(is(TT::LA)){
            adv(); auto n=mkN(NT::ArrL);
            while(!is(TT::RA)&&!is(TT::EOFT)){
                if(is(TT::COMMA)){n->ch.push_back(nullptr);adv();continue;}
                if(is(TT::SPREAD)){adv();auto s=mkN(NT::Spread);s->ch.push_back(parseAssign());n->ch.push_back(s);}
                else n->ch.push_back(parseAssign());
                if(!match(TT::COMMA)) break;
            }
            eat(TT::RA); return n;
        }
        if(is(TT::LB)){
            adv(); auto n=mkN(NT::ObjL);
            while(!is(TT::RB)&&!is(TT::EOFT)){
                if(is(TT::SPREAD)){adv();auto s=mkN(NT::Spread);s->ch.push_back(parseAssign());n->ch.push_back(s);}
                else {
                    if(is(TT::LA)){
                        // Computed property [expr]: val
                        adv(); auto ke=parseAssign(); eat(TT::RA);
                        eat(TT::COLON); auto val=parseAssign();
                        auto comp=mkN(NT::ArrL); comp->ch.push_back(ke); comp->ch.push_back(val);
                        comp->computed=true;
                        n->ch.push_back(comp);
                    } else {
                        string key;
                        if(is(TT::STR)||is(TT::NUM)) key=adv().v;
                        else key=adv().v;
                        if(match(TT::COLON)){n->props.push_back({key,parseAssign()});}
                        else if(is(TT::LP)){
                            // Method shorthand
                            auto fn=mkN(NT::FnEx); fn->str=key;
                            parseParamList(fn.get()); fn->ch.push_back(parseBlock());
                            n->props.push_back({key,fn});
                        } else {
                            // Shorthand {x} = {x:x}
                            auto id=mkN(NT::Id); id->str=key;
                            n->props.push_back({key,id});
                        }
                    }
                }
                if(!match(TT::COMMA)) break;
            }
            eat(TT::RB); return n;
        }
        if(is(TT::ID)){auto n=mkN(NT::Id);n->str=adv().v;return n;}
        throw runtime_error("Unexpected token '"+cur().v+"' at line "+to_string(cur().ln));
    }

public:
    Parser(vector<Tok> t) : toks(move(t)) {}
    NP parse() {
        auto prog=mkN(NT::Prog);
        while(!is(TT::EOFT)){ auto s=parseStmt(); if(s) prog->ch.push_back(s); }
        return prog;
    }
};

// INTERPRETER — control-flow signals via exceptions
struct RetSig  { JV val; };
struct BrkSig  {};
struct CtnSig  {};
struct ThrSig  { JV val; };

class Interp {
    EP global;
    default_random_engine rng{(unsigned)time(nullptr)};

    // ─── Built-in helpers ─────────────────────────────────────
    JV makeFn(string name, function<JV(vector<JV>,JV,EP)> fn) {
        auto f=make_shared<JsFn>();
        f->name=name; f->isNative=true; f->native=move(fn);
        return JSVal::fn_(f);
    }

    // Helper: get/set an LHS node value
    pair<JV*,JV> getLhs(NP node, EP env) {
        // Returns {pointer-to-slot, object} for assignment
        // We'll handle set separately
        return {nullptr, JSVal::undef()};
    }

    void assignLhs(NP lhs, JV val, EP env) {
        if(lhs->type==NT::Id) {
            env->set(lhs->str, val);
        } else if(lhs->type==NT::Mem) {
            JV obj=eval(lhs->ch[0],env);
            if(obj->type==JT::Arr) {
                obj->setProp(lhs->str, val);
                // Also handle 'length' setting
            } else obj->setProp(lhs->str, val);
        } else if(lhs->type==NT::Idx) {
            JV obj=eval(lhs->ch[0],env);
            JV idx=eval(lhs->ch[1],env);
            string k=jsStr(idx);
            if(obj->type==JT::Arr) {
                // numeric index
                double n=jsNum(idx);
                if(!isnan(n)&&n>=0&&n==(long long)n) {
                    size_t i=(size_t)(long long)n;
                    while(obj->arr->size()<=i) obj->arr->push_back(JSVal::undef());
                    (*obj->arr)[i]=val;
                    // update length
                    return;
                }
                obj->setProp(k,val);
            } else obj->setProp(k,val);
        }
    }

    // ─── Template literal evaluation ──────────────────────────
    JV evalTemplate(const string& tmpl, EP env) {
        string result;
        size_t i=0;
        while(i<tmpl.size()) {
            if(tmpl[i]=='$'&&i+1<tmpl.size()&&tmpl[i+1]=='{') {
                i+=2; // skip ${
                // find matching }
                int depth=1; string expr;
                while(i<tmpl.size()&&depth>0) {
                    if(tmpl[i]=='{') depth++;
                    else if(tmpl[i]=='}'){depth--;if(depth==0){i++;break;}}
                    if(depth>0) expr+=tmpl[i++];
                }
                // Parse and evaluate the expression
                try {
                    Lexer lex(expr);
                    auto toks=lex.tokenize();
                    Parser par(toks);
                    auto ast=par.parse();
                    JV val=JSVal::undef();
                    for(auto& s:ast->ch) val=eval(s,env);
                    result+=jsStr(val);
                } catch(...) { result+=expr; }
            } else {
                result+=tmpl[i++];
            }
        }
        return JSVal::st(result);
    }

    // ─── String built-in methods ──────────────────────────────
    JV stringMethod(const string& str, const string& method, vector<JV> args, EP env) {
        if(method=="length") return JSVal::nm(str.size());
        if(method=="toUpperCase"||method=="toLocaleUpperCase") {
            string r=str; for(auto& c:r) c=toupper(c); return JSVal::st(r);
        }
        if(method=="toLowerCase"||method=="toLocaleLowerCase") {
            string r=str; for(auto& c:r) c=tolower(c); return JSVal::st(r);
        }
        if(method=="trim") {
            string r=str;
            size_t a=r.find_first_not_of(" \t\n\r\f\v");
            size_t b=r.find_last_not_of(" \t\n\r\f\v");
            if(a==string::npos) return JSVal::st("");
            return JSVal::st(r.substr(a,b-a+1));
        }
        if(method=="trimStart"||method=="trimLeft") {
            string r=str; size_t a=r.find_first_not_of(" \t\n\r\f\v");
            return JSVal::st(a==string::npos?"":r.substr(a));
        }
        if(method=="trimEnd"||method=="trimRight") {
            string r=str; size_t b=r.find_last_not_of(" \t\n\r\f\v");
            return JSVal::st(b==string::npos?"":r.substr(0,b+1));
        }
        if(method=="charAt") {
            int idx=args.empty()?0:(int)jsNum(args[0]);
            if(idx<0||idx>=(int)str.size()) return JSVal::st("");
            return JSVal::st(string(1,str[idx]));
        }
        if(method=="charCodeAt") {
            int idx=args.empty()?0:(int)jsNum(args[0]);
            if(idx<0||idx>=(int)str.size()) return JSVal::nm(numeric_limits<double>::quiet_NaN());
            return JSVal::nm((unsigned char)str[idx]);
        }
        if(method=="codePointAt") {
            int idx=args.empty()?0:(int)jsNum(args[0]);
            if(idx<0||idx>=(int)str.size()) return JSVal::undef();
            return JSVal::nm((unsigned char)str[idx]);
        }
        if(method=="indexOf") {
            if(args.empty()) return JSVal::nm(-1);
            string sub=jsStr(args[0]);
            int from=args.size()>1?(int)jsNum(args[1]):0;
            if(from<0) from=0;
            size_t pos=str.find(sub,from);
            return JSVal::nm(pos==string::npos?-1:(double)pos);
        }
        if(method=="lastIndexOf") {
            if(args.empty()) return JSVal::nm(-1);
            string sub=jsStr(args[0]);
            size_t from=args.size()>1?(size_t)jsNum(args[1]):str.size();
            size_t pos=str.rfind(sub,from);
            return JSVal::nm(pos==string::npos?-1:(double)pos);
        }
        if(method=="includes") {
            if(args.empty()) return JSVal::bl(false);
            return JSVal::bl(str.find(jsStr(args[0]))!=string::npos);
        }
        if(method=="startsWith") {
            if(args.empty()) return JSVal::bl(false);
            string sub=jsStr(args[0]);
            int start=args.size()>1?(int)jsNum(args[1]):0;
            if(start<0) start=0;
            return JSVal::bl(str.substr(start).find(sub)==0);
        }
        if(method=="endsWith") {
            if(args.empty()) return JSVal::bl(false);
            string sub=jsStr(args[0]);
            int len=args.size()>1?(int)jsNum(args[1]):(int)str.size();
            if(len>(int)str.size()) len=str.size();
            if((int)sub.size()>len) return JSVal::bl(false);
            return JSVal::bl(str.substr(0,len).rfind(sub)==(size_t)(len-(int)sub.size()));
        }
        if(method=="slice") {
            int len=(int)str.size();
            int start=args.empty()?0:(int)jsNum(args[0]);
            int end=args.size()>1?(int)jsNum(args[1]):len;
            if(start<0) start=max(0,len+start);
            if(end<0)   end=max(0,len+end);
            if(start>=len||start>=end) return JSVal::st("");
            return JSVal::st(str.substr(start,end-start));
        }
        if(method=="substring") {
            int len=(int)str.size();
            int start=args.empty()?0:(int)jsNum(args[0]);
            int end=args.size()>1?(int)jsNum(args[1]):len;
            if(start<0) start=0; if(end<0) end=0;
            if(start>len) start=len; if(end>len) end=len;
            if(start>end) swap(start,end);
            return JSVal::st(str.substr(start,end-start));
        }
        if(method=="substr") {
            int len=(int)str.size();
            int start=args.empty()?0:(int)jsNum(args[0]);
            if(start<0) start=max(0,len+start);
            int length=args.size()>1?(int)jsNum(args[1]):len-start;
            if(length<0) return JSVal::st("");
            return JSVal::st(str.substr(start,length));
        }
        if(method=="split") {
            auto arr=JSVal::ar();
            if(args.empty()||args[0]->type==JT::Undef){arr->arr->push_back(JSVal::st(str));return arr;}
            string delim=jsStr(args[0]);
            if(delim.empty()){for(char c:str) arr->arr->push_back(JSVal::st(string(1,c)));return arr;}
            string s=str; size_t pos;
            while((pos=s.find(delim))!=string::npos){arr->arr->push_back(JSVal::st(s.substr(0,pos)));s=s.substr(pos+delim.size());}
            arr->arr->push_back(JSVal::st(s));
            return arr;
        }
        if(method=="replace") {
            if(args.size()<2) return JSVal::st(str);
            string from=jsStr(args[0]); string to=jsStr(args[1]);
            string r=str;
            size_t pos=r.find(from);
            if(pos!=string::npos) r.replace(pos,from.size(),to);
            return JSVal::st(r);
        }
        if(method=="replaceAll") {
            if(args.size()<2) return JSVal::st(str);
            string from=jsStr(args[0]); string to=jsStr(args[1]);
            string r=str; size_t pos=0;
            while((pos=r.find(from,pos))!=string::npos){r.replace(pos,from.size(),to);pos+=to.size();}
            return JSVal::st(r);
        }
        if(method=="repeat") {
            int count=args.empty()?0:(int)jsNum(args[0]);
            if(count<=0) return JSVal::st("");
            string r; for(int i=0;i<count;i++) r+=str;
            return JSVal::st(r);
        }
        if(method=="padStart") {
            int targetLen=args.empty()?0:(int)jsNum(args[0]);
            string pad=args.size()>1?jsStr(args[1]):" ";
            if((int)str.size()>=targetLen) return JSVal::st(str);
            string r; int need=targetLen-str.size();
            while((int)r.size()<need) r+=pad;
            return JSVal::st(r.substr(0,need)+str);
        }
        if(method=="padEnd") {
            int targetLen=args.empty()?0:(int)jsNum(args[0]);
            string pad=args.size()>1?jsStr(args[1]):" ";
            if((int)str.size()>=targetLen) return JSVal::st(str);
            string r=str; int need=targetLen-str.size();
            string p; while((int)p.size()<need) p+=pad;
            return JSVal::st(r+p.substr(0,need));
        }
        if(method=="concat") {
            string r=str; for(auto& a:args) r+=jsStr(a); return JSVal::st(r);
        }
        if(method=="at") {
            int idx=args.empty()?0:(int)jsNum(args[0]);
            if(idx<0) idx=(int)str.size()+idx;
            if(idx<0||idx>=(int)str.size()) return JSVal::undef();
            return JSVal::st(string(1,str[idx]));
        }
        if(method=="match"||method=="matchAll") return JSVal::null_();
        return JSVal::undef();
    }

    // ─── Array built-in methods ───────────────────────────────
    JV arrayMethod(JV arrObj, const string& method, vector<JV> args, EP env) {
        auto& arr=*arrObj->arr;
        if(method=="length") return JSVal::nm(arr.size());
        if(method=="push") {
            for(auto& a:args) arr.push_back(a);
            return JSVal::nm(arr.size());
        }
        if(method=="pop") {
            if(arr.empty()) return JSVal::undef();
            auto v=arr.back(); arr.pop_back(); return v;
        }
        if(method=="shift") {
            if(arr.empty()) return JSVal::undef();
            auto v=arr.front(); arr.erase(arr.begin()); return v;
        }
        if(method=="unshift") {
            arr.insert(arr.begin(),args.begin(),args.end());
            return JSVal::nm(arr.size());
        }
        if(method=="reverse") {
            reverse(arr.begin(),arr.end()); return arrObj;
        }
        if(method=="join") {
            string sep=args.empty()?",":(args[0]->type==JT::Undef?",":jsStr(args[0]));
            string r;
            for(size_t i=0;i<arr.size();i++){
                if(i) r+=sep;
                if(arr[i]&&arr[i]->type!=JT::Null&&arr[i]->type!=JT::Undef) r+=jsStr(arr[i]);
            }
            return JSVal::st(r);
        }
        if(method=="slice") {
            int len=(int)arr.size();
            int start=args.empty()?0:(int)jsNum(args[0]);
            int end=args.size()>1?(int)jsNum(args[1]):len;
            if(start<0) start=max(0,len+start);
            if(end<0)   end=max(0,len+end);
            if(start>=len||start>=end){return JSVal::ar();}
            auto res=JSVal::ar();
            for(int i=start;i<min(end,len);i++) res->arr->push_back(arr[i]);
            return res;
        }
        if(method=="splice") {
            int len=(int)arr.size();
            int start=args.empty()?0:(int)jsNum(args[0]);
            if(start<0) start=max(0,len+start);
            if(start>len) start=len;
            int delCount=args.size()<2?len-start:(int)jsNum(args[1]);
            if(delCount<0) delCount=0;
            if(delCount>len-start) delCount=len-start;
            auto removed=JSVal::ar();
            for(int i=0;i<delCount;i++) removed->arr->push_back(arr[start+i]);
            arr.erase(arr.begin()+start,arr.begin()+start+delCount);
            vector<JV> inserts(args.begin()+(args.size()<2?1:2),args.end());
            arr.insert(arr.begin()+start,inserts.begin(),inserts.end());
            return removed;
        }
        if(method=="concat") {
            auto res=JSVal::ar();
            for(auto& e:arr) res->arr->push_back(e);
            for(auto& a:args) {
                if(a->type==JT::Arr) for(auto& e:*a->arr) res->arr->push_back(e);
                else res->arr->push_back(a);
            }
            return res;
        }
        if(method=="indexOf") {
            if(args.empty()) return JSVal::nm(-1);
            JV target=args[0]; int from=args.size()>1?(int)jsNum(args[1]):0;
            if(from<0) from=max(0,(int)arr.size()+from);
            for(int i=from;i<(int)arr.size();i++) if(jsStrictEq(arr[i],target)) return JSVal::nm(i);
            return JSVal::nm(-1);
        }
        if(method=="lastIndexOf") {
            if(args.empty()) return JSVal::nm(-1);
            JV target=args[0]; int from=args.size()>1?(int)jsNum(args[1]):(int)arr.size()-1;
            if(from<0) from=(int)arr.size()+from;
            if(from>=(int)arr.size()) from=(int)arr.size()-1;
            for(int i=from;i>=0;i--) if(jsStrictEq(arr[i],target)) return JSVal::nm(i);
            return JSVal::nm(-1);
        }
        if(method=="includes") {
            if(args.empty()) return JSVal::bl(false);
            JV target=args[0];
            for(auto& e:arr) if(jsAbstractEq(e,target)) return JSVal::bl(true);
            return JSVal::bl(false);
        }
        if(method=="find") {
            if(args.empty()) return JSVal::undef();
            JV fn=args[0];
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(jsBool(r)) return arr[i];
            }
            return JSVal::undef();
        }
        if(method=="findIndex") {
            if(args.empty()) return JSVal::nm(-1);
            JV fn=args[0];
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(jsBool(r)) return JSVal::nm(i);
            }
            return JSVal::nm(-1);
        }
        if(method=="filter") {
            if(args.empty()) return JSVal::ar();
            JV fn=args[0]; auto res=JSVal::ar();
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(jsBool(r)) res->arr->push_back(arr[i]);
            }
            return res;
        }
        if(method=="map") {
            if(args.empty()) return JSVal::ar();
            JV fn=args[0]; auto res=JSVal::ar();
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                res->arr->push_back(r);
            }
            return res;
        }
        if(method=="reduce") {
            if(args.empty()||arr.empty()) return JSVal::undef();
            JV fn=args[0]; JV acc;
            size_t start=0;
            if(args.size()>1) acc=args[1];
            else { acc=arr[0]; start=1; }
            for(size_t i=start;i<arr.size();i++)
                acc=callFn(fn,{acc,arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
            return acc;
        }
        if(method=="reduceRight") {
            if(args.empty()||arr.empty()) return JSVal::undef();
            JV fn=args[0]; JV acc;
            int start=(int)arr.size()-1;
            if(args.size()>1) acc=args[1];
            else { acc=arr[start--]; }
            for(int i=start;i>=0;i--)
                acc=callFn(fn,{acc,arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
            return acc;
        }
        if(method=="forEach") {
            if(args.empty()) return JSVal::undef();
            JV fn=args[0];
            for(size_t i=0;i<arr.size();i++)
                callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
            return JSVal::undef();
        }
        if(method=="some") {
            if(args.empty()) return JSVal::bl(false);
            JV fn=args[0];
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(jsBool(r)) return JSVal::bl(true);
            }
            return JSVal::bl(false);
        }
        if(method=="every") {
            if(args.empty()) return JSVal::bl(false);
            JV fn=args[0];
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(!jsBool(r)) return JSVal::bl(false);
            }
            return JSVal::bl(true);
        }
        if(method=="flat") {
            int depth=args.empty()?1:(int)jsNum(args[0]);
            auto res=JSVal::ar();
            function<void(JV,int)> flatten=[&](JV v,int d){
                if(v&&v->type==JT::Arr&&d>0)
                    for(auto& e:*v->arr) flatten(e,d-1);
                else res->arr->push_back(v);
            };
            for(auto& e:arr) flatten(e,depth);
            return res;
        }
        if(method=="flatMap") {
            if(args.empty()) return JSVal::ar();
            JV fn=args[0]; auto res=JSVal::ar();
            for(size_t i=0;i<arr.size();i++){
                JV r=callFn(fn,{arr[i],JSVal::nm(i),arrObj},JSVal::undef(),env);
                if(r&&r->type==JT::Arr) for(auto& e:*r->arr) res->arr->push_back(e);
                else res->arr->push_back(r);
            }
            return res;
        }
        if(method=="sort") {
            JV cmpFn=args.empty()?JSVal::undef():args[0];
            sort(arr.begin(),arr.end(),[&](JV a,JV b)->bool{
                if(cmpFn&&cmpFn->type==JT::Fn){
                    JV r=callFn(cmpFn,{a,b},JSVal::undef(),env);
                    return jsNum(r)<0;
                }
                return jsStr(a)<jsStr(b);
            });
            return arrObj;
        }
        if(method=="fill") {
            JV val=args.empty()?JSVal::undef():args[0];
            int len=(int)arr.size();
            int start=args.size()>1?(int)jsNum(args[1]):0;
            int end=args.size()>2?(int)jsNum(args[2]):len;
            if(start<0) start=max(0,len+start);
            if(end<0)   end=max(0,len+end);
            for(int i=start;i<min(end,len);i++) arr[i]=val;
            return arrObj;
        }
        if(method=="keys") {
            auto res=JSVal::ar();
            for(size_t i=0;i<arr.size();i++) res->arr->push_back(JSVal::nm(i));
            return res;
        }
        if(method=="values") {
            auto res=JSVal::ar();
            for(auto& e:arr) res->arr->push_back(e);
            return res;
        }
        if(method=="entries") {
            auto res=JSVal::ar();
            for(size_t i=0;i<arr.size();i++){
                auto pair=JSVal::ar();
                pair->arr->push_back(JSVal::nm(i));
                pair->arr->push_back(arr[i]);
                res->arr->push_back(pair);
            }
            return res;
        }
        if(method=="toString") { return JSVal::st(arrToStr(arrObj)); }
        if(method=="at") {
            int idx=args.empty()?0:(int)jsNum(args[0]);
            if(idx<0) idx=(int)arr.size()+idx;
            if(idx<0||idx>=(int)arr.size()) return JSVal::undef();
            return arr[idx];
        }
        if(method=="copyWithin") { return arrObj; } // simplified
        return JSVal::undef();
    }

    // ─── Call a function value ─────────────────────────────────
    JV callFn(JV fnVal, vector<JV> args, JV thisVal, EP env) {
        if(!fnVal||fnVal->type!=JT::Fn) throw runtime_error("Not a function: "+jsStr(fnVal));
        auto& fn=*fnVal->fn;
        if(fn.isNative) return fn.native(args,thisVal,env);

        // User-defined function
        EP fenv=mkEnv(fn.closure);
        fenv->def("this", fn.isArrow ? env->get("this") : (thisVal?thisVal:JSVal::undef()));
        fenv->def("arguments", JSVal::undef());

        // Bind parameters
        for(size_t i=0;i<fn.params.size();i++)
            fenv->def(fn.params[i], i<args.size()?args[i]:JSVal::undef());
        if(fn.hasRest) {
            auto rest=JSVal::ar();
            size_t start=fn.params.size();
            for(size_t i=start;i<args.size();i++) rest->arr->push_back(args[i]);
            fenv->def(fn.restParam, rest);
        }
        // Hoist function declarations
        hoistFunctions(fn.body, fenv);
        try {
            execBlock(fn.body, fenv);
            return JSVal::undef();
        } catch(RetSig& r) { return r.val; }
    }

    // Hoist all function declarations to top of scope
    void hoistFunctions(NP block, EP env) {
        if(!block) return;
        for(auto& stmt:block->ch) {
            if(!stmt) continue;
            if(stmt->type==NT::FDecl) {
                auto fn=makeFunction(stmt->str, stmt->params, stmt->hasRest,
                                     stmt->restParam, stmt->ch[0], env, false);
                env->def(stmt->str, fn);
            }
        }
    }

    JV makeFunction(const string& name, vector<string> params, bool hasRest,
                    string restParam, NP body, EP closure, bool isArrow) {
        auto f=make_shared<JsFn>();
        f->name=name; f->params=params; f->hasRest=hasRest;
        f->restParam=restParam; f->body=body; f->closure=closure;
        f->isArrow=isArrow; f->isNative=false;
        return JSVal::fn_(f);
    }

    // ─── Statement execution ──────────────────────────────────
    void execBlock(NP block, EP env) {
        if(!block) return;
        for(auto& stmt:block->ch) {
            if(!stmt) continue;
            execStmt(stmt, env);
        }
    }

    void execStmt(NP n, EP env) {
        if(!n) return;
        switch(n->type) {
        case NT::Block:   execBlock(n, env); break;
        case NT::ExprS:   eval(n->ch[0], env); break;
        case NT::VDecl:   execVDecl(n, env); break;
        case NT::FDecl: {
            auto fn=makeFunction(n->str, n->params, n->hasRest,
                                 n->restParam, n->ch[0], env, false);
            env->def(n->str, fn);
            break;
        }
        case NT::Ret: {
            JV val=n->ch.empty()?JSVal::undef():eval(n->ch[0],env);
            throw RetSig{val};
        }
        case NT::Brk: throw BrkSig{};
        case NT::Ctn: throw CtnSig{};
        case NT::Throw: {
            JV val=eval(n->ch[0],env);
            throw ThrSig{val};
        }
        case NT::Try: {
            try { execBlock(n->ch[0], env); }
            catch(ThrSig& t) {
                if(n->ch.size()>1&&n->ch[1]) {
                    EP cenv=mkEnv(env);
                    if(!n->str.empty()) cenv->def(n->str, t.val);
                    execBlock(n->ch[1], cenv);
                } else throw;
            }
            if(n->ch.size()>2&&n->ch[2]) execBlock(n->ch[2], env);
            break;
        }
        case NT::If: {
            bool cond=jsBool(eval(n->ch[0],env));
            if(cond) execStmt(n->ch[1],env);
            else if(n->ch.size()>2&&n->ch[2]) execStmt(n->ch[2],env);
            break;
        }
        case NT::While: {
            while(jsBool(eval(n->ch[0],env))) {
                try { execStmt(n->ch[1],env); }
                catch(BrkSig&) { break; }
                catch(CtnSig&) {}
            }
            break;
        }
        case NT::DoWhile: {
            do {
                try { execStmt(n->ch[0],env); }
                catch(BrkSig&) { break; }
                catch(CtnSig&) {}
            } while(jsBool(eval(n->ch[1],env)));
            break;
        }
        case NT::For: {
            EP fenv=mkEnv(env);
            if(n->ch[0]) execStmt(n->ch[0],fenv);
            while(true) {
                if(n->ch[1]&&!jsBool(eval(n->ch[1],fenv))) break;
                try { execStmt(n->ch[3],fenv); }
                catch(BrkSig&) { break; }
                catch(CtnSig&) {}
                if(n->ch[2]) eval(n->ch[2],fenv);
            }
            break;
        }
        case NT::ForOf: {
            JV iter=eval(n->ch[0],env);
            EP lenv=mkEnv(env);
            if(n->flag) lenv->def(n->str, JSVal::undef());
            auto doIter=[&](JV elem){
                if(n->flag) lenv->set(n->str, elem);
                else        env->set(n->str, elem);
                try { execStmt(n->ch[1],lenv); }
                catch(BrkSig&) { throw; }
                catch(CtnSig&) {}
            };
            try {
                if(iter&&iter->type==JT::Arr) {
                    for(auto& e:*iter->arr) doIter(e);
                } else if(iter&&iter->type==JT::Str) {
                    for(char c:iter->s) doIter(JSVal::st(string(1,c)));
                } else if(iter&&iter->type==JT::Obj) {
                    if(iter->keys)for(auto& k:*iter->keys){
                        if(iter->props->count(k)) doIter((*iter->props)[k]);
                    }
                }
            } catch(BrkSig&) {}
            break;
        }
        case NT::ForIn: {
            JV iter=eval(n->ch[0],env);
            EP lenv=mkEnv(env);
            if(n->flag) lenv->def(n->str, JSVal::undef());
            auto doIter=[&](JV key){
                if(n->flag) lenv->set(n->str, key);
                else        env->set(n->str, key);
                try { execStmt(n->ch[1],lenv); }
                catch(BrkSig&) { throw; }
                catch(CtnSig&) {}
            };
            try {
                if(iter&&iter->type==JT::Obj&&iter->keys)
                    for(auto& k:*iter->keys) doIter(JSVal::st(k));
                else if(iter&&iter->type==JT::Arr)
                    for(size_t i=0;i<iter->arr->size();i++) doIter(JSVal::st(to_string(i)));
            } catch(BrkSig&) {}
            break;
        }
        case NT::Switch: {
            JV disc=eval(n->ch[0],env);
            bool matched=false; bool breaking=false;
            int defIdx=-1;
            EP senv=mkEnv(env);
            try {
                for(int i=1;i<(int)n->ch.size()&&!breaking;i++) {
                    auto& sc=n->ch[i];
                    if(sc->isDefault){defIdx=i;if(!matched) continue;}
                    if(!matched&&!sc->isDefault){
                        JV cv=eval(sc->ch[0],senv);
                        if(jsStrictEq(disc,cv)) matched=true;
                        if(!matched) continue;
                    }
                    // Execute case body (stmts from index 1)
                    for(int j=(sc->isDefault?1:1);j<(int)sc->ch.size();j++) {
                        if(sc->ch[j]) execStmt(sc->ch[j],senv);
                    }
                }
                if(!matched&&defIdx>=0) {
                    auto& sc=n->ch[defIdx];
                    for(int j=1;j<(int)sc->ch.size();j++)
                        if(sc->ch[j]) execStmt(sc->ch[j],senv);
                    // Fall through to subsequent cases
                    for(int i=defIdx+1;i<(int)n->ch.size();i++){
                        auto& sc2=n->ch[i];
                        for(int j=(sc2->isDefault?1:1);j<(int)sc2->ch.size();j++)
                            if(sc2->ch[j]) execStmt(sc2->ch[j],senv);
                    }
                }
            } catch(BrkSig&) {}
            break;
        }
        default: eval(n, env); break;
        }
    }

    void execVDecl(NP n, EP env) {
        for(auto& sub:n->ch) {
            if(!sub) continue;
            string name=sub->str;
            JV val=sub->ch.empty()?JSVal::undef():eval(sub->ch[0],env);

            if(name=="[d]") {
                // Array destructuring
                if(val&&val->type==JT::Arr) {
                    auto& arr=*val->arr;
                    for(size_t i=0;i<sub->params.size();i++) {
                        if(sub->params[i].empty()) continue;
                        JV v=i<arr.size()?arr[i]:JSVal::undef();
                        env->def(sub->params[i], v, sub->isConst);
                    }
                    if(sub->hasRest) {
                        auto rest=JSVal::ar();
                        for(size_t i=sub->params.size();i<arr.size();i++) rest->arr->push_back(arr[i]);
                        env->def(sub->restParam, rest, sub->isConst);
                    }
                } else {
                    for(auto& p:sub->params) if(!p.empty()) env->def(p,JSVal::undef(),sub->isConst);
                }
            } else if(name=="{d}") {
                // Object destructuring
                for(auto& p:sub->params) {
                    size_t colon=p.find(':');
                    string key=colon!=string::npos?p.substr(0,colon):p;
                    string varName=colon!=string::npos?p.substr(colon+1):p;
                    JV v=val&&(val->type==JT::Obj||val->type==JT::Arr)?val->getProp(key):JSVal::undef();
                    env->def(varName, v, sub->isConst);
                }
            } else {
                env->def(name, val, sub->isConst);
            }
        }
    }

    // ─── Expression evaluation ─────────────────────────────────
    JV eval(NP n, EP env) {
        if(!n) return JSVal::undef();
        switch(n->type) {
        case NT::Lit:
            if(n->str=="num")  return JSVal::nm(n->num);
            if(n->str=="str")  return JSVal::st(n->sval);
            if(n->str=="bool") return JSVal::bl(n->flag);
            if(n->str=="null") return JSVal::null_();
            return JSVal::undef();

        case NT::Id: {
            string name=n->str;
            if(name=="undefined") return JSVal::undef();
            if(name=="null")      return JSVal::null_();
            if(name=="NaN")       return JSVal::nm(numeric_limits<double>::quiet_NaN());
            if(name=="Infinity")  return JSVal::nm(numeric_limits<double>::infinity());
            if(name=="true")      return JSVal::bl(true);
            if(name=="false")     return JSVal::bl(false);
            return env->get(name);
        }

        case NT::Tmpl: return evalTemplate(n->sval, env);

        case NT::ArrL: {
            auto arr=JSVal::ar();
            for(auto& elem:n->ch) {
                if(!elem) { arr->arr->push_back(JSVal::undef()); continue; }
                if(elem->type==NT::Spread) {
                    JV v=eval(elem->ch[0],env);
                    if(v&&v->type==JT::Arr) for(auto& e:*v->arr) arr->arr->push_back(e);
                    else arr->arr->push_back(v);
                } else arr->arr->push_back(eval(elem,env));
            }
            return arr;
        }

        case NT::ObjL: {
            auto obj=JSVal::ob();
            for(auto& kv:n->props) {
                JV val=eval(kv.second,env);
                obj->setProp(kv.first, val);
            }
            for(auto& spr:n->ch) {
                if(!spr) continue;
                if(spr->type==NT::Spread) {
                    JV v=eval(spr->ch[0],env);
                    if(v&&(v->type==JT::Obj||v->type==JT::Arr)&&v->props) {
                        if(v->keys) for(auto& k2:*v->keys) obj->setProp(k2,(*v->props)[k2]);
                    }
                } else if(spr->computed) {
                    JV k2=eval(spr->ch[0],env);
                    JV v2=eval(spr->ch[1],env);
                    obj->setProp(jsStr(k2),v2);
                }
            }
            return obj;
        }

        case NT::FnEx: {
            auto fn=makeFunction(n->str, n->params, n->hasRest, n->restParam,
                                 n->ch.empty()?nullptr:n->ch[0], env, false);
            // Attach prototype methods
            fn->setProp("prototype", JSVal::ob());
            if(!n->props.empty()) {
                auto proto=fn->getProp("prototype");
                for(auto& mnmb:n->props) {
                    JV mfn=eval(mnmb.second,env);
                    proto->setProp(mnmb.first, mfn);
                }
            }
            return fn;
        }

        case NT::Arrow: {
            auto fn=makeFunction("", n->params, n->hasRest, n->restParam,
                                 n->ch.empty()?nullptr:n->ch[0], env, true);
            return fn;
        }

        case NT::FDecl: {
            auto fn=makeFunction(n->str, n->params, n->hasRest, n->restParam,
                                 n->ch[0], env, false);
            env->def(n->str, fn);
            return fn;
        }

        case NT::Asn: {
            NP lhs=n->ch[0]; JV rhs=eval(n->ch[1],env);
            string op=n->str;
            if(op!="=") {
                JV cur2=eval(lhs,env);
                if(op=="+=") {
                    if(cur2->type==JT::Str||rhs->type==JT::Str)
                        rhs=JSVal::st(jsStr(cur2)+jsStr(rhs));
                    else rhs=JSVal::nm(jsNum(cur2)+jsNum(rhs));
                } else if(op=="-=") rhs=JSVal::nm(jsNum(cur2)-jsNum(rhs));
                else if(op=="*=") rhs=JSVal::nm(jsNum(cur2)*jsNum(rhs));
                else if(op=="/=") rhs=JSVal::nm(jsNum(cur2)/jsNum(rhs));
                else if(op=="%=") rhs=JSVal::nm(fmod(jsNum(cur2),jsNum(rhs)));
            }
            assignLhs(lhs, rhs, env);
            return rhs;
        }

        case NT::Bin: {
            string op=n->str;
            // Short-circuit for logical (handled in Log node, but Bin might have comma)
            JV l=eval(n->ch[0],env), r=eval(n->ch[1],env);
            if(op=="+") {
                if(l->type==JT::Str||r->type==JT::Str) return JSVal::st(jsStr(l)+jsStr(r));
                return JSVal::nm(jsNum(l)+jsNum(r));
            }
            if(op=="-")  return JSVal::nm(jsNum(l)-jsNum(r));
            if(op=="*")  return JSVal::nm(jsNum(l)*jsNum(r));
            if(op=="/")  return JSVal::nm(jsNum(l)/jsNum(r));
            if(op=="%")  return JSVal::nm(fmod(jsNum(l),jsNum(r)));
            if(op=="**") return JSVal::nm(pow(jsNum(l),jsNum(r)));
            if(op=="==") return JSVal::bl(jsAbstractEq(l,r));
            if(op=="!=") return JSVal::bl(!jsAbstractEq(l,r));
            if(op=="===") return JSVal::bl(jsStrictEq(l,r));
            if(op=="!==") return JSVal::bl(!jsStrictEq(l,r));
            if(op=="<")  {
                if(l->type==JT::Str&&r->type==JT::Str) return JSVal::bl(l->s<r->s);
                return JSVal::bl(jsNum(l)<jsNum(r));
            }
            if(op==">")  {
                if(l->type==JT::Str&&r->type==JT::Str) return JSVal::bl(l->s>r->s);
                return JSVal::bl(jsNum(l)>jsNum(r));
            }
            if(op=="<=") {
                if(l->type==JT::Str&&r->type==JT::Str) return JSVal::bl(l->s<=r->s);
                return JSVal::bl(jsNum(l)<=jsNum(r));
            }
            if(op==">=") {
                if(l->type==JT::Str&&r->type==JT::Str) return JSVal::bl(l->s>=r->s);
                return JSVal::bl(jsNum(l)>=jsNum(r));
            }
            if(op=="in") {
                string k=jsStr(l);
                if(r&&(r->type==JT::Obj||r->type==JT::Arr)) return JSVal::bl(r->hasProp(k));
                return JSVal::bl(false);
            }
            // Bitwise
            if(op=="&")  return JSVal::nm((long long)jsNum(l)&(long long)jsNum(r));
            if(op=="|")  return JSVal::nm((long long)jsNum(l)|(long long)jsNum(r));
            if(op=="^")  return JSVal::nm((long long)jsNum(l)^(long long)jsNum(r));
            if(op=="<<") return JSVal::nm((int)(long long)jsNum(l)<<(int)(long long)jsNum(r));
            if(op==">>") return JSVal::nm((int)(long long)jsNum(l)>>(int)(long long)jsNum(r));
            if(op==">>>"){
                unsigned int a=(unsigned int)(long long)jsNum(l);
                unsigned int b=(unsigned int)(long long)jsNum(r);
                return JSVal::nm(a>>b);
            }
            if(op==",") return r;
            return JSVal::undef();
        }

        case NT::Un: {
            string op=n->str;
            JV v=eval(n->ch[0],env);
            if(op=="-")    return JSVal::nm(-jsNum(v));
            if(op=="+")    return JSVal::nm(jsNum(v));
            if(op=="!")    return JSVal::bl(!jsBool(v));
            if(op=="~")    return JSVal::nm(~(long long)jsNum(v));
            if(op=="void") return JSVal::undef();
            return JSVal::undef();
        }

        case NT::Upd: {
            string op=n->str; bool prefix=n->flag;
            NP tgt=n->ch[0]; JV old=eval(tgt,env);
            double oldN=jsNum(old);
            double newN=op=="++"?oldN+1:oldN-1;
            assignLhs(tgt, JSVal::nm(newN), env);
            return prefix?JSVal::nm(newN):JSVal::nm(oldN);
        }

        case NT::Log: {
            string op=n->str;
            JV l=eval(n->ch[0],env);
            if(op=="&&") return l->truthy()?eval(n->ch[1],env):l;
            if(op=="||") return l->truthy()?l:eval(n->ch[1],env);
            if(op=="??") return (l->type!=JT::Null&&l->type!=JT::Undef)?l:eval(n->ch[1],env);
            return JSVal::undef();
        }

        case NT::Cond: {
            return jsBool(eval(n->ch[0],env))?eval(n->ch[1],env):eval(n->ch[2],env);
        }

        case NT::Typeof: {
            JV v=JSVal::undef();
            try { v=eval(n->ch[0],env); } catch(...) {}
            switch(v->type){
                case JT::Undef: return JSVal::st("undefined");
                case JT::Null:  return JSVal::st("object");
                case JT::Bool:  return JSVal::st("boolean");
                case JT::Num:   return JSVal::st("number");
                case JT::Str:   return JSVal::st("string");
                case JT::Fn:    return JSVal::st("function");
                default:        return JSVal::st("object");
            }
        }

        case NT::Mem: {
            JV obj=eval(n->ch[0],env);
            string prop=n->str;
            return getMember(obj, prop, env);
        }

        case NT::Idx: {
            JV obj=eval(n->ch[0],env); JV idx=eval(n->ch[1],env);
            string k=jsStr(idx);
            return getIndex(obj, k, env);
        }

        case NT::Call: {
            // n->ch[0] = callee, n->ch[1+] = args
            NP calleeNode=n->ch[0];
            JV thisObj=JSVal::undef();
            JV fnVal;

            if(calleeNode->type==NT::Mem) {
                thisObj=eval(calleeNode->ch[0],env);
                string meth=calleeNode->str;
                fnVal=getMember(thisObj, meth, env, true);
            } else if(calleeNode->type==NT::Idx) {
                thisObj=eval(calleeNode->ch[0],env);
                JV idx=eval(calleeNode->ch[1],env);
                string k=jsStr(idx);
                fnVal=getIndex(thisObj, k, env, true);
            } else {
                fnVal=eval(calleeNode,env);
            }

            vector<JV> args;
            for(int i=1;i<(int)n->ch.size();i++) {
                if(!n->ch[i]) continue;
                if(n->ch[i]->type==NT::Spread) {
                    JV v=eval(n->ch[i]->ch[0],env);
                    if(v&&v->type==JT::Arr) for(auto& e:*v->arr) args.push_back(e);
                    else args.push_back(v);
                } else args.push_back(eval(n->ch[i],env));
            }

            if(!fnVal||fnVal->type!=JT::Fn)
                throw ThrSig{JSVal::st("TypeError: "+jsStr(calleeNode->type==NT::Mem?JSVal::st(calleeNode->str):eval(calleeNode,env))+" is not a function")};

            return callFn(fnVal, args, thisObj, env);
        }

        case NT::New_: {
            JV ctor=eval(n->ch[0],env);
            vector<JV> args;
            for(int i=1;i<(int)n->ch.size();i++) {
                if(!n->ch[i]) continue;
                if(n->ch[i]->type==NT::Spread) {
                    JV v=eval(n->ch[i]->ch[0],env);
                    if(v&&v->type==JT::Arr) for(auto& e:*v->arr) args.push_back(e);
                } else args.push_back(eval(n->ch[i],env));
            }
            return callNew(ctor, args, env);
        }

        case NT::Spread: {
            JV v=eval(n->ch[0],env);
            return v; // handled in parent
        }

        // Statements that also return values
        case NT::ExprS: return eval(n->ch[0],env);
        case NT::VDecl: execVDecl(n,env); return JSVal::undef();

        case NT::Prog:
        case NT::Block: {
            JV last=JSVal::undef();
            for(auto& s:n->ch) { if(s) last=eval(s,env); }
            return last;
        }
        default: return JSVal::undef();
        }
    }

    JV callNew(JV ctor, vector<JV> args, EP env) {
        if(!ctor||ctor->type!=JT::Fn) throw runtime_error("Not a constructor");
        // Built-in constructors
        if(ctor->fn&&ctor->fn->isNative) {
            return ctor->fn->native(args, JSVal::undef(), env);
        }
        // User-defined
        auto obj=JSVal::ob();
        // Set prototype
        JV proto=ctor->getProp("prototype");
        if(proto&&proto->type==JT::Obj&&proto->props) {
            if(proto->keys) for(auto& k:*proto->keys)
                obj->setProp(k, (*proto->props)[k]);
        }
        JV result=callFn(ctor, args, obj, env);
        if(result&&(result->type==JT::Obj||result->type==JT::Arr)) return result;
        return obj;
    }

    // ─── Member access (returns bound method or value) ─────────
    JV getMember(JV obj, const string& prop, EP env, bool forCall=false) {
        if(!obj) return JSVal::undef();

        // String properties
        if(obj->type==JT::Str) {
            if(prop=="length") return JSVal::nm(obj->s.size());
            // Return a bound native for string methods
            string str=obj->s;
            auto self=obj;
            return makeFn(prop, [this,str,prop,self](vector<JV> args, JV, EP env2)->JV {
                return stringMethod(str, prop, args, env2);
            });
        }

        // Number properties
        if(obj->type==JT::Num) {
            double n=obj->n;
            if(prop=="toFixed") {
                return makeFn("toFixed",[n](vector<JV> args,JV,EP)->JV{
                    int digits=args.empty()?0:(int)jsNum(args[0]);
                    ostringstream oss; oss<<fixed<<setprecision(digits)<<n;
                    return JSVal::st(oss.str());
                });
            }
            if(prop=="toString") {
                return makeFn("toString",[n](vector<JV> args,JV,EP)->JV{
                    int base=args.empty()?10:(int)jsNum(args[0]);
                    if(base==10) return JSVal::st(numToStr(n));
                    ostringstream oss; oss<<setbase(base)<<(long long)n;
                    return JSVal::st(oss.str());
                });
            }
            if(prop=="toPrecision") {
                return makeFn("toPrecision",[n](vector<JV> args,JV,EP)->JV{
                    if(args.empty()) return JSVal::st(numToStr(n));
                    int prec=(int)jsNum(args[0]);
                    ostringstream oss; oss<<setprecision(prec)<<n;
                    return JSVal::st(oss.str());
                });
            }
            return JSVal::undef();
        }

        // Array properties
        if(obj->type==JT::Arr) {
            if(prop=="length") return JSVal::nm(obj->arr->size());
            // Numeric index
            double idx=parseNumStr(prop);
            if(!isnan(idx)&&idx>=0&&idx==(long long)idx) {
                size_t i=(size_t)(long long)idx;
                if(i<obj->arr->size()) return (*obj->arr)[i];
                return JSVal::undef();
            }
            // Check object properties
            if(obj->hasProp(prop)) return obj->getProp(prop);
            // Built-in methods
            auto self=obj;
            return makeFn(prop, [this,self,prop](vector<JV> args,JV,EP env2)->JV {
                return arrayMethod(self, prop, args, env2);
            });
        }

        // Object properties
        if(obj->type==JT::Obj) {
            if(obj->hasProp(prop)) {
                JV v=obj->getProp(prop);
                // If it's a function and accessed for call, bind 'this'
                return v;
            }
            // Prototype lookup
            if(obj->hasProp("__proto__")) {
                JV proto=obj->getProp("__proto__");
                if(proto&&proto->type==JT::Obj) return getMember(proto,prop,env,forCall);
            }
            return JSVal::undef();
        }

        // Function properties
        if(obj->type==JT::Fn) {
            if(prop=="name") return JSVal::st(obj->fn?obj->fn->name:"");
            if(prop=="length") return JSVal::nm(obj->fn?obj->fn->params.size():0);
            if(prop=="prototype") return obj->getProp("prototype");
            if(obj->hasProp(prop)) return obj->getProp(prop);
            // bind/call/apply
            if(prop=="bind") {
                auto self=obj;
                return makeFn("bind",[this,self](vector<JV> args,JV,EP env2)->JV{
                    JV thisArg=args.empty()?JSVal::undef():args[0];
                    vector<JV> boundArgs(args.begin()+(args.empty()?0:1),args.end());
                    return makeFn("bound",[this,self,thisArg,boundArgs](vector<JV> args2,JV,EP env3)->JV{
                        vector<JV> allArgs=boundArgs;
                        allArgs.insert(allArgs.end(),args2.begin(),args2.end());
                        return callFn(self,allArgs,thisArg,env3);
                    });
                });
            }
            if(prop=="call") {
                auto self=obj;
                return makeFn("call",[this,self](vector<JV> args,JV,EP env2)->JV{
                    JV thisArg=args.empty()?JSVal::undef():args[0];
                    vector<JV> callArgs(args.begin()+(args.empty()?0:1),args.end());
                    return callFn(self,callArgs,thisArg,env2);
                });
            }
            if(prop=="apply") {
                auto self=obj;
                return makeFn("apply",[this,self](vector<JV> args,JV,EP env2)->JV{
                    JV thisArg=args.empty()?JSVal::undef():args[0];
                    vector<JV> callArgs;
                    if(args.size()>1&&args[1]&&args[1]->type==JT::Arr)
                        callArgs=*args[1]->arr;
                    return callFn(self,callArgs,thisArg,env2);
                });
            }
            return JSVal::undef();
        }

        return JSVal::undef();
    }

    JV getIndex(JV obj, const string& k, EP env, bool forCall=false) {
        if(!obj) return JSVal::undef();
        if(obj->type==JT::Str) {
            double idx=parseNumStr(k);
            if(!isnan(idx)&&idx>=0&&idx==(long long)idx) {
                size_t i=(size_t)(long long)idx;
                if(i<obj->s.size()) return JSVal::st(string(1,obj->s[i]));
                return JSVal::undef();
            }
            return getMember(obj,k,env,forCall);
        }
        if(obj->type==JT::Arr) {
            double idx=parseNumStr(k);
            if(!isnan(idx)&&idx>=0&&idx==(long long)idx) {
                size_t i=(size_t)(long long)idx;
                if(i<obj->arr->size()) return (*obj->arr)[i];
                return JSVal::undef();
            }
            return getMember(obj,k,env,forCall);
        }
        return getMember(obj,k,env,forCall);
    }

    // ─── Built-in setup ───────────────────────────────────────
    void setupBuiltins(EP env) {
        // console
        auto console=JSVal::ob();
        // console.log
        console->setProp("log", makeFn("log",[](vector<JV> args,JV,EP)->JV{
            for(size_t i=0;i<args.size();i++){
                if(i) cout<<' ';
                cout<<jsStr(args[i]);
            }
            cout<<'\n';
            return JSVal::undef();
        }));
        console->setProp("error", makeFn("error",[](vector<JV> args,JV,EP)->JV{
            for(size_t i=0;i<args.size();i++){if(i)cerr<<' ';cerr<<jsStr(args[i]);}
            cerr<<'\n'; return JSVal::undef();
        }));
        console->setProp("warn", console->getProp("error"));
        console->setProp("info", console->getProp("log"));
        console->setProp("dir",  console->getProp("log"));
        env->def("console", console);

        // Math object
        auto math=JSVal::ob();
        math->setProp("PI",      JSVal::nm(3.14159265358979323846));
        math->setProp("E",       JSVal::nm(2.71828182845904523536));
        math->setProp("LN2",     JSVal::nm(0.693147180559945309417));
        math->setProp("LN10",    JSVal::nm(2.30258509299404568402));
        math->setProp("LOG2E",   JSVal::nm(1.44269504088896340736));
        math->setProp("LOG10E",  JSVal::nm(0.434294481903251827651));
        math->setProp("SQRT2",   JSVal::nm(1.41421356237309504880));
        math->setProp("Infinity",JSVal::nm(numeric_limits<double>::infinity()));
        math->setProp("abs",   makeFn("abs",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(fabs(a.empty()?0:jsNum(a[0])));}));
        math->setProp("ceil",  makeFn("ceil",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(ceil(a.empty()?0:jsNum(a[0])));}));
        math->setProp("floor", makeFn("floor", [](vector<JV> a,JV,EP)->JV{return JSVal::nm(floor(a.empty()?0:jsNum(a[0])));}));
        math->setProp("round", makeFn("round", [](vector<JV> a,JV,EP)->JV{return JSVal::nm(round(a.empty()?0:jsNum(a[0])));}));
        math->setProp("trunc", makeFn("trunc", [](vector<JV> a,JV,EP)->JV{return JSVal::nm(trunc(a.empty()?0:jsNum(a[0])));}));
        math->setProp("sqrt",  makeFn("sqrt",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(sqrt(a.empty()?0:jsNum(a[0])));}));
        math->setProp("cbrt",  makeFn("cbrt",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(cbrt(a.empty()?0:jsNum(a[0])));}));
        math->setProp("pow",   makeFn("pow",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(pow(a.size()>0?jsNum(a[0]):0,a.size()>1?jsNum(a[1]):0));}));
        math->setProp("log",   makeFn("log",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(log(a.empty()?0:jsNum(a[0])));}));
        math->setProp("log2",  makeFn("log2",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(log2(a.empty()?0:jsNum(a[0])));}));
        math->setProp("log10", makeFn("log10", [](vector<JV> a,JV,EP)->JV{return JSVal::nm(log10(a.empty()?0:jsNum(a[0])));}));
        math->setProp("exp",   makeFn("exp",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(exp(a.empty()?0:jsNum(a[0])));}));
        math->setProp("sin",   makeFn("sin",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(sin(a.empty()?0:jsNum(a[0])));}));
        math->setProp("cos",   makeFn("cos",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(cos(a.empty()?0:jsNum(a[0])));}));
        math->setProp("tan",   makeFn("tan",   [](vector<JV> a,JV,EP)->JV{return JSVal::nm(tan(a.empty()?0:jsNum(a[0])));}));
        math->setProp("asin",  makeFn("asin",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(asin(a.empty()?0:jsNum(a[0])));}));
        math->setProp("acos",  makeFn("acos",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(acos(a.empty()?0:jsNum(a[0])));}));
        math->setProp("atan",  makeFn("atan",  [](vector<JV> a,JV,EP)->JV{return JSVal::nm(atan(a.empty()?0:jsNum(a[0])));}));
        math->setProp("atan2", makeFn("atan2", [](vector<JV> a,JV,EP)->JV{return JSVal::nm(atan2(a.size()>0?jsNum(a[0]):0,a.size()>1?jsNum(a[1]):0));}));
        math->setProp("hypot", makeFn("hypot", [](vector<JV> a,JV,EP)->JV{
            double s=0; for(auto& v:a){double x=jsNum(v);s+=x*x;} return JSVal::nm(sqrt(s));
        }));
        math->setProp("sign",  makeFn("sign",  [](vector<JV> a,JV,EP)->JV{
            double v=a.empty()?0:jsNum(a[0]);
            return JSVal::nm(v<0?-1:v>0?1:0);
        }));
        math->setProp("max", makeFn("max",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::nm(-numeric_limits<double>::infinity());
            double m=jsNum(a[0]); for(auto& v:a) m=max(m,jsNum(v));
            return JSVal::nm(m);
        }));
        math->setProp("min", makeFn("min",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::nm(numeric_limits<double>::infinity());
            double m=jsNum(a[0]); for(auto& v:a) m=min(m,jsNum(v));
            return JSVal::nm(m);
        }));
        // Math.random
        math->setProp("random", makeFn("random",[this](vector<JV>,JV,EP)->JV{
            uniform_real_distribution<double> dist(0.0,1.0);
            return JSVal::nm(dist(rng));
        }));
        math->setProp("clz32", makeFn("clz32",[](vector<JV> a,JV,EP)->JV{
            unsigned int v=(unsigned int)(long long)jsNum(a.empty()?JSVal::nm(0):a[0]);
            if(v==0) return JSVal::nm(32);
            int c=0; while(!(v&0x80000000)){c++;v<<=1;} return JSVal::nm(c);
        }));
        math->setProp("imul", makeFn("imul",[](vector<JV> a,JV,EP)->JV{
            int x=(int)(long long)jsNum(a.size()>0?a[0]:JSVal::nm(0));
            int y=(int)(long long)jsNum(a.size()>1?a[1]:JSVal::nm(0));
            return JSVal::nm(x*y);
        }));
        math->setProp("fround", makeFn("fround",[](vector<JV> a,JV,EP)->JV{
            float f=(float)jsNum(a.empty()?JSVal::nm(0):a[0]);
            return JSVal::nm((double)f);
        }));
        env->def("Math", math);

        // Number
        auto Number=makeFn("Number",[](vector<JV> args,JV,EP)->JV{
            if(args.empty()) return JSVal::nm(0);
            return JSVal::nm(jsNum(args[0]));
        });
        Number->setProp("isFinite", makeFn("isFinite",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()||a[0]->type!=JT::Num) return JSVal::bl(false);
            return JSVal::bl(isfinite(a[0]->n));
        }));
        Number->setProp("isInteger", makeFn("isInteger",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()||a[0]->type!=JT::Num) return JSVal::bl(false);
            return JSVal::bl(a[0]->n==trunc(a[0]->n));
        }));
        Number->setProp("isNaN", makeFn("isNaN",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()||a[0]->type!=JT::Num) return JSVal::bl(false);
            return JSVal::bl(isnan(a[0]->n));
        }));
        Number->setProp("parseInt", makeFn("parseInt",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::nm(numeric_limits<double>::quiet_NaN());
            string s=jsStr(a[0]); int base=a.size()>1?(int)jsNum(a[1]):10;
            if(base==0) base=10;
            try { return JSVal::nm((double)stoll(s,nullptr,base)); } catch(...) {}
            return JSVal::nm(numeric_limits<double>::quiet_NaN());
        }));
        Number->setProp("parseFloat", makeFn("parseFloat",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::nm(numeric_limits<double>::quiet_NaN());
            return JSVal::nm(parseNumStr(jsStr(a[0])));
        }));
        Number->setProp("MAX_VALUE",         JSVal::nm(numeric_limits<double>::max()));
        Number->setProp("MIN_VALUE",         JSVal::nm(numeric_limits<double>::min()));
        Number->setProp("MAX_SAFE_INTEGER",  JSVal::nm(9007199254740991.0));
        Number->setProp("MIN_SAFE_INTEGER",  JSVal::nm(-9007199254740991.0));
        Number->setProp("POSITIVE_INFINITY", JSVal::nm(numeric_limits<double>::infinity()));
        Number->setProp("NEGATIVE_INFINITY", JSVal::nm(-numeric_limits<double>::infinity()));
        Number->setProp("NaN",               JSVal::nm(numeric_limits<double>::quiet_NaN()));
        env->def("Number", Number);

        // String constructor
        auto String=makeFn("String",[](vector<JV> args,JV,EP)->JV{
            if(args.empty()) return JSVal::st("");
            return JSVal::st(jsStr(args[0]));
        });
        String->setProp("fromCharCode", makeFn("fromCharCode",[](vector<JV> a,JV,EP)->JV{
            string s; for(auto& v:a) s+=(char)(int)jsNum(v);
            return JSVal::st(s);
        }));
        env->def("String", String);

        // Boolean constructor
        auto Boolean=makeFn("Boolean",[](vector<JV> args,JV,EP)->JV{
            if(args.empty()) return JSVal::bl(false);
            return JSVal::bl(jsBool(args[0]));
        });
        env->def("Boolean", Boolean);

        // parseInt / parseFloat (global)
        env->def("parseInt",  Number->getProp("parseInt"));
        env->def("parseFloat",Number->getProp("parseFloat"));

        // isNaN / isFinite (global)
        env->def("isNaN", makeFn("isNaN",[](vector<JV> a,JV,EP)->JV{
            return JSVal::bl(isnan(jsNum(a.empty()?JSVal::undef():a[0])));
        }));
        env->def("isFinite", makeFn("isFinite",[](vector<JV> a,JV,EP)->JV{
            double v=jsNum(a.empty()?JSVal::undef():a[0]);
            return JSVal::bl(!isnan(v)&&!isinf(v));
        }));

        // Array constructor
        auto Array=makeFn("Array",[](vector<JV> args,JV,EP)->JV{
            auto arr=JSVal::ar();
            if(args.size()==1&&args[0]->type==JT::Num) {
                size_t len=(size_t)(long long)args[0]->n;
                for(size_t i=0;i<len;i++) arr->arr->push_back(JSVal::undef());
            } else {
                for(auto& a:args) arr->arr->push_back(a);
            }
            return arr;
        });
        Array->setProp("isArray", makeFn("isArray",[](vector<JV> a,JV,EP)->JV{
            return JSVal::bl(!a.empty()&&a[0]->type==JT::Arr);
        }));
        Array->setProp("from", makeFn("from",[this](vector<JV> args,JV,EP env2)->JV{
            if(args.empty()) return JSVal::ar();
            auto arr=JSVal::ar();
            JV src=args[0]; JV mapFn=args.size()>1?args[1]:JSVal::undef();
            if(src->type==JT::Arr) {
                for(size_t i=0;i<src->arr->size();i++){
                    JV v=(*src->arr)[i];
                    if(mapFn&&mapFn->type==JT::Fn) v=callFn(mapFn,{v,JSVal::nm(i)},JSVal::undef(),env2);
                    arr->arr->push_back(v);
                }
            } else if(src->type==JT::Str) {
                for(size_t i=0;i<src->s.size();i++){
                    JV v=JSVal::st(string(1,src->s[i]));
                    if(mapFn&&mapFn->type==JT::Fn) v=callFn(mapFn,{v,JSVal::nm(i)},JSVal::undef(),env2);
                    arr->arr->push_back(v);
                }
            }
            return arr;
        }));
        Array->setProp("of", makeFn("of",[](vector<JV> args,JV,EP)->JV{
            auto arr=JSVal::ar();
            for(auto& a:args) arr->arr->push_back(a);
            return arr;
        }));
        env->def("Array", Array);

        // Object constructor
        auto ObjCtor=makeFn("Object",[](vector<JV> args,JV,EP)->JV{
            if(args.empty()||args[0]->type==JT::Undef||args[0]->type==JT::Null) return JSVal::ob();
            return args[0];
        });
        ObjCtor->setProp("keys", makeFn("keys",[](vector<JV> a,JV,EP)->JV{
            auto arr=JSVal::ar();
            if(!a.empty()&&a[0]&&a[0]->keys) for(auto& k:*a[0]->keys) arr->arr->push_back(JSVal::st(k));
            return arr;
        }));
        ObjCtor->setProp("values", makeFn("values",[](vector<JV> a,JV,EP)->JV{
            auto arr=JSVal::ar();
            if(!a.empty()&&a[0]&&a[0]->keys&&a[0]->props)
                for(auto& k:*a[0]->keys) arr->arr->push_back((*a[0]->props)[k]);
            return arr;
        }));
        ObjCtor->setProp("entries", makeFn("entries",[](vector<JV> a,JV,EP)->JV{
            auto arr=JSVal::ar();
            if(!a.empty()&&a[0]&&a[0]->keys&&a[0]->props)
                for(auto& k:*a[0]->keys){
                    auto pair=JSVal::ar();
                    pair->arr->push_back(JSVal::st(k));
                    pair->arr->push_back((*a[0]->props)[k]);
                    arr->arr->push_back(pair);
                }
            return arr;
        }));
        ObjCtor->setProp("assign", makeFn("assign",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::ob();
            JV target=a[0];
            for(size_t i=1;i<a.size();i++) {
                JV src=a[i];
                if(src&&src->keys&&src->props)
                    for(auto& k:*src->keys) target->setProp(k,(*src->props)[k]);
            }
            return target;
        }));
        ObjCtor->setProp("create", makeFn("create",[](vector<JV> a,JV,EP)->JV{
            auto obj=JSVal::ob();
            if(!a.empty()&&a[0]&&a[0]->type==JT::Obj) {
                obj->setProp("__proto__", a[0]);
                if(a[0]->keys&&a[0]->props)
                    for(auto& k:*a[0]->keys) obj->setProp(k,(*a[0]->props)[k]);
            }
            return obj;
        }));
        ObjCtor->setProp("freeze", makeFn("freeze",[](vector<JV> a,JV,EP)->JV{
            return a.empty()?JSVal::ob():a[0];
        }));
        ObjCtor->setProp("fromEntries", makeFn("fromEntries",[](vector<JV> a,JV,EP)->JV{
            auto obj=JSVal::ob();
            if(a.empty()||a[0]->type!=JT::Arr) return obj;
            for(auto& e:*a[0]->arr) {
                if(e&&e->type==JT::Arr&&e->arr->size()>=2) {
                    obj->setProp(jsStr((*e->arr)[0]),(*e->arr)[1]);
                }
            }
            return obj;
        }));
        ObjCtor->setProp("defineProperty", makeFn("defineProperty",[](vector<JV> a,JV,EP)->JV{
            if(a.size()>=3) a[0]->setProp(jsStr(a[1]),a[2]->getProp("value"));
            return a.empty()?JSVal::ob():a[0];
        }));
        ObjCtor->setProp("getOwnPropertyNames", makeFn("getOwnPropertyNames",[](vector<JV> a,JV,EP)->JV{
            auto arr=JSVal::ar();
            if(!a.empty()&&a[0]&&a[0]->keys) for(auto& k:*a[0]->keys) arr->arr->push_back(JSVal::st(k));
            return arr;
        }));
        ObjCtor->setProp("hasOwn", makeFn("hasOwn",[](vector<JV> a,JV,EP)->JV{
            if(a.size()<2) return JSVal::bl(false);
            return JSVal::bl(a[0]->hasProp(jsStr(a[1])));
        }));
        env->def("Object", ObjCtor);

        // Date constructor
        auto DateCtor=makeFn("Date",[this](vector<JV> args,JV,EP)->JV{
            auto obj=JSVal::ob();
            obj->setProp("__isDate__", JSVal::bl(true));
            double ms;
            if(args.empty()) {
                ms=(double)time(nullptr)*1000;
            } else if(args.size()==1) {
                if(args[0]->type==JT::Str) {
                    // parse date string - simplified
                    struct tm t={};
                    int yr=0,mo=0,da=0,hr=0,mi=0,se=0;
                    sscanf(args[0]->s.c_str(),"%d-%d-%d",&yr,&mo,&da);
                    t.tm_year=yr-1900; t.tm_mon=mo-1; t.tm_mday=da;
                    t.tm_hour=hr; t.tm_min=mi; t.tm_sec=se;
                    ms=(double)mktime(&t)*1000;
                } else ms=jsNum(args[0]);
            } else {
                struct tm t={};
                t.tm_year=(int)jsNum(args[0])-1900;
                t.tm_mon=args.size()>1?(int)jsNum(args[1]):0;
                t.tm_mday=args.size()>2?(int)jsNum(args[2]):1;
                t.tm_hour=args.size()>3?(int)jsNum(args[3]):0;
                t.tm_min=args.size()>4?(int)jsNum(args[4]):0;
                t.tm_sec=args.size()>5?(int)jsNum(args[5]):0;
                ms=(double)mktime(&t)*1000;
            }
            obj->setProp("__ms__", JSVal::nm(ms));

            auto msFn=[obj]()->time_t{ return (time_t)(jsNum(obj->getProp("__ms__"))/1000); };

            obj->setProp("getTime",           makeFn("getTime",           [obj](vector<JV>,JV,EP)->JV{ return obj->getProp("__ms__"); }));
            obj->setProp("getFullYear",       makeFn("getFullYear",       [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); struct tm* t=localtime(&tt); return JSVal::nm(t->tm_year+1900); }));
            obj->setProp("getMonth",          makeFn("getMonth",          [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_mon); }));
            obj->setProp("getDate",           makeFn("getDate",           [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_mday); }));
            obj->setProp("getDay",            makeFn("getDay",            [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_wday); }));
            obj->setProp("getHours",          makeFn("getHours",          [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_hour); }));
            obj->setProp("getMinutes",        makeFn("getMinutes",        [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_min); }));
            obj->setProp("getSeconds",        makeFn("getSeconds",        [msFn](vector<JV>,JV,EP)->JV{ time_t tt=msFn(); return JSVal::nm(localtime(&tt)->tm_sec); }));
            obj->setProp("getMilliseconds",   makeFn("getMilliseconds",   [obj](vector<JV>,JV,EP)->JV{ return JSVal::nm(fmod(jsNum(obj->getProp("__ms__")),1000)); }));
            obj->setProp("getTimezoneOffset", makeFn("getTimezoneOffset", [](vector<JV>,JV,EP)->JV{ return JSVal::nm(0); }));
            obj->setProp("toISOString",       makeFn("toISOString",       [obj](vector<JV>,JV,EP)->JV{
                time_t tt=(time_t)(jsNum(obj->getProp("__ms__"))/1000);
                struct tm* ti=gmtime(&tt); char buf[32];
                strftime(buf,sizeof(buf),"%Y-%m-%dT%H:%M:%S.000Z",ti);
                return JSVal::st(buf);
            }));
            obj->setProp("toLocaleDateString",makeFn("toLocaleDateString",[obj](vector<JV>,JV,EP)->JV{
                time_t tt=(time_t)(jsNum(obj->getProp("__ms__"))/1000);
                struct tm* ti=localtime(&tt); char buf[32];
                strftime(buf,sizeof(buf),"%m/%d/%Y",ti);
                return JSVal::st(buf);
            }));
            obj->setProp("toLocaleTimeString",makeFn("toLocaleTimeString",[obj](vector<JV>,JV,EP)->JV{
                time_t tt=(time_t)(jsNum(obj->getProp("__ms__"))/1000);
                struct tm* ti=localtime(&tt); char buf[32];
                strftime(buf,sizeof(buf),"%I:%M:%S %p",ti);
                return JSVal::st(buf);
            }));
            obj->setProp("toString",          makeFn("toString",          [obj](vector<JV>,JV,EP)->JV{
                return JSVal::st(jsStr(obj));
            }));
            obj->setProp("valueOf",           makeFn("valueOf",           [obj](vector<JV>,JV,EP)->JV{
                return obj->getProp("__ms__");
            }));
            return obj;
        });
        DateCtor->setProp("now", makeFn("now",[](vector<JV>,JV,EP)->JV{
            return JSVal::nm((double)time(nullptr)*1000);
        }));
        DateCtor->setProp("parse", makeFn("parse",[](vector<JV> a,JV,EP)->JV{
            if(a.empty()) return JSVal::nm(numeric_limits<double>::quiet_NaN());
            return JSVal::nm(numeric_limits<double>::quiet_NaN()); // simplified
        }));
        env->def("Date", DateCtor);

        // JSON
        auto JSON=JSVal::ob();
        JSON->setProp("stringify", makeFn("stringify",[this](vector<JV> args,JV,EP env2)->JV{
            if(args.empty()) return JSVal::undef();
            string indent="";
            if(args.size()>2&&args[2]&&args[2]->type!=JT::Undef) {
                if(args[2]->type==JT::Num) indent=string((int)args[2]->n,' ');
                else if(args[2]->type==JT::Str) indent=args[2]->s;
            }
            string r=jsonStringify(args[0],indent,0);
            return JSVal::st(r);
        }));
        JSON->setProp("parse", makeFn("parse",[this](vector<JV> args,JV,EP env2)->JV{
            if(args.empty()) return JSVal::undef();
            string code="("+args[0]->s+")";
            try {
                Lexer lex(code); auto toks=lex.tokenize();
                Parser par(toks); auto ast=par.parse();
                JV val=JSVal::undef();
                for(auto& s:ast->ch) val=eval(s,env2);
                return val;
            } catch(...) { throw ThrSig{JSVal::st("SyntaxError: Invalid JSON")}; }
        }));
        env->def("JSON", JSON);

        // setTimeout / setInterval (no-op for non-async)
        env->def("setTimeout", makeFn("setTimeout",[this](vector<JV> args,JV,EP env2)->JV{
            if(!args.empty()&&args[0]&&args[0]->type==JT::Fn)
                callFn(args[0],{},JSVal::undef(),env2);
            return JSVal::nm(0);
        }));
        env->def("clearTimeout", makeFn("clearTimeout",[](vector<JV>,JV,EP)->JV{return JSVal::undef();}));
        env->def("setInterval",  makeFn("setInterval",[](vector<JV>,JV,EP)->JV{return JSVal::nm(0);}));
        env->def("clearInterval",makeFn("clearInterval",[](vector<JV>,JV,EP)->JV{return JSVal::undef();}));

        // Error constructor
        auto ErrorCtor=makeFn("Error",[](vector<JV> args,JV,EP)->JV{
            auto obj=JSVal::ob();
            obj->setProp("message",args.empty()?JSVal::st(""):JSVal::st(jsStr(args[0])));
            obj->setProp("name",   JSVal::st("Error"));
            obj->setProp("stack",  JSVal::st("Error: "+(args.empty()?"":jsStr(args[0]))));
            return obj;
        });
        env->def("Error", ErrorCtor);
        env->def("TypeError",   ErrorCtor);
        env->def("RangeError",  ErrorCtor);
        env->def("SyntaxError", ErrorCtor);

        // Promise (simplified stub)
        auto PromiseCtor=makeFn("Promise",[this](vector<JV> args,JV,EP env2)->JV{
            auto obj=JSVal::ob();
            JV resolvedVal=JSVal::undef(); bool resolved=false;
            if(!args.empty()&&args[0]->type==JT::Fn) {
                auto resolve=makeFn("resolve",[&resolvedVal,&resolved](vector<JV> a,JV,EP)->JV{
                    resolvedVal=a.empty()?JSVal::undef():a[0]; resolved=true; return JSVal::undef();
                });
                auto reject=makeFn("reject",[](vector<JV>,JV,EP)->JV{ return JSVal::undef(); });
                try { callFn(args[0],{resolve,reject},JSVal::undef(),env2); } catch(...) {}
            }
            JV finalVal=resolvedVal;
            obj->setProp("then", makeFn("then",[this,finalVal](vector<JV> a,JV,EP env2)->JV{
                if(!a.empty()&&a[0]&&a[0]->type==JT::Fn)
                    callFn(a[0],{finalVal},JSVal::undef(),env2);
                return finalVal;
            }));
            obj->setProp("catch", makeFn("catch",[](vector<JV>,JV,EP)->JV{ return JSVal::undef(); }));
            return obj;
        });
        PromiseCtor->setProp("resolve", makeFn("resolve",[this](vector<JV> a,JV,EP env2)->JV{
            auto obj=JSVal::ob();
            JV val=a.empty()?JSVal::undef():a[0];
            obj->setProp("then",makeFn("then",[this,val](vector<JV> a,JV,EP env2)->JV{
                if(!a.empty()&&a[0]&&a[0]->type==JT::Fn) callFn(a[0],{val},JSVal::undef(),env2);
                return val;
            }));
            return obj;
        }));
        env->def("Promise", PromiseCtor);

        // Symbol (simplified)
        env->def("Symbol", makeFn("Symbol",[](vector<JV> a,JV,EP)->JV{
            static int symId=0;
            string desc=a.empty()?"":(a[0]->type==JT::Undef?"":jsStr(a[0]));
            return JSVal::st("Symbol("+desc+")_"+to_string(++symId));
        }));

        // globalThis / window / global
        auto self=env;
        // We'll set these after building the global env

        // undefined/NaN/Infinity
        env->def("undefined", JSVal::undef());
        env->def("NaN",       JSVal::nm(numeric_limits<double>::quiet_NaN()));
        env->def("Infinity",  JSVal::nm(numeric_limits<double>::infinity()));

        // this at top level
        env->def("this", JSVal::undef());
    }

    string jsonStringify(JV v, const string& indent, int depth) {
        if(!v) return "null";
        switch(v->type) {
            case JT::Undef:  return "";  // undefined → skip in obj, null in arr
            case JT::Null:   return "null";
            case JT::Bool:   return v->b?"true":"false";
            case JT::Num:    if(isnan(v->n)||isinf(v->n)) return "null"; return numToStr(v->n);
            case JT::Str:    return jsonQuote(v->s);
            case JT::Fn:     return "";
            case JT::Arr: {
                if(v->arr->empty()) return "[]";
                string r="["; string nl=indent.empty()?"":(string("\n")+string((depth+1)*indent.size(),' '));
                string sep=indent.empty()?",":(","+ nl); string close=indent.empty()?"]":(string("\n")+string(depth*indent.size(),' ')+"]");
                for(size_t i=0;i<v->arr->size();i++){
                    if(i) r+=sep; else if(!indent.empty()) r+=nl;
                    string s=jsonStringify((*v->arr)[i],indent,depth+1);
                    r+=(s.empty()?"null":s);
                }
                r+=close; return r;
            }
            case JT::Obj: {
                if(!v->keys||v->keys->empty()) return "{}";
                string r="{"; bool first=true;
                string nl=indent.empty()?"":(string("\n")+string((depth+1)*indent.size(),' '));
                string close=indent.empty()?"}": (string("\n")+string(depth*indent.size(),' ')+"}");
                for(auto& k:*v->keys) {
                    JV val=(*v->props)[k];
                    if(!val||val->type==JT::Undef||val->type==JT::Fn) continue;
                    string vs=jsonStringify(val,indent,depth+1);
                    if(vs.empty()) continue;
                    if(!first) r+=","; if(!indent.empty()) r+=nl;
                    r+=jsonQuote(k)+(indent.empty()?":":": ")+vs;
                    first=false;
                }
                r+=close; return r;
            }
        }
        return "null";
    }
    string jsonQuote(const string& s) {
        string r="\"";
        for(char c:s) {
            if(c=='"') r+="\\\"";
            else if(c=='\\') r+="\\\\";
            else if(c=='\n') r+="\\n";
            else if(c=='\t') r+="\\t";
            else if(c=='\r') r+="\\r";
            else r+=c;
        }
        r+="\""; return r;
    }

public:
    Interp() {
        global=mkEnv();
        setupBuiltins(global);
    }

    void run(NP ast) {
        // First pass: hoist top-level function declarations
        hoistFunctions(ast, global);
        // Execute
        try {
            for(auto& s:ast->ch) { if(s) execStmt(s,global); }
        }
        catch(RetSig&)  {}
        catch(BrkSig&)  {}
        catch(CtnSig&)  {}
        catch(ThrSig& t){ cerr<<"Uncaught: "<<jsStr(t.val)<<"\n"; }
        catch(exception& e){ cerr<<"Runtime error: "<<e.what()<<"\n"; }
    }
};

// READ HELPERS

static string readFile(const string& path) {
    ifstream f(path, ios::binary);
    if(!f.is_open()) throw runtime_error("Cannot open file: "+path);
    ostringstream ss; ss<<f.rdbuf(); return ss.str();
}
static string readStdin() {
    ostringstream ss; ss<<cin.rdbuf(); return ss.str();
}

// MAIN

int main(int argc, char* argv[]) {
    string code;
    if(argc==1) {
        code=readStdin();
        if(code.empty()) {
            cerr<<"Usage: "<<argv[0]<<" <script.js>\n";
            cerr<<"       "<<argv[0]<<" --eval \"<code>\"\n";
            cerr<<"       echo \"<code>\" | "<<argv[0]<<"\n";
            return 1;
        }
    } else {
        string a1=argv[1];
        if(a1=="-e"||a1=="--eval") {
            for(int i=2;i<argc;i++){if(i>2)code+=' ';code+=argv[i];}
        } else {
            try { code=readFile(a1); }
            catch(exception& e){ cerr<<e.what()<<"\n"; return 1; }
        }
    }
    if(code.empty()) return 0;

    try {
        Lexer lex(code);
        auto tokens=lex.tokenize();
        Parser par(tokens);
        auto ast=par.parse();
        Interp interp;
        interp.run(ast);
    } catch(exception& e) {
        cerr<<"Error: "<<e.what()<<"\n";
        return 1;
    }
    return 0;
}
