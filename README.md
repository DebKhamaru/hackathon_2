# Custom JavaScript Runtime
A lightweight, custom JavaScript interpreter built entirely from scratch in C++.

## 📥 How to Provide Input

Once the C++ code is compiled into an executable (`js_runtime.exe`), you can feed JavaScript code into it using three different methods:

# 1. Run a JavaScript file (make sure test.js exists)
.\js_runtime test.js

# 2. Run a quick string of inline JavaScript code
.\js_runtime -e "console.log('Testing inline execution!');"

# 3. Pipe JavaScript code directly into the engine
echo "let x = 50; console.log(x * 2);" | .\js_runtime
