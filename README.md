# Custom JavaScript Runtime
A lightweight, custom JavaScript interpreter built entirely from scratch in C++.

## 📥 How to Provide Input

Once the C++ code is compiled into an executable (`js_runtime.exe`), you can feed JavaScript code into it using three different methods:

### 1. By reading a `.js` file (Recommended)
You can write your JavaScript code inside a file (for example, `test.js`) and pass the file name as an argument to the executable. The engine will read the file and execute it.
```powershell
# Example:
.\js_runtime test.js
