# SimpleStringObf

## build

```
mkdir build && cd build
cmake -DLT_LLVM_INSTALL_DIR=<your_llvm_path> ../
make
```

## Usage
```
opt -load-pass-plugin ./libSimpleStringObf.dylib -passes=stringobf input.ll -S -o output.ll
```
