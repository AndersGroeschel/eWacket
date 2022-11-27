# eWacket
**a compiler certification of the Wacket Language**
TODO: formalize things much more

# Main Theorem  
*Pulled from [CompCert](https://compcert.org/man/manual001.html)*

**Semantic preservation theorem:** 

    For all source programs ‍S and compiler-generated code ‍C, 
    if the compiler, applied to the source S, produces the code C, 
    without reporting a compile-time error, 
    then the observable behavior of C improves on one of the allowed observable behaviors of ‍S.


# Source program
Our source program *S* will be a subset of the [Wacket](https://github.com/stefanhts/wacket) language.

# Complier Generated code
The complier generated code will be written in the WASM language

# Observables
If we imagine the program as a black box, these are all of the times we can view the program. 
These include any input, output, errors, etc.
