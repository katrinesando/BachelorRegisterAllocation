;;; Simplified example of 64-bit mode Linux nasm assembly

global main                        ; Define entry point for this code
extern printf                      ; Refer to C library function

section .text
                
main:
        push rbp                ; Save old base pointer
        mov rbp, rsp            ; Set new base pointer
        mov rax, [myint]        ; Load constant 3456 into RAX
        mov rdi, qword mystring ; format for printf
        add rax, 120000         ; Add 120000 to RAX
        mov rsi, rax            ; Push RAX value to print
        call printf                ; Call C library printf function
        add rsp, 8              ; Discard arguments, 8 bytes
        mov rax, 0              ; Set return value, success
        mov rsp, rbp            ; Reset stack to base pointer
        pop rbp                 ; Restore old base pointer
        ret                     ; Return to caller

section .data
        myint           dq 3456
        mystring        db      'The result is ->%d<-', 10, 0