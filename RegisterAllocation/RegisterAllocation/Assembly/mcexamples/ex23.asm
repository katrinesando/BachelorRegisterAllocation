;; Prolog and epilog for 1-argument C function call (needed on MacOS)
%macro call_prolog 0
       mov rbx,rsp            ; Save pre-alignment stack pointer
       pop rax                 ; Pop the argument
       and rsp, 0xFFFFFFFFFFFFFFF0   ; Align rsp to 16 byte multiple
       sub rsp, 16             ; Pad 16 bytes
       push rbx                ; Push old stack top
       push rax                ; Push argument again
%endmacro

%macro call_epilog 0
       add rsp, 8              ; Pop argument
       pop rbx                 ; Get saved pre-alignment stack pointer
       mov rsp, rbx            ; Restore stack top to pre-alignment state
%endmacro

EXTERN printi
EXTERN printc
EXTERN checkargc
GLOBAL asm_main
section .data
	glovars dq 0
section .text
asm_main:
	push rbp ;old bp
	mov rbp, rsp ;new bp
	mov qword [glovars], rsp
	;check arg count:
	push qword [rbp+16]
	push rsi
	mov rsi, rdi
	mov rdi, 1
	call checkargc
	pop rsi
	add rsp, 16
	; allocate globals:
	;set up command line arguments on stack:
_args_next:
	cmp rdi, 0
	jz _args_end
	push qword [rsi]
	add rsi, 8
	sub rdi, 1
	jmp _args_next           ;repeat until --rcx == 0
_args_end:
	push rbp
	call near _main
	;clean up stuff pushed onto stack:
	mov rsp, qword [glovars]
	add rsp, 8
	mov rsp, rbp
	pop rbp
	ret
_main:				;start set up frame
	pop rax			; retaddr
	pop rbx			; oldbp
	sub rsp, 16
	mov rsi, rsp
	mov rbp, rsp
	add rbp, 8		; 8*arity
_main_pro_1:			; slide arguments
	cmp rbp, rsi
	jz _main_pro_2
	mov rcx, [rsi+16]
	mov [rsi], rcx
	add rsi, 8
	jmp _main_pro_1
_main_pro_2:
	sub rbp, 8
	mov [rbp+16], rax
	mov [rbp+8], rbx
_main_tc:	;end set up frame
	sub rsp, 8
	lea rcx, [rbp - 8]
	mov rbx, 0
	mov [rcx], rbx
	jmp near L2
L1:				;Label
	lea rbx, [rbp - 8]
	mov rbx, [rbx]
	mov rdi, rbx
	call_prolog
	call printi
	call_epilog
	lea rbx, [rbp - 8]
	mov rbx, [rbx]
	push rbx
	push rbp
	call near _fib
	mov rbx, rbx
	mov rdi, rbx
	call_prolog
	call printi
	call_epilog
	mov rbx, 10
	mov rdi, rbx
	call_prolog
	call printc
	call_epilog
	lea rcx, [rbp - 8]
	lea rbx, [rbp - 8]
	mov rbx, [rbx]
	mov rdx, 1
	add rbx, rdx
	mov [rcx], rbx
	sub rsp, 0
L2:				;Label
	lea rbx, [rbp - 8]
	mov rbx, [rbx]
	lea rcx, [rbp - 0]
	mov rcx, [rcx]
	xor rax, rax
	cmp rbx, rcx
	setl al
	mov rbx, rax
	cmp rbx, 0
	jnz near L1
	sub rsp, -8
	add rsp, 8
	pop rbp
	ret
_fib:				;start set up frame
	pop rax			; retaddr
	pop rbx			; oldbp
	sub rsp, 16
	mov rsi, rsp
	mov rbp, rsp
	add rbp, 8		; 8*arity
_fib_pro_1:			; slide arguments
	cmp rbp, rsi
	jz _fib_pro_2
	mov rcx, [rsi+16]
	mov [rsi], rcx
	add rsi, 8
	jmp _fib_pro_1
_fib_pro_2:
	sub rbp, 8
	mov [rbp+16], rax
	mov [rbp+8], rbx
_fib_tc:	;end set up frame
	lea rbx, [rbp - 0]
	mov rbx, [rbx]
	mov rcx, 2
	xor rax, rax
	cmp rbx, rcx
	setl al
	mov rbx, rax
	cmp rbx, 0
	jz near L3
	mov rbx, 1
	add rsp, 8
	pop rbp
	ret
	jmp near L4
L3:				;Label
	lea rbx, [rbp - 0]
	mov rbx, [rbx]
	mov rcx, 2
	sub rbx, rcx
	push rbx
	push rbp
	call near _fib
	mov rbx, rbx
	push rbx
	lea rcx, [rbp - 0]
	mov rcx, [rcx]
	mov rdx, 1
	sub rcx, rdx
	push rcx
	push rbp
	call near _fib
	mov rcx, rbx
	pop rbx
	add rbx, rcx
	add rsp, 8
	pop rbp
	ret
L4:				;Label
	sub rsp, 0
	add rsp, 8
	pop rbp
	ret
