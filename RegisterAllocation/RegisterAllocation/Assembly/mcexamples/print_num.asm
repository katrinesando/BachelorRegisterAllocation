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
	mov rbx, 1
	mov rdi, rbx
	call_prolog
	call printi
	call_epilog
	sub rsp, 0
	add rsp, 8
	pop rbp
	ret
