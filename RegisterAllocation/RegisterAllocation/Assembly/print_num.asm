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
	glovars dd 0
section .text
asm_main:
	push rbp ;old bp
	mov rbp, rsp ;new bp
	push rax
	push rbx
	push rcx
	push rdx
	push rsi
	push rdi
	push rbp
	push rsp
	push r8 
	push r9 
	push r10
	push r11
	push r12
	push r13
	push r14
	push r15
	mov qword [glovars], rsp
	sub qword [glovars], 8
	;check arg count:
	push qword [rbp+16]
	add rsp, 8
	mov rsi, rdi
	mov rdi, 2
	call checkargc
	add rsp, 16
	; allocate globals:
	;set up command line arguments on stack:
	mov rsi, [rbp+24]
_args_next:
	cmp rdi, 0
	jz _args_end
	push qword [rsi]
	add rsi, 8
	sub rdi, 1
	jmp _args_next               ;repeat until --rcx == 0
_args_end:
	sub rbp, 8                   ; make rbp point to first arg
	push rbp
	call near _main
	;clean up stuff pushed onto stack:
	mov rsp, qword [glovars]
	add rsp, 8
	pop rax
	pop rbx
	pop rcx
	pop rdx
	pop rsi
	pop rdi
	pop rbp
	pop rsp
	pop r8 
	pop r9 
	pop r10
	pop r11
	pop r12
	pop r13
	pop r14
	pop r15
	mov rsp, rbp
	pop rbp
	ret
_main:				;start set up frame
	pop rax			; retaddr
	pop rbx			; oldbp
	sub rsp, 16
	mov rsi, rsp
	mov rbp, rsp
	add rbp, 16		; 8*arity
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
	push rbx
	call near printi
	add rsp, 4
	sub rsp, 0
	add rsp, 8
	pop rbp
	ret
