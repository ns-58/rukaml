  $ cat << EOF | ../../back_amd64/amd64_compiler.exe -o program.asm -vamd64 -
  > let sq y = y * y
  > let double x = x+x
  > let main = sq 7
  > EOF
  After ANF transformation.
  let sq y =
    (y * y)
  let double x =
    (x + x)
  let main =
    sq 7 
  ANF: let sq y =
         (y * y)
       let double x =
         (x + x)
       let main =
         sq 7 

; generated code for amd64
  $ cat program.asm | nl -ba
       1	section .data
       2	            newline_char: db 10
       3	            codes: db '0123456789abcdef' 
       4	section .text
       5	global _start
       6	print_newline:
       7	          mov rax, 1 ; 'write' syscall identifier
       8	          mov rdi, 1 ; stdout file descriptor
       9	          mov rsi, newline_char ; where do we take data from
      10	          mov rdx, 1 ; the amount of bytes to write
      11	          syscall
      12	          ret 
      13	
      14	print_hex:
      15	  mov rax, rdi
      16	  mov rdi, 1
      17	  mov rdx, 1
      18	  mov rcx, 64 ; how far are we shifting rax?
      19	iterate:
      20	  push rax ; Save the initial rax value
      21	  sub rcx, 4
      22	  sar rax, cl ; shift to 60, 56, 52, ... 4, 0
      23	              ; the cl register is the smallest part of rcx
      24	  and rax, 0xf ; clear all bits but the lowest four
      25	  lea rsi, [codes + rax]; take a hexadecimal digit character code
      26	  mov rax, 1
      27	  push rcx  ; syscall will break rcx
      28	  syscall   ; rax = 1 (31) -- the write identifier,
      29	            ; rdi = 1 for stdout,
      30	            ; rsi = the address of a character, see line 29
      31	  pop rcx
      32	  pop rax          ; ˆ see line 24 ˆ
      33	  test rcx, rcx    ; rcx = 0 when all digits are shown
      34	  jnz iterate
      35	  ret
      36	
      37	_start:
      38	              push    rbp
      39	              mov     rbp, rsp   ; prologue
      40	              call main
      41	              mov rdi, rax    ; rdi stores return code
      42	              mov rax, 60     ; exit syscall
      43	              syscall
      44	
      45		; @[{stack||stack}@]
      46	
      47	sq:
      48	  push rbp
      49	  mov  rbp, rsp
      50	  sub rsp, 8 ; allocate for var "__temp3"
      51	  mov rdx, [rsp+3*8] 
      52	  mov [8*0+rsp], rdx ; access a var "y"
      53	  sub rsp, 8 ; allocate for var "__temp4"
      54	  mov rdx, [rsp+4*8] 
      55	  mov [8*0+rsp], rdx ; access a var "y"
      56	  mov rax, [8*1+rsp]
      57	  mov rbx, [8*0+rsp]
      58	  imul rbx, rax
      59	  mov rax, rbx
      60	  add rsp, 8 ; deallocate var "__temp4"
      61	  add rsp, 8 ; deallocate var "__temp3"
      62	  pop rbp
      63	  ret  ;;;; sq
      64	
      65		; @[{stack||stack}@]
      66	double:
      67	  push rbp
      68	  mov  rbp, rsp
      69	  sub rsp, 8 ; allocate for var "__temp7"
      70	  mov rdx, [rsp+3*8] 
      71	  mov [8*0+rsp], rdx ; access a var "x"
      72	  sub rsp, 8 ; allocate for var "__temp8"
      73	  mov rdx, [rsp+4*8] 
      74	  mov [8*0+rsp], rdx ; access a var "x"
      75	  mov rax, [8*1+rsp]
      76	  mov rbx, [8*0+rsp]
      77	  add  rbx, rax
      78	  mov rax, rbx
      79	  add rsp, 8 ; deallocate var "__temp8"
      80	  add rsp, 8 ; deallocate var "__temp7"
      81	  pop rbp
      82	  ret  ;;;; double
      83	
      84		; @[{stack||stack}@]
      85	main:
      86	  push rbp
      87	  mov  rbp, rsp
      88	  sub rsp, 8 ; allocate for var "__temp11"
      89	  mov qword [8*0+rsp],  7
      90	  call sq
      91	  add rsp, 8 ; deallocate var "__temp11"
      92	  mov rax, rax
      93	  pop rbp
      94	  ret  ;;;; main

  $ nasm -felf64 program.asm -o program.o && ld -o program.exe program.o && chmod u+x program.exe && ./program.exe
  [49]
