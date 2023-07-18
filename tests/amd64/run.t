$ which minimlc
$ ls /home/kakadu/asp/miniml/_build/install/default/bin
$ ls ../../back_amd64/amd64_compiler.exe

# CPS Factorial
$ cat << EOF | ../../back_amd64/amd64_compiler.exe -vamd64 -
> let rec fack n k =
>  if n=1 then k 1 else fack (n-1) (fun m -> k (n*m))
> 
> let id2 x = x
> let main = fack 6 id2
> EOF
> let rec fac n =
>   if n=1 then 1 else n * fac (n-1)

  $ cat << EOF | ../../back_amd64/amd64_compiler.exe -o fac.asm -vamd64 -
  > let sq y = y * y
  > let double x = x+x
  > let main = sq 6
  > EOF

; generated code for amd64
  $ cat fac.asm | nl -ba

  $ nasm -felf64 fac.asm -o fac.o && ld -o fac.exe fac.o && chmod u+x fac.exe && ./fac.exe
$ cat > .gdbinit << EOF
> b _start
> r 
> n
> n
> i r
> detach 
> kill
> EOF
$ cat .gdbinit
$ gdb ./fac.exe