
.class public prime.prime
.super java/lang/Object

.method public static writeVar(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method

.method public static writeStr(Ljava/lang/String;)V
    .limit stack 2
    .limit locals 1
    getstatic java/lang/System/out Ljava/io/PrintStream;
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return
.end method

.method public static read()I 
    .limit locals 10 
    .limit stack 10

    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream; 
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 13   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2

    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ; when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

   ldc 100
   istore 0 		; end
   ldc 2
   istore 1 		; n
Loop_begin_0:
   iload 1 		; n
   iload 0 		; end
   if_icmpge Loop_end_1
   ldc 2
   istore 2 		; f
   ldc 0
   istore 3 		; tmp
Loop_begin_2:
   iload 2 		; f
   iload 1 		; n
   ldc 2
   idiv
   ldc 1
   iadd
   if_icmpge Loop_end_3
   iload 3 		; tmp
   ldc 0
   if_icmpne Loop_end_3
   iload 1 		; n
   iload 2 		; f
   idiv
   iload 2 		; f
   imul
   iload 1 		; n
   if_icmpne If_else_4
   ldc 1
   istore 3 		; tmp
   goto If_end_5
If_else_4:
If_end_5:
   iload 2 		; f
   ldc 1
   iadd
   istore 2 		; f
   goto Loop_begin_2
Loop_end_3:
   iload 3 		; tmp
   ldc 0
   if_icmpne If_else_6
   iload 1 		; n
   invokestatic prime/prime/writeVar(I)V
   ldc "\n" 		; "\n"
   invokestatic prime/prime/writeStr(Ljava/lang/String;)V
   goto If_end_7
If_else_6:
If_end_7:
   iload 1 		; n
   ldc 1
   iadd
   istore 1 		; n
   goto Loop_begin_0
Loop_end_1:

; COMPILED CODE ENDS
   return

.end method
