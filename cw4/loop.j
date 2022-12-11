
.class public loop.loop
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
   istore 0 		; start
   iload 0 		; start
   istore 1 		; x
   iload 0 		; start
   istore 2 		; y
   iload 0 		; start
   istore 3 		; z
Loop_begin_0:
   ldc 0
   iload 1 		; x
   if_icmpge Loop_end_1
Loop_begin_2:
   ldc 0
   iload 2 		; y
   if_icmpge Loop_end_3
Loop_begin_4:
   ldc 0
   iload 3 		; z
   if_icmpge Loop_end_5
   iload 3 		; z
   ldc 1
   isub
   istore 3 		; z
   goto Loop_begin_4
Loop_end_5:
   iload 0 		; start
   istore 3 		; z
   iload 2 		; y
   ldc 1
   isub
   istore 2 		; y
   goto Loop_begin_2
Loop_end_3:
   iload 0 		; start
   istore 2 		; y
   iload 1 		; x
   ldc 1
   isub
   istore 1 		; x
   goto Loop_begin_0
Loop_end_1:

; COMPILED CODE ENDS
   return

.end method
