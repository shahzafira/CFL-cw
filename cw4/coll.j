
.class public coll.coll
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

   ldc 1
   istore 0 		; bnd
Loop_begin_0:
   iload 0 		; bnd
   ldc 101
   if_icmpge Loop_end_1
   iload 0 		; bnd
   invokestatic coll/coll/writeVar(I)V
   ldc ": " 		; ": "
   invokestatic coll/coll/writeStr(Ljava/lang/String;)V
   iload 0 		; bnd
   istore 1 		; n
   ldc 0
   istore 2 		; cnt
Loop_begin_2:
   iload 1 		; n
   ldc 1
   if_icmple Loop_end_3
   iload 1 		; n
   invokestatic coll/coll/writeVar(I)V
   ldc "," 		; ","
   invokestatic coll/coll/writeStr(Ljava/lang/String;)V
   iload 1 		; n
   ldc 2
   irem
   ldc 0
   if_icmpne If_else_4
   iload 1 		; n
   ldc 2
   idiv
   istore 1 		; n
   goto If_end_5
If_else_4:
   ldc 3
   iload 1 		; n
   imul
   ldc 1
   iadd
   istore 1 		; n
If_end_5:
   iload 2 		; cnt
   ldc 1
   iadd
   istore 2 		; cnt
   goto Loop_begin_2
Loop_end_3:
   ldc "=>" 		; "=>"
   invokestatic coll/coll/writeStr(Ljava/lang/String;)V
   iload 2 		; cnt
   invokestatic coll/coll/writeVar(I)V
   ldc "\n" 		; "\n"
   invokestatic coll/coll/writeStr(Ljava/lang/String;)V
   iload 0 		; bnd
   ldc 1
   iadd
   istore 0 		; bnd
   goto Loop_begin_0
Loop_end_1:

; COMPILED CODE ENDS
   return

.end method
