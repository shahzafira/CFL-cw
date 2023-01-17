// A Small LLVM Compiler for a Simple Functional Language
// (includes an external lexer and parser)
//
//
// call with 
//
//     amm fun_llvm.sc main fact.fun
//     amm fun_llvm.sc main defs.fun
//
// or
//
//     amm fun_llvm.sc write fact.fun
//     amm fun_llvm.sc write defs.fun
//
//       this will generate an .ll file. 
//
// or 
//
//     amm fun_llvm.sc run fact.fun
//     amm fun_llvm.sc run defs.fun
//
//
// You can interpret an .ll file using lli, for example
//
//      lli fact.ll
//
// The optimiser can be invoked as
//
//      opt -O1 -S in_file.ll > out_file.ll
//      opt -O3 -S in_file.ll > out_file.ll
//
// The code produced for the various architectures can be obtain with
//   
//   llc -march=x86 -filetype=asm in_file.ll -o -
//   llc -march=arm -filetype=asm in_file.ll -o -  
//
// Producing an executable can be achieved by
//
//    llc -filetype=obj in_file.ll
//    gcc in_file.o -o a.out
//    ./a.out


import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String, ty: String = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(f: Double) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KWrite(v: KVal) extends KVal
case class KConst(s: String) extends KVal
case class KFConst(s: String) extends KVal
case object KVoid extends KVal


case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp

// Typing environment that updates what type everything receives
type TyEnv = Map[String, String]
// Converting types to LLVM types
var type_conversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")
// From prelude
var builtin_funcs = Map("new_line" -> "Void", "print_star" -> "Void",
                        "print_space" -> "Void", "skip" -> "Void",
                        "print_int" -> "Void")


def typ_val(v: KVal, ts: TyEnv) : String = v match {
  case KVar(s, ty) => ts(s)
  case KNum(i) => "Int"
  case KFNum(f) => "Double"
  case Kop(o, v1, v2) => typ_val(v1, ts)
  case KCall(o, vrs) => ts(o)
  case KWrite(v) => "Void"
  case KConst(s) => "Int"
  case KFConst(s) => "Double"
  case KVoid => "Void"
  case _ => "UNDEF"
}

def typ_exp(a: KExp, ts: TyEnv) : String = a match {
  case KLet(x, e1, e2) => typ_val(e1, ts)
  case KIf(x1, e1, e2) => typ_exp(e1, ts)
}


// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  // Check the name to see if it is a constant
  // Var can store either Int or Double
  case Var(s) => {
    if (s.head.isUpper) {
      if (typ_val(KVar(s), builtin_funcs) == "Int") {
        val lab = Fresh("tmp")
        builtin_funcs += (lab -> "Int")
        KLet(lab, KConst(s), k(KVar(lab, "Int")))
      } else { // if Double
        val lab = Fresh("tmp")
        builtin_funcs += (lab -> "Double")
        KLet(lab, KFConst(s), k(KVar(lab, "Double")))
      }
    } else { // not a constant
      k(KVar(s, typ_val(KVar(s), builtin_funcs)))
    }
  }
  case Num(i) => k(KNum(i))
  case FNum(f) => k(KFNum(f))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => {
        // var type = typ_val(Kop(o, y1, y2), builtin_funcs)
        builtin_funcs += z -> typ_val(Kop(o, y1, y2), builtin_funcs)
        KLet(z, Kop(o, y1, y2), k(KVar(z, typ_val(Kop(o, y1, y2), builtin_funcs))))
      }))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  // Different cases for each return type
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
        typ_val(KVar(name), builtin_funcs) match {
          case "Int" => {
            val lab = Fresh("tmp")
            builtin_funcs += lab -> "Int"
            KLet(lab, KCall(name, vs), k(KVar(lab, "Int")))
          }
          case "Double" => {
            val lab = Fresh("tmp")
            builtin_funcs += lab -> "Double"
            KLet(lab, KCall(name, vs), k(KVar(lab, "Double")))
          }
          case "Void" => {
            val lab = Fresh("tmp")
            builtin_funcs += lab -> "Void"
            KLet(lab, KCall(name, vs), k(KVar(lab, "Void")))
          }
        }
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
  case Write(e) => {
    val z = Fresh("tmp")
    CPS(e)(y => KLet(z, KWrite(y), k(KVar(z, "Void"))))
  }
}   

//initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)

//some testcases:
// (1 + 2) * 3
println(CPSi(Aop("*", Aop("+", Num(1), Num(2)), Num(3))).toString)

// 3 * (1 + 2)
println(CPSi(Aop("*", Num(3), Aop("+", Num(1), Num(2)))).toString)

//some testcases:

// numbers and vars   
println(CPSi(Num(1)).toString)
println(CPSi(Var("z")).toString)

//  a * 3
val e1 = Aop("*", Var("a"), Num(3))
println(CPSi(e1).toString)

// (a * 3) + 4
val e2 = Aop("+", Aop("*", Var("a"), Num(3)), Num(4))
println(CPSi(e2).toString)

// 2 + (a * 3)
val e3 = Aop("+", Num(2), Aop("*", Var("a"), Num(3)))
println(CPSi(e3).toString)

//(1 - 2) + (a * 3)
val e4 = Aop("+", Aop("-", Num(1), Num(2)), Aop("*", Var("a"), Num(3)))
println(CPSi(e4).toString)

// 3 + 4 ; 1 * 7
val es = Sequence(Aop("+", Num(3), Num(4)),
                  Aop("*", Num(1), Num(7)))
println(CPSi(es).toString)

// if (1 == 1) then 3 else 4
val e5 = If(Bop("==", Num(1), Num(1)), Num(3), Num(4))
println(CPSi(e5).toString)

// if (1 == 1) then 3 + 7 else 4 * 2
val ei = If(Bop("==", Num(1), Num(1)), 
                Aop("+", Num(3), Num(7)),
                Aop("*", Num(4), Num(2)))
println(CPSi(ei).toString)


// if (10 != 10) then e5 else 40
val e6 = If(Bop("!=", Num(10), Num(10)), e5, Num(40))
println(CPSi(e6).toString)


// foo(3)
val e7 = Call("foo", List(Num(3)))
println(CPSi(e7).toString)

// foo(3 * 1, 4, 5 + 6)
val e8 = Call("foo", List(Aop("*", Num(3), Num(1)), 
                          Num(4), 
                          Aop("+", Num(5), Num(6))))
println(CPSi(e8).toString)

// a * 3 ; b + 6
val e9 = Sequence(Aop("*", Var("a"), Num(3)), 
                  Aop("+", Var("b"), Num(6)))
println(CPSi(e9).toString)


val e10 = Aop("*", Aop("+", Num(1), Call("foo", List(Var("a"), Num(3)))), Num(4))
println(CPSi(e10).toString)





// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32"
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop(op: String) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "/" => "fdiv double "
  case "%" => "frem double "
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "     // signed less or equal
  case "<"  => "fcmp olt double "     // signed less than
}



// compile K values
def compile_val(v: KVal) : String = v match {
  case KNum(i) => s"$i"
  case KFNum(f) => s"$f"
  case KVar(s, _) => s"%$s"
  case Kop(op, x1, x2) => 
    s"${compile_op(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  case KCall(x1, args) => 
    s"call i32 @$x1 (${args.map(compile_val).mkString("i32 ", ", i32 ", "")})"
  case KWrite(x1) =>
    s"call i32 @printInt (i32 ${compile_val(x1)})"
  
  // Should extend to add for kop using double and int
  // kcall for all the argument or return types?
}

// compile K expressions
def compile_exp(a: KExp) : String = a match {
  case KReturn(v) =>
    i"ret i32 ${compile_val(v)}"
  case KLet(x: String, v: KVal, e: KExp) => 
    i"%$x = ${compile_val(v)}" ++ compile_exp(e)
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1) ++
    l"\n$else_br" ++ 
    compile_exp(e2)
  }

  // extend for all the return types
  // possibly for klet
}


val prelude = """
@.str = private constant [4 x i8] c"%d\0A\00"

declare i32 @printf(i8*, ...)

define i32 @printInt(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret i32 %x
}

"""


// compile function for declarations and main
def compile_decl(d: Decl) : String = d match {
  case Def(name, args, ret_type, body) => { 
    m"define i32 @$name (${args.mkString("i32 %", ", i32 %", "")}) {" ++
    compile_exp(CPSi(body)) ++
    m"}\n"
  }
  case Main(body) => {
    m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0)))) ++
    m"}\n"
  }

  // Add other decl statements, const and fconst
  // def might need to be extended
}


// main compiler functions
def compile(prog: List[Decl]) : String = 
  prelude ++ (prog.map(compile_decl).mkString)


// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._


@main
def main(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    println(compile(ast))
}

@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}

@main
def run(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    write(fname)  
    os.proc("llc", "-filetype=obj", file ++ ".ll").call()
    os.proc("gcc", file ++ ".o", "-o", file ++ ".bin").call()
    os.proc(os.pwd / (file ++ ".bin")).call(stdout = os.Inherit)
    println(s"done.")
}




// CPS functions
/*

def fact(n: Int) : Int = 
  if (n == 0) 1 else n * fact(n - 1)

fact(6)

def factT(n: Int, acc: Int) : Int =
  if (n == 0) acc else factT(n - 1, acc * n)

factT(6, 1)

def factC(n: Int, ret: Int => Int) : Int = {
  if (n == 0) ret(1) 
  else factC(n - 1, x => ret(x * n))
}

factC(6, x => x)
factC(6, x => {println(s"The final Result is $x") ; 0})
factC(6, _ + 1)

def fibC(n: Int, ret: Int => Int) : Int = {
  if (n == 0 || n == 1) ret(1)
  else fibC(n - 1, x => fibC(n - 2, y => ret(x + y)))
}

fibC(10, x => {println(s"Result: $x") ; 1})


*/
