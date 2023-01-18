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


// chconst is turning ascii to a number

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
def CPS(e: Exp, env: TyEnv)(k: (KVal, TyEnv) => (KExp, TyEnv)) : (KExp, TyEnv) = e match {
  // Check the name to see if it is a constant
  // Var can store either Int or Double
  case Var(s) => {
    if (s.head.isUpper) {
      if (typ_val(KVar(s), env) == "Int") {
        val lab = Fresh("tmp")
        var new_env = env + (lab -> "Int")
        CPS(Var(lab), new_env)((y1, env1) => {
          val k1 = k(KVar(lab, "Int"), env1)
          (KLet(lab, KConst(s), k1._1), k1._2)
        })
      } else { // if Double
        val lab = Fresh("tmp")
        var new_env = env + (lab -> "Double")
        CPS(Var(lab), new_env)((y1, env1) => {
          val k1 = k(KVar(lab, "Double"), env1)
          (KLet(lab, KConst(s), k1._1), k1._2)
        })
      }
    } else { // not a constant
      k(KVar(s, typ_val(KVar(s), env)), env)
    }
  }
  case Num(i) => k(KNum(i), env)
  case FNum(f) => k(KFNum(f), env)
  case Aop(o, e1, e2) => {
    val lab = Fresh("tmp")
    CPS(e1, env)((y1, env1) => 
      CPS(e2, env1)((y2, env2) => {
        var new_env = env2 + (lab -> typ_val(Kop(o, y1, y2), env2))
        val k1 = k(KVar(lab, typ_val(Kop(o, y1, y2), new_env)), new_env)
        (KLet(lab, Kop(o, y1, y2), k1._1), k1._2)
      }))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val lab = Fresh("tmp")
    CPS(b1, env)((y1, env1) => 
      CPS(b2, env1)((y2, env2) => 
        (KLet(lab, Kop(o, y1, y2), KIf(lab, CPS(e1, env2)(k)._1, CPS(e2, env2)(k)._1)), env2)))
  }
  // Different cases for each return type
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : (KExp, TyEnv) = args match {
      case Nil => {
        typ_val(KVar(name), env) match {
          case "Int" => {
            val lab = Fresh("tmp")
            var new_env = env + (lab -> "Int")
            val k1 = k(KVar(lab, "Int"), new_env)
            (KLet(lab, KCall(name, vs), k1._1), k1._2)
          }
          case "Double" => {
            val lab = Fresh("tmp")
            var new_env = env + (lab -> "Double")
            val k1 = k(KVar(lab, "Double"), new_env)
            (KLet(lab, KCall(name, vs), k1._1), k1._2)
          }
          case "Void" => {
            val lab = Fresh("tmp")
            var new_env = env + (lab -> "Void")
            val k1 = k(KVar(lab, "Void"), new_env)
            (KLet(lab, KCall(name, vs), k1._1), k1._2)
          }
        }
      }
      case e::es => CPS(e, env)((y, env) => (aux(es, vs ::: List(y))))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1, env)((_, env1) => CPS(e2, env1)((y2, env2) => k(y2, env2)))
  case Write(e) => {
    val lab = Fresh("tmp")
    val k1 = k(KVar(lab, "Void"), env)
    CPS(e, env)((y, env) => (KLet(lab, KWrite(y), k1._1), k1._2))
  }
}

//initial continuation
def CPSi(e: Exp, env: TyEnv) = CPS(e, env)((e1, env1) => (KReturn(e1), env1))



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

// Converting types to LLVM types
var type_conversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")

// compile K values
def compile_val(v: KVal, env: TyEnv) : String = v match {
  case KNum(i) => s"$i"
  case KFNum(f) => s"$f"
  case KVar(s, _) => s"%$s"
  case Kop(op, x1, x2) => 
    s"${compile_op(op)} ${compile_val(x1,env)}, ${compile_val(x2, env)}"
  case KCall(x1, args) => {
    typ_val(KVar(x1), env) match {
      case "Int" => {
        var instr = s"call i32 @$x1 ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(arg, env))} %${compile_val(arg, env)}").mkString(", ")
        instr.concat(s"${args_list})")
      }
      case "Double" => {
        var instr = s"call double @$x1 ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(arg, env))} %${compile_val(arg, env)}").mkString(", ")
        instr.concat(s"${args_list})")
      }
      case "Void" => {
        var instr = s"call void @$x1 ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(arg, env))} %${compile_val(arg, env)}").mkString(", ")
        instr.concat(s"${args_list})")
      }
    }
  }
  case KWrite(x1) =>
    s"call i32 @printInt (i32 ${compile_val(x1, env)})"
  
  // Should extend to add for kop using double and int
  // kcall for all the argument or return types?
}

// compile K expressions
def compile_exp(a: KExp, env: TyEnv) : String = a match {
  case KReturn(v) =>
    i"ret i32 ${compile_val(v, env)}"
  case KLet(x: String, v: KVal, e: KExp) => 
    i"%$x = ${compile_val(v, env)}" ++ compile_exp(e, env)
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1, env) ++
    l"\n$else_br" ++ 
    compile_exp(e2, env)
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
def compile_decl(d: Decl, env: TyEnv) : (String, TyEnv) = d match {
  case Def(name, args, ret_type, body) => { 
    ret_type match {
      case "Int" => {
        val new_env = env + (name -> ret_type)
        var instr = s"define i32 @$name ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(KVar(arg._1), new_env))} %${compile_val(KVar(arg._1), new_env)}").mkString(", ")
        val cps = CPSi(body, new_env)
        (instr.concat(s"${args_list}) {${compile_exp(cps._1, cps._2)}}\n"), cps._2)
      }
      case "Double" => {val new_env = env + (name -> ret_type)
        var instr = s"define double @$name ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(KVar(arg._1), new_env))} %${compile_val(KVar(arg._1), new_env)}").mkString(", ")
        val cps = CPSi(body, new_env)
        (instr.concat(s"${args_list}) {${compile_exp(cps._1, cps._2)}}\n"), cps._2)
      }
      case "Void" => {
        val new_env = env + (name -> ret_type)
        var instr = s"define void @$name ("
        var args_list = args.map(arg => s"${type_conversion(typ_val(KVar(arg._1), new_env))} %${compile_val(KVar(arg._1), new_env)}").mkString(", ")
        val cps = CPSi(body, new_env)
        (instr.concat(s"${args_list}) {${compile_exp(cps._1, cps._2)}}\n"), cps._2)
      }
    }
  }
  case Main(body) => {
    val cps = CPS(body, env)((_, env1) => (KReturn(KNum(0)), env1))
    (s"define i32 @main() {${compile_exp(cps._1, cps._2)}}\n", cps._2)
  }

  // Add other decl statements, const and fconst
  // def might need to be extended
}


// main compiler functions
def compile(prog: List[Decl], env: TyEnv = builtin_funcs) : String = 
  prelude ++ (prog.map(line => compile_decl(line, env)).mkString)


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


// @main
// def test1() ={
//   val code = """val Max : Int = 10;

// def sqr(x: Int) : Int = x * x;

// def all(n: Int) : Void = {
//   if n <= Max
//   then { print_int(sqr(n)) ; new_line(); all(n + 1) }
//   else skip()
// };

// all(0)
//  """
//  print(tokenise(code))
// }

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
