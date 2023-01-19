// A tokeniser for the Fun language
//==================================
//
// call with 
//
//     amm fun_tokens.sc fact.fun
//
//     amm fun_tokens.sc defs.fun
//



import scala.language.implicitConversions    
import scala.language.reflectiveCalls 

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(ls: Set[Char]) extends Rexp
case class PL(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp
  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Pl(vs: List[Val]) extends Val
case class Opt(v: Val) extends Val
case class Ntimes(vs: List[Val]) extends Val
   
   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case RANGE(r) => false
  case PL(r) => nullable(r)
  case OPTIONAL(r) => true
  case UPTO(r, m) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
  case NOT(r) => !nullable(r)
}

def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case RANGE(ls) => if (ls.contains(c)) ONE else ZERO
  case PL(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case UPTO(r, i) =>
    if (i == 0) ZERO else SEQ(der(c, r), UPTO(r, i - 1))
  case FROM(r, i) =>
    if (i == 0) SEQ(der(c, r), STAR(r))
    else SEQ(der(c, r), FROM(r, i - 1))
  case BETWEEN(r, i, j) =>
    if (j == 0) ZERO
    else if (i == 0) SEQ(der(c, r), UPTO(r, j - 1))
    else SEQ(der(c, r), BETWEEN(r, i - 1, j - 1))
  case NOT(r) => NOT(der(c, r))
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  case Pl(vs) => vs.map(flatten).mkString
  case Opt(v) => flatten(v)
  case Ntimes(vs) => vs.map(flatten).mkString
}

// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Pl(vs) => vs.flatMap(env)
  case Opt(v) => env(v)
  case Ntimes(vs) => vs.flatMap(env)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PL(r) => Sequ(mkeps(r), Pl(Nil))
  case OPTIONAL(r) => Empty
  case NTIMES(r, i) => if (i == 0) Ntimes(Nil) else Ntimes(List(mkeps(r)))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (RANGE(ls), Empty) => Chr(c)
  case (PL(r), Sequ(v, Pl(vs))) => Pl(inj(r, c, v)::vs)  
  case (OPTIONAL(r), Empty) => Opt(inj(r, c, v))
  case (NTIMES(r, i), Sequ(v, Ntimes(vs))) => Ntimes(inj(r, c, v)::vs)
  case _ => { println ("Injection error") ; sys.exit(-1) } 
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else { println ("Lexing Error") ; sys.exit(0) } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))


// The Lexing Rules for the Fun Language

def PLUS(r: Rexp) = r ~ r.%

val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | 
          "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | 
          "w" | "x" | "y" | "z" | "_" | "A" | "B" | "C" | "D" | "E" | "F" |
          "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" |
          "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" | "_"
val TYPE = "Int" | "Double" | "Void"
val NUMTYPE = "Int" | "Double"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = OPTIONAL("-") ~ PLUS(DIGIT)
val KEYWORD : Rexp = "if" | "then" | "else" | "write" | "def" | "val"
val SEMI: Rexp = ";"
val COLON: Rexp = ":"
val OP: Rexp = "=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val LBRACE: Rexp = "{"
val RBRACE: Rexp = "}"
val COMMA: Rexp = ","
val ALL = SYM | DIGIT | OP | " " | ":" | ";" | "\"" | "=" | "," | "(" | ")" | "'"
val ALL2 = ALL | "\n" | "\r\n"
val COMMENT = ("/*" ~ ALL2.% ~ "*/") | ("//" ~ ALL.% ~ "\r\n")
val FLOAT = OPTIONAL("-") ~ NUM ~ "." ~ NUM.%
val APOST: Rexp = "'"
val CHARACTER = APOST ~ SYM ~ APOST
val NEWLINE: Rexp = "\n"

val FUN_REGS = (("k" $ KEYWORD) |
                  ("ty" $ TYPE) |
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("f" $ FLOAT) |
                  ("s" $ SEMI) | 
                  ("cl" $ COLON) |
                  ("c" $ COMMA) |
                  ("pl" $ LPAREN) |
                  ("pr" $ RPAREN) |
                  ("bl" $ LBRACE) |
                  ("br" $ RBRACE) |
                  ("apost" $ APOST) |
                  ("char" $ CHARACTER) |
                  ("com" $ COMMENT) |
                  ("w" $ WHITESPACE) |
                  ("newline" $ NEWLINE)).%


// The tokens for the Fun language

abstract class Token extends Serializable 
case object T_SEMI extends Token
case object T_COLON extends Token
case object T_COMMA extends Token
case object T_LPAREN extends Token
case object T_RPAREN extends Token
case object T_LBRACE extends Token
case object T_RBRACE extends Token
case object T_APOST extends Token
case object T_NEWLINE extends Token
case class T_ID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_FLOAT(n: Double) extends Token
case class T_KWD(s: String) extends Token
case class T_TYPE(s: String) extends Token
case class T_COMMENT(s: String) extends Token
case class T_CHAR(s: String) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KWD(s)
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("n", s) => T_FLOAT(s.toDouble)
  case ("s", _) => T_SEMI
  case ("cl", _) => T_COLON
  case ("c", _) => T_COMMA
  case ("pl", _) => T_LPAREN
  case ("pr", _) => T_RPAREN
  case ("bl", _) => T_LBRACE
  case ("br", _) => T_RBRACE
  case ("ty", s) => T_TYPE(s)
  case ("com", s) => T_COMMENT(s)
  case ("apost", _) => T_APOST
  case ("char", s) => T_CHAR(s)
  case ("newline", s) => T_NEWLINE
}

def tokenise(s: String) : List[Token] = {
  val tks = lexing_simp(FUN_REGS, s).collect(token)
  if (tks.length != 0) tks
  else { println (s"Tokenise Error") ; sys.exit(-1) }     
}

// pre-2.5.0 ammonite 
// import ammonite.ops._


// post 2.5.0 ammonite
// import os._

//@doc("Tokenising a file.")
@main
def main(fname: String) = {
  println(tokenise(os.read(os.pwd / fname)))
}
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}




