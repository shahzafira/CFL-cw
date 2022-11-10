// A simple lexer inspired by work of Sulzmann & Lu
//==================================================
//
// Call the test cases with 
//
//   amm lexer.sc small
//   amm lexer.sc fib
//   amm lexer.sc loops
//   amm lexer.sc email
//
//   amm lexer.sc all

// Zafira Shah k19008701


// regular expressions including records
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp  
                // records for extracting strings or tokens
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(ls: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp
  
// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Plus(vs: List[Val]) extends Val
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

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case RANGE(r) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case UPTO(r, m) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
  case NOT(r) => !nullable(r)
  case CFUN(f) => false
}

def der(c: Char, r: Rexp) : Rexp = r match {
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
  case PLUS(r) => SEQ(der(c, r), STAR(r))
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
  case CFUN(f) => if (f(c)) ONE else ZERO
}

def CHAR2(c: Char) = CFUN(_ == c)
def RANGE2(cs: Set[Char]) = CFUN(cs.contains(_))
val ALL = CFUN(_ => true)


// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  case Plus(vs) => vs.map(flatten).mkString
  case Opt(v) => flatten(v)
  case Ntimes(vs) => vs.map(flatten).mkString
}


// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Plus(vs) => vs.flatMap(env)
  case Opt(v) => env(v)
  case Ntimes(vs) => vs.flatMap(env)
}


// The injection and mkeps part of the lexer
//===========================================

// Question 2

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  // range cannot match the empty string
  // case RANGE(r) => 
  case PLUS(r) => Sequ(mkeps(r), Plus(Nil))
  case OPTIONAL(r) => Empty
  // case NTIMES(r, i) => if (i == 0) Empty else Stars(List(mkeps(r))) 
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
  case (PLUS(r), Sequ(v, Stars(vs))) => Plus(inj(r, c, v)::vs)  
  case (OPTIONAL(r), Empty) => Opt(inj(r, c, v))
  // case (NTIMES(r, 0), _) => Empty 
  case (NTIMES(r, i), Sequ(v, Ntimes(vs))) => Ntimes(inj(r, c, v)::vs)

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

def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification
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
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// The Lexing Rules for the WHILE Language

def PLUS(r: Rexp) = r ~ r.%

def Range(s : List[Char]) : Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => ALT(CHAR(c), Range(s))
}
def RANGE(s: String) = Range(s.toList)

// Question 1
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "for" | "to" | "true" | "false" 
val OP : Rexp = ":=" | "=" | "-" | "+" | "*" | "!=" | "<" | ">" | "%" | "/" | "==" | "<=" | ">=" | "&&" | "||"
val LETTER = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
val SYM = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz._><=;,\\:")
val DIGIT = RANGE("0123456789")
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r")
// curly brackets: {}, round brackets: ()
val LCURLY : Rexp = "{"
val RCURLY : Rexp = "}"
val LROUND : Rexp = "("
val RROUND : Rexp = ")"
val SEMI : Rexp = ";"
val STRING : Rexp = "\"" ~ (SYM | WHITESPACE | DIGIT).% ~ "\""
val ID : Rexp = LETTER ~ ("_" | LETTER | DIGIT).% 
val NUM = ALT(CHAR('0'), SEQ(RANGE("123456789"), STAR(DIGIT)))
val COMMENT : Rexp = "//" ~ (SYM | " " | DIGIT).% ~ "\n"


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("cu" $ LCURLY | RCURLY) |
                  ("r" $ LROUND | RROUND) |
                  ("w" $ WHITESPACE) |
                  ("l" $ LETTER) |
                  ("sy" $ SYM) |
                  ("c" $ COMMENT)).%


def filter_white_space(tokens: List[(String, String)]) = tokens.filter(_._1 != "w")

// Question 3 tokenise programs

// need to add \n to the end of new line or comments cannot be recognised
@arg(doc = "Tokenise fib.while program")
@main
def t_fib() = {
  val prog = scala.io.Source.fromFile("fib.while").getLines.mkString("\n")
  println("Tokenise fib.while, filtering whitespaces\n")
  println(escape(filter_white_space(lexing_simp(WHILE_REGS, prog))))
}

@arg(doc = "Tokenise loops.while program")
@main
def t_loops() = {
  val prog = scala.io.Source.fromFile("loops.while").getLines.mkString("\n")
  println("Tokenise loops.while, filtering whitespaces\n")
  println(escape(filter_white_space(lexing_simp(WHILE_REGS, prog))))
}

@arg(doc = "Tokenise factors.while program")
@main
def t_factors() = {
  val prog = scala.io.Source.fromFile("factors.while").getLines.mkString("\n")
  println("Tokenise factors.while, filtering whitespaces\n")
  println(escape(filter_white_space(lexing_simp(WHILE_REGS, prog))))
}

@arg(doc = "Tokenise collatz2.while program")
@main
def t_collatz() = {
  val prog = scala.io.Source.fromFile("collatz2.while").getLines.mkString("\n")
  println("Tokenise collatz2.while, filtering whitespaces\n")
  println(escape(filter_white_space(lexing_simp(WHILE_REGS, prog))))
}

// Question 2 tests

@arg(doc = "test inj for extended regular expressions")
@main
def testinj() = {
  println("rexp: a*\n string: aa")
  println(lex_simp(STAR(CHAR('a')), "aa".toList))

  println("rexp: a + b\n string: a")
  println(lex_simp(ALT(CHAR('a'), CHAR('b')), "a".toList))

  println("rexp: a{3}\n string: aaa")
  println(lex_simp(NTIMES(CHAR('a'), 3), "aaa".toList))

  println("rexp: (a + 1){3}\n string: aa")
  println(lex_simp(NTIMES(ALT(CHAR('a'), ONE), 3), "aa".toList))
  
}

// Two Simple While Tests
//========================

@arg(doc = "small tests")
@main
def small() = {

  val prog0 = """read n"""
  println(s"test: $prog0")
  println(lexing_simp(WHILE_REGS, prog0))

  val prog1 = """read  n; write n"""  
  println(s"test: $prog1")
  println(lexing_simp(WHILE_REGS, prog1))
}

// Bigger Tests
//==============

// escapes strings and prints them out as "", "\n" and so on
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}


val prog2 = """
write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "Result";
write minus2
// some comment
"""

@arg(doc = "Fibonacci test")
@main
def fib() = {
  println("lexing fib program")
  println(escape(lexing_simp(WHILE_REGS, prog2)).mkString("\n"))
}


val prog3 = """
start := 1000;
x := start;
y := start;
z := start;
while 0 < x do {
 while 0 < y do {
  while 0 < z do {
    z := z - 1
  };
  z := start;
  y := y - 1
 };     
 y := start;
 x := x - 1
}
"""

@arg(doc = "Loops test")
@main
def loops() = {
  println("lexing Loops")
  println(escape(lexing_simp(WHILE_REGS, prog3)).mkString("\n"))
}

@arg(doc = "Email Test")
@main
def email() = {
  val lower = "abcdefghijklmnopqrstuvwxyz"

  val NAME = RECD("name", PLUS(RANGE(lower ++ "_.-")))
  val DOMAIN = RECD("domain", PLUS(RANGE(lower ++ "-")))
  val RE = RANGE(lower ++ ".")
  val TOPLEVEL = RECD("top", (RE ~ RE) |
                             (RE ~ RE ~ RE) | 
                             (RE ~ RE ~ RE ~ RE) | 
                             (RE ~ RE ~ RE ~ RE ~ RE) |
                             (RE ~ RE ~ RE ~ RE ~ RE ~ RE))

  val EMAIL = NAME ~ "@" ~ DOMAIN ~ "." ~ TOPLEVEL

  println(lexing_simp(EMAIL, "christian.urban@kcl.ac.uk"))
}


@arg(doc = "All tests.")
@main
def all() = { small(); fib() ; loops() ; email() } 



// runs with amm2 and amm3




