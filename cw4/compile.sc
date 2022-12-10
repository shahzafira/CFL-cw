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
case class PL(r: Rexp) extends Rexp
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
  case PL(r) => nullable(r)
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
  case Pl(vs) => vs.map(flatten).mkString
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
  case Pl(vs) => vs.flatMap(env)
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

def PL(r: Rexp) = r ~ r.%

def Range(s : List[Char]) : Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => ALT(CHAR(c), Range(s))
}
def RANGE(s: String) = Range(s.toList)

// Question 1
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "for" | "to" | "true" | "false" | "upto"
val OP : Rexp = ":=" | "=" | "-" | "+" | "*" | "!=" | "<" | ">" | "%" | "/" | "==" | "<=" | ">=" | "&&" | "||"
val LETTER = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
val SYM = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz._><=;,\\:")
val DIGIT = RANGE("0123456789")
val WHITESPACE : Rexp = " " | "\n" | "\t" | "\r"
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

// escapes strings and prints them out as "", "\n" and so on
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

def filter_white_space(tokens: List[(String, String)]) = tokens.filter(_._1 != "w")




// runs with amm2 and amm3


// Parser Combinators:
// Simple Version for WHILE-language
//====================================
//
// with some added convenience for
// map-parsers and grammar rules
//
// call with
//
//    amm comb2.sc


// more convenience for the map parsers later on;
// it allows writing nested patterns as
// case x ~ y ~ z => ...



case class ~[+A, +B](x: A, y: B)

// constraint for the input
type IsSeq[A] = A => Seq[_]
type Tokens = List[(String, String)]


abstract class Parser[I : IsSeq, T]{
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}


// remember that tokens (String, String) are the type and then what it actually contains
// atomic parser for (particular) strings
case class TknParser(s: (String, String)) extends Parser[Tokens, String] {
  def parse(sb: Tokens) = {
    if (!sb.isEmpty && s._2 == sb.head._2) Set((s._2, sb.tail)) else Set()
  }
}

case object StrParser extends Parser[Tokens, String] {
  def parse(sb: Tokens) = {
    if (!sb.isEmpty && sb.head._1 == "str") Set((sb.head._2, sb.tail)) else Set()
  }
}

// atomic parser for identifiers (variable names)
case object IdParser extends Parser[Tokens, String] {
  val reg = "[a-z][a-z,0-9]*".r
  def parse(sb: Tokens) = {
    if (!sb.isEmpty && sb.head._1 == "i") Set((sb.head._2, sb.tail)) else Set()
  }
}


// atomic parser for numbers (transformed into ints)
case object NumParser extends Parser[Tokens, Int] {
  val reg = "[0-9]+".r
  def parse(sb: Tokens) = {
    if (!sb.isEmpty && sb.head._1 == "n") Set((sb.head._2.toInt, sb.tail)) else Set()
  }
}

    

// more convenient syntax for parser combinators
implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}



// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]


case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class For(id: String, x: AExp, y: AExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class WriteVar(s: String) extends Stmt
case class WriteStr(s: String) extends Stmt
case class Read(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class Lop(o: String, b1: BExp, b2: BExp) extends BExp



// arithmetic expressions
lazy val AExp: Parser[Tokens, AExp] = 
  (Te ~ TknParser("o", "+") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ TknParser("o", "-") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[Tokens, AExp] = 
  (Fa ~ TknParser("o", "*") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
  (Fa ~ TknParser("o", "/") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || 
  (Fa ~ TknParser("o", "%") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || Fa  
lazy val Fa: Parser[Tokens, AExp] = 
   (TknParser("r", "(") ~ AExp ~ TknParser("r", ")")).map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num)

// boolean expressions with some simple nesting
lazy val BExp: Parser[Tokens, BExp] = 
   (AExp ~ TknParser("o", "==") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ TknParser("o", "!=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ TknParser("o", "<") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ TknParser("o", ">") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ TknParser("o", "<=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } || 
   (AExp ~ TknParser("o", ">=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } ||
   (TknParser("r", "(") ~ BExp ~ TknParser("r", ")") ~ TknParser("o", "&&") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Lop("&&", y, v) } ||
   (TknParser("r", "(") ~ BExp ~ TknParser("r", ")") ~ TknParser("o", "||") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Lop("||", y, v) } ||
   (TknParser("k", "true").map[BExp]{ _ => True }) || 
   (TknParser("k", "false").map[BExp]{ _ => False }) ||
   (TknParser("r", "(") ~ BExp ~ TknParser("r", ")")).map[BExp]{ case _ ~ x ~ _ => x }

// a single statement 
lazy val Stmt: Parser[Tokens, Stmt] =
  ((TknParser("k", "skip").map[Stmt]{_ => Skip }) ||
   (IdParser ~ TknParser("o", ":=") ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (TknParser("k", "write") ~ TknParser("r", "(") ~ IdParser ~ TknParser("r", ")")).map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteVar(y) } ||
   (TknParser("k", "write") ~ IdParser).map[Stmt]{ case _ ~ z => WriteVar(z) } ||
   (TknParser("k", "write") ~ TknParser("r", "(") ~ StrParser ~ TknParser("r", ")")).map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
   (TknParser("k", "write") ~ StrParser).map[Stmt]{ case _ ~ z => WriteStr(z) } ||
   (TknParser("k", "read") ~ TknParser("r", "(") ~ IdParser ~ TknParser("r", ")")).map[Stmt]{ case _ ~ _ ~ y ~ _ => Read(y) } ||
   (TknParser("k", "read") ~ IdParser).map[Stmt]{ case _ ~ z => Read(z) } ||
   (TknParser("k", "if") ~ BExp ~ TknParser("k", "then") ~ Block ~ TknParser("k", "else") ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (TknParser("k", "while") ~ BExp ~  TknParser("k", "do") ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ z => While(y, z) } ||
   (TknParser("k", "for") ~ IdParser ~ TknParser("o", ":=") ~ AExp ~ TknParser("k", "upto") ~ AExp ~ TknParser("k", "do") ~ Block)
     .map[Stmt]{ case _ ~ w ~ _ ~ x ~ _ ~ y ~ _ ~ z => For(w, x, y, z) })   
 
 
// statements
lazy val Stmts: Parser[Tokens, Block] =
  (Stmt ~ TknParser("s", ";") ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[Tokens, Block] =
  ((TknParser("cu", "{") ~ Stmts ~ TknParser("cu", "}")).map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))

// filters out whitespaces and comments from tokens
def filter_tokens(toks: Tokens) = toks.filter(_._1 != "w").filter(_._1 != "c")



// Examples
// Stmt.parse_all("x2:=5+3")
// Block.parse_all("{x:=5;y:=8}")
// Block.parse_all("if(false)then{x:=5}else{x:=10}")


val fib = """n := 10;
             minus1 := 0;
             minus2 := 1;
             temp := 0;
             while (n > 0) do {
                 temp := minus2;
                 minus2 := minus1 + minus2;
                 minus1 := temp;
                 n := n - 1
             };
             result := minus2""".replaceAll("\\s+", "")

// println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, fib))).head))


// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case Lop("&&", b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Lop("||", b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

// you can only assign AExps to variables, so no need to use escape for WriteVar
def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case For(id, x, y, bl) =>
    val env1 = eval_stmt(Assign(id, x), env)
    if (eval_bexp(Bop("<=", Var(id), y), env1)) eval_stmt(For(id, Aop("+", x, Num(1)), y, bl), eval_bl(bl, env1))
    else env1
  case WriteVar(x) => { print(env(x)) ; env }
  case WriteStr(x) => { if (x == esc("\n")) print('\n') else print(x.replaceAll("^\"|\"$", "")); env }
  case Read(x) => env + (x -> Console.in.readLine().toInt)
  // try also Console.in.readLine().toInt
}


def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())

// parse + evaluate fib program; then lookup what is
// stored under the variable "result" 
// println(eval(Stmts.parse_all(fib).head)("result"))



// A Small Compiler for the WHILE Language
// (it does not use a parser nor lexer)
//
// cal with 
//
//   amm compile.sc test
//   amm compile.sc test2



// compiler headers needed for the JVM
// (contains methods for read and write)
val beginning = """
.class public XXX.XXX
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

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""

// Compiler functions


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// convenient string interpolations 
// for instructions and labels
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows us to write things like
// i"iadd" and l"Label"


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
  case "/" => i"idiv"
  case "%" => i"irem"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop(">", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp"
  case Bop("<=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case Bop(">=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmplt $jmp"
}
// add the logical operators

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  // b is bexp and bl is the block to run
  // aexp doesn't change the env
  case For(id, x, y, bl) => {
    val for_begin = Fresh("For_begin")
    val for_end = Fresh("For_end")
    val (instrs1, env1) = compile_stmt(Assign(id, x), env)
    val (instrs2, env2) = compile_block(bl, env1)
    val cond = Bop("<=", Var(id), y)
    (instrs1 ++
     l"$for_begin" ++
     compile_bexp(cond, env1, for_end) ++
     instrs2 ++
     compile_stmt(Assign(id, Aop("+", Var(id), Num(1))), env2)._1 ++
     i"goto $for_begin" ++
     l"$for_end", env1)
  }
  case WriteVar(x) => {
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/writeVar(I)V", env)
  }
  case WriteStr(x) => {
    val y = x.stripPrefix("\"").stripSuffix("\"")
    (i"ldc ${x} \t\t; $y" ++ 
     i"invokestatic XXX/XXX/writeStr(Ljava/lang/String;)V", env)
  }
  case Read(x) => {
   val index = env.getOrElse(x, env.keys.size) 
   (i"invokestatic XXX/XXX/read()I" ++ 
    i"istore $index \t\t; $x", env + (x -> index))
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}

def parse_code(code: String) : List[Stmt] = {
  Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, code))).head
}


// Question 1
// Create files for fib and fact
val fib_toks =
  List(WriteStr("Fib: "),
    Read("n"),
    Assign("minus1",Num(1)),
    Assign("minus2",Num(0)),
    While(Bop(">",Var("n"),Num(0)),
      List(Assign("temp",Var("minus2")),
        Assign("minus2",Aop("+",Var("minus1"),Var("minus2"))),
        Assign("minus1",Var("temp")),
        Assign("n",Aop("-",Var("n"),Num(1))))),
    WriteStr("Result: "),
    WriteVar("minus2"),
    WriteStr("\n")) 

@main
def comp_fib() = 
  compile(fib_toks, "c_fib")

@main
def run_fib() = 
  run(fib_toks, "r_fib")


val fact_code = 
  """write "Fact: ";
  read n;
  f := 1;
  i := 1;
  while (i <= n) do {f := f * i; i := i + 1};
  write(f)"""

val fact_toks = parse_code(fact_code)

@main
def comp_fact() =
  compile(fact_toks, "c_fact")

@main
def run_fact() =
  run(fact_toks, "r_fact")



// compiling and running .j-files
//
// JVM files can be assembled with 
//
//    java -jar jasmin.jar fib.j
//
// and started with
//
//    java fib/fib


def run(bl: Block, class_name: String) = {
    val code = compile(bl, class_name)
    os.write.over(os.pwd / s"$class_name.j", code)
    os.proc("java", "-jar", "jasmin-2.4/jasmin.jar", s"$class_name.j").call()
    os.proc("java", s"$class_name/$class_name").call(stdout = os.Inherit, stdin = os.Inherit)
}

// C:/Users/zafiz/OneDrive/Documents/GitHub/CFL-cw/cw4/


// Tests
val for_code = 
  """for i := 2 upto 4 do { write i };
     for i := 2 upto 2 do { write i };
     for i := 2 upto 1 do { write i }"""

@main
def comp_for() =
  compile(parse_code(for_code), "c_for")

@main
def run_for() =
  run(parse_code(for_code), "r_for")

@main
def eval_for() =
  eval(parse_code(for_code))




/* Jasmin code for reading an integer

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
    ldc 10   ; the newline delimiter 
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

*/





// runs with amm2 and amm3
