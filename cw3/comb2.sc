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
// type Tokens = List[Token]
// use List(String, String) if you cannot get it to work with the lexer


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
case class TknParser(s: (String, String)) extends Parser[List[(String, String)], String] {
  def parse(sb: List[(String, String)]) = {
    if (!sb.isEmpty && s._2 == sb.head._2) Set((s._2, sb.tail)) else Set()
  }
}

case object StrParser extends Parser[List[(String, String)], String] {
  def parse(sb: List[(String, String)]) = {
    if (!sb.isEmpty && sb.head._1 == "str") Set((sb.head._2, sb.tail)) else Set()
  }
}

// atomic parser for identifiers (variable names)
case object IdParser extends Parser[List[(String, String)], String] {
  val reg = "[a-z][a-z,0-9]*".r
  def parse(sb: List[(String, String)]) = {
    if (!sb.isEmpty && sb.head._1 == "i") Set((sb.head._2, sb.tail)) else Set()
  }
}


// atomic parser for numbers (transformed into ints)
case object NumParser extends Parser[List[(String, String)], Int] {
  val reg = "[0-9]+".r
  def parse(sb: List[(String, String)]) = {
    if (!sb.isEmpty && sb.head._1 == "n") Set((sb.head._2.toInt, sb.tail)) else Set()
  }
}

// the following string interpolation allows us to write 
// StrParser(_some_string_) more conveniently as 
//
// p"<_some_string_>" 

// implicit def parser_interpolation(sc: StringContext) = new {
//     def p(args: Any*) = StrParser(sc.s(args:_*))
// }    

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
lazy val AExp: Parser[List[(String, String)], AExp] = 
  (Te ~ TknParser("o", "+") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ TknParser("o", "-") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[List[(String, String)], AExp] = 
  (Fa ~ TknParser("o", "*") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
  (Fa ~ TknParser("o", "/") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || 
  (Fa ~ TknParser("o", "%") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || Fa  
lazy val Fa: Parser[List[(String, String)], AExp] = 
   (TknParser("r", "(") ~ AExp ~ TknParser("r", ")")).map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num)

// boolean expressions with some simple nesting
lazy val BExp: Parser[List[(String, String)], BExp] = 
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
lazy val Stmt: Parser[List[(String, String)], Stmt] =
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
   (TknParser("k", "while") ~ BExp ~  TknParser("k", "do") ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ z => While(y, z) })   
 
 
// statements
lazy val Stmts: Parser[List[(String, String)], Block] =
  (Stmt ~ TknParser("s", ";") ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[(String, String)], Block] =
  ((TknParser("cu", "{") ~ Stmts ~ TknParser("cu", "}")).map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))

// filters out whitespaces and comments from tokens
def filter_tokens(toks: List[(String, String)]) = toks.filter(_._1 != "w").filter(_._1 != "c")



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

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case WriteVar(x) => { println(env(x)) ; env }
  case WriteStr(x) => { println(x.stripPrefix("\"").stripSuffix("\"")) ; env }
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


// more examles

// calculate and print all factors bigger 
// than 1 and smaller than n
println("Factors")

val factors =  
   """n := 12;
      f := 2;
      while (f < n / 2 + 1) do {
        if ((n / f) * f == n) then  { write(f) } else { skip };
        f := f + 1
      }""".replaceAll("\\s+", "")

// println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, factors))).head))


// calculate all prime numbers up to a number 
println("Primes")

val primes =  
   """end := 100;
      n := 2;
      while (n < end) do {
        f := 2;
        tmp := 0;
        while ((f < n / 2 + 1) && (tmp == 0)) do {
          if ((n / f) * f == n) then  { tmp := 1 } else { skip };
          f := f + 1
        };
        if (tmp == 0) then { write(n) } else { skip };
        n  := n + 1
      }""".replaceAll("\\s+", "")

// println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, primes))).head))



// tests

def time_elapsed(t0: Long, t1: Long) = { println("Elapsed time: " + (t1 - t0).toDouble/1000000000 + "s") }

val q2_prog = "if (a < b) then skip else a := a * b + 1"

@arg(doc = "Test from question 2")
@main
def q2() = {
  println("if (a < b) then skip else a := a * b + 1")
  Stmt.parse_all(filter_tokens(lexing_simp(WHILE_REGS, q2_prog)))
}


@arg(doc = "Evaluate fib.while program")
@main
def e_fib() = {
  val prog = scala.io.Source.fromFile("fib.while").getLines.mkString("\n")
  println("Evaluate fib.while\n")
  val t0 = System.nanoTime()
  println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, prog))).head))
  val t1 = System.nanoTime()
  time_elapsed(t0, t1)
}

// just the time for evaluating a parse tree, not the time to lex the program
@arg(doc = "Evaluate loop.while program")
@main
def e_loop() = {
  val prog = scala.io.Source.fromFile("loop.while").getLines.mkString("\n")
  println("Evaluate loop.while\n")
  val t0 = System.nanoTime()
  println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, prog))).head))
  val t1 = System.nanoTime()
  time_elapsed(t0, t1)
}

@arg(doc = "Evaluate loop.while parse tree")
@main
def eval_loop() = {
  val prog = scala.io.Source.fromFile("loop.while").getLines.mkString("\n")
  println("Evaluate loop.while\n")
  val parse_tree = Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, prog))).head
  val t0 = System.nanoTime()
  println(eval(parse_tree))
  val t1 = System.nanoTime()
  time_elapsed(t0, t1)
}

@arg(doc = "Evaluate prime.while program")
@main
def e_prime() = {
  val prog = scala.io.Source.fromFile("prime.while").getLines.mkString("\n")
  println("Evaluate prime.while\n")
  val t0 = System.nanoTime()
  println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, prog))).head))
  val t1 = System.nanoTime()
  time_elapsed(t0, t1)
}

@arg(doc = "Evaluate collatz.while program")
@main
def e_coll() = {
  val prog = scala.io.Source.fromFile("collatz.while").getLines.mkString("\n")
  println("Evaluate collatz.while\n")
  val t0 = System.nanoTime()
  println(eval(Stmts.parse_all(filter_tokens(lexing_simp(WHILE_REGS, prog))).head))
  val t1 = System.nanoTime()
  time_elapsed(t0, t1)
}

// runs with amm2 and amm3
