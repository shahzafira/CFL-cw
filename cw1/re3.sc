// A version with simplification of derivatives;
// this keeps the regular expressions small, which
// is good for the run-time
// 
// call the test cases with X = {1,2}
//
//   amm re3.sc testX
//
// or 
//
//   amm re3.sc all

// Zafira Shah k19008701
// CFL Coursework 1 submission



abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(ls: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp



// the nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
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


// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  // as long as ls contains at least one matching char then it can pass an empty string
  case RANGE(ls) => if (ls.contains(c)) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), OPTIONAL(PLUS(r)))
  case OPTIONAL(r) => der(c, r)
  case UPTO(r, m) => if (m == 0) ZERO else SEQ(der(c, r), UPTO(r, m-1))
  case FROM(r, n) => if (n == 0) SEQ(der(c, r), PLUS(OPTIONAL(r))) else SEQ(SEQ(der(c, r), FROM(r, n-1)), PLUS(OPTIONAL(r)))
  // n times at least, followed up upto(m) 
  case BETWEEN(r, n, m) => if (m == 0) ZERO else if (n == 0) SEQ(der(c, r), UPTO(r, n)) else SEQ(SEQ(der(c, r), NTIMES(r, n-1)), UPTO(r, m-n)) 
  case NOT(r) => NOT(der(c, r))
  case CFUN(f) => if (f(c)) ONE else ZERO
  // if f accepts char, then there is a set to derivate
}

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}



// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}


// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = 
  nullable(ders(s.toList, r))


// one or zero
def OPT(r: Rexp) = ALT(r, ONE)

// question 4
// can replicate the other functions of CHAR, RANGE
// had to be before q3 so that it can be used
def CFUNCHAR(c: Char) : Rexp = {
  def f(d: Char) = c == d
  CFUN(f)
}
def CFUNRANGE(ls: Set[Char]) : Rexp = {
  def f(d: Char) = ls.contains(d)
  CFUN(f)
}
// always true
def CFUNALL() : Rexp = {
  def f(d: Char) = true
  CFUN(f)
}

// question 3
// should print out in the same order as the table in the 
// coursework document
@main
def q3() = {
  val rexps = List(
    OPTIONAL(CFUNCHAR('a')),
    NOT(CFUNCHAR('a')),
    NTIMES(CFUNCHAR('a'), 3),
    NTIMES(OPTIONAL(CFUNCHAR('a')), 3),
    UPTO(CFUNCHAR('a'), 3),
    UPTO(OPTIONAL(CFUNCHAR('a')), 3),
    BETWEEN(CFUNCHAR('a'), 3, 5),
    BETWEEN(OPTIONAL(CFUNCHAR('a')), 3, 5)
  )

  val strings = List(
    "",
    "a",
    "aa",
    "aaa",
    "aaaaa",
    "aaaaaa"
  )

  for (string <- strings) {
    for (rexp <- rexps) {
      print(matcher(rexp, string) + "    ")
    }
    println("\n")
  }

}


// question 5
// zafira.shah@kcl.ac.uk
@main
def q5() = {
  val charset = ('a' to 'z').toSet ++ ('0' to '9').toSet ++ Set('.')
  val charset2 = ('a' to 'z').toSet ++ ('0' to '9').toSet ++ (".-").toSet
  val charset3 = ('a' to 'z').toSet ++ ('0' to '9').toSet ++ (".-_").toSet
  val emailrexp = SEQ(SEQ(SEQ(SEQ(PLUS(RANGE(charset3)), CHAR('@')), PLUS(RANGE(charset2))), CHAR('.')), BETWEEN(RANGE(charset), 2, 6))
  println(ders(("zafira.shah@kcl.ac.uk").toList, emailrexp))
  println(matcher(emailrexp, "zafira.shah@kcl.ac.uk"))
}


// question 6
@main
def q6() {
  val notrexp = NOT(SEQ(SEQ(SEQ(STAR(CFUNALL), CFUNCHAR('*')), CFUNCHAR('/')), STAR(CFUNALL)))
  val rexp = SEQ(SEQ(SEQ(SEQ(CFUNCHAR('/'), CFUNCHAR('*')), notrexp), CFUNCHAR('*')), CFUNCHAR('/'))

  val strings = List(
    "/**/",
    "/*foobar*/",
    "/*test*/test*/",
    "/*test/*test*/"
  )
  
  for (string <- strings) {
    println(string + " " + matcher(rexp, string))
  }
}

// question 7
@main
def q7() {
  val r1 = SEQ(SEQ(CFUNCHAR('a'), CFUNCHAR('a')), CFUNCHAR('a'))
  val r2 = SEQ(BETWEEN(CFUNCHAR('a'), 19, 19), OPTIONAL(CFUNCHAR('a')))

  val strings = List(
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  )

  println("((a . a . a)+)+")
  for (string <- strings) {
    println(matcher(PLUS(PLUS(r1)), string))
  }
  println("\n(((a{19,19}) . (a?))+)+")
  for (string <- strings) {
    println(matcher(PLUS(PLUS(r2)), string))
  }
}


// Test Cases

// evil regular expressions: (a?){n} a{n}  and (a*)* b
def EVIL1(n: Int) = SEQ(NTIMES(OPT(CHAR('a')), n), NTIMES(CHAR('a'), n))
val EVIL2 = SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))


def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


@arg(doc = "Test (a?{n}) (a{n})")
@main
def test1() = {
  println("Test (a?{n}) (a{n})")

  for (i <- 0 to 9000 by 1000) {
    println(f"$i: ${time_needed(3, matcher(EVIL1(i), "a" * i))}%.5f")
  }
}  

@arg(doc = "Test (a*)* b")
@main
def test2() = {
  println("Test (a*)* b")

  for (i <- 0 to 6000000 by 500000) {
    println(f"$i: ${time_needed(3, matcher(EVIL2, "a" * i))}%.5f")
  }
}

// size of a regular expressions - for testing purposes 
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size(r2)
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case STAR(r) => 1 + size(r)
  case NTIMES(r, _) => 1 + size(r)
}


// now the size of the derivatives grows 
// much, much slower

size(ders("".toList, EVIL2))      // 5
size(ders("a".toList, EVIL2))     // 8
size(ders("aa".toList, EVIL2))    // 8
size(ders("aaa".toList, EVIL2))   // 8
size(ders("aaaa".toList, EVIL2))  // 8
size(ders("aaaaa".toList, EVIL2)) // 8


@arg(doc = "All tests.")
@main
def all() = { test1(); test2() } 


@arg(doc = "Test range regular expression")
@main
def testrange() = {
  println("matcher(CFUNRANGE(Set('a', 'b')), \"\")")
  println(if (matcher(CFUNRANGE(Set('a', 'b')), "") == false) "pass" else "fail")

  println("matcher(CFUNRANGE(Set('a', 'b')), \"a\")")
  println(if (matcher(CFUNRANGE(Set('a', 'b')), "a") == true) "pass" else "fail")

  println("matcher(CFUNRANGE(Set('a', 'b')), \"b\")")
  println(if (matcher(CFUNRANGE(Set('a', 'b')), "b") == true) "pass" else "fail")

  println("matcher(CFUNRANGE(Set('a', 'b')), \"c\")")
  println(if (matcher(CFUNRANGE(Set('a', 'b')), "c") == false) "pass" else "fail")

  println("matcher(CFUNRANGE(Set('a', 'b')), \"ab\")")
  println(if (matcher(CFUNRANGE(Set('a', 'b')), "ab") == false) "pass" else "fail")
}

@arg(doc = "Test plus regular expression")
@main
def testplus() = {
  println("matcher(PLUS(CFUNCHAR('a')), \"\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "") == false) "pass" else "fail")

  println("matcher(PLUS(CFUNCHAR('a')), \"a\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "a") == true) "pass" else "fail")

  println("matcher(PLUS(CFUNCHAR('a')), \"aa\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "aa") == true) "pass" else "fail")

  println("matcher(PLUS(CFUNCHAR('a')), \"aaa\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "aaa") == true) "pass" else "fail")

  println("matcher(PLUS(CFUNCHAR('a')), \"b\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "b") == false) "pass" else "fail")

  println("matcher(PLUS(CFUNCHAR('a')), \"ab\")")
  println(if (matcher(PLUS(CFUNCHAR('a')), "ab") == false) "pass" else "fail")
}

@arg(doc = "Test optional regular expression")
@main
def testoptional() = {
  println("matcher(OPTIONAL(CFUNCHAR('a')), \"\")")
  println(if (matcher(OPTIONAL(CFUNCHAR('a')), "") == true) "pass" else "fail")

  println("matcher(OPTIONAL(CFUNCHAR('a')), \"a\")")
  println(if (matcher(OPTIONAL(CFUNCHAR('a')), "a") == true) "pass" else "fail")

  println("matcher(OPTIONAL(CFUNCHAR('a')), \"aa\")")
  println(if (matcher(OPTIONAL(CFUNCHAR('a')), "aa") == false) "pass" else "fail")

  println("matcher(OPTIONAL(CFUNCHAR('a')), \"b\")")
  println(if (matcher(OPTIONAL(CFUNCHAR('a')), "b") == false) "pass" else "fail")
}

@arg(doc = "Test upto regular expression")
@main
def testupto() = {
  println("matcher(UPTO(CFUNCHAR('a'), 3), \"\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "") == true) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"a\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "a") == true) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"aa\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "aa") == true) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"aaa\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "aaa") == true) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"aaaa\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "aaaa") == false) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"b\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "b") == false) "pass" else "fail")

  println("matcher(UPTO(CFUNCHAR('a'), 3), \"bbb\")")
  println(if (matcher(UPTO(CFUNCHAR('a'), 3), "bbb") == false) "pass" else "fail")
}

@arg(doc = "Test from regular expression")
@main
def testfrom() = {
  println("matcher(FROM(CFUNCHAR('a'), 2), \"\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "") == false) "pass" else "fail")

  println("matcher(FROM(CFUNCHAR('a'), 2), \"a\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "a") == false) "pass" else "fail")

  println("matcher(FROM(CFUNCHAR('a'), 2), \"aa\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "aa") == true) "pass" else "fail")

  println("matcher(FROM(CFUNCHAR('a'), 2), \"aaa\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "aaa") == true) "pass" else "fail")

  println("matcher(FROM(CFUNCHAR('a'), 2), \"b\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "b") == false) "pass" else "fail")

  println("matcher(FROM(CFUNCHAR('a'), 2), \"bb\")")
  println(if (matcher(FROM(CFUNCHAR('a'), 2), "bb") == false) "pass" else "fail")
}

@arg(doc = "Test between regular expression")
@main
def testbetween() = {
  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "") == false) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"a\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "a") == false) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"aa\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "aa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"aaa\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "aaa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"aaaa\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "aaaa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"aaaaa\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "aaaaa") == false) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"b\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "b") == false) "pass" else "fail")

  println("matcher(BETWEEN(CFUNCHAR('a'), 2, 4), \"bbb\")")
  println(if (matcher(BETWEEN(CFUNCHAR('a'), 2, 4), "bbb") == false) "pass" else "fail")
}

@arg(doc = "Test not regular expression")
@main
def testnot() = {
  println("matcher(NOT(CFUNCHAR('a')), \"\")")
  println(if (matcher(NOT(CFUNCHAR('a')), "") == true) "pass" else "fail")

  println("matcher(NOT(CFUNCHAR('a')), \"a\")")
  println(if (matcher(NOT(CFUNCHAR('a')), "a") == false) "pass" else "fail")

  println("matcher(NOT(CFUNCHAR('a')), \"aa\")")
  println(if (matcher(NOT(CFUNCHAR('a')), "aa") == true) "pass" else "fail")

  println("matcher(NOT(CFUNCHAR('a')), \"b\")")
  println(if (matcher(NOT(CFUNCHAR('a')), "b") == true) "pass" else "fail")

  println("matcher(NOT(CFUNCHAR('a')), \"bb\")")
  println(if (matcher(NOT(CFUNCHAR('a')), "bb") == true) "pass" else "fail")
}



// PS:
//
// If you want to dig deeper into the topic, you can have 
// a look at these examples which still explode. They
// need an even more aggressive simplification.

// test: (a + aa)*
val EVIL3 = STAR(ALT(CHAR('a'), SEQ(CHAR('a'), CHAR('a'))))


@arg(doc = "Test EVIL3")
@main
def test3() = {
  println("Test (a + aa)*")

  for (i <- 0 to 30 by 5) {
    println(f"$i: ${time_needed(1, matcher(EVIL3, "a" * i))}%.5f")
  }
}


// test: (1 + a + aa)*
val EVIL4 = STAR(ALT(ONE, ALT(CHAR('a'), SEQ(CHAR('a'), CHAR('a')))))

@arg(doc = "Test EVIL4")
@main
def test4() = {
  println("Test (1 + a + aa)*")

  for (i <- 0 to 30 by 5) {
    println(f"$i: ${time_needed(1, matcher(EVIL4, "a" * i))}%.5f")
  }
}

@arg(doc = "Tests that show not all is hunky-dory, but a solution leads too far afield.")
@main
def fail() = { test3(); test4() } 

