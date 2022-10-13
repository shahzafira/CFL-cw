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

// Testing
// matcher(BETWEEN(CHAR('a'), 2, 4), "")


abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
// check range input type, could be list or set
case class RANGE(ls: List[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTION(r: Rexp) extends Rexp
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
  // characters will never be nullible
  // cannot return ZERO or ONE as it needs to be boolean directly
  case RANGE(r) => false
  case PLUS(r) => nullable(r)
  case OPTION(r) => true
  // upto = true###
  case UPTO(r, m) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  // maybe check n? what difference does it make
  case BETWEEN(r, n, m) => if (m == 0) true else nullable(r)
  case NOT(r) => !nullable(r)
  // case CFUN(f) => 
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
  // for range pass s as a counter, check first character is C, else recursive with s-1 s[0]
  // Look at look for contains and derivatives
  case RANGE(ls) => if (ls.contains(c)) ONE else ZERO
  // because of the SEQ it cant be nullable, so theres no need to check
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  // case OPTION(r) => if (nullable(r)) ZERO else der(c, r)
  case OPTION(r) => der(c, r)
  case UPTO(r, m) => if (m == 0) ZERO else SEQ(der(c, r), UPTO(r, m-1))
  // check these cases and the last section
  case FROM(r, n) => SEQ(SEQ(der(c, r), FROM(r, n-1)), STAR(r))
  // case FROM(r, n) => if (n == 0) ZERO else SEQ(der(c, r), FROM(r, n-1))
  case BETWEEN(r, n, m) => if (n == 0) ZERO else SEQ(der(c, r), UPTO(r, m-1))
  // case recursive?
  case NOT(r) => NOT(der(c, r))
  // case CFUN(f) => 
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

// email address rexp
// SEQ(SEQ(SEQ(SEQ(PLUS(_), @), PLUS(_)), .), BETWEEN(_, 2, 6))
// zafira.shah@kcl.ac.uk
// use the matcher algorithm
// or use the der function?
// ders("zafira.shah@kcl.ac.uk".toList, SEQ(SEQ(SEQ(SEQ(PLUS(_), @), PLUS(_)), .), BETWEEN(_, 2, 6)))


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

@arg(doc = "Test range regular expression")
@main
def testrange() = {
  println("matcher(RANGE(List('a', 'b')), \"\")")
  println(if (matcher(RANGE(List('a', 'b')), "") == false) "pass" else "fail")

  println("matcher(RANGE(List('a', 'b')), \"a\")")
  println(if (matcher(RANGE(List('a', 'b')), "a") == true) "pass" else "fail")

  println("matcher(RANGE(List('a', 'b')), \"b\")")
  println(if (matcher(RANGE(List('a', 'b')), "b") == true) "pass" else "fail")

  println("matcher(RANGE(List('a', 'b')), \"c\")")
  println(if (matcher(RANGE(List('a', 'b')), "c") == false) "pass" else "fail")

  println("matcher(RANGE(List('a', 'b')), \"ab\")")
  println(if (matcher(RANGE(List('a', 'b')), "ab") == false) "pass" else "fail")
}

@arg(doc = "Test plus regular expression")
@main
def testplus() = {
  println("matcher(PLUS(CHAR('a')), \"\")")
  println(if (matcher(PLUS(CHAR('a')), "") == false) "pass" else "fail")

  println("matcher(PLUS(CHAR('a')), \"a\")")
  println(if (matcher(PLUS(CHAR('a')), "a") == true) "pass" else "fail")

  println("matcher(PLUS(CHAR('a')), \"aa\")")
  println(if (matcher(PLUS(CHAR('a')), "aa") == true) "pass" else "fail")

  println("matcher(PLUS(CHAR('a')), \"aaa\")")
  println(if (matcher(PLUS(CHAR('a')), "aaa") == true) "pass" else "fail")

  println("matcher(PLUS(CHAR('a')), \"b\")")
  println(if (matcher(PLUS(CHAR('a')), "b") == false) "pass" else "fail")

  println("matcher(PLUS(CHAR('a')), \"ab\")")
  println(if (matcher(PLUS(CHAR('a')), "ab") == false) "pass" else "fail")
}

@arg(doc = "Test between regular expression")
@main
def testbetween() = {
  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "") == false) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"a\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "a") == false) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"aa\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "aa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"aaa\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "aaa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"aaaa\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "aaaa") == true) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"aaaaa\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "aaaaa") == false) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"b\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "b") == false) "pass" else "fail")

  println("matcher(BETWEEN(CHAR('a'), 2, 4), \"bbb\")")
  println(if (matcher(BETWEEN(CHAR('a'), 2, 4), "bbb") == false) "pass" else "fail")
}

@arg(doc = "Test upto regular expression")
@main
def testupto() = {
  println("matcher(UPTO(CHAR('a'), 3), \"\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "") == true) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"a\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "a") == true) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"aa\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "aa") == true) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"aaa\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "aaa") == true) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"aaaa\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "aaaa") == false) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"b\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "b") == false) "pass" else "fail")

  println("matcher(UPTO(CHAR('a'), 3), \"bbb\")")
  println(if (matcher(UPTO(CHAR('a'), 3), "bbb") == false) "pass" else "fail")

}

@arg(doc = "Test from regular expression")
@main
def testfrom() = {
  println("matcher(FROM(CHAR('a'), 2), \"\")")
  println(if (matcher(FROM(CHAR('a'), 2), "") == false) "pass" else "fail")

  println("matcher(FROM(CHAR('a'), 2), \"a\")")
  println(if (matcher(FROM(CHAR('a'), 2), "a") == false) "pass" else "fail")

  println("matcher(FROM(CHAR('a'), 2), \"aa\")")
  println(if (matcher(FROM(CHAR('a'), 2), "aa") == true) "pass" else "fail")

  println("matcher(FROM(CHAR('a'), 2), \"aaa\")")
  println(if (matcher(FROM(CHAR('a'), 2), "aaa") == true) "pass" else "fail")

  println("matcher(FROM(CHAR('a'), 2), \"b\")")
  println(if (matcher(FROM(CHAR('a'), 2), "b") == false) "pass" else "fail")

  println("matcher(FROM(CHAR('a'), 2), \"bb\")")
  println(if (matcher(FROM(CHAR('a'), 2), "bb") == false) "pass" else "fail")
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


