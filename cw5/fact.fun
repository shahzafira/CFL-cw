// a simple factorial program
// (including a tail recursive version)


def fact(n: Int) : Int =
  if n == 0 then 1 else n * fact(n - 1);

def facT(n: Int, acc: Int) : Int =
  if n == 0 then acc else facT(n - 1, n * acc);

def facTi(n: Int) : Int = facT(n, 1);

def top() : Void = {
  print_int(fact(6));
  print_char(',');
  print_int(facTi(6));
  print_char('\n')
};

top()
