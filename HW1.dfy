method Q2(x : int, y : int) returns (big : int, small : int)
requires x != y;
ensures big > small;
{
  if (x > y)
    {big, small := x, y;}
  else
    {big, small := y, x;}
}

method Q3(n0 : int, m0 : int) returns (res : int)
ensures res == n0 * m0
{
  var n, m : int;
  res := 0;
  if (n0 >= 0) 
       {n,m := n0, m0;} 
  else 
       {n,m := -n0, -m0;}
  while (n > 0) 
  decreases n
  invariant (n*m + res) == n0*m0 && n >= 0
  { 
    res := res + m; 
    n := n - 1; 
  }
}

// method subproblem1(n0 : int, m0 : int) returns (res : int)
// ensures (n*m + res) == n0*m0
// {
//   var n, m : int;
//   res := 0;
//   if (n0 >= 0) 
//        {n,m := n0, m0;} 
//   else 
//        {n,m := -n0, -m0;}
// }

// method subproblem2(n0 : int, m0 : int) returns (res : int)
// requires (n*m + res) == n0*m0 && 0 < n
// ensures (n*m + res) == n0*m0
// {
//     res := res + m; 
//     n := n - 1; 
// }

// method subproblem5(n0 : int, m0 : int) returns (res : int)
// requires ((n*m + res) == n0*m0) && (n>0)
// ensures old(n) == n+1
// {
//   res := res + m; 
//   n := n - 1; 
// }

method ComputeFact(n : nat) returns (res : nat)
requires n > 0;
ensures res == fact(n);
{
  res := 1;
  var i := 2;
  while (i <= n)
  decreases n - i + 1
  invariant res == fact(i-1) && 1 <= i && i <= n + 1
  {
    res := res * i;
    i := i + 1;
  }
}

function fact(n : nat): nat
requires n > 0;
{
  if n == 1 then 1 else n*fact(n-1)
}

// method subproblem1(n : nat) returns (res : nat)
// requires n > 0;
// ensures res == fact(i-1) && 1 <= i && i <= n + 1;
// {
//   res := 1;
//   var i := 2;
// }

// method subproblem2(n : nat) returns (res : nat)
// requires (res == fact(i-1) && 1 <= i && i <= n + 1) && (i <= n)
// ensures res == fact(i-1) && 1 <= i && i <= n + 1
// {
//   res := res * i;
//   i := i + 1;
// }

// method subproblem5(n : nat) returns (res : nat)
// requires (res == fact(i-1) && 1 <= i && i <= n + 1) && (i <= n)
// ensures old(n - i + 1) > n - i + 1
// {
//   res := res * i;
//   i := i + 1;
// }