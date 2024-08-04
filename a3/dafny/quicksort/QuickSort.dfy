include "part.dfy"


method qsort(a:array<int>, l:nat, u:nat)
  requires a != null
  requires l <= u < a.Length
  modifies a

  ensures sorted_between(a, l, u+1)

{


}
