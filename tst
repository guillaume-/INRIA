type integer;
type boolean = enum (true, false);
procedure proc1 (integer) -> integer;

process P1 = (
? integer z;
  boolean w;
! integer y;
  boolean x;
)
(
| y := z default 2
| x :=  (not w) when w 
| w ^= z
|)
end;

process toy = (
? integer a;
  boolean d; 
! integer b;
  boolean c;
)
(| submodule P1(b,c)(a,d)
 | b ^= d
 |)
end;

process truc = (
? integer r;
  boolean s;
! integer t;
  boolean u;
)
(|submodule toy(t,u)(r,s)
|)
end;
