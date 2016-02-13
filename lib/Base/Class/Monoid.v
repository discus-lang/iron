

Class Monoid
  {A     : Type}          (* The carrier type *)
  (unit  : A)             (* A neutral element *)
  (dot   : A -> A -> A)   (* An associative binary operator *)
:= {
  unit_left 
   : forall x
   , dot unit x = x;

  unit_right
   : forall x
   , dot x unit = x;

  dot_assoc
   : forall x y z
   , dot x (dot y z) = dot (dot x y) z
}.


