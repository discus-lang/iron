
Require Import Program.Basics.


Class Functor 
  {F     : Type -> Type}
  (map   : forall {A B : Type}
         , (A -> B) -> F A -> F B)
:= {
  map_id 
   : forall {A} (xx : F A)
   , map id xx = id xx;

  map_map 
   : forall {A B C} (p : B -> C) (q : A -> B) (xx: F A)
   , map (compose p q) xx = compose (map p) (map q) xx
}.



