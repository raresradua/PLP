From Coq Require Import Strings.String.
From Coq Require Import Ascii.
Scheme Equality for string.
Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Import Nat.


Inductive Sstack (t : Set) : Set :=
| nill : Sstack t
| SStack : t -> Sstack t -> Sstack t.
Check Sstack nat.
Check nill nat.
Check SStack bool true.


Definition push_Sstack (t : Set)(S : Sstack t)(v : t) : Sstack t := (SStack t v S).
Compute (push_Sstack bool (nill bool) true).
Compute (push_Sstack nat (SStack nat 2(nill nat)) 2).
Definition pop_Sstack (t : Set)(S : Sstack t) : Sstack t :=
  match S with
  | SStack _ v s => s
  | nill _ => nill t
  end.
Compute pop_Sstack string (SStack string "helo" (SStack string "ok" (nill string))).
Compute pop_Sstack bool (SStack bool true(nill bool)).

(*
Inductive vector :=
| vector_nat : string -> list nat -> vector
| vector_bool : string -> list bool -> vector
| vector_str : string -> list string -> vector
| vector_all : string -> list ValueTypes -> vector.

Notation "X [int]::= L" := (vector_nat X L) (at level 40).
Notation "X [boolean]::= L" := (vector_bool X L) (at level 40).
Notation "X [str]::= L" := (vector_str X L)(at level 40).
Notation "X [all]::= L" := (vector_all X L) (at level 40).
Check "vec" [int]::= [1;2;3].
Check "vec" [boolean]::= [true;false;false].
Check "vec" [str]::= ["a";"b";"c"].
Check "vec" [all]::= [vs "a";vn 2;vb true].
Compute nth 2 [true].


(*Definition vector_n := string -> list nat.
Definition vector_b := string -> list bool.
Definition vector_s := string -> list string.
Definition vector_a := string -> list ValueTypes.

Inductive vectorExp :=
| push_nat: vector_nat -> nat -> vectorExp
| push_bool: vector_bool -> bool -> vectorExp
| push_string: vector_string -> string -> vectorExp
| push_all: vector_all -> ValueTypes -> vectorExp
| pop_back_nat: vector_nat -> vectorExp
| pop_back_bool: vector_bool -> vectorExp
| pop_back_string: vector_string -> vectorExp
| pop_back_all: vector_all -> vectorExp.
*)

Inductive vectorExp :=
| vec_natelem : string -> nat -> vectorExp
| vec_n : string -> list nat -> vectorExp
| vec_booleanelem : string -> bool -> vectorExp
| vec_b : string -> list bool -> vectorExp
| vec_strelem : string -> list string -> vectorExp
| vec_s : string -> string -> vectorExp
| push_nat : vectorExp -> nat -> vectorExp
| push_bool : vectorExp -> bool -> vectorExp
| push_string : vectorExp -> string -> vectorExp
| pop_back_nat : vectorExp -> vectorExp
| pop_back_boolean : vectorExp -> vectorExp
| pop_back_string: vectorExp -> vectorExp.
*)


Definition vector_nat := list nat.
Definition vector_bool := list bool.
Definition vector_str := list string.
(*
Inductive VecExp :=
| vec_n : vector_nat -> nat -> VecExp
| vec_b : vector_bool -> bool -> VecExp
| vec_s : vector_str -> string -> VecExp
| push_back_nat : vector_nat -> nat -> VecExp
| push_back_bool : vector_bool -> bool -> VecExp
| push_back_str : vector_str -> string -> VecExp
| push_front_nat : vector_nat -> nat -> VecExp
| push_front_bool : vector_bool -> bool -> VecExp
| push_front_str : vector_str -> string -> VecExp
| pop_back_nat : vector_nat -> VecExp
| pop_back_boolean : vector_bool -> VecExp
| pop_back_string : vector_str -> VecExp.
*)
Definition indexNVec(vec : vector_nat) (n : nat) : nat := nth n vec 0. 
Definition indexBVec(vec : vector_bool) (n : nat) : bool := nth n vec true. 
Definition indexSVec(vec : vector_str) (n : nat) : string := nth n vec "". 

Definition pb_nat (vec : vector_nat) (n : nat) : vector_nat := rev( n :: rev vec).
Definition pb_bool (vec : vector_bool) (b : bool) : vector_bool := rev( b :: rev vec).
Definition pb_str (vec : vector_str) (s : string) : vector_str := rev( s :: rev vec).

Definition pf_nat (vec : vector_nat) (n : nat) : vector_nat := n :: vec.
Definition pf_bool (vec : vector_bool) (b : bool) : vector_bool := b :: vec.
Definition pf_str (vec : vector_str) (s : string) : vector_str := s :: vec.

Definition pop_n (vec : vector_nat) : vector_nat := rev(removelast (rev vec)).
Definition pop_b (vec : vector_bool) : vector_bool := rev(removelast (rev vec)).
Definition pop_s (vec : vector_str) : vector_str := rev(removelast (rev vec)).

Inductive ValueTypes :=
| vn : nat -> ValueTypes 
| vb : bool -> ValueTypes
| vs : string -> ValueTypes
| fn : nat -> ValueTypes
| fb : bool -> ValueTypes
| fs : string -> ValueTypes
| sn : Sstack nat -> ValueTypes
| sb : Sstack bool -> ValueTypes
| ss : Sstack string -> ValueTypes
| vvn : list nat -> ValueTypes
| vvb : list bool -> ValueTypes
| vvs : list string -> ValueTypes
| empty : ValueTypes.


Inductive AExp:=
| avar : string -> AExp
| favar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| afrac : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B)(at level 60, right associativity).
Notation "A -' B" := (aminus A B)(at level 60, right associativity).
Notation "A *' B" := (amul A B)(at level 58, left associativity).
Notation "A /' B" := (afrac A B)(at level 58, left associativity).
Notation "A %' B" := (amod A B)(at level 58, left associativity).


Inductive StrExp :=
| strvar : string -> StrExp
| strfvar : string -> StrExp
| strconc : StrExp -> StrExp -> StrExp.


Notation "S <strcat> S'" := (strconc S S')(at level 70).

Inductive BExp :=
| boolvar : string -> BExp
| boolfvar : string -> BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| bor : BExp -> BExp -> BExp
| band : BExp -> BExp -> BExp
| bmorethaneq : AExp -> AExp -> BExp
| blessthaneq : AExp -> AExp -> BExp
| bstrcomp : StrExp -> StrExp -> BExp.

Notation "A <=' B" := (blessthaneq A B) (at level 70).
Notation "A >=' B" := (bmorethaneq A B)(at level 70).
Notation " ! A " := (bnot A)(at level 20).
Notation "A eq?' B" := (bstrcomp A B) (at level 80).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 81).



Coercion avar : string >-> AExp.
Coercion anum : nat >-> AExp.
Coercion boolvar : string >-> BExp.
Coercion strvar : string >-> StrExp.

Check "X" +' "Y".
Check "X" +' 2.
Check "X" -' "Y".
Check "X" -' 10.
Check "X" *' "Y".
Check 2 *' "A".
Check 2 <=' 3.
Check 2 >=' "Y".
Check ! "X".
Check "A" and' btrue.
Check bfalse or' "B".
Check "A" eq?' "B".
Check strvar "X".
Check "X" <strcat> "Y".


Definition Env := string -> ValueTypes.
(* adaugat de aici *)
Definition update_nat (env : Env)
           (var : string) (value : nat) : Env :=
  fun var' => if (string_eq_dec var' var)
              then vn value
              else (env var').

Definition update_bool (env : Env)
           (var : string) (value : bool) : Env :=
  fun var' => if (string_eq_dec var' var)
              then vb value
              else (env var').

Definition update_str (env : Env)
                      (var : string) (value : string) : Env :=
  fun var' => if(string_eq_dec var' var)
              then vs value
              else (env var').

Definition update_fnat (env : Env)
           (var : string) (value : nat) : Env :=
  fun var' => if (string_eq_dec var' var)
              then fn value
              else (env var').

Definition update_fbool (env : Env)
           (var : string) (value : bool) : Env :=
  fun var' => if (string_eq_dec var' var)
              then fb value
              else (env var').

Definition update_fstr (env : Env)
                      (var : string) (value : string) : Env :=
  fun var' => if(string_eq_dec var' var)
              then fs value
              else (env var').
Definition update_VecN (env : Env)(vec : string)(value : list nat) : Env :=
  fun var' => if(string_eq_dec var' vec)
              then vvn value
              else (env var').
Definition update_VecB (env : Env)(vec: string)(value : list bool) : Env :=
  fun var' => if(string_eq_dec var' vec)
              then vvb value
              else (env var').
Definition update_VecS (env : Env)(vec: string)(value : list string) : Env :=
  fun var' => if(string_eq_dec var' vec)
              then vvs value
              else (env var').

Definition env0 : Env :=
    fun v => if(string_beq v "placeholdervar")
             then vn 0
             else if(string_beq v "booltrue")
             then vb true
             else if(string_beq v "boolfalse")
             then vb false
             else if(string_beq v "emptystring")
             then vs ""
             else empty.

Definition env2 : Env :=
  fun v => if(string_beq v "s")
           then vs "hello"
           else if(string_beq v "n")
           then vn 10
           else if(string_beq v "b")
           then vb true
           else empty.


Reserved Notation "A =[ S ]=> N" (at level 61).
Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                            | vn var => var
                                            | _ => 0
                                            end
| fvar: forall v sigma, favar v =[ sigma ]=> match (sigma v) with
                                            | fn var => var
                                            | _ => 0
                                            end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    true = negb (Nat.ltb i1 i2) ->
    a1 -' a2 =[ sigma ]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = i1 mod i2 ->
  true = negb (Nat.leb i2 0) ->
  a1 %' a2 =[ sigma ]=> n
| div : forall a1 a2 i1 i2 sigma n,
   a1 =[ sigma ]=> i1 ->
   a2 =[ sigma ]=> i2 ->
   n = i1 / i2 ->
   true = negb (Nat.leb i2 0) ->
   a1 /' a2 =[ sigma ]=> n

where "a =[ sigma ]=> n" := (aeval a sigma n).

Reserved Notation "A ~{ S }=> B" (at level 75).
Inductive streval : StrExp -> Env -> string -> Prop :=
| s_const : forall s sigma, (strvar s) ~{ sigma }=> match (sigma s) with
                                                  | vs s => s
                                                  | _ => ""
                                                 end
| s_fconst : forall s sigma, (strfvar s) ~{ sigma }=> match (sigma s) with
                                                      | fs s => s
                                                      | _ => ""
                                                      end
| s_conc : forall s s1 s2 sigma a1 a2,
         a1 ~{ sigma }=> s1 ->
         a2 ~{ sigma }=> s2 ->
         s = (append s1 s2) ->
         a1 <strcat> a2 ~{ sigma }=> s
where "A ~{ S }=> B" := (streval A S B).
         
Reserved Notation "B ={ S }=> B'" (at level 70).


Inductive beval : BExp -> Env -> bool -> Prop :=
| e_const : forall b sigma, boolvar b ={ sigma }=> match (sigma b) with
                                                   | vb b => b
                                                   | _ => true
                                                   end
| e_fconst : forall b sigma, boolfvar b ={ sigma }=> match (sigma b) with
                                                     | fb b => b
                                                     | _ => true
                                                     end
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_strcomp : forall s1 s2 sigma a1 a2,
    a1 ~{ sigma }=> s1 ->
    a2 ~{ sigma }=> s2 ->
    (a1 eq?' a2) ={ sigma }=> (string_beq s1 s2)
where "B ={ S }=> B'" := (beval B S B').





Inductive Stmt :=
| declareN : AExp -> Stmt
| declareB : BExp -> Stmt
| declareS : StrExp -> Stmt
| declareVecN : string -> Stmt
| declareVecB : string -> Stmt
| declareVecS : string -> Stmt
| declarareStivaN : string -> Stmt
| declarareStivaB : string -> Stmt
| declarareStivaS : string -> Stmt
| assignmentN : AExp -> AExp -> Stmt
| assignmentB : BExp -> BExp -> Stmt
| assignmentS : StrExp -> StrExp -> Stmt
| assignmentVecN : string -> list nat -> Stmt
| assignmentVecB : string -> list bool -> Stmt
| assignmentVecS : string -> list string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| push_stack_n : string -> nat -> Stmt
| push_stack_b : string -> bool -> Stmt
| push_stack_s : string -> string -> Stmt
| pop_stack_n : string -> Stmt
| pop_stack_b : string -> Stmt
| pop_stack_s : string -> Stmt
| pushb_vec_nat : string -> nat -> Stmt
| pushb_vec_bool : string -> bool -> Stmt
| pushb_vec_string : string -> string -> Stmt
| pushf_vec_nat : string -> nat -> Stmt
| pushf_vec_bool : string -> bool -> Stmt
| pushf_vec_string : string -> string -> Stmt
| pop_vec_nat : string -> Stmt
| pop_vec_bool : string -> Stmt
| pop_vec_string: string -> Stmt
| while : BExp -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| foor : Stmt -> BExp -> Stmt -> Stmt -> Stmt
.
Inductive FStmt :=
| declareFN : AExp -> FStmt
| declareFB : BExp -> FStmt
| declareFS : StrExp -> FStmt
| funct : string -> list FStmt -> Stmt -> FStmt.


Notation "<int> X" := (declareN X)(at level 50).
Notation "<boolean> B" := (declareB B)(at level 50).
Notation "<str> S" := (declareS S)(at level 50).
Notation "X <int>::= Y" := (assignmentN X Y)(at level 50, left associativity).
Notation "B <boolean>::= B'" := (assignmentB B B')(at level 50).
Notation "S <str>::= S'" := (assignmentS S S')(at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'If' ( B ) 'Then' S" := (ifthen B S)(at level 60).
Notation "'If' ( B ) 'Then' S1 'Else' S2" := (ifthenelse B S1 S2)(at level 61).
Notation "'While' ( B ) 'do' S" := (while B S)(at level 60).
Notation "'For' ( I1 ';' B ';' It ) 'do' S" := (foor I1 B It S)(at level 60).
Notation "<fint> X" := (declareFN X)(at level 50).
Notation "<fboolean> B" := (declareFB B)(at level 50).
Notation "<fstring> S" := (declareFS S)(at level 50).

Check funct "main" [ <fint> "X" ] ( <int> "Y" ).

Definition update_StackN (env : Env)(stack : string)(s : Sstack nat) :=
fun x => if (string_eq_dec stack x)
         then sn s
         else env stack.

Definition update_StackB (env : Env)(stack : string)(s : Sstack bool) :=
fun x => if (string_eq_dec stack x)
         then sb s
         else env stack.

Definition update_StackS (env : Env)(stack : string)(s : Sstack string) :=
fun x => if (string_eq_dec stack x)
         then ss s
         else env stack.


Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval_st : Stmt -> Env -> Env -> Prop :=
| e_declareN: forall x sigma sigma',
  sigma' = (update_nat sigma x 0) ->
  (<int> x) -{ sigma }-> sigma'
| e_declareB: forall b sigma sigma',
  sigma' = (update_bool sigma b true) ->
  (<boolean> b) -{ sigma }-> sigma'
| e_declareS: forall s sigma sigma',
  sigma' = (update_str sigma s "") ->
  (<str> s) -{ sigma }-> sigma'
| e_assignmentN : forall a i x sigma (sigma' : Env),
   a =[ sigma ]=> i->
   sigma' = (update_nat sigma x i) ->
   (x <int>::= a) -{ sigma }-> sigma'
| e_assignmentB : forall a i x sigma sigma',
  a ={ sigma }=> i ->
  sigma' = (update_bool sigma x i) ->
  (x <boolean>::= a) -{ sigma }-> sigma'
| e_assignmentS : forall a i x sigma sigma',
  a ~{ sigma }=> i ->
  sigma' = (update_str sigma x i) ->
  (x <str>::= a) -{ sigma }-> sigma'  
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_ifthentrue : forall b s sigma sigma1,
  b ={ sigma }=> true ->
  s -{ sigma }-> sigma1 ->
  (ifthen b s) -{ sigma }-> sigma1
| e_ifthenfalse : forall b s sigma,
  b ={ sigma }=> false ->
  (ifthen b s) -{ sigma }-> sigma
| e_iftrue : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (ifthenelse b s1 s2) -{ sigma }-> sigma1
| e_iffalse : forall b s1 s2 sigma sigma2,
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma2 ->
    (ifthenelse b s1 s2) -{ sigma }-> sigma2
| e_for : forall i1 b sigma sigma' it seq,
  (i1 ;; (while b (seq ;; it) ) ) -{ sigma }-> sigma' ->
  (foor i1 b it seq) -{ sigma }-> sigma'
| e_breakfirst : forall s1 s2 sigma,
   s1 -{ sigma }-> sigma ->
   s2 -{ sigma }-> sigma ->
   (s1 ;; s2) -{ sigma }-> sigma
| e_breaklater : forall s1 s2 sigma sigma',
   s1 -{ sigma }-> sigma' ->
   s2 -{ sigma' }-> sigma' ->
   (s1 ;; s2) -{ sigma }-> sigma'
| e_break : forall s sigma,
   s -{ sigma }-> sigma
| e_continueseq : forall s1 s2 sigma' sigma,
   s1 -{ sigma }-> sigma ->
   s2 -{ sigma }-> sigma' ->
   (s1 ;; s2) -{ sigma }-> sigma'
| e_continue : forall s sigma,
   s -{ sigma }-> sigma
| e_declStivaN : forall s sigma sigma',
  sigma' = update_StackN sigma s (nill nat) ->
  (declarareStivaN s) -{ sigma }-> sigma'
| e_declStivaB : forall s sigma sigma',
  sigma' = update_StackB sigma s (nill bool) ->
  (declarareStivaB s) -{ sigma }-> sigma'
| e_declStivaS : forall s sigma sigma',
  sigma' = update_StackS sigma s (nill string) ->
  (declarareStivaS s) -{ sigma }-> sigma'
| e_push_stack_nat : forall sigma sigma' sigma'' stk n st,
  sigma' = (update_StackN sigma st stk) ->
  sigma'' = (update_StackN sigma st ( push_Sstack nat stk n) ) ->
  push_stack_n st n -{ sigma' }-> sigma''
| e_push_stack_bool : forall sigma sigma' sigma'' stk b st,
  sigma' = (update_StackB sigma st stk) ->
  sigma'' = (update_StackB sigma st ( push_Sstack bool stk b) ) ->
  push_stack_b st b -{ sigma' }-> sigma''
| e_push_stack_string : forall sigma sigma' sigma'' stk s st,
  sigma' = (update_StackS sigma st stk) ->
  sigma'' = (update_StackS sigma st ( push_Sstack string stk s) ) ->
  push_stack_s st s -{ sigma' }-> sigma''
| e_pop_stack_nat : forall sigma sigma' sigma'' stk st,
  sigma' = (update_StackN sigma st stk ) ->
  sigma'' = (update_StackN sigma st ( pop_Sstack nat stk)) ->
  pop_stack_n st -{ sigma' }-> sigma''
| e_pop_stack_bool : forall sigma sigma' sigma'' stk st,
  sigma' = (update_StackB sigma st stk ) ->
  sigma'' = (update_StackB sigma st ( pop_Sstack bool stk)) ->
  pop_stack_b st -{ sigma' }-> sigma''
| e_pop_stack_string : forall sigma sigma' sigma'' stk st,
  sigma' = (update_StackS sigma st stk ) ->
  sigma'' = (update_StackS sigma st ( pop_Sstack string stk)) ->
  pop_stack_s st -{ sigma' }-> sigma''
| e_declareVecN : forall sigma sigma' v,
  sigma' = update_VecN sigma v [ ] ->
  declareVecN v -{ sigma }-> sigma'
| e_declareVecB : forall sigma sigma' v,
  sigma' = update_VecB sigma v [ ] ->
  declareVecB v -{ sigma }-> sigma'
| e_declareVecS : forall sigma sigma' v,
  sigma' = update_VecS sigma v [ ] ->
  declareVecS v -{ sigma }-> sigma'
| e_assignVecN : forall sigma sigma' v l,
  sigma' = update_VecN sigma v l ->
  assignmentVecN v l -{ sigma }-> sigma'
| e_assignVecB : forall sigma sigma' v l,
  sigma' = update_VecB sigma v l ->
  assignmentVecB v l -{ sigma }-> sigma'
| e_assignVecS : forall sigma sigma' v l,
  sigma' = update_VecS sigma v l ->
  assignmentVecS v l -{ sigma }-> sigma'
| e_pushb_vec_nat : forall sigma sigma' sigma'' v l n,
  sigma' = (update_VecN sigma v l) ->
  sigma'' = (update_VecN sigma v (pb_nat l n) ) ->
  (pushb_vec_nat v n) -{ sigma' }-> sigma''
| e_pushb_vec_bool : forall sigma sigma' sigma'' v l b,
  sigma' = (update_VecB sigma v l) ->
  sigma'' = (update_VecB sigma v (pb_bool l b) ) ->
  (pushb_vec_bool v b) -{ sigma' }-> sigma''
| e_pushb_vec_string : forall sigma sigma' sigma'' v l s,
  sigma' = (update_VecS sigma v l) ->
  sigma'' = (update_VecS sigma v (pb_str l s) ) ->
  (pushb_vec_string v s) -{ sigma' }-> sigma''
| e_pushf_vec_nat : forall sigma sigma' sigma'' v l n,
  sigma' = (update_VecN sigma v l) ->
  sigma'' = (update_VecN sigma v (pf_nat l n) ) ->
  (pushb_vec_nat v n) -{ sigma' }-> sigma''
| e_pushf_vec_bool : forall sigma sigma' sigma'' v l b,
  sigma' = (update_VecB sigma v l) ->
  sigma'' = (update_VecB sigma v (pf_bool l b) ) ->
  (pushf_vec_bool v b) -{ sigma' }-> sigma''
| e_pushf_vec_string : forall sigma sigma' sigma'' v l s,
  sigma' = (update_VecS sigma v l) ->
  sigma'' = (update_VecS sigma v (pf_str l s) ) ->
  (pushf_vec_string v s) -{ sigma' }-> sigma''
| e_pop_vec_nat : forall sigma sigma' sigma'' v l,
  sigma' = (update_VecN sigma v l) ->
  sigma'' = (update_VecN sigma v (pop_n l)) ->
  (pop_vec_nat v) -{ sigma' }-> sigma''                
| e_pop_vec_bool : forall sigma sigma' sigma'' v l,
  sigma' = (update_VecB sigma v l) ->
  sigma'' = (update_VecB sigma v (pop_b l)) ->
  (pop_vec_bool v) -{ sigma' }-> sigma''
| e_pop_vec_string : forall sigma sigma' sigma'' v l,
  sigma' = (update_VecS sigma v l) ->
  sigma'' = (update_VecS sigma v (pop_s l)) ->
  (pop_vec_string v) -{ sigma' }-> sigma''

where "s -{ sigma }-> sigma'" := (eval_st s sigma sigma'). 

Reserved Notation "S >{ sigma }-> sigma'" (at level 60).

Inductive eval_fst: FStmt -> Env -> Env -> Prop :=
| e_declareFN: forall x sigma sigma',
  sigma' = (update_fnat sigma x 0) ->
  (<fint> x) >{ sigma }-> sigma'
| e_declareFB: forall b sigma sigma',
  sigma' = (update_fbool sigma b true) ->
  (<fboolean> b) >{ sigma }-> sigma'
| e_declareFS: forall s sigma sigma',
  sigma' = (update_fstr sigma s "") ->
  (<fstring> s) >{ sigma }-> sigma'
where "S >{ sigma }-> sigma'" := (eval_fst S sigma sigma').


Definition env1 : Env :=
    fun v => if(string_beq v "a")
             then vn 5
             else if(string_beq v "b")
             then vn 2
             else empty.

Example eval_decN: <int> "x" -{ env0 }-> (update_nat env0 "x" 0).
Proof.
   eapply e_declareN. reflexivity.
Qed.

Example eval_decB: <boolean> "ok" -{ env0 }-> (update_bool env0 "ok" true).
Proof.
   eapply e_declareB. reflexivity.
Qed.

Example eval_assigNat: ("y" <int>::= "a") -{ env1 }-> (update_nat env1 "y" 5).
Proof.
   eapply e_assignmentN.
   - apply var.
   - auto.
Qed.

Example eval_assigBool: ("okay" <boolean>::= bfalse) -{ env0 }-> (update_bool env0 "okay" false).
Proof.
   eapply e_assignmentB.
   - eapply e_false.
   - reflexivity.
Qed.

(* verificare seq *)
Check (<int> "ana" ;; <boolean> "okay").
Check (<int> "x" ;; "x" <int>::= 10 ;; <boolean> "notok" ;; "notok" <boolean>::= bfalse).

Example eval_whileF: while ("a" <=' 4) ("var" <int>::= 10) -{ env1 }-> env1.
Proof.
  eapply e_whilefalse.
  eapply e_lessthan.
  - apply var.
  - apply const.
  - auto.
Qed.

Example eval_whileT: exists sigma, while("a" <=' 5) ("a" <int>::= 6) -{ env1 }-> sigma /\ sigma "a" = vn 6.
Proof.
    eexists.
    split.
    - eapply e_whiletrue.
      + eapply e_lessthan.
        ++ apply var.
        ++ apply const.
        ++ auto.
      + eapply e_seq.
        ++ eapply e_assignmentN.
           ** eapply const.
           ** auto.
        ++ eapply e_whilefalse.
           ** eapply e_lessthan.
              * eapply var.
              * eapply const.
              * auto.
    - auto.
Qed.

Example eval_ifthentrue: exists sigma, ifthen ("a" <=' 4) ("x" <int>::= 20) -{ env0 }-> sigma /\ sigma "x" = vn 20.
Proof.
    eexists.
    split.
    - eapply e_ifthentrue.
      + eapply e_lessthan.
        * eapply var.
        * eapply const.
        * auto.
      + eapply e_assignmentN.
        * eapply const.
        * reflexivity.
    - auto.
Qed.

Example eval_ifthenfalse: ifthen ("a" <=' 1) ("oke" <boolean>::= bfalse) -{ env1 }-> env1.
Proof.
   eapply e_ifthenfalse.
   eapply e_lessthan.
   - eapply var.
   - eapply const.
   - simpl. reflexivity.
Qed.

Example eval_ifthenelsetrue : ifthenelse ("a" <=' 4) ("rr" <int>::= 4) ("rr" <int>::= ("rr" -' 1)) -{ env0 }-> update_nat env0 "rr" 4.
Proof.
    eapply e_iftrue.
    eapply e_lessthan.
    - apply var.
    - apply const.
    - simpl. reflexivity.
    - eapply e_assignmentN.
      + eapply const.
      + reflexivity.
Qed.

Example eval_ifthenelsefalse : ifthenelse ("rr" +' 5 <=' 4 ) ("rr" <int>::= 4) ("rr" <int>::= 20) -{ env0 }-> update_nat env0 "rr" 20.
Proof.
    eapply e_iffalse.
    eapply e_lessthan.
    - eapply add.
      + apply var.
      + apply const.
      + simpl. reflexivity.
    - apply const.
    - simpl. reflexivity.
    - eapply e_assignmentN.
      + apply const.
      + reflexivity.
    
Qed.

Example eval_for: exists sigma, foor ("a" <int>::= 0) ("a" <=' 0) ("a" <int>::= ("a" +' 1))("rr" <int>::= ("a" +' 1)) -{ env0 }-> sigma /\ sigma "a" = vn 1 /\ sigma "rr" = vn 1.
Proof.
    eexists.
    split.
    - eapply e_for.
      eapply e_seq.
      * eapply e_assignmentN.
        ** eapply const.
        ** auto.
      * eapply e_whiletrue.
        ** eapply e_lessthan.
          + eapply var.
          + eapply const.
         + auto.
       ** eapply e_seq.
         + eapply e_seq.
           ++ eapply e_assignmentN.
              +++ eapply add.
                  ++++ eapply var.
                  ++++ eapply const.
                  ++++ auto.
              +++ auto.
           ++ eapply e_assignmentN.
              +++ eapply add.
                  ++++ eapply var.
                  ++++ eapply const.
                  ++++ auto.
              +++ auto.
         + eapply e_whilefalse.
           eapply e_lessthan.
           ++ eapply var.
           ++ eapply const.
           ++ auto.
    - auto.
Qed.

Check
  "n" <int>::= 10 ;;
  <int> "i";;
  "sum" <int>::= 0 ;; 
  
  While ( "i" <=' "n" ) do (
          "sum" <int>::= ("sum" +' "i") ;;
          "i" <int>::= ("i" +' 1)
  );;
  If("sum" <=' 60)
    Then "n" <int>::= (("sum" %' "n") +' 1)
    Else "n" <int>::= (("sum" *' "n") /' 5) 
.

Check
  "x" <boolean>::= btrue;;
  "y" <int>::= 20;;
  <int> "i";;
  For ( "i" <int>::= 0 ; "i" <=' 1 ; "i" <int>::= ("i" +' 1) ) do
      "y" <int>::= ( "y" +' "y" )
.
Compute env1 "a".
Example eval_break : exists sigma, while("a" <=' 10) ("a" <int>::= ("a" +' 2);; break) -{ env1 }-> sigma /\ sigma "a" = vn 7.
Proof.
  eexists.
  split.
  - eapply e_whiletrue.
    + eapply e_lessthan.
      ++ eapply var.
      ++ eapply const.
      ++ eauto.
    + eapply e_seq.
      ++ eapply e_seq.
        +++ eapply e_assignmentN; eauto. eapply add; eauto. eapply var. eapply const.
        +++ unfold update_nat. eapply e_break.
      ++ eapply e_whiletrue; simpl.
        +++ eapply e_lessthan. eapply var. eapply const. eauto.
        +++ eapply e_break.
  - eauto.
Qed.

Example eval_continue: exists sigma, ifthenelse ("a" <=' 10) continue ("a" <int>::= ("a" +' 2)) -{ env1 }-> sigma /\ sigma "a" = vn 5.
Proof.
  eexists.
  split.
  - eapply e_iftrue.
    + eapply e_lessthan.
      ++ eapply var.
      ++ eapply const.
      ++ eauto.
    + eapply e_continue.
  - eauto.
Qed.
Inductive RegExp :=
| gol : RegExp
| eps : RegExp
| chr : ascii -> RegExp
| conc : RegExp -> RegExp -> RegExp
| oor : RegExp -> RegExp -> RegExp
| star : RegExp -> RegExp
| nott : RegExp -> RegExp.

Notation "a <.> b" := (conc a b) (at level 80).
Notation "a || b" := (oor a b).

Fixpoint init (exp : RegExp) : bool :=
match exp with
| gol => false
| eps => true
| chr a%string => false
| conc a b => (init a && init b)%bool
| oor a b => (init a || init b)%bool
| star a => true
| nott a => negb (init a)
end.

Fixpoint derivare (a : ascii)(exp : RegExp) : RegExp :=
  match exp with
  | gol => gol
  | eps => gol
  | chr c%string => match (ascii_dec c a) with
                    | left _ => eps
                    | right _ => gol 
                    end
  | conc x y => match (init x) with
                | true => (derivare a x) <.> y || (derivare a y)
                | false => (derivare a x) <.> y
                end
  | oor x y => (derivare a x) || (derivare a y)
  | star x => (derivare a x) <.> (star x)
  | nott x => nott (derivare a x)
  end.

Fixpoint matching (exp:RegExp)(s:string) : bool :=
match s with
| EmptyString => init exp
| String a w => matching (derivare a exp) w
end.


(*Inductive Instruction :=
| push_const : nat -> Instruction
| push_var : string -> Instruction
| add : Instruction
| mul : Instruction.
*)
Inductive Memory :=
| memory_default : Memory
| offset : nat -> Memory.

Definition Envr := string -> Memory.
Definition MemoryLayer := Memory -> ValueTypes.
Definition Stack := list Envr.


Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Envr -> MemoryLayer -> Stack -> Config.


