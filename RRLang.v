From Coq Require Import Strings.String.
From Coq Require Import Ascii.
Scheme Equality for string.
Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Import Nat.


Inductive ValueTypes :=
| vn : nat -> ValueTypes 
| vb : bool -> ValueTypes
| vs : string -> ValueTypes
| empty : ValueTypes.

Scheme Equality for ValueTypes.

Inductive AExp:=
| avar : string -> AExp
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
| strconc : StrExp -> StrExp -> StrExp.


Notation "S <strcat> S'" := (strconc S S')(at level 70).

Inductive BExp :=
| boolvar : string -> BExp
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

Reserved Notation "A =[ S ]=> N" (at level 61).
Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                            | vn var => var
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
| assignmentN : AExp -> AExp -> Stmt
| assignmentB : BExp -> BExp -> Stmt
| assignmentS : StrExp -> StrExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| foor : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| funct : string -> list Stmt -> Stmt -> Stmt.

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
where "s -{ sigma }-> sigma'" := (eval_st s sigma sigma'). 

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


Definition vector_nat := string -> nat.
Definition vector_bool := string -> bool.
Definition vector_string := string -> string.
Definition vector_all := string -> ValueTypes.

Inductive vectorExp :=
| push_nat: vector_nat -> nat -> vectorExp
| push_bool: vector_bool -> bool -> vectorExp
| push_string: vector_string -> string -> vectorExp
| push_all: vector_all -> ValueTypes -> vectorExp
| pop_back_nat: vector_nat -> vectorExp
| pop_back_bool: vector_bool -> vectorExp
| pop_back_string: vector_string -> vectorExp
| pop_back_all: vector_all -> vectorExp.

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



