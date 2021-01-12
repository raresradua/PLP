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

Definition vector_nat := list nat.
Definition vector_bool := list bool.
Definition vector_str := list string.



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


Inductive AExp:=
| avar : string -> AExp
| favar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| afrac : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| idx_vecn : string -> list nat -> nat -> AExp.

Notation "A +' B" := (aplus A B)(at level 60, right associativity).
Notation "A -' B" := (aminus A B)(at level 60, right associativity).
Notation "A *' B" := (amul A B)(at level 58, left associativity).
Notation "A /' B" := (afrac A B)(at level 58, left associativity).
Notation "A %' B" := (amod A B)(at level 58, left associativity).


Inductive StrExp :=
| strvar : string -> StrExp
| strfvar : string -> StrExp
| strconc : StrExp -> StrExp -> StrExp
| idx_vecs : string -> list string -> nat -> StrExp.


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
| bstrcomp : StrExp -> StrExp -> BExp
| idx_vecb : string -> list bool -> nat -> BExp.

Notation "A <=' B" := (blessthaneq A B) (at level 70).
Notation "A >=' B" := (bmorethaneq A B)(at level 70).
Notation " ! A " := (bnot A)(at level 20).
Notation "A eq?' B" := (bstrcomp A B) (at level 80).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 81).

Inductive VecExpN :=
| vecvar_n : string -> VecExpN
| list_n : list nat -> VecExpN
| pb_vecn : string -> list nat -> nat -> VecExpN
| pf_vecn : string -> list nat -> nat -> VecExpN
| pop_vecn : string -> list nat -> VecExpN.

Inductive VecExpB :=
| vecvar_b : string -> VecExpB
| list_b : list bool -> VecExpB
| pb_vecb : string -> list bool -> bool -> VecExpB
| pf_vecb : string -> list bool -> bool -> VecExpB
| pop_vecb : string -> list bool -> VecExpB.

Inductive VecExpS :=
| vecvar_s : string -> VecExpS
| list_s : list string -> VecExpS
| pb_vecs : string -> list string -> string -> VecExpS
| pf_vecs : string -> list string -> string -> VecExpS
| pop_vecs : string -> list string -> VecExpS.




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
Reserved Notation "V ~~{ S }=> V'" (at level 70).
Inductive veceval_n : VecExpN -> Env -> list nat -> Prop :=
| vn_var : forall v sigma, (vecvar_n v) ~~{ sigma }=> match (sigma v) with
                                                    | vvn v => v
                                                    | _ => []
                                                    end
| vn_const : forall l sigma, list_n l ~~{ sigma }=> l
| pushb_n : forall v l n l1 sigma,
  list_n l ~~{ sigma }=> l1 -> 
  pb_vecn v l n ~~{ sigma }=> (pb_nat l1 n)
| pushf_n : forall v l n l1 sigma,
  list_n l ~~{ sigma }=> l1 ->
  pf_vecn v l n ~~{ sigma }=> (pf_nat l1 n)
| popv_n : forall v l l1 sigma,
  list_n l ~~{ sigma }=> l1 ->
  pop_vecn v l ~~{ sigma }=> (pop_n l1)

  
where "V ~~{ S }=> V'" := (veceval_n V S V').

Reserved Notation "V ~~~{ S }=> V'" (at level 70).
Inductive veceval_b : VecExpB -> Env -> list bool -> Prop :=
| vb_var : forall v sigma, (vecvar_b v) ~~~{ sigma }=> match (sigma v) with
                                                    | vvb v => v
                                                    | _ => []
                                                    end
| vb_const : forall l sigma, list_b l ~~~{ sigma }=> l
| pushb_b : forall v l b l1 sigma,
  list_b l ~~~{ sigma }=> l1 -> 
  pb_vecb v l b ~~~{ sigma }=> (pb_bool l1 b)
| pushf_b : forall v l b l1 sigma,
  list_b l ~~~{ sigma }=> l1 ->
  pf_vecb v l b ~~~{ sigma }=> (pf_bool l1 b)
| popv_b : forall v l l1 sigma,
  list_b l ~~~{ sigma }=> l1 ->
  pop_vecb v l ~~~{ sigma }=> (pop_b l1)

where "V ~~~{ S }=> V'" := (veceval_b V S V').

Reserved Notation "V ~~~~{ S }=> V'" (at level 70).
Inductive veceval_s : VecExpS -> Env -> list string -> Prop :=
| vs_var : forall v sigma, (vecvar_s v) ~~~~{ sigma }=> match (sigma v) with
                                                    | vvs v => v
                                                    | _ => []
                                                    end
| vs_const : forall l sigma, list_s l ~~~~{ sigma }=> l
| pushb_s : forall v l s l1 sigma,
  list_s l ~~~~{ sigma }=> l1 -> 
  pb_vecs v l s ~~~~{ sigma }=> (pb_str l1 s)
| pushf_s : forall v l s l1 sigma,
  list_s l ~~~~{ sigma }=> l1 ->
  pf_vecs v l s ~~~~{ sigma }=> (pf_str l1 s)
| popv_s : forall v l l1 sigma,
  list_s l ~~~~{ sigma }=> l1 ->
  pop_vecs v l ~~~~{ sigma }=> (pop_s l1)
where "V ~~~~{ S }=> V'" := (veceval_s V S V').


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
| idx_n : forall v l n l1 sigma,
  list_n l ~~{ sigma }=> l1 ->
  idx_vecn v l n =[ sigma ]=> (indexNVec l1 n)

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
| idx_s : forall v l n l1 sigma,
  list_s l ~~~~{ sigma }=> l1 ->
  idx_vecs v l n ~{ sigma }=> (indexSVec l1 n)
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
| idx_b : forall v l n l1 sigma,
  list_b l ~~~{ sigma }=> l1 ->
  idx_vecb v l n ={ sigma }=> (indexBVec l1 n)
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
Notation "X [int]" := (declareVecN X) (at level 40).
Notation "X [boolean]" := (declareVecB X) (at level 40).
Notation "X [str]" := (declareVecS X)(at level 40).
Notation "X [int]::= L" := (assignmentVecN X L) (at level 40).
Notation "X [boolean]::= L" := (assignmentVecB X L) (at level 40).
Notation "X [str]::= L" := (assignmentVecS X L)(at level 40).

Check funct "main" [ <fint> "X" ] ( <int> "Y" ).



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

| e_push_stack_nat : forall sigma sigma'' stk n st,
  sigma'' = (update_StackN sigma st ( push_Sstack nat stk n) ) ->
  push_stack_n st n -{ sigma }-> sigma''
| e_push_stack_bool : forall sigma sigma'' stk b st,
  sigma'' = (update_StackB sigma st ( push_Sstack bool stk b) ) ->
  push_stack_b st b -{ sigma }-> sigma''
| e_push_stack_string : forall sigma sigma'' stk s st,
  sigma'' = (update_StackS sigma st ( push_Sstack string stk s) ) ->
  push_stack_s st s -{ sigma }-> sigma''

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

| e_assignVecN : forall sigma sigma' v l l1,
  list_n l ~~{ sigma }=> l1 ->
  sigma' = update_VecN sigma v l1 ->
  assignmentVecN v l -{ sigma }-> sigma'
| e_assignVecB : forall sigma sigma' v l l1,
  list_b l ~~~{ sigma }=> l1 ->
  sigma' = update_VecB sigma v l1 ->
  assignmentVecB v l -{ sigma }-> sigma'
| e_assignVecS : forall sigma sigma' v l l1,
  list_s l ~~~~{ sigma }=> l1 ->
  sigma' = update_VecS sigma v l ->
  assignmentVecS v l -{ sigma }-> sigma'

| e_pushb_vec_nat : forall sigma sigma'' v x n,
  (vecvar_n v) ~~{ sigma }=> x ->
  pb_vecn v x n ~~{ sigma }=> (pb_nat x n) ->
  sigma'' = (update_VecN sigma v (pb_nat x n)) ->
  (pushb_vec_nat v n) -{ sigma }-> sigma''
| e_pushb_vec_bool : forall sigma sigma'' v x b,
  (vecvar_b v) ~~~{ sigma }=> x ->
  pb_vecb v x b ~~~{ sigma }=> (pb_bool x b) ->
  sigma'' = (update_VecB sigma v (pb_bool x b)) ->
  (pushb_vec_bool v b) -{ sigma }-> sigma''
| e_pushb_vec_string : forall sigma sigma'' v x s,
  (vecvar_s v) ~~~~{ sigma }=> x ->
  pb_vecs v x s ~~~~{ sigma }=> (pb_str x s) ->
  sigma'' = (update_VecS sigma v (pb_str x s)) ->
  (pushb_vec_string v s) -{ sigma }-> sigma''

| e_pushf_vec_nat : forall sigma sigma'' v x n,
  (vecvar_n v) ~~{ sigma }=> x ->
  pf_vecn v x n ~~{ sigma }=> (pf_nat x n) ->
  sigma'' = (update_VecN sigma v (pf_nat x n)) ->
  (pushf_vec_nat v n) -{ sigma }-> sigma''
| e_pushf_vec_bool : forall sigma sigma'' v x b,
  (vecvar_b v) ~~~{ sigma }=> x ->
  pf_vecb v x b ~~~{ sigma }=> (pf_bool x b) ->
  sigma'' = (update_VecB sigma v (pf_bool x b)) ->
  (pushf_vec_bool v b) -{ sigma }-> sigma''
| e_pushf_vec_string :  forall sigma sigma'' v x s,
  (vecvar_s v) ~~~~{ sigma }=> x ->
  pf_vecs v x s ~~~~{ sigma }=> (pf_str x s) ->
  sigma'' = (update_VecS sigma v (pf_str x s)) ->
  (pushf_vec_string v s) -{ sigma }-> sigma''

| e_pop_vec_nat : forall sigma sigma'' v x,
  (vecvar_n v) ~~{ sigma }=> x ->
  pop_vecn v x ~~{ sigma }=> (pop_n x) ->
  sigma'' = (update_VecN sigma v (pop_n x)) ->
  (pop_vec_nat v) -{ sigma }-> sigma''                
| e_pop_vec_bool : forall sigma sigma'' v x,
  (vecvar_b v) ~~~{ sigma }=> x ->
  pop_vecb v x ~~~{ sigma }=> (pop_b x) ->
  sigma'' = (update_VecB sigma v (pop_b x)) ->
  (pop_vec_bool v) -{ sigma }-> sigma''
| e_pop_vec_string : forall sigma sigma'' v x,
  (vecvar_s v) ~~~~{ sigma }=> x ->
  pop_vecs v x ~~~~{ sigma }=> (pop_s x) ->
  sigma'' = (update_VecS sigma v (pop_s x)) ->
  (pop_vec_string v) -{ sigma }-> sigma''




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

Definition envvec : Env :=
  fun v => if(string_beq v "vecn")
           then vvn [1;2;3]
           else if(string_beq v "vecb")
           then vvb [true;false]
           else if(string_beq v "vecs")
           then vvs ["hei";"hello"]
           else empty.
Compute envvec "vecn".

Example eval_decVecN: "vec1" [int] -{ envvec }-> (update_VecN envvec "vec1" []).
Proof.
    eapply e_declareVecN. reflexivity.
Qed.

Example eval_decVecB: "vec2" [boolean] -{ envvec }-> (update_VecB envvec "vec2" []).
Proof.
    eapply e_declareVecB. reflexivity.
Qed.

Example eval_decVecS: "vec3" [str] -{ envvec }-> (update_VecS envvec "vec3" []).
Proof.
    eapply e_declareVecS. reflexivity.
Qed.

Example eval_assignVecN: ("vecn" [int]::= [3;4;5]) -{ envvec }-> (update_VecN envvec "vecn" [3;4;5]).
Proof.
   eapply e_assignVecN.
   - eapply vn_const.
   - reflexivity.
Qed.

Example eval_assignVecB: ("vecb" [boolean]::= [true;true;true]) -{ envvec }-> (update_VecB envvec "vecb" [true;true;true]).
Proof.
   eapply e_assignVecB.
   - eapply vb_const.
   - reflexivity.
Qed.

Example eval_assignVecS: ("vecs" [str]::= ["x"]) -{ envvec }-> (update_VecS envvec "vecs" ["x"]).
Proof.
   eapply e_assignVecS.
   - eapply vs_const.
   - reflexivity.
Qed.


Example eval_pbVecN: exists sigma, pushb_vec_nat "vecn" 7 -{ envvec }-> sigma /\ sigma "vecn" = vvn [1;2;3;7].
Proof.
  eexists.
  split.
  - eapply e_pushb_vec_nat.
    + eapply vn_var; eauto.
    + eapply pushb_n. eapply vn_const.
    + eauto.
  - eauto.
Qed.

Example eval_pbVecB: exists sigma, pushb_vec_bool "vecb" true -{ envvec }-> sigma /\ sigma "vecb" = vvb [true;false;true].
Proof.
  eexists.
  split.
  - eapply e_pushb_vec_bool.
    + eapply vb_var; eauto.
    + eapply pushb_b. eapply vb_const.
    + eauto.
  - eauto.
Qed.

Example eval_pbVecS: exists sigma, pushb_vec_string "vecs" "oo" -{ envvec }-> sigma /\ sigma "vecs" = vvs ["hei";"hello";"oo"].
Proof.
  eexists.
  split.
  - eapply e_pushb_vec_string.
    + eapply vs_var; eauto.
    + eapply pushb_s. eapply vs_const.
    + eauto.
  - eauto.
Qed.

Example eval_pfVecN: exists sigma, pushf_vec_nat "vecn" 7 -{ envvec }-> sigma /\ sigma "vecn" = vvn [7;1;2;3].
Proof.
  eexists.
  split.
  - eapply e_pushf_vec_nat.
    + eapply vn_var; eauto.
    + eapply pushf_n. eapply vn_const.
    + eauto.
  - eauto.
Qed.

Example eval_pfVecB: exists sigma, pushf_vec_bool "vecb" true -{ envvec }-> sigma /\ sigma "vecb" = vvb [true;true;false].
Proof.
  eexists.
  split.
  - eapply e_pushf_vec_bool.
    + eapply vb_var; eauto.
    + eapply pushf_b. eapply vb_const.
    + eauto.
  - eauto.
Qed.

Example eval_pfVecS: exists sigma, pushf_vec_string "vecs" "oo" -{ envvec }-> sigma /\ sigma "vecs" = vvs ["oo";"hei";"hello"].
Proof.
  eexists.
  split.
  - eapply e_pushf_vec_string.
    + eapply vs_var; eauto.
    + eapply pushf_s. eapply vs_const.
    + eauto.
  - eauto.
Qed.

Example eval_popVecN: exists sigma, pop_vec_nat "vecn" -{ envvec }-> sigma /\ sigma "vecn" = vvn [2;3].
Proof.
  eexists.
  split.
  - eapply e_pop_vec_nat.
    + eapply vn_var; eauto.
    + eapply popv_n. eapply vn_const.
    + eauto.
  - eauto.
Qed.

Example eval_popVecB: exists sigma, pop_vec_bool "vecb" -{ envvec }-> sigma /\ sigma "vecb" = vvb [false].
Proof.
  eexists.
  split.
  - eapply e_pop_vec_bool.
    + eapply vb_var; eauto.
    + eapply popv_b. eapply vb_const.
    + eauto.
  - eauto.
Qed.

Example eval_popVecS: exists sigma, pop_vec_string "vecs" -{ envvec }-> sigma /\ sigma "vecs" = vvs ["hello"].
Proof.
  eexists.
  split.
  - eapply e_pop_vec_string.
    + eapply vs_var; eauto.
    + eapply popv_s. eapply vs_const.
    + eauto.
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
(*
Fixpoint interpret (e:AExp) (env : Env): nat :=
  match e with
  | anum x => x
  | avar x => match (env x) with
              | vn x => x
              | _ => 0
              end
  | favar x => match (env x) with
              | fn x => x
              | _ => 0
              end
  | aplus x y => (interpret x env) + (interpret y env)
  | aminus x y => (interpret x env) - (interpret y env)
  | amul x y => (interpret x env) * (interpret y env)
  | afrac x y => (interpret x env) / (interpret y env)
  | amod x y => (interpret x env) mod (interpret y env)
  end
.

Compute (interpret "a" env1).
Compute (interpret (10 +' "a") env1).
Inductive instr_AExp :=
| push_num : nat -> instr_AExp
| push_var : string -> instr_AExp
| push_fvar : string -> instr_AExp
| addd : instr_AExp
| sub : instr_AExp
| mul : instr_AExp
| divv : instr_AExp
| rest : instr_AExp.


Definition AExp_Stack := list nat.
Definition run_instruction_AExp (i : instr_AExp) (env : Env) (stack : AExp_Stack) : AExp_Stack :=
  match i with
  | push_num x => (x :: stack)
  | push_var x => (match (env x) with
                  | vn x => x
                  | _ => 0
                  end
                  :: stack)
  | push_fvar x => (match (env x) with
                  | fn x => x
                  | _ => 0
                  end :: stack)
  | addd => match stack with
         | x :: y :: stack' => ((x + y) :: stack')
         | _ => stack
          end
  | sub => match stack with
         | x :: y :: stack' => ((x - y) :: stack')
         | _ => stack
          end
  | mul => match stack with
        | x :: y :: stack' => ((x * y) :: stack')
        | _ => stack
          end
  | divv => match stack with
        | x :: y :: stack' => ((x / y) :: stack')
        | _ => stack
          end
  | rest => match stack with
         | x :: y :: stack' => ((x mod y) :: stack')
         | _ => stack
          end

  end.

Compute (run_instruction_AExp (push_num 10) env0 []).
Compute (run_instruction_AExp (push_var "var") env0 []).
Compute (run_instruction_AExp mul env0 [20;30;40;50]).


Fixpoint run_instructionS_AExp (i' : list instr_AExp) (env : Env) (stack : AExp_Stack) : AExp_Stack :=
  match i' with
  | [] => stack
  | i :: i'' => run_instructionS_AExp i'' env (run_instruction_AExp i env stack)
  end.

Definition pgm1 := [ push_num 20 ; push_var "var" ].
Compute run_instructionS_AExp pgm1 env0 [].
Definition pgm2 := [ push_num 30; push_num 40; mul; push_num 100; addd].
Compute run_instructionS_AExp pgm2 env0 [].

Fixpoint AExp_Compile (e : AExp) : list instr_AExp :=
  match e with
  | anum x => [push_num x]
  | favar x => [push_fvar x]
  | avar x => [push_var x]
  | aplus x y => (AExp_Compile x) ++ (AExp_Compile y) ++ [addd]
  | aminus x y => (AExp_Compile y) ++ (AExp_Compile x) ++ [sub]
  | amul x y => (AExp_Compile x) ++ (AExp_Compile y) ++ [mul]
  | afrac x y => (AExp_Compile y) ++ (AExp_Compile x) ++ [divv]
  | amod x y => (AExp_Compile y) ++ (AExp_Compile x) ++ [rest]
  end.


Lemma soundness_helperAExp:
forall e env stack is',
  run_instructionS_AExp(AExp_Compile e ++ is') env stack =
    run_instructionS_AExp is' env ((interpret e env) :: stack).
Proof.
  induction e; intro; simpl; trivial.
  - intuition. 
    rewrite <- app_assoc. 
    rewrite <- app_assoc. 
    rewrite IHe1. 
    rewrite IHe2. 
    simpl. 
    rewrite PeanoNat.Nat.add_comm. 
    reflexivity.
  - intuition.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite PeanoNat.Nat.mul_comm.
    reflexivity.
  - intuition.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
 - intuition.
   rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
 - intuition.
   rewrite <- app_assoc.
   rewrite <- app_assoc.
   rewrite IHe2.
   rewrite IHe1.
   simpl.
   reflexivity.
Qed.

Lemma soundness_AExp:
  forall e env,
  run_instructionS_AExp(AExp_Compile e) env [] = [interpret e env].
Proof.
  intros.
  Check app_nil_r.
  intuition.
  rewrite <- app_nil_r with (l := (AExp_Compile e)).
  rewrite soundness_helperAExp.
  simpl.
  trivial.
Qed.

Fixpoint interpretBExp (e : BExp)(env : Env) : bool :=
  match e with
  | btrue => true
  | bfalse => false
  | boolvar b => match (env b) with
              | vb b => b
              | _ => true
              end
  | boolfvar b => match (env b) with
              | fb b => b
              | _ => true
              end
  | blessthaneq b1 b2 => leb (interpret b1 env) (interpret b2 env)
  | bmorethaneq b1 b2 => leb (interpret b2 env) (interpret b1 env)
  | bnot b => negb (interpretBExp b env)
  | band b1 b2 => andb (interpretBExp b1 env) (interpretBExp b2 env)
  | bor b1 b2 => orb (interpretBExp b1 env) (interpretBExp b2 env)
end.

Compute interpretBExp (10 <=' "a") env1.
Compute interpretBExp (! "a") env1.
Compute interpretBExp ((btrue) and' (bfalse)) env1.

Inductive instr_BExp :=
| push_bool : bool -> instr_BExp
| push_boolvar : string -> instr_BExp
| push_boolfvar : string -> instr_BExp
| boollt : AExp -> AExp -> instr_BExp
| boolgt : AExp -> AExp -> instr_BExp
| boolnot : instr_BExp
| booland : instr_BExp
| boolor : instr_BExp.

Definition BExp_Stack := list bool.
Definition run_instruction_BExp(i : instr_BExp)(env : Env)(stack : BExp_Stack) : BExp_Stack :=
  match i with
  | push_bool b => (b :: stack)
  | push_boolvar b=> (match (env b) with
                  | vb b => b
                  | _ => true
                  end
                  :: stack)
  | push_boolfvar b=> (match (env b) with
                  | fb b => b
                  | _ => true
                  end
                  :: stack)
  | boollt b1 b2 => ((leb (interpret b1 env)(interpret b2 env)) :: stack)
  | boolgt b1 b2 => ((leb (interpret b2 env)(interpret b1 env)) :: stack)
  | boolnot => match stack with
              | b :: stack' => ((negb b) :: stack')
              | _ => stack
              end
  | booland => match stack with
              | b1 :: b2 :: stack' => ((andb b2 b1) :: stack')
              | _ => stack 
              end
  | boolor => match stack with
              | b1 :: b2 :: stack' => ((orb b2 b1) :: stack')
              | _ => stack
              end
 end.  

Compute run_instruction_BExp booland env0 [true; false].
Compute run_instruction_BExp boolor env0 [true; false]. 
Compute run_instruction_BExp boolnot env0 [true].  

Fixpoint run_instructionS_BExp(i' : list instr_BExp)(env : Env)(stack : BExp_Stack) : BExp_Stack :=
  match i' with
  | [] => stack
  | i :: i'' => run_instructionS_BExp i'' env (run_instruction_BExp i env stack)
  end.

Definition pgmm1 := (push_bool false :: push_boolvar "x" :: nil).
Definition pgmm2 := (push_bool true :: push_boolvar "xx" :: booland :: push_bool false :: push_bool true :: boolnot :: nil).           

Compute run_instructionS_BExp pgmm2 env0 [].

Fixpoint Compile_BExp (e : BExp) : list instr_BExp :=
  match e with
  | btrue => [push_bool true]
  | bfalse => [push_bool false]
  | boolvar b => [push_boolvar b]
  | boolfvar b => [push_boolfvar b]
  | blessthaneq b1 b2 => [boollt b1 b2]
  | bmorethaneq b1 b2 => [boolgt b1 b2]
  | band b1 b2 => (Compile_BExp b1) ++ (Compile_BExp b2) ++ [booland]
  | bor b1 b2 => (Compile_BExp b1) ++ (Compile_BExp b2) ++ [boolor]
  | bnot b => (Compile_BExp b) ++ [boolnot]
  end.

Compute Compile_BExp( 10 <=' 3).
Compute interpretBExp (10 <=' 3) env0.

Lemma soundness_helperBExp :
forall e env stack is',
   run_instructionS_BExp (Compile_BExp e ++ is') env stack =
   run_instructionS_BExp is' env ((interpretBExp e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite IHe.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
Qed.

Theorem soundness_BExp :
  forall e env,
    run_instructionS_BExp (Compile_BExp e) env [] =
    [interpretBExp e env].
Proof.
  intros.
  Check app_nil_r.
  rewrite <- app_nil_r with (l := (Compile_BExp e)).
  rewrite soundness_helperBExp.
  simpl. trivial.
Qed.
*)
