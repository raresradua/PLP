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
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 81).
Infix "eq?'" := bstrcomp (at level 80).


Coercion avar : string >-> AExp.
Coercion anum : nat >-> AExp.
Coercion boolvar : string >-> BExp.
Coercion strvar : string >-> StrExp.


Definition Env := string -> ValueTypes.

Inductive Stmt :=
| declareN : AExp -> Stmt (* global *)
| declareB : BExp -> Stmt (* global *)
| declareS : StrExp -> Stmt (* global *)
| assignmentN : AExp -> AExp -> Stmt (* assignment pentru int-uri *)
| assignmentB : BExp -> BExp -> Stmt (* assignment pentru bool-uri *)
| assignmentS : StrExp -> StrExp -> Stmt (* assignment pentru str-uri *)
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt (* if then *)
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| foor : Stmt -> BExp -> Stmt -> Stmt -> Stmt. (* pt for *)

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

Inductive RegExp :=
| gol : RegExp
| eps : RegExp
| char : ascii -> RegExp
| conc : RegExp -> RegExp -> RegExp
| oor : RegExp -> RegExp -> RegExp
| star : RegExp -> RegExp
| nott : RegExp -> RegExp.






