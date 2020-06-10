Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Relations_3.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.

Require Import Coq.Program.Wf.
Require Import Lia.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.Arith.PeanoNat.


Ltac contradictT H :=
  unfold notT at 1 in H; contradict H.

Definition eq_dec T := forall (x y : T), {x=y} + {x<>y}.

Hint Unfold eq_dec : eqdec.
Hint Extern 5 (eq_dec ?T) => unfold eq_dec; repeat decide equality : eqdec.

Inductive VarName := MkVarName : nat -> VarName.

Inductive CoreType := .
Scheme Equality for CoreType.
Hint Resolve CoreType_eq_dec : eqdec.

Inductive Literal := .
Scheme Equality for Literal.
Hint Resolve Literal_eq_dec : eqdec.

Inductive Id :=
| SomeId : VarName -> Id
| ExternalizeId : Id
| InternalizeId : Id
| RepId : Id
| UnrepId : Id
| ConstructId : Id
| RunIterId : Id
| StepId : Id
| DoneId : Id.

Lemma VarName_dec_eq : eq_dec VarName. auto with eqdec. Defined.
Hint Resolve VarName_dec_eq : eqdec.

Lemma Id_dec_eq : eq_dec Id. auto with eqdec. Defined.
Hint Resolve Id_dec_eq : eqdec.

(*
Axiom DataCon : Type.
Axiom DataCon_dec_eq : eq_dec DataCon.
Hint Resolve DataCon_dec_eq : eqdec.
*)
Inductive DataCon := .
Scheme Equality for DataCon.
Hint Resolve DataCon_eq_dec : eqdec.

Inductive AltCon :=
| DataAlt : DataCon -> AltCon
| LitAlt : Literal -> AltCon
| DEFAULT : AltCon.
Scheme Equality for AltCon.

Lemma AltCon_dec_eq : eq_dec AltCon.  auto with eqdec. Defined.
Hint Resolve AltCon_dec_eq : eqdec.

Inductive Tickish := .
Scheme Equality for Tickish.
Hint Resolve Tickish_eq_dec : eqdec.

Inductive Coercion := .
Scheme Equality for Coercion.
Hint Resolve Coercion_eq_dec : eqdec.

Inductive Expr :=
| Var : Id -> Expr
| Lit : Literal -> Expr
| App : Expr -> Expr -> Expr
| Lam : VarName -> Expr -> Expr
(* | Let : ((VarName * Expr) + list (VarName * Expr)) -> Expr -> Expr *)
| LetNonRec : VarName -> Expr -> Expr -> Expr
| LetRec : list (VarName * Expr) -> Expr -> Expr
| Case : Expr -> VarName -> CoreType -> list (AltCon * list VarName * Expr) -> Expr
| Cast : Expr -> Coercion -> Expr
| Tick : Tickish -> Expr -> Expr
| TypeExpr : CoreType -> Expr
| CoercionExpr : Coercion -> Expr.

Check fold_right.

Definition Bind := ((VarName * Expr) + list (VarName * Expr)) %type.

Definition NonRec (v : VarName) (e : Expr) : Bind := inl (v, e).
Definition Rec bs : Bind := inr bs.

Fixpoint Expr_size (e : Expr) : nat :=
  match e with
  | Var _ => 1
  | Lit _ => 1
  | App a b => 1 + Expr_size a + Expr_size b
  | Lam _ x => 1 + Expr_size x
  | LetNonRec v b x => 1 + Expr_size b + Expr_size x
  | LetRec bs x => 1 + fold_right (fun p q => match p with (_, e) => q + Expr_size e end) 0 bs + Expr_size x
(*
  | Let (NonRec v b) x => 1 + Expr_size b + Expr_size x
  | Let (Rec bs) x => 1 + fold_right (fun p q => match p with (_, e) => q + Expr_size e end) 0 bs + Expr_size x
*)
  | Case s wild ty alts =>
      1 + Expr_size s + fold_right (fun p q => match p with (_, _, e) => q + Expr_size e end) 0 alts
  | Cast e co => 1 + Expr_size e
  | Tick t e => 1 + Expr_size e
  | TypeExpr _ => 1
  | CoercionExpr _ => 1
  end.

Lemma Expr_size_pos : forall e,
  0 < Expr_size e.
Proof.
  induction e; simpl; try lia.
Defined.

Lemma Expr_size_LetRec_swap : forall x y xs body,
  Expr_size (LetRec (x :: y :: xs) body) = Expr_size (LetRec (y :: x :: xs) body).
Proof.
  intros.
  simpl.

  destruct x. destruct y. lia.
Defined.

Lemma Expr_size_LetRec : forall x xs body,
  Expr_size (LetRec xs body) < Expr_size (LetRec (x :: xs) body).
Proof.
  intros.
  simpl.
  destruct x.
  induction xs. simpl.
  pose (Expr_size_pos e).
  lia.
  lia.
Defined.

Lemma Expr_size_Case : forall s wild ty x xs,
  Expr_size (Case s wild ty xs) < Expr_size (Case s wild ty (x :: xs)).
Proof.
  intros.
  induction xs. simpl.
  destruct x.
  pose (Expr_size_pos e). destruct p.
  lia.
  simpl.
  destruct x. destruct p.
  destruct a. destruct p.
  pose (Expr_size_pos e). lia.
Defined.

Definition Expr_size_order (a b : Expr) := Expr_size a < Expr_size b.

Require Import Coq.Arith.Wf_nat.

Theorem Expr_size_wf : well_founded Expr_size_order.
Proof.
  apply well_founded_ltof.
Defined.

Check list_eq_dec.

Program Fixpoint Expr_dec_eq (x y : Expr) : {x=y} + {x<>y} :=
ltac:(refine
  match x, y with
  | Var a, Var b =>
      match Id_dec_eq a b with
        | left prf => left (f_equal Var prf)
        | right prf => right (fun H => _)
      end
  | Lit a, Lit b =>
      match Literal_eq_dec a b with
        | left prf => left (f_equal Lit prf)
        | right prf => right (fun H => _)
      end
  | App a1 b1, App a2 b2 =>
      match Expr_dec_eq a1 a2 with
      | left prf =>
          match Expr_dec_eq b1 b2 with
          | left prf2 => left _
          | right prf2 => right _
          end
      | right prf => right _
      end
  | Lam v1 e1, Lam v2 e2 =>
      match VarName_dec_eq v1 v2 with
      | left prf =>
          match Expr_dec_eq e1 e2 with
          | left prf2 => left _
          | right prf2 => right _
          end
      | right prf => right _
      end
  | LetNonRec v1 b1 x1, LetNonRec v2 b2 x2 =>
      match VarName_dec_eq v1 v2 with
      | left prf =>
          match Expr_dec_eq b1 b2 with
          | left prf2 =>
              match Expr_dec_eq x1 x2 with
              | left prf3 => left _
              | right prf3 => right _
              end
          | right prf2 => right _
          end
      | right prf => right _
      end
  | LetRec bs1 x1, LetRec bs2 x2 =>
      let f := fun p q =>
          match p, q with
          | (v1, e1), (v2, e2) =>
            match VarName_dec_eq v1 v2 with
            | left prf' =>
                match Expr_dec_eq e1 e2 with
                | left prf2' => left _
                | right prf2' => right _
                end
            | right prf' => right _
            end
          end
      in
      match list_eq_dec f bs1 bs2 with
      | left prf =>
          match Expr_dec_eq x1 x2 with
          | left prf2 => left _
          | right prf2 => right _
          end
      | right prf => right _
      end
  | Case s1 wild1 ty1 alts1, Case s2 wild2 ty2 alts2 =>
      let f := fun p q =>
          match p, q with
          | (altCon1, patVars1, e1), (altCon2, patVars2, e2) =>
            match AltCon_eq_dec altCon1 altCon2 with
            | left prf' =>
                match list_eq_dec VarName_dec_eq patVars1 patVars2 with
                | left prf2' =>
                    match Expr_dec_eq e1 e2 with
                    | left prf3' => left _
                    | right prf3' => right _
                    end
                | right prf2' => right _
                end
            | right prf' => right _
            end
          end
      in
      match Expr_dec_eq s1 s2 with
      | left prf =>
          match VarName_dec_eq wild1 wild2 with
          | left prf2 =>
              match CoreType_eq_dec ty1 ty2 with
              | left prf3 =>
                  match list_eq_dec f alts1 alts2 with
                  | left prf4 => left _
                  | right prf4 => right _
                  end
              | right prf3 => right _
              end
          | right prf2 => right _
          end
      | right prf => right _
      end
  | _, _ => _
  end).
Solve All Obligations with try (right; intro; discriminate).
Solve All Obligations with try (injection H; intro; contradiction).
Solve All Obligations with try (decide equality; try now decide equality).

Definition Alt : Type := AltCon * list VarName * Expr.


Definition CoreProgram := list Bind.

(*
Inductive NotInRecList : Id -> list (VarName * Expr) -> Prop :=
| NotInRecList_cons : forall v v' e rest,
    v <> SomeId v' ->
    NotInRecList v rest ->
    NotInRecList v (cons (v', e) rest)
| NotInRecList_nil : forall v,
    NotInRecList v nil.
*)

Inductive InRecList : Id -> list (VarName * Expr) -> Prop :=
| InRecList_here : forall v v' e rest,
  v = SomeId v' -> InRecList v (cons (v', e) rest)
| InRecList_there : forall v v' e rest,
  v <> SomeId v' -> InRecList v rest -> InRecList v (cons (v', e) rest).


Definition decidableT (P : Type) := (P + notT P)%type.

Theorem InRecList_dec : forall v xs, decidableT (InRecList v xs).
Proof.
  intros.
  induction xs.
  unfold decidable.
  right.
  intro.
  inversion H.

  destruct a.
  destruct (Id_dec_eq v (SomeId v0)). subst.
  constructor. constructor. reflexivity.

  unfold decidable.
  case_eq IHxs; intros.
  left.
  apply InRecList_there. assumption.
  assumption.

  right.
  intro.
  remember H0.
  inversion H0. subst. contradiction. subst.
  contradiction.
Defined.

Lemma shrinkNotInRecList (v : Id) (x : VarName * Expr) (xs : list (VarName * Expr)) :
  ~ InRecList v (x :: xs) -> ~ InRecList v xs.
Proof.
  intros.
  intro.
  case_eq H; intros.
  destruct x.
  destruct (Id_dec_eq v (SomeId v0)). subst.
  constructor. reflexivity.

  apply InRecList_there. assumption.
  assumption.
Defined.

Lemma swapNotInRecList (v : Id) (x1 x2 : VarName * Expr) (xs : list (VarName * Expr)) :
  ~ InRecList v (x1 :: x2 :: xs) -> ~ InRecList v (x2 :: x1 :: xs).
Proof.
  intros.
  intro.
  case_eq H; intros.
  destruct x1. destruct x2.
  destruct (Id_dec_eq v (SomeId v0)); destruct (Id_dec_eq v (SomeId v1)).
  subst.
  constructor. reflexivity.
  assert (A : InRecList v ((v0, e) :: (v1, e0) :: xs)).
    constructor. assumption.
  contradiction.
  assert (A : InRecList v ((v0, e) :: (v1, e0) :: xs)).
    apply InRecList_there. assumption.
    constructor. assumption.
  contradiction.
  inversion H0. subst.
  apply InRecList_there. assumption. intuition.
  subst.
  inversion H6. subst. intuition.
  subst.
  apply InRecList_there. assumption.
  apply InRecList_there. assumption.
  assumption.
Defined.


Inductive InVarList : Id -> list VarName -> Prop :=
| InVarList_cons : forall v v' rest,
  v = SomeId v' -> InVarList v (cons v' rest).

Theorem InVarList_dec : forall v xs, decidableT (InVarList v xs).
Proof.
  intros.
  induction xs.
  unfold decidable.
  right.
  intro.
  inversion H.

  destruct (Id_dec_eq v (SomeId a)). subst.
  constructor. constructor. reflexivity.

  unfold decidable.
  right.
  intro.
  inversion H. subst. inversion H. subst. intuition.
Defined.

Definition RecList := list (VarName * Expr).

Definition relationT (A : Type) := A -> A -> Type.

Inductive MapRelation {A} (R : relationT A) : list A -> list A -> Type :=
| MapRelation_nil : MapRelation R nil nil
| MapRelation_cons : forall x x' xs xs',
    R x x' ->
    MapRelation R xs xs' ->
    MapRelation R (x::xs) (x'::xs').

Fixpoint MapRelation_exists {A} (R : relationT A) (xs : list A) (R_prf : forall a (prf : In a xs), {a' : A & R a a'}) {struct xs} :
  {xs' : list A &
  MapRelation R xs xs'}. refine(
    match xs as xs_ return xs = xs_ -> _ with
    | nil => fun Hyp_ => existT _ nil (MapRelation_nil R)
    | cons y ys => fun Hyp_ =>
        match R_prf y _ with
        | existT _ y' prf_y' =>
          let zs' := MapRelation_exists _ R ys (fun p prf' => R_prf p _)
          in
          match zs' with
          | existT _ ys' prf_ys' => existT _ (cons y' ys') (MapRelation_cons R _ _ _ _ prf_y' prf_ys')
          end
        end
    end (eq_refl xs)).
Proof.
  rewrite Hyp_. intuition.
  rewrite Hyp_. intuition.
Defined.


Inductive RelationOnSnd {A B} (R : relationT B) : (A * B) -> (A * B) -> Type :=
| MkRelationOnSnd : forall x y y',
    R y y' ->
    RelationOnSnd R (x, y) (x, y').

Definition RelationOnSnd_exists {A B} (R : relationT B) (ab : A * B) (R_prf : forall a0 b (prf : ab = (a0, b)), {b' : B & R b b'}):
  {ab' : A * B &
  RelationOnSnd R ab ab'} :=
    match ab as x return ab = x -> _ with
    | (a, b) => fun Hyp =>
        match R_prf a b Hyp with
        | existT _ x x_prf => existT _ (a, x) (MkRelationOnSnd R _ _ _ x_prf)
        end
    end (eq_refl ab).

Print RelationOnSnd_exists.


Inductive PropType (P : Prop) : P -> Type :=
| MkPropType : forall p, PropType P p.

Inductive ReplaceIdWith : Id -> Id -> Expr -> Expr -> Type :=
| ReplaceIdWith_Var : forall a a' b r,
    {b = a /\ r = a'} + {b <> a /\ r = b} ->
    ReplaceIdWith a a' (Var b) (Var r)
| ReplaceIdWith_Lit : forall a b lit,
    ReplaceIdWith a b (Lit lit) (Lit lit)
| ReplaceIdWith_App : forall a b f x f' x',
    ReplaceIdWith a b f f' ->
    ReplaceIdWith a b x x' ->
    ReplaceIdWith a b (App f x) (App f' x')
| ReplaceIdWith_Lam : forall a b n body body',
    ((SomeId n <> a) *
     (SomeId n <> b) *
     ReplaceIdWith a b body body')
     +
     {(SomeId n = a \/ SomeId n = b) /\ body' = body} ->
    ReplaceIdWith a b (Lam n body) (Lam n body')
| ReplaceIdWith_Let_NonRec : forall a b v rhs rhs' body body',
     ((SomeId v <> a) *
      (SomeId v <> b) *
      ReplaceIdWith a b rhs rhs' *
      ReplaceIdWith a b body body')
      +
     {(SomeId v = a \/
       SomeId v = b) /\ 
      rhs' = rhs /\
      body' = body} ->
    ReplaceIdWith a b (LetNonRec v rhs body) (LetNonRec v rhs' body')
| ReplaceIdWith_Let_Rec : forall a b recList recList' body body',
    ((~ InRecList a recList) *
     (~ InRecList b recList) *
     MapRelation (RelationOnSnd (ReplaceIdWith a b)) recList recList' *
     ReplaceIdWith a b body body')
     +
    {(InRecList a recList \/ InRecList b recList) /\ recList' = recList /\ body' = body} ->
    ReplaceIdWith a b (LetRec recList body) (LetRec recList' body')

| ReplaceIdWith_Case : forall a b s s' wild ty alts alts',
    ReplaceIdWith a b s s' ->
    ((SomeId wild <> a) * (SomeId wild <> b) *
     MapRelation (RelationOnSnd (ReplaceIdWith a b)) alts alts')
     +
    {(SomeId wild = a \/ SomeId wild = b) /\ alts' = alts} ->
    ReplaceIdWith a b (Case s wild ty alts) (Case s' wild ty alts')
| ReplaceIdWith_Cast : forall a b e e' co,
    ReplaceIdWith a b e e' ->
    ReplaceIdWith a b (Cast e co) (Cast e' co)
| ReplaceIdWith_Tick : forall a b t e e',
    ReplaceIdWith a b e e' ->
    ReplaceIdWith a b (Tick t e) (Tick t e')

| ReplaceIdWith_TypeExpr : forall a b ty,
    ReplaceIdWith a b (TypeExpr ty) (TypeExpr ty)

| ReplaceIdWith_CoercionExpr : forall a b co,
    ReplaceIdWith a b (CoercionExpr co) (CoercionExpr co).




Fixpoint ReplaceIdWith_size (a b : Id) (e e' : Expr) (H : ReplaceIdWith a b e e') : nat.
  refine (
    match H with
    | ReplaceIdWith_Var _ _ _ _ _ => 1
    | ReplaceIdWith_Lit _ _ _ => 1
    | ReplaceIdWith_App _ _ _ _ _ _ H1 H2 => S (ReplaceIdWith_size _ _ _ _ H1 + ReplaceIdWith_size _ _ _ _ H2)
    | ReplaceIdWith_Lam _ _ _ _ _ (inleft (_, _, H)) => S (ReplaceIdWith_size _ _ _ _ H)
    | ReplaceIdWith_Lam _ _ _ _ _ (inright _) => 1
    | ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ (inleft (_, _, H1, H2)) => S (ReplaceIdWith_size _ _ _ _ H1 + ReplaceIdWith_size _ _ _ _ H2)
    | ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _ => 1
    | ReplaceIdWith_Let_Rec _ _ _ _ _ _ (inleft (_, _, mr, H))  => S (_ + ReplaceIdWith_size _ _ _ _ H)
    | ReplaceIdWith_Let_Rec _ _ _ _ _ _ (inright _) => 1
    | ReplaceIdWith_Case _ _ _ _ _ _ _ _ H (inleft (_, _, mr)) => S _
    | ReplaceIdWith_Case _ _ _ _ _ _ _ _ H (inright _) => S (ReplaceIdWith_size _ _ _ _ H)
    | ReplaceIdWith_Cast _ _ _ _ _ H => S (ReplaceIdWith_size _ _ _ _ H)
    | ReplaceIdWith_Tick _ _ _ _ _ H => S (ReplaceIdWith_size _ _ _ _ H)
    | ReplaceIdWith_TypeExpr _ _ _ => 1
    | ReplaceIdWith_CoercionExpr _ _ _ => 1
    end).
clear s p p0 H p1 n n0.
induction mr. exact 0.
destruct r. pose (ReplaceIdWith_size _ _ _ _ r).
exact (n + IHmr).

clear s p p0 n n0.
dependent induction mr. exact 0.
destruct r. pose (ReplaceIdWith_size _ _ _ _ r).
exact (n + IHmr).
Defined.

Definition ReplaceIdWith_size_order a1 b1 e1 e1' a2 b2 e2 e2' H1 H2 :=
  ReplaceIdWith_size a1 b1 e1 e1' H1 < ReplaceIdWith_size a2 b2 e2 e2' H2.

Definition ReplaceIdWith' a b :=
  {e : Expr & { e' : Expr & ReplaceIdWith a b e e' }}.

Definition packReplaceIdWith a b e e' (H : ReplaceIdWith a b e e') : ReplaceIdWith' a b :=
  existT _ e (existT _ e' H).

Definition applyReplaceIdWith {R} a b e e'
  (f : forall (H : ReplaceIdWith' a b), projT1 H = e -> projT1 (projT2 H) = e' -> R) (x : ReplaceIdWith a b e e') : R.
  refine (f (packReplaceIdWith a b e e' x) _ _).
  simpl. reflexivity.
  simpl. reflexivity.
Defined.

Definition onReplaceIdWith' a b e e' (f : forall (H : ReplaceIdWith' a b), projT1 H = e -> projT1 (projT2 H) = e' -> ReplaceIdWith' a b)
  : forall (H : ReplaceIdWith a b e e'),
    ReplaceIdWith
      a
      b
      (projT1 (applyReplaceIdWith a b e e' f H))
      (projT1 (projT2 (applyReplaceIdWith a b e e' f H))).
Proof.
  intros.
  pose (projT1 (applyReplaceIdWith a b e e' f H)).
  destruct (applyReplaceIdWith a b e e' f H).
  simpl in *.
  destruct s.
  simpl.
  assumption.
Defined.

Definition ReplaceIdWith_size_order' a b : ReplaceIdWith' a b -> ReplaceIdWith' a b -> Prop.
  refine (ltof _ _).
intros.
  destruct X. destruct s.
  exact (ReplaceIdWith_size _ _ _ _ r).
Defined.

Definition ReplaceIdWith_size_wf : forall a b,
  well_founded (ReplaceIdWith_size_order' a b).
  intros. apply well_founded_ltof.
Defined.


Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
  R t t' /\ normal_form R t'.

Definition fst_lt (p : nat * nat) (q : nat * nat) := fst p < fst q.


Program Fixpoint ReplaceIdWith_exist (a b : Id) e {measure (Expr_size e)} :
  {e' : Expr &
   ReplaceIdWith a b e e'} :=
  _.
Next Obligation.
refine (match e as res return e = res -> _ with
  | Var i => fun Hyp =>
      if Id_dec_eq i a
      then existT _ (Var b) (ReplaceIdWith_Var _ _ _ _ _)
      else existT _ (Var i) (ReplaceIdWith_Var _ _ _ _ _)
  | Lit l => fun Hyp => existT _ (Lit l) (ReplaceIdWith_Lit _ _ _)
  | App f x => fun Hyp =>
      match ReplaceIdWith_exist a b f _, ReplaceIdWith_exist a b x _ with
      | existT _ f' prf_f', existT _ x' prf_x' =>
          existT _ (App f' x') (ReplaceIdWith_App _ _ _ _ _ _ _ _)
      end
  | Lam v body => fun Hyp =>
    if Id_dec_eq (SomeId v) a
    then existT _ (Lam v body) (ReplaceIdWith_Lam _ _ _ _ _ _)
    else if Id_dec_eq (SomeId v) b
         then existT _ (Lam v body) (ReplaceIdWith_Lam _ _ _ _ _ _)
         else
           match ReplaceIdWith_exist a b body _ with
           | existT _ body' prf => existT _ (Lam v body') (ReplaceIdWith_Lam _ _ _ _ _ _)
           end
  | LetNonRec v rhs body => fun Hyp =>
      if Id_dec_eq (SomeId v) a
      then existT _ (LetNonRec v rhs body) (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
      else if Id_dec_eq (SomeId v) b
           then existT _ (LetNonRec v rhs body) (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
           else
             match ReplaceIdWith_exist a b rhs _, ReplaceIdWith_exist a b body _ with
             | existT _ rhs' prf_rhs', existT _ body' prf_body' =>
                 existT _ (LetNonRec v rhs' body') (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
             end
  | LetRec recList body => fun Hyp =>
      if InRecList_dec a recList
      then existT _ (LetRec recList body) (ReplaceIdWith_Let_Rec _ _ _ _ _ _ _)
      else if InRecList_dec b recList
           then existT _ (LetRec recList body) (ReplaceIdWith_Let_Rec _ _ _ _ _ _ _)
           else
             let r := ReplaceIdWith_exist a b body _
             in
             match r as res2 return r = res2 -> _ with
             | existT _ body' prf_body' => fun Hyp2 =>
                 let prf := _ (* @RelationOnSnd_exists VarName _ (ReplaceIdWith a b) (fun e'1 => ReplaceIdWith_exist a b e'1 _) *)
                 in
                 let m := MapRelation_exists (RelationOnSnd (ReplaceIdWith a b)) recList prf
                 in
                 match m as res3 return m = res3 -> _ with
                 | existT _ recList' prf_recList' => fun Hyp3 =>
                     existT _ (LetRec recList' body') _
                 end (eq_refl m)
             end (eq_refl r)
  | Case s wild ty alts => fun Hyp =>
      match ReplaceIdWith_exist a b s _ with
        | existT _ s' prf_s' =>
            if Id_dec_eq (SomeId wild) a
            then existT _ (Case s wild ty alts) (ReplaceIdWith_Case _ _ _ _ _ _ _ _ _ _)
            else if Id_dec_eq (SomeId wild) b
                 then existT _ (Case s wild ty alts) (ReplaceIdWith_Case _ _ _ _ _ _ _ _ _ _)
                 else
                 let prf := _ (*@RelationOnSnd_exists (AltCon * list VarName) _ (ReplaceIdWith a b) _ (fun e'2 => ReplaceIdWith_exist a b e'2 _) *)
                 in
                 match MapRelation_exists (RelationOnSnd (ReplaceIdWith a b)) alts prf with
                 | existT _ alts' prf_alts' =>
                     existT _ (Case s' wild ty alts') _
                 end
      end
  | Cast x co => fun Hyp =>
      match ReplaceIdWith_exist a b x _ with
      | existT _ x' prf_x' =>
          existT _ (Cast x' co) _
      end
  | Tick t x => fun Hyp =>
      match ReplaceIdWith_exist a b x _ with
      | existT _ x' prf_x' =>
          existT _ (Tick t x') _
      end
  | _ => fun Hyp => _
  end (eq_refl e)).
Proof.
  intuition. intuition.
  rewrite Hyp. simpl. now intuition.
  rewrite Hyp. simpl. now intuition.
  assumption. assumption.
  intuition. intuition.
  rewrite Hyp. simpl. now intuition.
  intuition. intuition. intuition.
  rewrite Hyp. simpl. now intuition.
  rewrite Hyp. simpl. now intuition.
  intuition. intuition. intuition.
  constructor. intuition.


  rewrite Hyp. simpl. now intuition.

  intuition. intuition. intuition.
  intuition.
  constructor. intuition. intuition.
  rewrite Hyp. simpl. now intuition.
  constructor. assumption.
  rewrite Hyp. simpl. now intuition.

  constructor. assumption.

  exists (TypeExpr c). constructor.
  exists (CoercionExpr c). constructor.
Unshelve.
  subst. intuition. simpl. intuition.
  intros.  subst. simpl. intuition.
  intros.  intuition.
  apply RelationOnSnd_exists.
  refine (fun a0 e'' prf => ReplaceIdWith_exist a b e'' _). subst.

  clear Hyp2.
  clear r.
  clear ReplaceIdWith_exist.
  clear n.
  clear n0.
  induction recList. easy.
  induction (in_inv prf0). subst.
  simpl. intuition.
  pose (IHrecList H).
  assert (A : forall z zs, Expr_size (LetRec zs body) < Expr_size (LetRec (z :: zs) body)).
    induction zs. simpl.
    intuition.
    case_eq (Expr_size b0); intros.
    destruct b0; try ( simpl in H0; discriminate).
    lia.

    simpl.
    destruct a2.
    destruct z.
    case_eq (Expr_size e0); intros.
    destruct e0; try (simpl in H0; discriminate).
    lia.
  subst.
  pose (A a1 recList).
  lia.

  intros.

  apply RelationOnSnd_exists.
  intros.
  apply ReplaceIdWith_exist. subst.
  clear n. clear n0.
  clear prf_s'.
  clear ReplaceIdWith_exist.
  clear prf.
  induction alts. easy.

  assert (A : forall z zs, Expr_size (Case s wild ty zs) < Expr_size (Case s wild ty (z :: zs))).
    induction zs. simpl. easy.
    simpl. easy.

  pose (A a0 alts).
  subst.
  lia.
Defined.

Definition evalReplaceIdWith (a b : Id) (e : Expr) : Expr :=
  match ReplaceIdWith_exist a b e with
  | existT _ x _ => x
  end.

Eval cbv in (evalReplaceIdWith RepId UnrepId (App (Var RepId) (Var ConstructId))).

Lemma ReplaceIdWith_det1 : forall a b x x',
  evalReplaceIdWith a b x = x' ->
  ReplaceIdWith a b x x'.
Proof.
  intros.
  unfold evalReplaceIdWith in H.
  destruct (ReplaceIdWith_exist a b x). subst. assumption.
Defined.

Fixpoint ReplaceIdWith_unchanged (a : Id) (x : Expr) :
  ReplaceIdWith a a x x.
Proof.
  intros.
  induction x; intros.
  constructor.
  destruct (Id_dec_eq i a); now intuition.
  subst.
  constructor.
  subst.
  constructor; try now assumption.
  constructor.
  induction (Id_dec_eq (SomeId v) a); try now intuition.

  destruct (Id_dec_eq (SomeId v) a).
  constructor. right. intuition.
  constructor. left. intuition.

  destruct (InRecList_dec a l).
  constructor. intuition.
  constructor. left. intuition.
  induction l.
  constructor.
  pose (shrinkNotInRecList _ _ _ n).
  pose (IHl n0).
  
  constructor.
  destruct a0.
  constructor.
  apply ReplaceIdWith_unchanged.
  assumption.

  constructor. assumption.
  intuition.

  all: (constructor; assumption).
Defined.

Lemma ReplaceIdWith_unchanged2_ (a : Id) (b : Id) :
  forall (x : Expr),
  forall  (x' : Expr) (H : ReplaceIdWith a b x x') (prf : a = b),
  x' = x.
refine (Fix Expr_size_wf _ _).
Proof.
  intros.

  dependent induction H0. subst.
  destruct (Id_dec_eq r b).
  destruct s. destruct a. subst. reflexivity.
  destruct a. subst. reflexivity.
  destruct s. destruct a. subst. contradiction.
  destruct a. subst. contradiction.

  reflexivity.

  cut (forall z, Expr_size_order z f -> Expr_size_order z (App f x)).
  cut (forall z, Expr_size_order z x -> Expr_size_order z (App f x)).

  intros.

  assert (A : f' = f).
    apply IHReplaceIdWith1. intros. subst.
    apply H. intuition. assumption. reflexivity. assumption.
  rewrite A.
  assert (A2 : x' = x).
    apply IHReplaceIdWith2. intros. subst.
    apply H. intuition. assumption. reflexivity. assumption.
  rewrite A2. reflexivity.

  intros. unfold Expr_size_order in *.
  simpl. lia.
  intros. unfold Expr_size_order in *.
  simpl. lia.


  destruct s. destruct p. destruct p.
  assert (A : Expr_size_order body (Lam n body)).
    unfold Expr_size_order. simpl. lia.

  rewrite (H body A body'). reflexivity.
  assumption. assumption.
  destruct a0. subst. reflexivity.

  destruct s. destruct p. destruct p. destruct p.

  assert (A1 : rhs' = rhs).
    apply H.
    unfold Expr_size_order. simpl. lia.
    assumption. assumption.

  assert (A2 : body' = body).
    apply H.
    unfold Expr_size_order. simpl. lia.
    assumption. assumption.
  subst. reflexivity.

  destruct a0. destruct H1.
  subst. reflexivity.

  destruct s. destruct p. destruct p. destruct p.

  assert (A1 : body' = body).
    apply H.
    unfold Expr_size_order. simpl. lia.
    assumption. assumption.

  subst.

  induction m. reflexivity.
  destruct x'. destruct x.
  assert (A2 : e = e0).
    apply H.
    unfold Expr_size_order. simpl. lia.
    inversion r0. assumption. reflexivity.
  subst.
  inversion m. inversion r0. subst. reflexivity.

  assert (A3 : xs' = xs).
    clear H1. clear H0.
    clear IHm. clear n n0 r0 X X0 v.
    dependent induction m; intros. reflexivity.
    cut (forall z, Expr_size_order z (LetRec ((v0, e0) :: xs) body) -> Expr_size_order z (LetRec ((v0, e0) :: x :: xs) body)).
    cut (x' = x). intro.
    cut (xs' = xs). intro.
    subst. intros. reflexivity.
    pose (Expr_size_LetRec x ((v0, e0) :: xs) body).
    assert (H' : forall y, Expr_size_order y (LetRec ((v0,e0) :: xs) body) ->
                 forall x', ReplaceIdWith b b y x' -> b = b -> x' = y).
      intros. apply H.
      unfold Expr_size_order in *.
      pose (Expr_size_LetRec_swap (v0, e0) x xs body).
      pose (Expr_size_LetRec x ((v0, e0) :: xs) body).
      lia. assumption. assumption.
    apply (IHm H' x x' xs xs'). intros.  subst.
    inversion r0. subst.
    assert (A3' : y' = y).
      apply H.
      unfold Expr_size_order. simpl. lia.
      assumption. reflexivity.
    subst. reflexivity.

    intros.
    pose (Expr_size_LetRec_swap (v0, e0) x xs body).
    pose (Expr_size_LetRec x ((v0, e0) :: xs) body).
    unfold Expr_size_order in *. lia.

  subst.
  inversion r0.
  subst. rewrite A3. reflexivity.

  destruct a0. destruct H0. destruct H1. subst. reflexivity.
  destruct H1. subst. reflexivity.

  assert (A : s' = s).
    apply H.
    unfold Expr_size_order. simpl.
    lia. assumption. assumption.
  rewrite A.

  destruct s0. destruct p. destruct p.
  assert (A2 : alts' = alts).
    dependent induction m. reflexivity.
    cut (x' = x). intro.
    cut (xs' = xs). intro.
    subst. reflexivity.
    apply IHm.
    intros. subst.
    apply H.
    pose (Expr_size_Case s wild ty x xs).
    unfold Expr_size_order in *. lia.
    assumption. reflexivity. intros. assumption. assumption. assumption.
    destruct x'. destruct p.
    destruct x. destruct p. subst.
    inversion r. subst.
    assert (A2' : e = e0).
      apply H.
      unfold Expr_size_order.
      simpl. lia.
      assumption. reflexivity.
    rewrite A2'.
    reflexivity.
  rewrite A2.

  reflexivity.

  destruct a0. subst. reflexivity.

  easy. easy. easy. easy.
Defined.

Definition ReplaceIdWith_unchanged2 (a : Id) (x : Expr) (x' : Expr) (H : ReplaceIdWith a a x x') :
  x' = x := ReplaceIdWith_unchanged2_ a a x x' H (eq_refl a).


Fixpoint ReplaceIdWith_size_inv (a b : Id) (x y : Expr) (H : ReplaceIdWith a b x y):
  Expr_size x = Expr_size y.
Proof.
  intros.
  induction H; subst; try easy.
  simpl. lia.
  destruct s. destruct p. destruct p.
  pose (ReplaceIdWith_size_inv a b _ _ r).
  simpl. lia.

  destruct a0. subst. reflexivity.

  destruct s. destruct p. destruct p. destruct p.
  simpl.
  pose (ReplaceIdWith_size_inv a b _ _ r0).
  pose (ReplaceIdWith_size_inv a b _ _ r).
  lia.
  destruct a0. destruct H0. subst.
  reflexivity.
  destruct s. destruct p. destruct p.
  destruct p.

  clear n n0.
  induction m. simpl.
  pose (ReplaceIdWith_size_inv a b _ _ r). simpl. lia.

  destruct x.
  assert (A : forall v_ e_ xs_ body_, Expr_size (LetRec ((v_,e_) :: xs_) body_) = Expr_size e_ + Expr_size (LetRec xs_ body_)).
    induction xs; simpl; lia.
  destruct x'.
  destruct r0.
  pose (ReplaceIdWith_size_inv a b _ _ r).
  rewrite (A x y xs body).
  rewrite (A x y' xs' body').

  rewrite IHm.
  rewrite (ReplaceIdWith_size_inv a b _ _ r0).
  reflexivity.

  destruct a0. destruct H0. subst. reflexivity.
Defined.

Definition length_order A (a b : list A) : Prop := length a < length b.

Theorem length_order_wf A : well_founded (length_order A).
  apply well_founded_ltof.
Defined.


Definition well_founded_induction_type' :
  forall {A : Type} {R : A -> A -> Prop} (a : A),
       well_founded R ->
       forall P : A -> Set,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       P a.
  intros.
  apply (@well_founded_induction_type A R H P X).
Defined.

Theorem ReplaceIdWith_confluent (a b : Id) :
  forall x,
  forall x1' x2',
  ReplaceIdWith a b x x1' ->
  ReplaceIdWith a b x x2' ->
  x1' = x2'.
refine (Fix Expr_size_wf _ _).
Proof.
  intros.
  dependent induction x; try easy.
  inversion X. inversion X0. subst.
  destruct H3; destruct a0. subst.
  destruct H8; destruct a0. subst.
  reflexivity. easy. subst.
  destruct H8; destruct a0. subst. easy.
  subst. reflexivity.

  inversion X. inversion X0. subst.
  assert (A1 : f' = f'0).
    apply (H x1). unfold Expr_size_order. unfold Expr_size. lia.
    assumption. assumption.
  assert (A2 : x' = x'0).
    apply (H x2). unfold Expr_size_order. unfold Expr_size. lia.
    assumption.
    assumption.
  subst. reflexivity.

  inversion X. inversion X0. subst.
  destruct X1. destruct p.
  destruct X2. destruct p0.
  assert (body' = body'0).
    apply (H x).
    unfold Expr_size_order. unfold Expr_size. lia.
    assumption. assumption.
  subst. reflexivity.

  destruct a0. subst.
  destruct p. destruct H0. subst. easy. subst.
  easy. destruct X2. destruct p.
  destruct a0.
  destruct p. destruct H0. subst. easy.
  subst. easy.
  destruct a0. subst. destruct a1.
  destruct H0. subst. reflexivity. subst.
  reflexivity.

  inversion X. inversion X0. subst.
  destruct X1. destruct p. destruct p.
  destruct X2. destruct p0. destruct p0.
  assert (rhs' = rhs'0).
    apply (H x1). unfold Expr_size_order.
    unfold Expr_size. lia.
    assumption. assumption.
  assert (body' = body'0).
    apply (H x2). unfold Expr_size_order.
    unfold Expr_size. lia.
    assumption. assumption.
  subst. reflexivity.
  destruct a0.
  destruct H1.
  subst.
  destruct p.
  destruct H0.
  subst.
  easy.
  subst. easy.
  destruct X2. destruct p.
  destruct p.
  inversion X. subst. inversion X0. subst.
  destruct X1. destruct X2. destruct a0.
  destruct H0. subst. destruct p.
  easy.
  destruct p0. destruct p1.
  destruct p0. destruct p1.
  assert (rhs' = rhs'0).
    apply (H x1).
    unfold Expr_size_order. unfold Expr_size.
    lia.
    assumption. assumption.
  assert (body' = body'0).
    apply (H x2).
    unfold Expr_size_order. unfold Expr_size. lia.
    subst. assumption. assumption.
  subst.
  reflexivity.
  destruct p. destruct a0. destruct H0.
  subst. easy.
  destruct a1. subst. easy.
  destruct a1. destruct X2.
  destruct H0. destruct p. subst.
  easy.
  destruct p. destruct p0. destruct p.
  destruct p. easy. destruct p. destruct H0.
  easy.
  easy.
  destruct a0. destruct H1. destruct H0.
  destruct a1. destruct H3. destruct H4.
  subst. reflexivity.
  subst. destruct H4. subst.
  reflexivity.
  subst. destruct a1.
  destruct H0.
  destruct H1.
  subst.
  reflexivity.
  destruct H1.
  subst.

  reflexivity.

  inversion X. inversion X0. subst.
  destruct X1. destruct p. destruct p.
  inversion X0. subst.
  destruct X1. destruct p0.
  assert (body' = body'0).
    apply (H x).
    unfold Expr_size_order. unfold Expr_size. lia.
    assumption. assumption.
  destruct p0. destruct X2. destruct p1. destruct p1.

  subst.

  induction recList'; induction recList'0. subst. reflexivity.
  subst.
  inversion X. inversion X0. subst.
  destruct X1. destruct p2. destruct p2. inversion m2. subst.
  destruct X2. destruct p3. destruct p3. inversion m3.
  destruct a1. easy. destruct X2. destruct a1.
  destruct H1. subst.
  destruct p2. destruct p2. inversion m2. destruct a1.
  destruct H1. subst. easy.
  subst. inversion m. subst. inversion m1.

  inversion X. subst. inversion X0. subst.
  destruct X1; destruct X2; destruct p1.
  destruct p2. destruct p1. destruct p3. destruct p2.

  assert (A : ReplaceIdWith a b (LetRec l x) (LetRec (a1 :: recList'0) body'0)).
    constructor.
    left. easy.
  assert (A2 : ReplaceIdWith a b (LetRec l x) (LetRec (a1 :: recList') body'0)).
    constructor.
    left. split. split. assumption.
    inversion m3. subst.
    constructor. assumption.
    inversion m. subst. assumption. assumption.
(*
  inversion m2. subst.
  inversion m3. subst.
*)
  inversion A. subst. destruct X1. destruct p3. destruct p3.
  inversion m4. subst.

  assert (A3 : ReplaceIdWith a b (LetRec xs x) (LetRec recList'0 body'0)).
    constructor.
    left. split. split.
    destruct p2. pose (shrinkNotInRecList a x0 xs n1).
    pose (shrinkNotInRecList b x0 xs n2). easy.
    assumption. assumption.

  assert (A4 : ReplaceIdWith a b (LetRec xs x) (LetRec recList' body'0)).
    constructor.
    left. split. split.
    destruct p2. pose (shrinkNotInRecList a x0 xs n1).
    pose (shrinkNotInRecList b x0 xs n2). easy. 
    inversion m2. subst.
    assumption. assumption.

  assert (A_R : LetRec recList' body'0 = LetRec recList'0 body'0).
    apply (H (LetRec xs x)).
    unfold Expr_size_order. simpl.
    destruct x0. pose (Expr_size_pos e). lia.
    assumption. assumption.

  injection A_R; intros. subst.
  destruct a0. destruct a1.
  inversion m2. subst.
  inversion X3. subst. inversion X1. subst.
  assert (e = e0).
    apply (H y).
    unfold Expr_size_order. simpl. lia.
    assumption. assumption.
  subst.

  reflexivity.

  destruct a2. destruct H1. subst. destruct H0.
  destruct p2. easy. destruct p2. easy.

  destruct a2. destruct p2. destruct p1. destruct p1.
  firstorder. firstorder.
  destruct a2. destruct a3. destruct H1. destruct H3.
  subst. firstorder. firstorder. firstorder.

  destruct X2. destruct p. destruct p. firstorder.
  destruct a0. destruct a1. destruct H1. destruct H3.
  subst. reflexivity.
Defined.


Theorem ReplaceIdWith_det (a b : Id) (x : Expr) :
  forall x',
  ReplaceIdWith a b x x' ->
  evalReplaceIdWith a b x = x'.
(* refine (Fix Expr_size_wf _ _). *)
Proof.
  intros.
  unfold evalReplaceIdWith.
  unfold ReplaceIdWith_exist.
  set (ReplaceIdWith_exist_func
     (existT (fun _ : Id => {_ : Id & Expr}) a
        (existT (fun _ : Id => Expr) b x))).
  destruct s.
  rewrite (ReplaceIdWith_confluent a b x _ _ X r).
  reflexivity.
Defined.


Inductive HasExternalize : Expr -> Prop :=
| HasExternalize_Var : HasExternalize (Var ExternalizeId)
| HasExternalize_App : forall a b,
    { HasExternalize a } + { HasExternalize b } -> HasExternalize (App a b)
| HasExternalize_Lam : forall v e,
    HasExternalize e -> HasExternalize (Lam v e)
| HasExternalize_LetNonRec : forall v rhs e,
    { HasExternalize rhs } + { HasExternalize e } -> HasExternalize (LetNonRec v rhs e)
| HasExternalize_LetRec : forall bs e,
    { HasExternalizeRec bs } + { HasExternalize e } -> HasExternalize (LetRec bs e)
| HasExternalize_Case : forall s wild ty altcon patVars rhs restAlts,
    { HasExternalize rhs } + { HasExternalize (Case s wild ty restAlts) } ->
    HasExternalize (Case s wild ty (cons (altcon, patVars, rhs) restAlts))
| HasExternalize_Cast : forall e co,
    HasExternalize e -> HasExternalize (Cast e co)
| HasExternalize_Tick : forall t e,
    HasExternalize e -> HasExternalize (Tick t e)

with HasExternalizeRec : list (VarName * Expr) -> Prop :=
| HasExternalizeBind_Rec : forall b e rest,
    { HasExternalize e } + { HasExternalizeRec rest } -> HasExternalizeRec (cons (b, e) rest).

Notation "x :@ y" := (App x y) (left associativity, at level 40).

(* "Strict" reflexive closure *)
Inductive StrictReflClo {A} (r : A -> A -> Prop) : A -> A -> Prop :=
| StrictReflClo_step : forall x y, r x y -> StrictReflClo r x y
| StrictReflClo_refl : forall x y, ~ r x y -> StrictReflClo r x x.

Check InRecList.

Definition VarNameBoundIn (v : VarName) : list (VarName * Expr) -> Prop :=
  InRecList (SomeId v).

Theorem VarNameBoundIn_dec : forall v xs,
  (VarNameBoundIn v xs) + (~VarNameBoundIn v xs).
  unfold VarNameBoundIn. intros. apply InRecList_dec.
Defined.

Inductive VarNameOccursFreeIn : VarName -> Expr -> Type :=
| VarNameOccursFreeIn_Var : forall v, VarNameOccursFreeIn v (Var (SomeId v))

| VarNameOccursFreeIn_App : forall v a b,
    (VarNameOccursFreeIn v a) + (VarNameOccursFreeIn v b) -> VarNameOccursFreeIn v (App a b)

| VarNameOccursFreeIn_Lam : forall v1 v2 e,
    v2 <> v1 ->
    VarNameOccursFreeIn v1 e ->
    VarNameOccursFreeIn v1 (Lam v2 e)

| VarNameOccursFreeIn_Let_NonRec : forall v1 v2 e body,
    v2 <> v1 ->
    (VarNameOccursFreeIn v1 e) + (VarNameOccursFreeIn v1 body) ->
    VarNameOccursFreeIn v1 (LetNonRec v2 e body)

| VarNameOccursFreeIn_Let_Rec_nil : forall v body,
    VarNameOccursFreeIn v body ->
    VarNameOccursFreeIn v (LetRec nil body)

| VarNameOccursFreeIn_Let_Rec_cons : forall v1 v2 e rest body,
    ~ VarNameBoundIn v1 (cons (v2, e) rest) ->
    (VarNameOccursFreeIn v1 e) + (VarNameOccursFreeIn v1 (LetRec rest body)) ->

    VarNameOccursFreeIn v1 (LetRec (cons (v2, e) rest) body)

| VarNameOccursFreeIn_Case_nil : forall v s wild ty,
    VarNameOccursFreeIn v s ->
    VarNameOccursFreeIn v (Case s wild ty nil)

| VarNameOccursFreeIn_Case : forall v s wild ty altcon patVars rhs restAlts,
    ((wild <> v) * (~ (In v patVars)) * VarNameOccursFreeIn v rhs)
      + (VarNameOccursFreeIn v (Case s wild ty restAlts)) ->
    VarNameOccursFreeIn v (Case s wild ty (cons (altcon, patVars, rhs) restAlts))

| VarNameOccursFreeIn_Cast : forall v e co,
    VarNameOccursFreeIn v e ->
    VarNameOccursFreeIn v (Cast e co)

| VarNameOccursFreeIn_Tick : forall v t e,
    VarNameOccursFreeIn v e ->
    VarNameOccursFreeIn v (Tick t e).

Theorem VarNameOccursFreeIn_dec v :
  forall e, VarNameOccursFreeIn v e + notT (VarNameOccursFreeIn v e).
refine (Fix Expr_size_wf _ _).
Proof.
  intros.
  induction x; try easy.
  destruct i; try (right; easy).
  destruct (VarName_dec_eq v v0).
  subst. left. constructor.
  right. intro. inversion H0. subst. easy.

  destruct (H x1); destruct (H x2); try (unfold Expr_size_order; simpl; lia).
  left. constructor. left. assumption.
  left. constructor. left. assumption.
  left. constructor. right. assumption.
  right. intro. inversion H0. subst. firstorder.

  destruct (VarName_dec_eq v0 v). subst.
  right. intro. inversion H0. easy.
  destruct (H x). unfold Expr_size_order. simpl. lia.
  left. constructor. assumption. assumption.
  right. intro. inversion H0. subst. easy.

   
  destruct (VarName_dec_eq v0 v).
  subst.
  right. intro. inversion H0. easy.
  destruct (H x1); destruct (H x2); try (unfold Expr_size_order; simpl; lia).
  left. constructor. assumption. left. assumption.
  left. constructor. assumption. left. assumption.
  left. constructor. assumption. right. assumption.
  right. intro. inversion H0. subst. destruct H6; easy.

  destruct (VarNameBoundIn_dec v l).
  right. intro. inversion H0. subst.
  inversion v0. subst. easy.

  induction l.
  destruct (H x).
  unfold Expr_size_order. simpl. lia.
  left. constructor. assumption.
  right. intro. inversion H0. subst. easy.

  destruct a.
  destruct (H x).
  unfold Expr_size_order. simpl. lia.
  left. constructor. intro. inversion H0; subst. easy.

  destruct l. inversion H6.
  easy. destruct (H e).
  unfold Expr_size_order. simpl. lia.
  left. assumption.

  clear H IHx IHl.
  dependent induction l. right.
  constructor. assumption.
  destruct a. right. constructor.
  intro. contradict n.
  destruct (VarName_dec_eq v v0). subst.
  apply InRecList_here. reflexivity.
  apply InRecList_there. congruence. assumption.
  right.
  destruct (IHl x).
  intro. contradict n.
  destruct (VarName_dec_eq v v0). subst.
  apply InRecList_here. reflexivity.
  apply InRecList_there. congruence.
  destruct (VarName_dec_eq v v2). subst.
  apply InRecList_here. reflexivity.
  apply InRecList_there. congruence. inversion H. subst.
  congruence. subst. assumption.
  assumption.
  assumption. easy.
  assumption.

  destruct (H (LetRec l x)).
  unfold Expr_size_order. simpl. pose (Expr_size_pos e). lia.

  left. constructor. assumption. right. assumption.
  destruct (H e).
  unfold Expr_size_order. simpl. lia.
  left. constructor. assumption.
  left. assumption.
  right. intro.
  inversion H0. subst.
  destruct H7. easy.
  easy.
Defined.

Theorem notFreeReplace v v' : forall e,
  notT (VarNameOccursFreeIn v e) ->
  ReplaceIdWith (SomeId v) v' e e.
refine (Fix Expr_size_wf _ _).
Proof.
  intro e. intros.
  induction e; try easy.
  constructor.
  right. split.
  contradictT H.
  subst. constructor.
  reflexivity.
  constructor.
  apply IHe1.
  intros. apply X.
  unfold Expr_size_order in *. simpl. lia.
  assumption. intro. contradictT H.
  constructor. left. assumption.
  apply X.
  unfold Expr_size_order in *. simpl. lia.
  intro. contradictT H. constructor. right. assumption.

  constructor.

  destruct (VarName_dec_eq v0 v); destruct (Id_dec_eq (SomeId v) v'); destruct (Id_dec_eq (SomeId v0) v'); subst.
  right. split. left. reflexivity. reflexivity.
  right. split. left. reflexivity. reflexivity.
  left. split. split. congruence. congruence.
  apply ReplaceIdWith_unchanged.
  right. split. left. reflexivity. reflexivity. injection e1; intros; subst.
  contradiction.
  left. split. easy.
  apply X. unfold Expr_size_order. simpl. lia.
  intro. contradictT H. constructor. assumption. assumption.
  right. split. right. reflexivity. reflexivity.
  left. split. split. congruence. congruence.
  apply X. unfold Expr_size_order. simpl. lia.
  intro. contradictT H. constructor. assumption. assumption.


  destruct (VarName_dec_eq v0 v); destruct (Id_dec_eq (SomeId v) v'); destruct (Id_dec_eq (SomeId v0) v'); subst.
  constructor. right. split. left. easy. easy.
  contradiction.
  constructor. right. split. left. easy. easy.
  constructor. right. split. left. reflexivity. easy.
  injection e0; intros; subst.
  contradiction.
  constructor.
  left. split. split. split. assumption. assumption.
  apply ReplaceIdWith_unchanged.
  apply ReplaceIdWith_unchanged.
  constructor.
  right. split. right. reflexivity.
  easy.
  constructor. left. split. split. split.
  congruence. congruence.
  apply IHe1. intros.
  apply X. unfold Expr_size_order in *. simpl. lia.
  assumption. intro. contradictT H.
  constructor. assumption. left. assumption.
  apply IHe2. intros.
  apply X. unfold Expr_size_order in *. simpl. lia.
  assumption. intro. contradictT H.
  constructor. assumption. right. assumption.

  induction l.
  constructor.
  left. split. split. split.
  intro. inversion H0. intro. inversion H0.
  constructor.
  apply IHe. intros.
  apply X. unfold Expr_size_order in *. simpl. lia.
  assumption. intro. contradictT H.
  constructor. assumption.

  constructor.

  destruct (InRecList_dec (SomeId v) (a :: l)); destruct (InRecList_dec v' (a :: l)).
  right. split. left. assumption. easy.
  right. split. left. assumption. easy.
  right. split. right. assumption. easy.
  left. split. split. easy.
  constructor. destruct a. constructor.
  apply X. unfold Expr_size_order. simpl. lia.
  intro. contradictT H. constructor. assumption.
  left. assumption.

  induction l. constructor.
  constructor. destruct a0. constructor.
  apply X.
  unfold Expr_size_order. simpl. destruct a. lia.
  intro. contradictT H.
  destruct a.
  constructor. assumption. right.
  constructor. intro. contradictT n.
  destruct (VarName_dec_eq v1 v). subst.
  apply InRecList_here. reflexivity.
  apply InRecList_there. congruence. assumption.
  left. assumption.
  apply IHl0.
  intros.
  apply X.
  unfold Expr_size_order in *. simpl. destruct a. simpl in H0. destruct a0.
  lia.
  assumption.
  intro. contradictT H.
  destruct a.
  destruct (VarName_dec_eq v v0). subst.
  constructor. assumption.
  inversion H0. subst.
  destruct H6. left. assumption.
  right. destruct a0.
  destruct (IHl); try (intros; subst; easy). intros.

  destruct (Id_dec_eq (SomeId v0) v'). subst.
  apply ReplaceIdWith_unchanged.

  { apply (X y). unfold Expr_size_order in *. simpl. simpl in H. lia.
    assumption.

    all: try (contradict H3; constructor; reflexivity).
  }
  all: try (contradict H3; constructor; reflexivity).
  constructor. easy. inversion H0.
  subst. destruct H6. left. assumption.
  right. destruct a0.
  destruct (VarName_dec_eq v v2). subst.
  contradictT n. apply InRecList_there. congruence.
  apply InRecList_here. reflexivity.
  constructor. intro. contradictT n.
  apply InRecList_there. congruence. assumption.
  right. assumption.

  intros.
  { apply X. destruct a, a0. unfold Expr_size_order in *. simpl. simpl in H.
    pose (Expr_size_pos e0). lia.
    assumption.
  }

  { intro. contradictT n.
    destruct a.
    inversion H0; subst. injection H3; intros; subst.
    apply InRecList_here. reflexivity.
    apply InRecList_there. assumption.
    destruct a0.
    destruct (VarName_dec_eq v v1). subst.
    apply InRecList_here. reflexivity.
    apply InRecList_there. congruence.
    assumption.
  }

  { intro. contradictT n0.
    inversion H0; subst.
    apply InRecList_here. reflexivity.
    apply InRecList_there. assumption.
    destruct a0.
    destruct (Id_dec_eq v' (SomeId v0)). subst.
    apply InRecList_here. reflexivity.
    apply InRecList_there. assumption.
    assumption.
  }

  { apply X. destruct a.  unfold Expr_size_order in *. simpl. lia.
    intro. contradictT H.
    destruct a.
    destruct (VarName_dec_eq v v0). subst.
    constructor. assumption.
    right. induction l. constructor. assumption.
    destruct a.
    constructor. intro. contradictT n.
    apply InRecList_here. reflexivity.
    right. apply IHl0.
    intro. contradictT n.
    apply InRecList_here. reflexivity.
    intros.
    apply (X (LetRec l e)).
    unfold Expr_size_order. simpl. pose (Expr_size_pos e0). lia.
    assumption.
    intros.
    apply X.
    unfold Expr_size_order in *. simpl. simpl in H. lia.
    assumption.
    intro. contradictT n0.
    destruct (Id_dec_eq v' (SomeId v0)). subst.
    apply InRecList_here. reflexivity.
    apply InRecList_there. assumption.
    destruct (Id_dec_eq v' (SomeId v)). subst.
    apply InRecList_here. reflexivity.
    inversion H; subst. easy.
    apply InRecList_there. assumption.
    assumption.

    constructor. assumption.
    right.
    { induction l. constructor. assumption.
      destruct a.
      constructor. intro.
      contradictT n.
      destruct (VarName_dec_eq v v0). subst.
      apply InRecList_here. reflexivity.
      apply InRecList_there. congruence.
      assumption.

      right.
      apply IHl0.
      intros.
      apply X.
      unfold Expr_size_order in *. simpl. simpl in H. lia.
      assumption.
      intros.
      apply X.
      unfold Expr_size_order. simpl. pose (Expr_size_pos e0). lia.
      assumption.
      intro.
      contradictT n. inversion H; subst.
      apply InRecList_here. assumption.
      apply InRecList_there. assumption.
      destruct (VarName_dec_eq v v1). subst.
      apply InRecList_here. reflexivity.
      apply InRecList_there. congruence. assumption.

      intro. contradictT n0.
      inversion H; subst.
      apply InRecList_here. reflexivity.
      apply InRecList_there. assumption.
      destruct (Id_dec_eq v' (SomeId v1)). subst.
      apply InRecList_here. reflexivity.
      apply InRecList_there. assumption.
      assumption.
    }
  }
Defined.



(* Remove a lambda *)
Inductive TransformTailRec0 : Expr -> Expr -> Prop :=
| MkTransformTailRec0 : forall v body,
    TransformTailRec0 (Lam v body) body.

(* Remove a internalize (externalize ...) from around a 'case' expression *)
Inductive TransformTailRec1 : Expr -> Expr -> Prop :=
| MkTransformTailRec1 : forall ty dict s wild alts,
    TransformTailRec1
      (Var InternalizeId :@ TypeExpr ty :@ dict :@ (Var ExternalizeId :@ TypeExpr ty :@ dict :@ Case s wild ty alts))
      (Case s wild ty alts).


Inductive NotCase : Expr -> Type :=
| MkNotCase : forall e,
    (~ exists s wild ty alts, e = Case s wild ty alts) -> NotCase e.

(* TODO: Make sure patVars does not contain recName *)
Inductive TransformTailRec_Alts : VarName -> list Alt -> list Alt -> Type :=
| MkTransformTailRec_Alts_nil : forall recName, TransformTailRec_Alts recName nil nil
| MkTransformTailRec_Alts_Case_Case :  (* Descend into sub-case *)
    forall recName altcon patVars s wild ty alts alts' restAlts restAlts',
    ( (~ InVarList (SomeId recName) patVars) * TransformTailRec_Alts recName alts alts' )
     +
    { InVarList (SomeId recName) patVars /\ alts' = alts } ->
    notT (VarNameOccursFreeIn recName s) ->
    wild <> recName ->
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, Case s wild ty alts) restAlts)
      (cons (altcon, patVars, Case s wild ty alts') restAlts')

| MkTransformTailRec_Alts_Case_rec : forall recName altcon patVars body0 body0' restAlts restAlts',
    VarNameOccursFreeIn recName body0 -> (* Recursive case *)
    NotCase body0 -> (* Not case-of-case *)
    NotCase body0' ->
    ReplaceIdWith (SomeId recName) StepId body0 body0' ->
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, body0) restAlts)
      (cons (altcon, patVars, body0') restAlts')

| MkTransformTailRec_Alts_Case_nonrec : forall recName altcon patVars body0 restAlts restAlts',
    notT (VarNameOccursFreeIn recName body0) -> (* Base case *)
    NotCase body0 -> (* Not case-of-case *)
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, body0) restAlts)
      (cons (altcon, patVars, Var DoneId :@ body0) restAlts').

Ltac solveNotCase H :=
  (destruct H; destruct H; destruct H; destruct H; discriminate).

Ltac solveNotCaseGoal :=
  let H := fresh "H" in
  constructor; intro H; solveNotCase H.

Lemma StepNotInRecList : forall xs,
  ~ InRecList StepId xs.
Proof.
  intros.
  intro.
  dependent induction H.
  apply IHInRecList. reflexivity.
Defined.

Theorem TransformTailRec_Alts_progress :
  forall recName alts,
  { alts' : list Alt & TransformTailRec_Alts recName alts alts' }.
Proof.
  intros.

  induction alts.
  exists nil. constructor.

  destruct a. destruct p.
  induction e.
  destruct (Id_dec_eq (SomeId recName) i). subst.
  destruct IHalts.
  exists ((a, l, Var StepId) :: x).
  constructor. constructor. solveNotCaseGoal.
  solveNotCaseGoal. constructor. left. easy.
  assumption.

  destruct IHalts.
  exists ((a, l, Var DoneId :@ Var i) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec.
  intro. inversion H. subst. contradiction.
  solveNotCaseGoal.
  assumption.

  destruct IHalts.
  exists ((a, l, Var DoneId :@ Lit l0) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec. easy.
  solveNotCaseGoal. assumption.
  destruct IHalts.
  destruct IHe1.
  destruct IHe2.
  inversion t0; inversion t1; subst; try easy.
  exists ((a, l, (body0' :@ body0'0)) :: restAlts'0).
  constructor. constructor. left. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  constructor. assumption. assumption.
  assumption.
  exists ((a, l, (body0' :@ e2)) :: restAlts'0).
  constructor. constructor. left. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  constructor. assumption.
  apply notFreeReplace. assumption.
  assumption.

  exists ((a, l, (e1 :@ body0')) :: restAlts'0).
  constructor. constructor. right. assumption.
  solveNotCaseGoal. solveNotCaseGoal.

  constructor.
  apply notFreeReplace. assumption.
  assumption. assumption.

  exists ((a, l, Var DoneId :@ (e1 :@ e2)) :: restAlts'0).
  apply MkTransformTailRec_Alts_Case_nonrec.
  intro. inversion H; subst. destruct H2.
  easy. easy.
  solveNotCaseGoal. assumption.

  destruct (VarNameOccursFreeIn_dec recName (Lam v e)).
  destruct IHalts.
  destruct IHe.
  induction x0. inversion t0.
  destruct a0.
  exists ((a, l, Lam v e0) :: x0).
  constructor. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  constructor.
  left. split. split.
  inversion v0. subst. congruence.
  easy.
  inversion t0. subst.
  destruct X. destruct p.
  constructor.
  apply notFreeReplace. assumption.
  left. split. split. congruence. easy.
  induction alts0; induction alts'; try easy.
  constructor.
  apply notFreeReplace. assumption.
  left. split. split. congruence. easy.
  induction alts0; induction alts'; try easy. subst.
  assumption. subst.
  contradictT H2.
  inversion v0; subst. assumption.
  inversion t0; subst. assumption.
  assumption. assumption.

  destruct IHalts.
  destruct IHe.
  exists ((a, l, Var DoneId :@ (Lam v e)) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec. assumption.
  solveNotCaseGoal. assumption.

  destruct IHalts.
  destruct IHe1.
  destruct IHe2.
  destruct (VarNameOccursFreeIn_dec recName (LetNonRec v e1 e2)).
  inversion t0; inversion t1; subst.
  all: try easy.
  inversion v0; subst.
  exists ((a, l, LetNonRec v body0' body0'0) :: x).
  constructor. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  constructor. left. split. split. split. congruence.
  easy. assumption. assumption. assumption.

  exists ((a, l, LetNonRec v body0' e2) :: x).
  constructor. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  constructor. left. split. split. split.
  inversion v0; subst. congruence. easy.
  assumption.
  apply notFreeReplace. assumption.
  assumption.

  exists ((a, l, LetNonRec v e1 body0') :: x).
  constructor. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  inversion v0; subst.
  constructor. left. split. split. split. congruence.
  easy. apply notFreeReplace. assumption.
  assumption. assumption.

  exists ((a, l, Var DoneId :@ (LetNonRec v e1 e2)) :: x).
  inversion v0; subst. destruct H4; easy.

  exists ((a, l, Var DoneId :@ (LetNonRec v e1 e2)) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec. assumption.
  solveNotCaseGoal.
  assumption.

  destruct IHalts. destruct IHe.
  destruct (InRecList_dec (SomeId recName) l0).
  exists ((a, l, Var DoneId :@ (LetRec l0 e)) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec. intro.
  inversion i; subst. inversion H0; subst. inversion H; subst.
  easy. inversion i; subst. easy.
  inversion H; subst. easy.
  solveNotCaseGoal. assumption.

  destruct (VarNameOccursFreeIn_dec recName e).
  {
    { generalize dependent t0.

      induction l0; intro t0.
      destruct x0. inversion t0; subst.
      destruct a0.
      exists ((a, l, LetRec nil e0) :: x).
      constructor. constructor. assumption.
      solveNotCaseGoal. solveNotCaseGoal.
      constructor. left.
      split. split. split; easy.
      constructor.

      inversion t0; subst.
      destruct X. destruct p. easy.
      destruct a0. subst. easy.
      assumption. easy.
      assumption.

      destruct IHl0.
      intro. contradictT n.
      destruct a0.
      destruct (VarName_dec_eq recName v0).
      apply InRecList_here. congruence.
      apply InRecList_there. congruence.
      assumption. assumption.

      destruct x1. easy.
      destruct a1.


      destruct (MapRelation_exists (RelationOnSnd (ReplaceIdWith (SomeId recName) StepId)) (a0 :: l0)).
      intros.
      apply (RelationOnSnd_exists (ReplaceIdWith (SomeId recName) StepId) a1).
      intros.
      apply (ReplaceIdWith_exist (SomeId recName) StepId).

      destruct x0. easy.
      destruct a1.
      exists ((a, l, LetRec x2 e1) :: x).

      constructor.
      destruct a0. constructor.
      assumption.
      right. clear m t1 t0. induction l0. constructor. assumption.
      destruct a0. constructor.
      intro. contradictT n.
      destruct (VarName_dec_eq recName v0).
      apply InRecList_here. congruence.
      apply InRecList_there. congruence.
      assumption.
      right. apply IHl0.
      intro. contradictT n.
      destruct (VarName_dec_eq recName v0).
      apply InRecList_here. congruence.
      apply InRecList_there. congruence.
      destruct (VarName_dec_eq recName v1).
      apply InRecList_here. congruence.
      apply InRecList_there. congruence.
      inversion H; subst. congruence. assumption.
      solveNotCaseGoal. solveNotCaseGoal.
      constructor.
      left. split. split. split. assumption.
      apply StepNotInRecList.
      assumption.
      inversion t0; subst; try easy.
      assumption.
    }

  }

  induction l0.
  exists ((a, l, Var DoneId :@ (LetRec nil e)) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec.
  intro. inversion H; subst. easy.
  solveNotCaseGoal. assumption.

  destruct (MapRelation_exists (RelationOnSnd (ReplaceIdWith (SomeId recName) StepId)) (a0 :: l0)).
  intros.
  apply (RelationOnSnd_exists (ReplaceIdWith (SomeId recName) StepId) a1).
  intros.
  apply (ReplaceIdWith_exist (SomeId recName) StepId).


  destruct (VarNameOccursFreeIn_dec recName (LetRec (a0 :: l0) e)).
  exists ((a, l, (LetRec x1 e)) :: x).
  destruct x1.
  inversion m. constructor. assumption.
  solveNotCaseGoal. solveNotCaseGoal.
  destruct a0. destruct p.
  constructor.
  left. split. split. split. assumption.
  apply StepNotInRecList.
  assumption.
  apply notFreeReplace.
  assumption. assumption.


  exists ((a, l, Var DoneId :@ (LetRec (a0 :: l0) e)) :: x).
  apply MkTransformTailRec_Alts_Case_nonrec.
  assumption. solveNotCaseGoal.
  assumption.
Defined.



Inductive TransformTailRec : VarName -> Expr -> Expr -> Prop :=
| MkTransformTailRec : forall recName a b s wild ty alts alts',
    TransformTailRec0 a b ->
    TransformTailRec1 b (Case s wild ty alts) ->
    TransformTailRec_Alts recName alts alts' ->
    TransformTailRec recName a (Case s wild ty alts').
(*
Inductive TransformTailRec : VarName -> Expr -> Expr -> Prop :=
| MkTransformTailRec : forall recName e e',
    { exists s wild ty alts alts', e = Case s wild ty alts /\
      TransformTailRecCase recName 
*)

Theorem TransformTailRec_Case_progress :
  forall recName e e' s wild ty alts alts',
        TransformTailRec0 e e' ->
        TransformTailRec1 e' (Case s wild ty alts) ->
        TransformTailRec recName e (Case s wild ty alts').
Proof.
  intros.
  econstructor.
  apply H.
  apply H0.
  constructor.

  case_eq e; intros; try ((left; right; easy) || right; easy).
  case_eq e'; intros; try(subst; discriminate).
  case_eq e0; intros. subst.
  subst. right. 
    subst; right; intros; intro; inversion H.
Defined.


Inductive TransformTailRecBinds : CoreProgram -> CoreProgram -> Prop :=
| TransformTailRecBinds_nil : TransformTailRecBinds nil nil

| TransformTailRecBinds_NonRec_cons : forall v e restBinds restBinds',
    TransformTailRecBinds restBinds restBinds' ->
    TransformTailRecBinds (NonRec v e :: restBinds) (NonRec v e :: restBinds')

| TransformTailRecBinds_cons : forall fName fBody fBody' restRec restRec' restBinds restBinds',
    { VarNameOccursFreeIn fName fBody /\ TransformTailRec fName fBody fBody' }
      +
    { ~ VarNameOccursFreeIn fName fBody /\ fBody' = fBody} ->
    TransformTailRecBinds (cons (Rec restRec) nil) (cons (Rec restRec') nil) ->
    TransformTailRecBinds restBinds restBinds' ->
    TransformTailRecBinds
      (cons (Rec (cons (fName, fBody) restRec)) restBinds)
      (cons (Rec (cons (fName, fBody') restRec')) restBinds').

Theorem TransformTailRecBinds_progress
  : forall p,
    exists p',
    TransformTailRecBinds p p'.
Proof.
  intros.
  induction p.
  exists nil. constructor.

  destruct IHp.
  destruct a.
  exists x.
  induction p. induction x.
  destruct p0.
  constructor.
  constructor.
  destruct p0.
  constructor.
