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




(*
Fixpoint ReplaceWithId_size (a b : Id) (e e' : Expr) (H : ReplaceIdWith a b e e') : nat.
  inversion H.
*)

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


(*
    assumption. reflexivity.
    assumption.
    destruct x. destruct x'.
    inversion H0. subst.
    assert (A3' : e1 = e).
      apply H.
      unfold Expr_size_order. simpl. lia. assumption.
      reflexivity.
    subst. reflexivity.
    intros.
    pose (Expr_size_LetRec_swap (v, e0) x xs body).
    pose (Expr_size_LetRec x ((v, e0) :: xs) body).
    unfold Expr_size_order in *. lia.

  rewrite A3.
  reflexivity.

  destruct a0. destruct H1. subst. reflexivity.
*)

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

Theorem ReplaceIdWith_trans (a b : Id) (x : Expr) (y : Expr) :
  forall z,
  ReplaceIdWith a b x y ->
  ReplaceIdWith a b y z ->
  ReplaceIdWith a b x z.
refine (Fix Expr_size_wf _ _).
Proof.
(*
  intros.
  induction x;
  case_eq x0; intros; try (easy || (inversion X0; inversion X1; now subst)).
  inversion X0. subst. destruct H3. destruct a0. subst.

  destruct (Id_dec_eq a b).
  subst. assumption.

  inversion X1. subst. destruct H3. destruct a0. subst.
  assumption. destruct a0. subst. assumption.
  destruct a0. subst. assumption.
  subst.
  induction X1.
*)



  inversion X1. subst. inversion H1.
  subst. destruct H7; destruct a0. subst.
  assumption. subst. assumption.

  destruct a0. subst. assumption. subst.
  apply H.

  easy. subst.

  unfold Expr_size_order in *.
  rewrite <- (ReplaceIdWith_size_inv a b y x0 H1) in *.
  rewrite <- (ReplaceIdWith_size_inv a b (App x1 x2) y) in *.

  apply (H z).


  dependent induction x; inversion H; inversion H0
    ; try((subst; easy) || (
  subst; destruct H4; destruct a0; destruct H6;
  subst; destruct a0; subst; easy)).


  subst. destruct H4. destruct a0. destruct H6.
  destruct a0. subst. easy. destruct a0. subst. injection H9. intro. subst.
  assumption.
  destruct a0. destruct H6. destruct a0. subst. injection H9. intro. subst.
  assumption.

  destruct a0. subst. injection H9. intro. subst.
  assumption.

  subst.
  injection H12. intros.
  subst.
  assert (A1 : ReplaceIdWith a b x1 f'0).
    apply (IHx1 f').
    assumption. assumption.
  assert (A2 : ReplaceIdWith a b x2 x'0).
    apply (IHx2 x').
    assumption. assumption.

  assert (A3 : forall p q, ReplaceIdWith a b x1 p -> ReplaceIdWith a b x2 q -> ReplaceIdWith a b (App x1 x2) (App p q)).
    intros.
    dependent induction H1. subst. destruct H3. destruct a0. subst.

  dependent induction A1; inversion A2; try easy. subst.

  inversion A1; inversion A2; try easy.
  subst. destruct H1. destruct a0.
  destruct H10. destruct a0. subst.
  apply IHx1.

  clear IHx1. clear IHx2.
  clear H12. clear H. clear A1. clear A2.
  dependent induction H0; intros.
  all: try now inversion H.
  apply (IHReplaceIdWith1 f' x').
  destruct s. destruct a1. subst.

  assert (A3 : 


Theorem ReplaceIdWith_confluent (a b : Id) (x : Expr) :
  forall x1' x2',
  ReplaceIdWith a b x x1' ->
  ReplaceIdWith a b x x2' ->
  x1' = x2'.
refine (Fix Expr_size_wf _ _).
Proof.
  intros.

  dependent induction x;
  inversion H0; inversion H1. subst.
  destruct H5. destruct a0. destruct H10. destruct a0.
  subst. reflexivity. subst. destruct a0. contradiction.
  destruct a0. destruct H10. destruct a0. subst. contradiction.
  destruct a0. subst. reflexivity.

  subst. reflexivity. subst.

  assert (A1 : f' = f'0).
    apply IHx1.
    intros.
    apply H. unfold Expr_size_order in *. 
    simpl. lia.

  pose (IHx1 f' _ f'0 H6).


  inversion H0; inversion H1; try( subst; intuition; now subst).

  subst. destruct H2. destruct a0. destruct H7. destruct a0. subst.
  reflexivity.
  subst. destruct H2.  destruct a0. destruct H7. destruct a0. subst.

  induction H; inversion H0; try (subst; intuition; subst; now intuition).
  subst.

  

  case_eq H0; intros.
  destruct s. destruct a1. subst.

  induction H; try (epose (IHReplaceIdWith1 _); discriminate).


  induction H6. intuition. subst.
  inversion H6. subst. intuition. subst.


Theorem ReplaceIdWith_det (a b : Id) (x : Expr) :
  forall x',
  ReplaceIdWith a b x x' ->
  evalReplaceIdWith a b x = x'.
refine (Fix Expr_size_wf _ _).
Proof.
  intros.

  induction H0.
  - induction (Id_dec_eq a a'). subst.
    destruct H0. destruct a.
    subst.
    unfold evalReplaceIdWith.
    set (ReplaceIdWith_exist a' a' (Var a')).
    induction s.
    apply (ReplaceIdWith_unchanged2 a' (Var a') x).
    assumption.
    destruct a. subst.
    unfold evalReplaceIdWith.
    set (ReplaceIdWith_exist a' a' (Var b)).
    destruct s.
    apply (ReplaceIdWith_unchanged2 a' (Var b) x). assumption.

    destruct H0. destruct a0. subst.
    unfold evalReplaceIdWith.
    set (ReplaceIdWith_exist a a' (Var a)).
    destruct s.
    inversion r. subst.
    destruct H3. destruct a0. subst. reflexivity.
    destruct a0. contradiction.
    destruct a0. subst.
    unfold evalReplaceIdWith.
    set (ReplaceIdWith_exist a a' (Var b)).
    destruct s.
    inversion r.
    subst. destruct H4. destruct a0. subst. contradiction.
    destruct a0. subst. reflexivity.

  - easy.
  - unfold evalReplaceIdWith.
    destruct (ReplaceIdWith_exist a b (App f x)).
    inversion r. subst.
    cut (evalReplaceIdWith a b f = f'). intro A.
    unfold evalReplaceIdWith in A.

    assert (A1 : evalReplaceIdWith a b f = f').
      apply IHReplaceIdWith1.
    pose (ReplaceIdWith_unchanged 




  induction H.
  - destruct H. destruct a0.
    rewrite H. rewrite H0.

    unfold evalReplaceIdWith.
    induction (ReplaceIdWith_exist a a' (Var a)).
    inversion p.
    destruct H4. destruct a1. subst. intuition. subst. intuition.
    destruct a0. rewrite H0.

    unfold evalReplaceIdWith.
    induction (ReplaceIdWith_exist a a' (Var b)).
    inversion p.
    destruct H4. destruct a1. subst. intuition. subst.
    destruct a1. subst. reflexivity.

  - cbv. reflexivity.
  - destruct H. destruct H. destruct a0.
    rewrite H. rewrite H1.

    unfold evalReplaceIdWith.
    induction (ReplaceIdWith_exist a a' (App (Var a) x)).
    inversion p. subst.
    inversion H0. destruct H4. destruct a1. subst.
    inversion H6. destruct H4. destruct a1. subst.
    inversion H8. destruct H5. destruct a1. subst.
    reflexivity. intuition. intuition. destruct a1. subst.
    induction H8. destruct H1. destruct a0. subst.
    
    rewrite IHReplaceIdWith1.
(*    pose (Q := ReplaceIdWith_det1 a a' x (evalReplaceIdWith a a' x) ltac:(reflexivity)). *)
    inversion H0. subst. destruct H. destruct a0.





  induction x; inversion H; subst.
  destruct H3. destruct a0. subst.
  unfold evalReplaceIdWith.
  induction (ReplaceIdWith_exist a b (Var a)).
  induction p. destruct H0. destruct a0. subst.
  reflexivity. destruct a0. subst.



Inductive HasExternalize : Expr -> Prop :=
| HasExternalize_Var : HasExternalize (Var ExternalizeId)
| HasExternalize_App : forall a b,
    { HasExternalize a } + { HasExternalize b } -> HasExternalize (App a b)
| HasExternalize_Lam : forall v e,
    HasExternalize e -> HasExternalize (Lam v e)
| HasExternalize_Let : forall b e,
    { HasExternalizeBind b } + { HasExternalize e } -> HasExternalize (Let b e)
| HasExternalize_Case : forall s wild ty altcon patVars rhs restAlts,
    { HasExternalize rhs } + { HasExternalize (Case s wild ty restAlts) } ->
    HasExternalize (Case s wild ty (cons (altcon, patVars, rhs) restAlts))
| HasExternalize_Cast : forall e co,
    HasExternalize e -> HasExternalize (Cast e co)
| HasExternalize_Tick : forall t e,
    HasExternalize e -> HasExternalize (Tick t e)

with HasExternalizeBind : Bind -> Prop :=
| HasExternalizeBind_NonRec : forall b e,
    HasExternalize e -> HasExternalizeBind (NonRec b e)
| HasExternalizeBind_Rec : forall b e rest,
    { HasExternalize e } + { HasExternalizeBind (Rec rest) } -> HasExternalizeBind (Rec (cons (b, e) rest)).

Notation "x :@ y" := (App x y) (left associativity, at level 40).

(* "Strict" reflexive closure *)
Inductive StrictReflClo {A} (r : A -> A -> Prop) : A -> A -> Prop :=
| StrictReflClo_step : forall x y, r x y -> StrictReflClo r x y
| StrictReflClo_refl : forall x y, ~ r x y -> StrictReflClo r x x.

Inductive VarNameOccursFreeIn : VarName -> Expr -> Prop :=
| VarNameOccursFreeIn_Var : forall v, VarNameOccursFreeIn v (Var (SomeId v))
| VarNameOccursFreeIn_App : forall v a b,
    { VarNameOccursFreeIn v a } + { VarNameOccursFreeIn v b } -> VarNameOccursFreeIn v (App a b)
| VarNameOccursFreeIn_Lam : forall v1 v2 e,
    v2 <> v1 ->
    VarNameOccursFreeIn v1 e ->
    VarNameOccursFreeIn v1 (Lam v2 e)
| VarNameOccursFreeIn_Let_NonRec : forall v1 v2 e body,
    v2 <> v1 ->
    { VarNameOccursFreeIn v1 e } + { VarNameOccursFreeIn v1 body } ->
    VarNameOccursFreeIn v1 (Let (NonRec v2 e) body)
| VarNameOccursFreeIn_Let_Rec_nil : forall v body,
    VarNameOccursFreeIn v body ->
    VarNameOccursFreeIn v (Let (Rec nil) body)
| VarNameOccursFreeIn_Let_Rec_cons : forall v1 v2 e rest body,
    v2 <> v1 ->
    VarNameOccursFreeIn v1 (Let (Rec rest) body) ->
    VarNameOccursFreeIn v1 (Let (Rec (cons (v2, e) rest)) body)
| VarNameOccursFreeIn_Case : forall v s wild ty altcon patVars rhs restAlts,
    {VarNameOccursFreeIn v s} + {wild <> v /\ ~ (In v patVars) /\ VarNameOccursFreeIn v rhs} ->
    VarNameOccursFreeIn v (Case s wild ty (cons (altcon, patVars, rhs) restAlts))
| VarNameOccursFreeIn_Cast : forall v e co,
    VarNameOccursFreeIn v e ->
    VarNameOccursFreeIn v (Cast e co)
| VarNameOccursFreeIn_Tick : forall v t e,
    VarNameOccursFreeIn v e ->
    VarNameOccursFreeIn v (Tick t e).

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


(* TODO: Make sure patVars does not contain recName *)
Inductive TransformTailRec_Alts : VarName -> list Alt -> list Alt -> Prop :=
| MkTransformTailRec_Alts_Case_Case :  (* Descend into sub-case *)
    forall recName altcon patVars s wild ty alts alts' restAlts restAlts',
    { ~ InVarList (SomeId recName) patVars /\ TransformTailRec_Alts recName alts alts' }
     +
    { InVarList (SomeId recName) patVars /\ alts' = alts } ->
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, Case s wild ty alts) restAlts)
      (cons (altcon, patVars, Case s wild ty alts') restAlts')

| MkTransformTailRec_Alts_Case_rec : forall recName altcon patVars body0 body0' restAlts restAlts',
    VarNameOccursFreeIn recName body0 -> (* Recursive case *)
    ReplaceIdWith (SomeId recName) StepId body0 body0' ->
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, body0) restAlts)
      (cons (altcon, patVars, body0') restAlts')

| MkTransformTailRec_Alts_Case_nonrec : forall recName altcon patVars body0 restAlts restAlts',
    ~ VarNameOccursFreeIn recName body0 -> (* Base case *)
    TransformTailRec_Alts recName restAlts restAlts' ->
    TransformTailRec_Alts
      recName
      (cons (altcon, patVars, body0) restAlts)
      (cons (altcon, patVars, Var DoneId :@ body0) restAlts').

Inductive TransformTailRec : VarName -> Expr -> Expr -> Prop :=
| MkTransformTailRec : forall recName a b s wild ty alts alts',
    TransformTailRec0 a b ->
    TransformTailRec1 b (Case s wild ty alts) ->
    TransformTailRec_Alts recName alts alts' ->
    TransformTailRec recName a (Case s wild ty alts').

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
