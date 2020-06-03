Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Relations_3.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.

Definition eq_dec T := forall (x y : T), {x=y} + {x<>y}.

Hint Unfold eq_dec : eqdec.
Hint Extern 5 (eq_dec ?T) => unfold eq_dec; repeat decide equality : eqdec.

Check @confluent.
Check Confluent.
Check Relation.

Definition evalRelation {A} (r : relation A) {conf_prf : Confluent _ r} {n_prf : Noetherian _ r} (x : A) : A :=  x.

Inductive VarName := MkVarName : nat -> VarName.

Inductive CoreType := .
Scheme Equality for CoreType.

Inductive Literal := .
Scheme Equality for Literal.

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

Inductive AltCon :=
| DataAlt : DataCon -> AltCon
| LitAlt : Literal -> AltCon
| DEFAULT : AltCon.
Scheme Equality for AltCon.

Lemma AltCon_dec_eq : eq_dec AltCon.  auto with eqdec. Defined.
Hint Resolve AltCon_dec_eq : eqdec.

Inductive Tickish := .
Scheme Equality for Tickish.

Inductive Coercion := .
Scheme Equality for Coercion.

Inductive Expr :=
| Var : Id -> Expr
| Lit : Literal -> Expr
| App : Expr -> Expr -> Expr
| Lam : VarName -> Expr -> Expr
| Let : Bind -> Expr -> Expr
| Case : Expr -> VarName -> CoreType -> list (AltCon * list VarName * Expr) -> Expr
| Cast : Expr -> Coercion -> Expr
| Tick : Tickish -> Expr -> Expr
| TypeExpr : CoreType -> Expr
| CoercionExpr : Coercion -> Expr

with Bind :=
| NonRec : VarName -> Expr -> Bind
| Rec : list (VarName * Expr) -> Bind.

Scheme Expr_mut := Induction for Expr Sort Prop
with Bind_mut := Induction for Bind Sort Prop.

Combined Scheme Expr_Bind_mutind from Expr_mut,Bind_mut.

Check fold_right.

Fixpoint Expr_size (e : Expr) : nat :=
  match e with
  | Var _ => 1
  | Lit _ => 1
  | App a b => 1 + Expr_size a + Expr_size b
  | Lam _ x => 1 + Expr_size x
  | Let bind x =>
      1 + match bind with
          | NonRec v b => Expr_size b + Expr_size x
          | Rec bs => fold_right (fun p q => match p with (_, e) => q + Expr_size e end) 0 bs + Expr_size x
          end
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


Proposition Expr_dec_eq (x y : Expr) : {x=y} + {x<>y}
with Bind_dec_eq (x y : Bind) : {x=y} + {x<>y}. decide equality; auto with eqdec.
  repeat decide equality. subst. repeat decide equality. subst. decide equality.
  repeat (try subst; decide equality). decide equality. decide equality. decide equality.
  decide equality. decide equality. decide equality. repeat decide equality.
Defined.

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

Fixpoint shrinkNotInRecList (v : Id) (x : VarName * Expr) (xs : list (VarName * Expr)) :
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

Inductive MapRelation {A} (R : relation A) : list A -> list A -> Prop :=
| MapRelation_nil : MapRelation R nil nil
| MapRelation_cons : forall x x' xs xs',
    R x x' ->
    MapRelation R xs xs' ->
    MapRelation R (x::xs) (x'::xs').

Fixpoint MapRelation_exists {A} (R : relation A) (xs : list A) (R_prf : forall a (prf : In a xs), {a' : A & R a a'}) {struct xs} :
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


Inductive RelationOnSnd {A B} (R : relation B) : (A * B) -> (A * B) -> Prop :=
| MkRelationOnSnd : forall x y y',
    R y y' ->
    RelationOnSnd R (x, y) (x, y').

Definition RelationOnSnd_exists {A B} (R : relation B) (ab : A * B) (R_prf : forall a0 b (prf : ab = (a0, b)), {b' : B & R b b'}):
  {ab' : A * B &
  RelationOnSnd R ab ab'} :=
    match ab as x return ab = x -> _ with
    | (a, b) => fun Hyp =>
        match R_prf a b Hyp with
        | existT _ x x_prf => existT _ (a, x) (MkRelationOnSnd R _ _ _ x_prf)
        end
    end (eq_refl ab).

Print RelationOnSnd_exists.

Inductive ReplaceIdWith : Id -> Id -> Expr -> Expr -> Prop :=
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
    {SomeId n <> a /\
     SomeId n <> b /\
     ReplaceIdWith a b body body' }
     +
     {(SomeId n = a \/ SomeId n = b) /\ body' = body} ->
    ReplaceIdWith a b (Lam n body) (Lam n body')
| ReplaceIdWith_Let_NonRec : forall a b v rhs rhs' body body',
     {SomeId v <> a /\
      SomeId v <> b /\
      ReplaceIdWith a b rhs rhs' /\
      ReplaceIdWith a b body body'}
      +
     {(SomeId v = a \/
       SomeId v = b) /\ 
      rhs' = rhs /\
      body' = body} ->
    ReplaceIdWith a b (Let (NonRec v rhs) body) (Let (NonRec v rhs') body')
| ReplaceIdWith_Let_Rec : forall a b recList recList' body body',
    {~ InRecList a recList /\
     ~ InRecList b recList /\
     MapRelation (RelationOnSnd (ReplaceIdWith a b)) recList recList' /\
     ReplaceIdWith a b body body'}
     +
    {(InRecList a recList \/ InRecList b recList) /\ recList' = recList /\ body' = body} ->
    ReplaceIdWith a b (Let (Rec recList) body) (Let (Rec recList') body')

| ReplaceIdWith_Case : forall a b s s' wild ty alts alts',
    ReplaceIdWith a b s s' ->
    {SomeId wild <> a /\ SomeId wild <> b /\
     MapRelation (RelationOnSnd (ReplaceIdWith a b)) alts alts'}
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

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
  R t t' /\ normal_form R t'.

Definition fst_lt (p : nat * nat) (q : nat * nat) := fst p < fst q.

Require Import Coq.Program.Wf.
Require Import Lia.

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
  | Let (NonRec v rhs) body => fun Hyp =>
      if Id_dec_eq (SomeId v) a
      then existT _ (Let (NonRec v rhs) body) (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
      else if Id_dec_eq (SomeId v) b
           then existT _ (Let (NonRec v rhs) body) (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
           else
             match ReplaceIdWith_exist a b rhs _, ReplaceIdWith_exist a b body _ with
             | existT _ rhs' prf_rhs', existT _ body' prf_body' =>
                 existT _ (Let (NonRec v rhs') body') (ReplaceIdWith_Let_NonRec _ _ _ _ _ _ _ _)
             end
  | Let (Rec recList) body => fun Hyp =>
      if InRecList_dec a recList
      then existT _ (Let (Rec recList) body) (ReplaceIdWith_Let_Rec _ _ _ _ _ _ _)
      else if InRecList_dec b recList
           then existT _ (Let (Rec recList) body) (ReplaceIdWith_Let_Rec _ _ _ _ _ _ _)
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
                     existT _ (Let (Rec recList') body') _
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
                 let prf := _ (* @RelationOnSnd_exists (AltCon * list VarName) _ (ReplaceIdWith a b) (fun e'2 => ReplaceIdWith_exist a b e'2 _) *)
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
  subst. simpl. intuition.
  intros.
  apply RelationOnSnd_exists.
  refine (fun a0 e'' prf => ReplaceIdWith_exist a b e'' _).

  rewrite Hyp. rewrite prf in prf0.
  subst.
  clear Hyp2.
  clear r.
  clear ReplaceIdWith_exist.
  clear n.
  clear n0.
  induction recList.
  intuition.
  pose (P := in_inv prf0).
  dependent induction P. subst. simpl. intuition.

  subst.

  assert (A : forall z zs, Expr_size (Let (Rec zs) body) < Expr_size (Let (Rec (z :: zs)) body)).
    induction zs. simpl.
    intuition.
    case_eq (Expr_size b1); intros.
    destruct b1; try ( simpl in H0; discriminate).
    lia.

    simpl.
    destruct a2.
    destruct z.
    case_eq (Expr_size e0); intros.
    destruct e0; try (simpl in H0; discriminate).
    lia.
  pose (IHrecList H).
  subst.

  pose (A' := A a1 recList).
  lia.

  intros.

  apply RelationOnSnd_exists. eapply (fun a0 e'' prf => ReplaceIdWith_exist a b e'' _).
Unshelve.
  subst.
  induction alts. intuition.
  induction (in_inv prf0). intuition.

  assert (A : forall z zs, Expr_size (Case s wild ty zs) < Expr_size (Case s wild ty (z :: zs))).
    induction zs. simpl. intuition.
    intuition.

  simpl. intuition.
Defined.

Print ReplaceIdWith_exist.

Definition evalReplaceIdWith (a b : Id) (e : Expr) : Expr :=
  match ReplaceIdWith_exist a b e with
  | existT _ x _ => x
  end.

Eval cbv in (evalReplaceIdWith RepId UnrepId (App (Var RepId) (Var ConstructId))).

(*
Inductive NatPred : nat -> nat -> Prop :=
| MkNatPred : forall n, NatPred (S n) n.

Lemma NatPred_n : Noetherian _ NatPred.
Proof.
  unfold Noetherian.
  intros.
  constructor.
  intros. inversion H. subst.
  induction H. constructor. intros.
  constructor. intros. Check Fix. Check Acc_iter. Check Acc_intro_generator. auto with sets.

Lemma ReplaceIdWith_n : forall a b, Noetherian _ (ReplaceIdWith a b).
Proof.
  unfold Noetherian.
  intros.
  constructor.
  intros.

Lemma ReplaceIdWith_confluent : forall a b, Confluent _ (ReplaceIdWith a b).
Proof.
  intros.
  unfold Confluent.
  unfold confluent.
  intros.
  unfold coherent.

  induction H0.
  - (* refl case *)
    induction H.
      + (* refl case *)
        exists x.
        split.
        constructor. constructor.
      + 
*)

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
| HasExternalizee_Tick : forall t e,
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

Inductive TransformTailRec0 : Expr -> Expr -> VarName -> Prop :=
| MkTransformTailRec0 : forall v body,
    TransformTailRec0 (Lam v body) body v.

Inductive TransformTailRec1 : Expr -> Expr -> Prop :=
| MkTransformTailRec1 : forall ty dict s wild alts,
    TransformTailRec1
      (Var InternalizeId :@ TypeExpr ty :@ dict :@ (Var ExternalizeId :@ TypeExpr ty :@ dict :@ Case s wild ty alts))
      (Case s wild ty alts).


Inductive TransformTailRec_Alts : VarName -> list Alt -> list Alt -> Prop :=
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
| MkTransformTailRec : forall a b c d,
    TransformTailRec0 a b -> TransformTailRec1 b c -> TransformTailRec2 c d -> TransformTailRec a d.

Inductive TransformBinds_rewrite : CoreProgram -> CoreProgram -> Prop := .
