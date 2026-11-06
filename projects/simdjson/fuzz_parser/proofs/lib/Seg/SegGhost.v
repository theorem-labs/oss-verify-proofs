(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound AsanPlanCore MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegLearn SegTmpl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import ST.
Open Scope Z_scope.

Module SG.


Fixpoint exprs_eqb (a b : list expr) : bool :=
  match a, b with [] , [] => true | x :: a', y :: b' => (expr_eqb x y && exprs_eqb a' b')%bool | _, _ => false end.
Definition gatom_eqb (a b : gatom) : bool := (Nat.eqb (g_id a) (g_id b) && exprs_eqb (g_args a) (g_args b))%bool.

Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite (expr_eqb_eq _ _ H1), (IH _ H2). reflexivity.
Qed.
Lemma gatom_eqb_eq : forall a b, gatom_eqb a b = true -> a = b.
Proof.
  intros [i a] [j b] H. unfold gatom_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply exprs_eqb_eq in H2. subst. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bc_eqb (a b : branch_cond) : bool :=
  match a, b with
  | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
  | _, _ => false
  end.
Lemma bc_eqb_eq : forall a b, bc_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.

Definition sc_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCBr t c a b, SCBr t' c' a' b' => Bool.eqb t t' && bc_eqb c c' && expr_eqb a a' && expr_eqb b b'
  | SCFlat a n, SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | SCDisj a n b m, SCDisj a' n' b' m' => saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCInside a n b m, SCInside a' n' b' m' => saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCStoreOk a n, SCStoreOk a' n' => saddr_eqb a a' && Nat.eqb n n'
  | SCReadBase a n sx e, SCReadBase a' n' sx' e' => saddr_eqb a a' && Nat.eqb n n' && Bool.eqb sx sx' && expr_eqb e e'
  | SCEq a b, SCEq a' b' => expr_eqb a a' && expr_eqb b b'
  | _, _ => false
  end%bool.
Lemma sc_eqb_eq : forall x y, sc_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [sc_eqb] in H; try discriminate;
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
    | H : bc_eqb _ _ = true |- _ => apply bc_eqb_eq in H
    end; subst; reflexivity.
Qed.

Definition se_eqb (x y : sentry) : bool :=
  (saddr_eqb (e_addr x) (e_addr y) && Nat.eqb (e_width x) (e_width y) && expr_eqb (e_val x) (e_val y))%bool.
Fixpoint log_eqb (a b : list sentry) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => if se_eqb x y then log_eqb a' b' else false | _, _ => false end.
Lemma log_eqb_eq : forall a b, log_eqb a b = true -> a = b.
Proof.
  induction a as [|[xa xw xv] a IH]; intros [|[ya yw yv] b] H; try discriminate; [reflexivity|].
  cbn [log_eqb] in H. destruct (se_eqb _ _) eqn:H1 in H; [|discriminate]. rename H into H2. unfold se_eqb in H1. cbn in H1.
  apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [H1 H4].
  apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H4. apply expr_eqb_eq in H3. subst. rewrite (IH _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition subsetb {A} (eqb : A -> A -> bool) (a b : list A) : bool := SLin.lall (fun x => SLin.lex (eqb x) b) a.
Lemma subsetb_in : forall {A} (eqb : A -> A -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall a b x, subsetb eqb a b = true -> In x a -> In x b.
Proof.
  intros A eqb Heq a b x H Hx. unfold subsetb in H. pose proof (SLin.lall_forall _ _ _ H x Hx) as X.
  apply SLin.lex_exists in X as (y & Hy & E). apply Heq in E. subst. exact Hy.
Qed.
Lemma Forall_subset : forall {A} (P : A -> Prop) (eqb : A -> A -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall a b, subsetb eqb a b = true -> Forall P b -> Forall P a.
Proof.
  intros A P eqb Heq a b H HF. apply Forall_forall. intros x Hx.
  exact (proj1 (Forall_forall _ _) HF x (subsetb_in eqb Heq a b x H Hx)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sem.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.

Definition gholds (E : env) (M : word -> option byte) (l : list gatom) : Prop :=
  Forall (fun g => GP (g_id g) (map (edenot E) (g_args g)) M) l.

Lemma gholds_sub : forall E M sg l, gholds E M (map (gsub sg) l) -> gholds (senv E sg) M l.
Proof.
  intros E M sg l H. unfold gholds in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) H (gsub sg g) (in_map _ _ _ Hg)) as X. cbn [gsub g_id g_args] in X.
  rewrite map_map in X. erewrite map_ext; [exact X|]. intros e. apply esub_den.
Qed.

Lemma gholds_agree : forall n E E' M l, AxSymRun3.env_agree n E E' -> gvars_lt n l = true -> gholds E M l -> gholds E' M l.
Proof.
  intros n E E' M l Ha Hv H. unfold gholds in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) H g Hg) as X.
  unfold gvars_lt in Hv. pose proof (proj1 (forallb_forall _ _) Hv g Hg) as Hg'.
  erewrite map_ext_in; [exact X|]. intros e He. cbn beta. symmetry.
  exact (AxSymRun3.edenot_agree n E E' e Ha (proj1 (forallb_forall _ _) Hg' e He)).
Qed.

Lemma gholds_app : forall E M a b, gholds E M a -> gholds E M b -> gholds E M (a ++ b).
Proof. intros. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Record vc : Type := VC {
  vc_kn : list kentry;         (* [comment removed for export] *)
  vc_path : list sidecond;     (* [comment removed for export] *)
  vc_log : list sentry;        (* [comment removed for export] *)
  vc_src : list gatom;         (* [comment removed for export] *)
  vc_tgt : list gatom;         (* [comment removed for export] *)
  vc_facts : list kentry       (* [comment removed for export] *)
}.

Definition vc_holds (c : vc) : Prop :=
  forall E m, know_ok segs E m (vc_kn c) -> scs_denot segs m E (vc_path c) -> log_flat E (vc_log c) ->
    gholds E m (vc_src c) ->
    gholds E (mem_denot E m (vc_log c)) (vc_tgt c) /\ know_ok segs E (mem_denot E m (vc_log c)) (vc_facts c).

(* [comment removed for export] *)
Definition covers (r c : vc) : bool :=
  if log_eqb (vc_log r) (vc_log c) then
  if subsetb sc_eqb (vc_path r) (vc_path c) then
  if subsetb gatom_eqb (vc_src r) (vc_src c) then
  if subsetb gatom_eqb (vc_tgt c) (vc_tgt r) then
  if subsetb APC.kentry_eqb (vc_facts c) (vc_facts r) then subsetb APC.kentry_eqb (vc_kn r) (vc_kn c)
  else false else false else false else false else false.

Lemma covers_ok : forall r c, covers r c = true -> vc_holds r -> vc_holds c.
Proof.
  intros r c H Hr E m HK HP HL HS. unfold covers in H.
  destruct (log_eqb (vc_log r) (vc_log c)) eqn:Hlog; [|discriminate].
  destruct (subsetb sc_eqb (vc_path r) (vc_path c)) eqn:Hpath; [|discriminate].
  destruct (subsetb gatom_eqb (vc_src r) (vc_src c)) eqn:Hsrc; [|discriminate].
  destruct (subsetb gatom_eqb (vc_tgt c) (vc_tgt r)) eqn:Htgt; [|discriminate].
  destruct (subsetb APC.kentry_eqb (vc_facts c) (vc_facts r)) eqn:Hfac; [|discriminate].
  rename H into Hkn.
  apply log_eqb_eq in Hlog. rewrite <- Hlog in HL |- *.
  destruct (Hr E m) as [T F].
  - exact (Forall_subset _ _ SLin.kentry_eqb_eq _ _ Hkn HK).
  - exact (Forall_subset _ _ sc_eqb_eq _ _ Hpath HP).
  - exact HL.
  - exact (Forall_subset _ _ gatom_eqb_eq _ _ Hsrc HS).
  - split; [exact (Forall_subset _ _ gatom_eqb_eq _ _ Htgt T) | exact (Forall_subset _ _ SLin.kentry_eqb_eq _ _ Hfac F)].
Qed.

Definition gvc_list (GV : list vc) (c : vc) : bool := SLin.lex (fun r => covers r c) GV.

Lemma gvc_list_ok : forall GV c, Forall vc_holds GV -> gvc_list GV c = true -> vc_holds c.
Proof.
  intros GV c HV H. unfold gvc_list in H. apply SLin.lex_exists in H as (r & Hin & Hc).
  exact (covers_ok r c Hc (proj1 (Forall_forall _ _) HV r Hin)).
Qed.

(* [comment removed for export] *)
Definition gvc_or (g1 g2 : vc -> bool) (c : vc) : bool := (g1 c || g2 c)%bool.

Lemma gvc_or_ok : forall (g1 g2 : vc -> bool),
  (forall c, g1 c = true -> vc_holds c) -> (forall c, g2 c = true -> vc_holds c) ->
  forall c, gvc_or g1 g2 c = true -> vc_holds c.
Proof. intros g1 g2 H1 H2 c H. unfold gvc_or in H. apply orb_prop in H as [H|H]; [exact (H1 c H) | exact (H2 c H)]. Qed.

End Sem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gwin : Type := (expr * Z * expr)%type.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart1 (kn : list kentry) (ab : expr) (ak : Z) (w : nat) (b : expr) (off : Z) (n : expr) : bool :=
  if ranges_apart_x kn ab ak (elen w) b off n then true else ranges_apart_x (SL.aff_facts kn ++ kn) ab ak (elen w) b off n.
Definition log_apart (kn : list kentry) (lg : list sentry) (W : list gwin) : bool :=
  forallb (fun s => forallb (fun w => match w with (b, off, n) =>
              ranges_apart_x kn (a_base (e_addr s)) (a_off (e_addr s)) (elen (e_width s)) b off n end) W) lg.
(* [comment removed for export] *)
Definition log_apartX (kn : list kentry) (lg : list sentry) (W : list gwin) : bool :=
  forallb (fun s => forallb (fun w => match w with (b, off, n) =>
              apart1 kn (a_base (e_addr s)) (a_off (e_addr s)) (e_width s) b off n end) W) lg.

Section Frame.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variable gfp : nat -> list expr -> list gwin.

Definition win_den (E : env) (w : gwin) : Z * Z :=
  match w with (b, off, n) => (bv_unsigned (edenot E b) + off, bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n))%Z end.

(* [comment removed for export] *)
Definition gp_frameP : Prop :=
  forall id args E (M M' : word -> option byte),
    (forall x : word, (exists w, In w (gfp id args) /\ let '(lo, hi) := win_den E w in (lo <= bv_unsigned x < hi)%Z) -> M' x = M x) ->
    GP id (map (edenot E) args) M -> GP id (map (edenot E) args) M'.

Lemma elenZ_elen8' : forall E w, (w <= 8)%nat -> elenZ E (elen w) = Z.of_nat w.
Proof. exact elenZ_elen'. Qed.

Lemma mem_denot_apart : forall E kn base lg W x,
  know_ok segs E base kn -> log_flat E lg -> log_apart kn lg W = true ->
  (exists w, In w W /\ let '(lo, hi) := win_den E w in (lo <= bv_unsigned x < hi)%Z) ->
  mem_denot E base lg x = base x.
Proof.
  intros E kn base lg W x HK. induction lg as [|[a w v] rest IH]; intros Hlf Hap Hin; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf'). cbn [log_apart forallb] in Hap. apply andb_prop in Hap as [Ha1 Ha2].
  cbn [mem_denot]. rewrite <- (IH Hlf' Ha2 Hin).
  destruct Hin as ([[b off] n] & HinW & Hx). cbn [win_den] in Hx.
  pose proof (proj1 (forallb_forall _ _) Ha1 _ HinW) as Hap1. cbn beta iota in Hap1. cbn [e_addr e_width] in Hap1.
  destruct a as [ab ak]. cbn [a_base a_off] in Hap1.
  pose proof (ranges_apart_x_sound segs E base kn ab ak (elen w) b off n HK Hap1) as R.
  rewrite elenZ_elen8' in R by exact Hw8. unfold estart in R. cbn [a_base a_off] in R. unfold elenZ in R.
  pose proof (flat_u E _ _ Hfa) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
  apply wbytes_outside.
  - rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
  - rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Lemma mem_denot_apartX : forall E kn base lg W x,
  know_ok segs E base kn -> log_flat E lg -> log_apartX kn lg W = true ->
  (exists w, In w W /\ let '(lo, hi) := win_den E w in (lo <= bv_unsigned x < hi)%Z) ->
  mem_denot E base lg x = base x.
Proof.
  intros E kn base lg W x HK. induction lg as [|[a w v] rest IH]; intros Hlf Hap Hin; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf'). cbn [log_apartX forallb] in Hap. apply andb_prop in Hap as [Ha1 Ha2].
  cbn [mem_denot]. rewrite <- (IH Hlf' Ha2 Hin).
  destruct Hin as ([[b off] n] & HinW & Hx). cbn [win_den] in Hx.
  pose proof (proj1 (forallb_forall _ _) Ha1 _ HinW) as Hap1. cbn beta iota in Hap1. cbn [e_addr e_width] in Hap1.
  destruct a as [ab ak]. cbn [a_base a_off] in Hap1.
  assert (R : ((estart E (SA ab ak) + elenZ E (elen w) <= estart E (SA b off))%Z
               \/ (estart E (SA b off) + elenZ E n <= estart E (SA ab ak))%Z)).
  { unfold apart1 in Hap1. destruct (ranges_apart_x kn ab ak (elen w) b off n) eqn:Hxa.
    - exact (ranges_apart_x_sound segs E base kn ab ak (elen w) b off n HK Hxa).
    - apply (ranges_apart_x_sound segs E base (SL.aff_facts kn ++ kn) ab ak (elen w) b off n); [|exact Hap1].
      apply Forall_app. split; [exact (SL.aff_facts_ok segs E base kn HK) | exact HK]. }
  rewrite elenZ_elen8' in R by exact Hw8. unfold estart in R. cbn [a_base a_off] in R. unfold elenZ in R.
  pose proof (flat_u E _ _ Hfa) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
  apply wbytes_outside.
  - rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
  - rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Definition keep_ok (kn : list kentry) (lg : list sentry) (src : list gatom) (g : gatom) : bool :=
  if SLin.lex (gatom_eqb g) src then log_apartX kn lg (gfp (g_id g) (g_args g)) else false.

Lemma keep_ok_sound : forall E m kn lg src g, gp_frameP ->
  know_ok segs E m kn -> log_flat E lg -> gholds GP E m src -> keep_ok kn lg src g = true ->
  GP (g_id g) (map (edenot E) (g_args g)) (mem_denot E m lg).
Proof.
  intros E m kn lg src g HF HK HL HS H. unfold keep_ok in H.
  destruct (SLin.lex (gatom_eqb g) src) eqn:H1; [|discriminate]. rename H into H2.
  apply SLin.lex_exists in H1 as (g' & Hin & Heq). apply gatom_eqb_eq in Heq. subst g'.
  pose proof (proj1 (Forall_forall _ _) HS g Hin) as Hg.
  apply (HF (g_id g) (g_args g) E m); [|exact Hg].
  intros x Hx. exact (mem_denot_apartX E kn m lg _ x HK HL H2 Hx).
Qed.

End Frame.
End SG.
