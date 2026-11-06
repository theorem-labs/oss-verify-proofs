(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac pa_lia_prev := Zify.zify; xlia zchecker.
#[local] Ltac lia ::= first [ solve [ pa_tiers ltac:(pa_lia_prev) ] | pa_lia_prev ].
#[local] Notation W8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept15_kept_ok : forall R R',
  (forall x : bv 5, In x kept15 -> getr R' x = getr R x) -> kept_ok R R'.
Proof.
  intros R R' H. apply kept_ok_of_callee_saved. intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
  repeat (destruct Hr as [<-|Hr]; [apply H; cbv [kept15 In]; repeat first [left; apply bv_eq; reflexivity | right] |]).
  destruct Hr.
Qed.


(* [comment removed for export] *)
Lemma word_to_le_bytes_ext : forall (w : nat) v E,
  (w <= 8)%nat -> word_to_le_bytes w (edenot E (EExt false 0 w v)) = word_to_le_bytes w (edenot E v).
Proof.
  intros w v E Hw. cbn [edenot]. unfold ext_val, ext_Z, word_to_le_bytes.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  pose proof (u64_range (edenot E v)) as Hr.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E v)) (2 ^ (8 * Z.of_nat w)) ltac:(apply Z.pow_pos_nonneg; lia)) as Hm.
  assert (Hle : 2 ^ (8 * Z.of_nat w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite u64_lit by lia. apply Z_to_le_bytes_mod.
Qed.

Lemma eaddz_u : forall E a z, bv_unsigned (edenot E (eaddz a z)) = (bv_unsigned (edenot E a) + z) mod 2 ^ 64.
Proof.
  intros E a z. unfold eaddz. rewrite mkAlu_denot, alu_add. unfold v_add. cbn [edenot].
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_r. reflexivity.
Qed.
Lemma eadd_u : forall E a b, bv_unsigned (edenot E (eadd a b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof.
  intros E a b. unfold eadd. rewrite mkAlu_denot, alu_add. unfold v_add. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma escale_u : forall E c a, bv_unsigned (edenot E (escale c a)) = (c * bv_unsigned (edenot E a)) mod 2 ^ 64.
Proof.
  intros E c a. unfold escale. rewrite mkMd_denot, m_mul. unfold v_mul. cbn [edenot].
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_mul_idemp_l. reflexivity.
Qed.
Lemma esub_u : forall E a b, bv_unsigned (edenot E (esub a b)) = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof.
  intros E a b. unfold esub. rewrite mkAlu_denot, alu_sub. unfold v_sub. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma some_inj : forall {A} (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. injection H as H. exact H. Qed.

Lemma mark_dead_false : forall cs, mark_dead false cs = cs.
Proof. reflexivity. Qed.

Lemma store_ok1_wview : forall segs m (x : word), store_ok segs m x 1 = true -> wview segs m x <> None.
Proof.
  intros segs m x H. pose proof (u64_range x).
  eapply (store_ok_all segs m 1 x); [cbn; lia | exact H | cbn; lia].
Qed.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Hypothesis AINV_mono : forall Lc B C B' C' M mdl,
  AINV Lc B C M mdl -> B <= B' -> C <= C' -> AINV Lc B' C' M mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
Variable bcap ccap : Z.
(* [comment removed for export] *)
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
Hypothesis SEGS_wr : segs_wr_ok SEGS.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation frame_kept := (GlzSpecsStr.GlzContracts.frame_kept SWIN PERMc SPTOPc G).
#[local] Notation node2_stmt := (GlzSpecsStr.GlzContracts.node2_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

(* [comment removed for export] *)
Lemma kentails_word_sound : forall E M k b o (w : nat) v,
  know_ok SEGS E M k -> (1 <= w <= 8)%nat -> kentails_word SEGS k b o w v = true ->
  flat E (SA b o) (Z.of_nat w)
  /\ rdn SEGS M (Z_to_bv 64 (estart E (SA b o))) w = Some (word_to_le_bytes w (edenot E v)).
Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
  intros E M k b o w v HK Hw H. unfold kentails_word in H. apply orb_prop in H as [H|H].
  - apply existsb_exists in H as [K [HKin Heq]]. apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & Hfl & Hrd).
    split; [exact Hfl|]. rewrite <- adenot_SA. exact Hrd.
  - apply andb_prop in H as [H Hlk]. apply andb_prop in H as [H Hflx]. apply andb_prop in H as [Hw1 Hw8].
    pose proof (flat_x_sound SEGS E M k b o (ELit (Z.of_nat w)) HK Hflx) as (F1 & F2 & F3).
    unfold elenZ in F2, F3. cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
    assert (Hfl : flat E (SA b o) (Z.of_nat w)) by (unfold flat; lia).
    split; [exact Hfl|].
    destruct (know_lookup SEGS k b o w false [] []) as [v' scs hs| | ] eqn:HL; try discriminate.
    destruct scs as [|? ?]; [|discriminate].
    destruct (lookup_piece SEGS E M k b o w v' hs HK ltac:(lia) HL Hfl) as (bs & Hrd & Hlen & Hbs).
    rewrite Hrd. f_equal. rewrite <- Hbs.
    apply orb_prop in Hlk as [Heq|Heq]; apply expr_eqb_eq in Heq; subst v'; [reflexivity|].
    apply word_to_le_bytes_ext. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inr (lo n z : Z) : bool := (Z.leb lo z && Z.ltb z (lo + n))%bool.
Lemma inr_true : forall lo n z, inr lo n z = true <-> lo <= z < lo + n.
Proof using G_img_hull G_ro_img G. clear - G_img_hull G_ro_img G. intros. unfold inr. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma inr_false : forall lo n z, inr lo n z = false <-> ~ (lo <= z < lo + n).
Proof using G_img_hull G_ro_img G. clear - G_img_hull G_ro_img G. intros. rewrite <- inr_true. destruct (inr lo n z); split; intros; congruence. Qed.

Definition old_lo (E : env) (old : option (expr * expr)) : Z :=
  match old with Some (od, _) => let '(odb, odk) := split_lit od in estart E (SA odb odk) | None => 0 end.
Definition old_n (E : env) (old : option (expr * expr)) : Z :=
  match old with Some (_, olen) => elenZ E olen | None => 0 end.

Lemma str_keep_sound : forall E M M' k live perm fl top bud sp spb spk ob ok old v,
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc ->
  split_lit sp = (spb, spk) -> 0 <= bv_unsigned (edenot E spb) + spk < 2 ^ 64 ->
  GPS.floor_sem E fl top bud ->                                                       (* [comment removed for export] *)
  let o := estart E (SA ob ok) in
  (forall a : word, frame_kept (blocks_den E live) (bv_unsigned (edenot E sp)) a ->
                    ~ (o <= bv_unsigned a < o + 24) -> ~ (old_lo E old <= bv_unsigned a < old_lo E old + old_n E old) ->
                    M' a = M a) ->
  (forall a : word, bv_unsigned (edenot E sp) - MSTK <= bv_unsigned a < bv_unsigned (edenot E sp) ->
                    M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
  (forall a : word, bv_unsigned (edenot E sp) - MSTK <= bv_unsigned a < bv_unsigned (edenot E sp) ->
                    ~ (o <= bv_unsigned a < o + 24) /\ ~ (old_lo E old <= bv_unsigned a < old_lo E old + old_n E old)) ->
  know_ok SEGS E M' (str_keep G k (live ++ perm) fl top bud sp ob ok old v).
Proof using G_img_hull G_ro_img. clear - G_img_hull G_ro_img.
  intros E M M' k live perm fl top bud sp spb spk ob ok old v HK Hflat Hperm Htop Hsp Hspr Hceil o Hfr Hscr Hapart.
  set (ol := old_lo E old) in *. set (on := old_n E old) in *.
  set (Mm := fun a : word => if (inr o 24 (bv_unsigned a) || inr ol on (bv_unsigned a))%bool then M a else M' a).
  set (Mo := fun a : word => if inr ol on (bv_unsigned a) then M a else M' a).
  (* [comment removed for export] *)
  assert (S1 : know_ok SEGS E Mm (keep_owned G k (live ++ perm) fl top bud sp v)).
  { unfold know_ok. apply Forall_forall. intros K HKin.
    eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G E M Mm k live perm fl top bud sp spb spk v K HK Hflat Hperm Htop Hsp Hspr Hceil); [| |exact HKin].
    - intros a Hka. unfold Mm. destruct (inr o 24 (bv_unsigned a) || inr ol on (bv_unsigned a))%bool eqn:Hc; [reflexivity|].
      apply Bool.orb_false_iff in Hc as [Hc1 Hc2]. apply inr_false in Hc1. apply inr_false in Hc2. exact (Hfr a Hka Hc1 Hc2).
    - intros a Ha. destruct (Hapart a Ha) as [N1 N2].
      assert (E1 : Mm a = M' a).
      { unfold Mm. destruct (inr o 24 (bv_unsigned a)) eqn:H1; [apply inr_true in H1; tauto|].
        destruct (inr ol on (bv_unsigned a)) eqn:H2; [apply inr_true in H2; tauto|]. reflexivity. }
      destruct (Hscr a Ha) as [D S]. split; [rewrite E1; exact D|].
      cbn [RiscvSemantics.store_ok] in S |- *. unfold wview in S |- *. rewrite E1. exact S. }
  (* [comment removed for export] *)
  assert (S2 : know_ok SEGS E Mo (kn_cutout (keep_owned G k (live ++ perm) fl top bud sp v) ob ok (ELit 24))).
  { eapply know_ok_cutout; [exact S1|]. intros x Hx. unfold Mo, Mm.
    rewrite elenZ_lit in Hx by lia. fold o in Hx.
    destruct (inr o 24 (bv_unsigned x)) eqn:H1; [apply inr_true in H1; lia|]. reflexivity. }
  rewrite str_keep_eq. unfold str_keep_ref. apply know_ok_filter.
  destruct old as [[od olen]|].
  - (* [comment removed for export] *)
    destruct (split_lit od) as [odb odk] eqn:Hos.
    eapply know_ok_cutout; [exact S2|]. intros x Hx. unfold Mo.
    assert (Hol : ol = estart E (SA odb odk)) by (unfold ol, old_lo; rewrite Hos; reflexivity).
    assert (Hon : on = elenZ E olen) by reflexivity.
    destruct (inr ol on (bv_unsigned x)) eqn:H1; [apply inr_true in H1; rewrite Hol, Hon in H1; lia|]. reflexivity.
  - (* [comment removed for export] *)
    assert (EQ : forall x, Mo x = M' x).
    { intros x. unfold Mo. unfold on, old_n. unfold inr. 
      destruct (Z.leb ol (bv_unsigned x) && Z.ltb (bv_unsigned x) (ol + 0))%bool eqn:H1; [|reflexivity].
      apply Bool.andb_true_iff in H1 as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia. }
    unfold know_ok in S2 |- *. apply Forall_forall. intros K HKin.
    eapply kentry_ok_footprint; [exact (proj1 (Forall_forall _ _) S2 K HKin)|]. intros x _. symmetry. apply EQ.
Qed.

Lemma str_keep_vars : forall k live fl top bud sp ob ok old v, AP.kn_vars_lt v (str_keep G k live fl top bud sp ob ok old v) = true.
Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
  intros. rewrite str_keep_eq. unfold str_keep_ref. rewrite kn_vars_lt_forallb. apply forallb_forall. intros K HK.
  apply filter_In in HK as [_ HK]. apply andb_prop in HK as [HK _]. exact HK.
Qed.

Lemma defined_store_ok : forall M (a : word),
  g_img_hi G <= bv_unsigned a -> M a <> None -> RiscvSemantics.store_ok SEGS M a 1 = true.
Proof using G_img_ceil SEGS_out RC. clear - G_img_ceil SEGS_out RC.
  intros M a Ha Hd. pose proof G_img_ceil. cbn [RiscvSemantics.store_ok]. unfold wview. rewrite (SEGS_out a ltac:(lia)).
  destruct (M a) as [b|] eqn:E; [reflexivity | exfalso; exact (Hd eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma galloc_facts : forall n cap, 0 <= cap ->
  n <= galloc n cap - 1 /\ 2 * cap <= galloc n cap - 1 /\ galloc n cap <= Z.max n (2 * cap) + 8 /\ galloc n cap mod 8 = 0.
Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
  intros n cap Hc. unfold galloc. set (g := Z.max n (2 * cap)) in *.
  pose proof (lor7_bounds g ltac:(lia)) as Lb.
  pose proof (Z.add_lor_land g 7) as E. pose proof (Z.land_ones g 3) as L3. change (Z.ones 3) with 7 in L3.
  change (2 ^ 3) with 8 in L3. rewrite L3 in E by lia.
  pose proof (Z.mod_pos_bound g 8 ltac:(lia)). pose proof (Z.div_mod g 8 ltac:(lia)).
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (Z.lor g 7 + 1) with ((g / 8 + 1) * 8) by lia. apply Z_mod_mult.
Qed.


Lemma long_post_sound : forall cs E fx fx' R R' M M' mdl mdl' (ret : Z) ob ok nlo' nhi Alo' Ahi' oldA bnd live' kept spb spk tb tk
                              (p : word) (g o n : Z),
  cs_ok E cs fx R M mdl -> fresh_ok nx0 cs = true ->
  estart E (SA ob ok) = o -> edenot E (reg cs 10) = Z_to_bv 64 o -> AP.expr_vars_lt (nxt cs) ob = true ->
  bv_unsigned (edenot E (reg cs 11)) = n -> AP.expr_vars_lt (nxt cs) (reg cs 11) = true ->
  0 <= o -> o + 24 <= 2 ^ 64 -> 0 <= n ->
  1 <= g -> g mod 8 = 0 -> 8 * Alo' <= g -> g <= 8 * Ahi' -> n + 1 <= g -> nlo' <= n -> 0 <= Alo' ->
  blk_ok G (bv_unsigned p) g -> bv_unsigned p mod 16 = 0 ->
  (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + g -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
  M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
  rdn SEGS M' (Z_to_bv 64 o) 8 = Some (W8 (Z_to_bv 64 (g + 1))) ->
  rdn SEGS M' (Z_to_bv 64 (o + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
  rdn SEGS M' (Z_to_bv 64 (o + 16)) 8 = Some (W8 p) ->
  (forall a : word, o <= bv_unsigned a < o + 24 -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
  (forall b m, In (b, m) (blocks_den E live') -> bv_unsigned p + g <= b \/ b + m <= bv_unsigned p) ->
  (forall lo hi, In (lo, hi) PERMc -> lo < hi -> bv_unsigned p + g <= lo \/ hi <= bv_unsigned p) ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (a_vis cs ++ a_ghost cs) = true ->
  (forall x, In x live' -> In x (a_vis cs)) ->
  (* [comment removed for export] *)
  split_lit (reg cs 2) = (spb, spk) -> uE E (reg cs 2) = uE E spb + spk -> CEIL_run + MSTK <= uE E (reg cs 2) -> uE E (reg cs 2) <= SPTOPc ->
  split_lit (a_brk cs) = (tb, tk) -> top_ok (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) = true ->
  (forall E', env_agree (nxt cs) E E' -> edenot E' (EVar (nxt cs)) = p -> edenot E' (EVar (S (nxt cs))) = Z_to_bv 64 (g / 8) ->
     know_ok SEGS E' M' (bnd ++ match oldA with
             | Some A => [KRange (esub (reg cs 11) (escale 8 A)) 0 nhi;
                          KRange (esub (eaddz (eadd (reg cs 11) (escale 16 A)) 6) (escale 8 (EVar (S (nxt cs))))) 0 (16 * (SMAXR / 8) + 6);
                          KRange (esub (eaddz (escale 2 (reg cs 11)) 8) (escale 8 (EVar (S (nxt cs))))) 0 (2 * nhi + 8)]
             | None => [KRange (reg cs 11) 23 nhi; KRange (esub (eaddz (reg cs 11) 52) (escale 8 (EVar (S (nxt cs))))) 0 52]
             end)) ->
  know_ok SEGS E M' kept -> AP.kn_vars_lt (nxt cs) kept = true ->
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> getr R' (Z_to_bv 5 10) = Z_to_bv 64 o ->
  FXOK fx' ->
  AINV ((bv_unsigned p, g) :: blocks_den E live') (GPS.bcost E live' + mcost g) (GPS.bcount live' + MCNT) M' mdl' ->
  m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
  exists E', env_agree nx0 E E' /\ env_agree (nxt cs) E E' /\ m_fs mdl' = m_fs mdl /\
    cs_ok E' (str_long_post2 G cs ret ob ok (reg cs 11) nlo' nhi Alo' Ahi' oldA bnd live' kept) fx' R' M' mdl'.
Proof using G_img_hull G_img_ceil G_ro_img UINV_agree. clear - G_img_hull G_img_ceil G_ro_img UINV_agree.
  intros cs E fx fx' R R' M M' mdl mdl' ret ob ok nlo' nhi Alo' Ahi' oldA bnd live' kept spb spk tb tk p g o n
         HC Hfresh Ho Hobjw Hobv Hn Hnv Ho0 Ho24 Hn0 Hg1 Hg8 HgAlo HgAhi Hgn Hnlo HAlo0 Hpblk Hpal Hblk NUL RD0 RD1 RD2 Hobj
         Hdisj Hperm Hflat Hsub Hsp Hspv Hsplo Hsptop Htop Htok REL HKept Hkv Hkept Ha0 HFX' HAINV' Hh' Hlz' Hmat' Hfs' Hfds'.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs) in *.
  pose proof (u64_range p) as Hpr.
  pose proof Hpblk as (Hplo & Hphi & Himg). pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL.
  unfold GlzConst.PTRLO in Hplo.
  assert (Hg64 : bv_unsigned p + g < 2 ^ 64) by lia.
  set (aw := Z_to_bv 64 (g / 8)).
  set (E1 := ext1 E v p). set (E2 := ext1 E1 (S v) aw). set (E' := ext_call E2 (S (S v)) R').
  assert (Hag1 : env_agree v E E1) by apply ext1_agree.
  assert (Hag2 : env_agree (S v) E1 E2) by apply ext1_agree.
  assert (Hag3 : env_agree (S (S v)) E2 E') by apply ext_call_agree.
  assert (Hag12 : env_agree v E E2) by (eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]).
  assert (Hag : env_agree v E E') by (eapply env_agree_trans; [exact Hag12 | eapply env_agree_le; [exact Hag3 | lia]]).
  assert (Hpv : edenot E' (EVar v) = p).
  { cbn [edenot]. rewrite <- (proj1 Hag3 v ltac:(lia)). rewrite <- (proj1 Hag2 v ltac:(lia)). unfold E1. apply ext1_at. }
  assert (Hav : edenot E' (EVar (S v)) = aw).
  { cbn [edenot]. rewrite <- (proj1 Hag3 (S v) ltac:(lia)). unfold E2. apply ext1_at. }
  exists E'. split; [eapply env_agree_le; [exact Hag | exact Fle]|]. split; [exact Hag|]. split; [exact Hfs'|].
  (* [comment removed for export] *)
  assert (Hne11 : edenot E' (reg cs 11) = edenot E (reg cs 11)) by (symmetry; eapply edenot_agree'; [exact Hag | exact Hnv]).
  assert (Hne10 : edenot E' ob = edenot E ob) by (symmetry; eapply edenot_agree'; [exact Hag | exact Hobv]).
  assert (Ho' : estart E' (SA ob ok) = o) by (rewrite <- Ho, !estart_SA, Hne10; reflexivity).
  pose proof (Z.div_mod g 8 ltac:(lia)) as Hgdm.
  assert (Hawu : bv_unsigned aw = g / 8) by (unfold aw; apply u64_lit; lia).
  assert (Hlen : bv_unsigned (edenot E' (escale 8 (EVar (S v)))) = g).
  { rewrite escale_u, Hav, Hawu. rewrite Z.mod_small by lia. lia. }
  assert (HKE' : know_ok SEGS E' M (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
  (* [comment removed for export] *)
  destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
  destruct (floor_win_sound SEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo Hfwl].
  assert (Hfwb : edenot E' fwb = edenot E fwb).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. exact (floor_win_vars v (a_maps cs) (a_brk cs) (a_ylo cs) fwb fwo _ Fmaps Fbrk Hfw). }
  assert (Hspb : edenot E' spb = edenot E spb).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. eapply GCL.split_lit_vars; [exact Hsp|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hceil : CEIL_run <= sp_lin E (reg cs 2)) by (unfold sp_lin; rewrite Hsp; unfold MSTK in *; lia).
  assert (Hlv : pairs_vars_lt v live' = true).
  { unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
    exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (Hsub x Hx)). }
  assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (live' ++ a_ghost cs) = true).
  { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hflat x).
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hsub x Hx) | right; exact Hx]. }
  unfold str_long_post2. unfold block_rng, block_sep. rewrite Hfw. subst fwl. cbv zeta. fold v.
  constructor; cbn [a_ss s_regs s_log s_know kn a_vis a_totsz a_eager a_ghost a_brk a_ylo a_maps a_fd a_tidset].
  - (* [comment removed for export] *)
    change (regs_ok E' (sr_upd (sr_fresh (s_regs (a_ss cs)) caller_saved (S (S v))) 10 (eaddz ob ok)) R').
    rewrite <- (ridx_lit 10) by lia. apply regs_ok_pin.
    + apply (regs_after_call E2 (s_regs (a_ss cs)) R R' (S (S v)) None); [| | apply kept_ok_of_callee_saved; exact Hkept | exact I].
      * eapply regs_ok_agree'; [exact Hag12 | exact Fsr | exact HR].
      * eapply sr_vars_lt_mono; [exact Fsr | lia].
    + change (Z.of_nat 10) with 10. rewrite Ha0. apply bv_eq. rewrite eaddz_u, Hne10, u64_lit by lia.
      rewrite <- Ho, estart_SA. rewrite Z.mod_small; [reflexivity|]. rewrite <- estart_SA, Ho. lia.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (Hp0 : estart E' (SA (EVar v) 0) = bv_unsigned p) by (rewrite estart_SA, Hpv; lia).
    assert (Hel : elenZ E' (escale 8 (EVar (S v))) = g) by (unfold elenZ; exact Hlen).
    assert (He8 : estart E' (SA ob (ok + 8)) = o + 8) by (rewrite estart_SA, Hne10; rewrite <- Ho, estart_SA; lia).
    assert (He16 : estart E' (SA ob (ok + 16)) = o + 16) by (rewrite estart_SA, Hne10; rewrite <- Ho, estart_SA; lia).
    pose proof (REL E' Hag Hpv ltac:(rewrite Hav; reflexivity)) as RELok. unfold know_ok in RELok.
    apply (proj1 (Forall_app _ _ _)) in RELok as [RB RM].
    unfold know_ok. rewrite <- !app_assoc. repeat (apply Forall_app; split).
    + (* [comment removed for export] *)
      repeat apply Forall_cons; [| | apply Forall_nil]; cbn [kentry_ok].
      * rewrite Hav, Hawu. lia.
      * rewrite esub_u, Hlen, Hne11, Hn. rewrite Z.mod_small by lia. lia.
    + (* [comment removed for export] *)
      repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok].
      * rewrite Hpv. unfold GlzConst.PTRLO, GlzConst.PTRHI. lia.
      * rewrite eadd_u, Hpv, Hlen. rewrite Z.mod_small by lia. unfold GlzConst.PTRLO, GlzConst.PTRHI. lia.
      * rewrite Hpv. lia.
    + (* [comment removed for export] *)
      repeat apply Forall_cons; [| | | | | | | | apply Forall_nil]; cbn [kentry_ok].
      * rewrite Hp0, Hel. split; [unfold flat; rewrite Hp0; lia|].
        intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
        intros x Hx. rewrite u64_lit in Hx by lia. apply store_ok1_wview. apply (proj2 (Hblk x ltac:(lia))).
      * rewrite Hp0, Hel. split; [unfold flat; rewrite Hp0; lia|].
        intros i Hi. apply (proj1 (Hblk (Z_to_bv 64 (bv_unsigned p + i)) ltac:(rewrite u64_lit by lia; lia))).
      * assert (Hen : estart E' (SA (eadd (EVar v) (reg cs 11)) 0) = bv_unsigned p + n).
        { rewrite estart_SA, eadd_u, Hpv, Hne11, Hn. rewrite Z.mod_small by lia. lia. }
        split; [lia|]. split; [unfold flat; rewrite Hen; cbn; lia|].
        rewrite adenot_SA, Hen, (rdn1_overlay _ _ _ _ NUL). reflexivity.
      * split; [lia|]. split; [unfold flat; rewrite Ho'; cbn; lia|].
        rewrite adenot_SA, Ho', RD0. do 2 f_equal. apply bv_eq. rewrite eaddz_u, Hlen, !u64_lit by lia.
        rewrite Z.mod_small by lia. reflexivity.
      * split; [lia|]. split; [unfold flat; rewrite He8; cbn; lia|].
        rewrite adenot_SA, He8, RD1. do 2 f_equal. apply bv_eq. rewrite Hne11, u64_lit by (pose proof (u64_range (edenot E (reg cs 11))); lia). symmetry. exact Hn.
      * split; [lia|]. split; [unfold flat; rewrite He16; cbn; lia|].
        rewrite adenot_SA, He16, RD2, Hpv. reflexivity.
      * rewrite Ho', (elenZ_lit E') by lia. split; [unfold flat; rewrite Ho'; lia|].
        intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
        intros x Hx. rewrite u64_lit in Hx by lia. apply store_ok1_wview. apply (proj2 (Hobj x ltac:(lia))).
      * rewrite Ho', (elenZ_lit E') by lia. split; [unfold flat; rewrite Ho'; lia|].
        intros i Hi. apply (proj1 (Hobj (Z_to_bv 64 (o + i)) ltac:(rewrite u64_lit by lia; lia))).
    + (* [comment removed for export] *) exact RB.
    + (* [comment removed for export] *) exact RM.
    + (* [comment removed for export] *)
      repeat apply Forall_cons; [| | apply Forall_nil]; cbn [kentry_ok]; rewrite Hp0, Hel, estart_SA.
      * rewrite Hfwb. left. unfold uE in *. lia.
      * cbn [edenot]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by lia. lia.
    + (* [comment removed for export] *)
      set (gh := List.filter (fun g0 : expr * expr => match xlo (kn cs) (snd g0) with Some l => Z.leb 1 l | None => false end) (a_ghost cs)).
      assert (Hghsub : forall x, In x gh -> In x (a_ghost cs)) by (intros x Hx; unfold gh in Hx; apply filter_In in Hx as [Hx _]; exact Hx).
      assert (Hlgv : pairs_vars_lt v (live' ++ gh) = true).
      { unfold pairs_vars_lt in Hlv |- *. rewrite forallb_app, Hlv. cbn [andb]. apply forallb_forall. intros x Hx.
        exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_r _ _ _ Fallow) x (Hghsub x Hx)). }
      eapply (disj_facts_ok SEGS E' M' M (kn cs) (EVar v) (escale 8 (EVar (S v))) (live' ++ gh) p HKE').
      * apply forallb_forall. intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
        -- exact (proj1 (forallb_forall _ _) Hflat x ltac:(apply in_app_iff; left; exact (Hsub x Hx))).
        -- exact (proj1 (forallb_forall _ _) Hflat x ltac:(apply in_app_iff; right; exact (Hghsub x Hx))).
      * exact Hpv.
      * rewrite (blocks_den_agree v E E' (live' ++ gh) Hag Hlgv). unfold uE. rewrite Hlen.
        intros b m Hin. unfold blocks_den in Hin. rewrite map_app in Hin. apply in_app_iff in Hin as [Hin|Hin].
        -- apply Hdisj. exact Hin.
        -- apply in_map_iff in Hin as [[gb glen] [Hbm Hing]]. cbn [fst snd] in Hbm. injection Hbm as <- <-.
           unfold gh in Hing. apply filter_In in Hing as [Hing Hnz]. cbn [snd] in Hnz.
           destruct (xlo (kn cs) glen) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hnz.
           pose proof (xlo_sound SEGS E M (kn cs) glen l HK Hxl) as Hl.
           apply (Hperm (uE E gb) (uE E gb + uE E glen)).
           ++ rewrite <- (co_perm HC). unfold wins_den. apply in_map_iff. exists (gb, glen). split; [reflexivity | exact Hing].
           ++ unfold uE in *. lia.
    + (* [comment removed for export] *)
      eapply (kdisj_of_facts_ok SEGS E' M' M (kn cs)); [exact HKE' | exact Hpv | | constructor].
      intros K b off len HKin HKR Hl.
      assert (HKok : kentry_ok SEGS E M K).
      { rewrite keep_owned_eq in HKin. unfold keep_owned_ref in HKin. rewrite Hsp in HKin. apply in_app_iff in HKin as [HKin'|HKin']; apply filter_In in HKin' as [HKin' _].
        - exact (proj1 (Forall_forall _ _) HK K HKin').
        - refine (proj1 (Forall_forall _ _) _ K HKin'). eapply know_ok_cutout; [exact HK|]. intros; reflexivity. }
      pose proof (kentry_range_foot SEGS E M K b off len HKok HKR) as HF.
      assert (HKv : kentry_vars_lt v K = true).
      { pose proof (keep_owned_vars G (kn cs) (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) as KV.
        rewrite kn_vars_lt_forallb in KV. exact (proj1 (forallb_forall _ _) KV K HKin). }
      assert (Hbe : uE E' b = uE E b).
      { unfold uE. f_equal. symmetry. eapply edenot_agree'; [exact Hag|].
        destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
          cbn [kentry_vars_lt saddr_vars_lt a_base] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [exact HKv | assumption]. }
      assert (Hle : uE E' len = uE E len).
      { unfold uE. f_equal. symmetry. eapply edenot_agree'; [exact Hag|].
        destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
          cbn [kentry_vars_lt saddr_vars_lt a_base expr_vars_lt] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [reflexivity | exact HKv | assumption]. }
      rewrite Hbe, Hle in *. unfold uE at 1. rewrite Hlen.
      destruct (Z_lt_ge_dec (bv_unsigned p + g) (uE E b + off + 1)) as [|Hge1]; [left; lia|].
      destruct (Z_lt_ge_dec (uE E b + off + uE E len) (bv_unsigned p + 1)) as [|Hge2]; [right; lia|].
      exfalso. set (z := Z.max (bv_unsigned p) (uE E b + off)).
      assert (Hz1 : bv_unsigned p <= z < bv_unsigned p + g) by (unfold z; unfold uE in *; lia).
      assert (Hz2 : uE E b + off <= z < uE E b + off + uE E len) by (unfold z; unfold uE in *; lia).
      assert (Hsp1 : CEIL_run <= uE E (reg cs 2)) by (unfold MSTK in *; lia).
      refine (block_not_kept_loc PERMc SPTOPc G (blocks_den E live') (bv_unsigned p) g (uE E (reg cs 2)) z Hpblk (proj1 G_ro_img) Hdisj Hperm Hsp1 Hsptop Hz1 _).
      eapply (keep_owned_loc SEGS PERMc SPTOPc G E M (kn cs) live' (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K z
                HK Hflat' (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin).
      unfold in_kfoot. rewrite HF, estart_SA. unfold uE in *. lia.
    + (* [comment removed for export] *)
      eapply know_ok_agree'; [exact Hag | exact Hkv | exact HKept].
  - exact Hh'.
  - exact Hlz'.
  - rewrite Hfs'. exact (co_fs HC).
  - rewrite Hfds'. exact (co_fds HC).
  - (* [comment removed for export] *)
    cbn [blocks_den map fst snd GPS.bcost GPS.bcount length].
    fold (blocks_den E' live'). fold (GPS.bcost E' live').
    rewrite (blocks_den_agree v E E' live' Hag Hlv), (bcost_agree v E E' live' Hag Hlv).
    unfold uE. rewrite Hpv, Hlen.
    replace (g + GPS.MBLK + GPS.bcost E live') with (GPS.bcost E live' + mcost g) by (unfold mcost, GlzIface.MBLK, GPS.MBLK; lia).
    replace (GPS.bcount ((EVar v, escale 8 (EVar (S v))) :: live')) with (GPS.bcount live' + MCNT) by (unfold GPS.bcount, MCNT; cbn [length]; lia).
    exact HAINV'.
  - eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
  - exact HFX'.
  - rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
  - rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
  - exact Hmat'.
  - eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

Theorem node_str_resize2_sound :
  resize_specs SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap (g_str_resize G) ->
  forall args, node2_stmt (node_str_resize2 SEGS nx0 G bcap ccap args).
Proof using SEGS_wr G_img_hull G_img_ceil G_ro_img SEGS_out RZ_msteps UINV_agree AINV_mono AINV_frame. clear - SEGS_wr G_img_hull G_img_ceil G_ro_img SEGS_out RZ_msteps UINV_agree AINV_mono AINV_frame.
  intros [KS KL GS GL] args cs csa csb E fx R M model T HC Hn HT0 Hk1 Hk2.
  rewrite node_str_resize2_eq in Hn. unfold node_str_resize2_ref in Hn.
  destruct (call_ok nx0 G (g_str_resize G) cs) as [ret|] eqn:Hco; [|discriminate].
  pose proof (call_ok_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV G (g_str_resize G) cs ret E fx R M model HC Hco) as CO.
  (* [comment removed for export] *)
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 10)) as [ob ok] eqn:Hob.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hstk & Hflat).
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  apply andb_prop in Hc as [Hc Hcc]. apply andb_prop in Hc as [Hc Hnv]. apply andb_prop in Hc as [Hc Hosc].
  apply andb_prop in Hc as [Hc Hosp]. apply andb_prop in Hc as [Hoo Hokw].
  destruct (cost_hi (kn cs) (a_vis cs)) as [ch|] eqn:Hch; [|discriminate].
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hnr; [|discriminate] end. cbn [negb] in Hn.
  apply andb_prop in Hnr as [Hn0 HnS]. apply Z.leb_le in Hn0. apply Z.leb_le in HnS. apply Z.leb_le in Hcc.
  (* [comment removed for export] *)
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (spw := edenot E (reg cs 2)) in *.
  set (objw := edenot E (reg cs 10)).
  set (o := estart E (SA ob ok)).
  pose proof (split_lit_denot E (reg cs 10) ob ok Hob) as Hobd.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11.
  pose proof (reg_sound E cs R 12 HR ltac:(lia)) as R12.
  change (Z.of_nat 10) with 10 in R10. change (Z.of_nat 11) with 11 in R11. change (Z.of_nat 12) with 12 in R12.
  set (n := bv_unsigned (edenot E (reg cs 11))) in *.
  pose proof (xlo_sound SEGS E M (kn cs) (reg cs 11) nlo HK Hnlo) as Nlo.
  pose proof (xhi_sound SEGS E M (kn cs) (reg cs 11) nhi HK Hnhi) as Nhi.
  unfold str_obj_ok in Hoo. apply andb_prop in Hoo as [Hoown Hobfl].
  pose proof (bflat_x_sound SEGS E M (kn cs) ob ok (ELit 24) HK Hobfl) as (Of1 & Of2 & Of3).
  cbn [edenot] in Of2. rewrite u64_lit in Of2 by lia.
  assert (Hou : bv_unsigned objw = o).
  { unfold objw, o. rewrite Hobd, estart_SA. apply u64_lit. rewrite estart_SA in Of1, Of3. lia. }
  fold o in Of1, Of2, Of3.
  assert (Hobjw : objw = Z_to_bv 64 o) by (apply bv_eq; rewrite Hou, u64_lit by lia; reflexivity).
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) ob ok (ELit 24) HK HK Hokw) as (OW & _ & _).
  rewrite (elenZ_lit E) in OW by lia. fold o in OW.
  assert (STO : store_ok SEGS M objw 24 = true) by (rewrite Hobjw; apply (OW 24%nat); cbn; lia).
  pose proof (lin_ge0_sound SEGS E M (kn cs) [(ob, ok)] [(reg cs 2, 0)] HK Hosp) as Hosp'. cbn [xt_den] in Hosp'.
  fold spw in Hosp'. rewrite <- estart_SA in Hosp'. fold o in Hosp'.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) ob ok (ELit 24) spb (spk - MSTK) (ELit MSTK) HK Hosc) as Hosc'.
  rewrite !estart_SA in Hosc'. rewrite !(elenZ_lit E) in Hosc' by (unfold MSTK; lia). rewrite <- (estart_SA E ob ok) in Hosc'. fold o in Hosc'.
  pose proof (split_lit_denot E (reg cs 2) spb spk Hsp) as Hspd. fold spw in Hspd.
  unfold uE in Hspv, Hal, Hsplo, Hsptop, Hstk. fold spw in Hspv, Hal, Hsplo, Hsptop, Hstk.
  assert (Hoimg : g_img_hi G <= o) by (unfold MSTK in *; lia).
  assert (Hceil : CEIL_run <= sp_lin E (reg cs 2)) by (unfold sp_lin; rewrite Hsp; unfold uE, MSTK in *; lia).
  pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL.
  assert (ODEF : forall a : word, o <= bv_unsigned a < o + 24 -> M a <> None).
  { intros a Ha. eapply (store_ok_defined SEGS G SEGS_out); [lia|].
    eapply (store_ok_bytes SEGS M objw 24); [rewrite Hou; cbn; lia | exact STO | rewrite Hou; cbn; lia]. }
  assert (OST1 : forall a : word, o <= bv_unsigned a < o + 24 -> store_ok SEGS M a 1 = true).
  { intros a Ha. eapply (store_ok_bytes SEGS M objw 24); [rewrite Hou; cbn; lia | exact STO | rewrite Hou; cbn; lia]. }
  assert (OOWN : forall a : word, o <= bv_unsigned a < o + 24 -> owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a).
  { intros a Ha. eapply (owned_x_sound SEGS SWIN PERMc SPTOPc); [exact HK | exact Hflat | exact (co_perm HC) | exact (co_top HC) | exact (co_floor HC) | exact Hoown |].
    rewrite (elenZ_lit E) by lia. fold o. lia. }
  assert (Hretok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by lia; exact Re).
  assert (R11n : getr R (Z_to_bv 5 11) = Z_to_bv 64 n) by (rewrite R11; unfold n; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (store_ok_rdn SEGS SEGS_wr 8 M objw ltac:(rewrite Hou; cbn; lia)
              ltac:(apply store_ok_of_all; [rewrite Hou; cbn; lia|]; intros x Hx; apply store_ok1_wview; apply OST1; rewrite Hou in Hx; cbn in Hx; lia))
    as (hbs & RDH & Hhlen).
  set (w0 := Z_to_bv 64 (bytes_le_to_Z hbs)).
  assert (RD8 : rdn SEGS M objw 8 = Some (W8 w0)).
  { rewrite RDH. f_equal. symmetry. subst w0. apply (word_to_le_bytes_of_bytes_n 8 hbs Hhlen). lia. }
  (* [comment removed for export] *)
  assert (Hsp80 : 80 <= bv_unsigned spw) by (unfold CEIL, MSTK in *; lia).
  assert (STF : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 80)) 80 = true).
  { pose proof (u64_range spw) as Hspr.
    apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|]. intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
    apply store_ok1_wview. apply Hstk. unfold MSTK. lia. }
  (* [comment removed for export] *)
  destruct args as [|a1 args1]; [discriminate|].
  destruct a1 as [z| | | | | | |]; try discriminate.
  destruct z as [|pz|]; [| destruct pz; try discriminate |discriminate].
  - (* [comment removed for export] *)
    destruct args1 as [|a2 rest]; [discriminate|]. destruct a2 as [|sv| | | | | |]; try discriminate.
    match type of Hn with context [match ?ob with _ => _ end] =>
      match ob with (match rest with _ => _ end, _) => idtac | _ => fail end end || idtac.
    destruct (match rest with [] => Some None | [b] => Some (Some b) | _ :: _ :: _ => None end) as [obnd|] eqn:Hobnd; [|discriminate].
    destruct (xhi (kn cs) (EVar sv)) as [shi|] eqn:Hshi; [|discriminate].
    match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hsc; [|discriminate] end. cbn [negb] in Hn.
    apply andb_prop in Hsc as [Hkw0 Hs22]. apply Z.leb_le in Hs22.
    match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hbc; [|discriminate] end. cbn [negb] in Hn.
    apply Z.leb_le in Hbc.
    destruct (grow_bound (kn cs) (eaddz (reg cs 11) 52) obnd (nxt cs)) as [bnd|] eqn:Hgb; [|discriminate].
    injection Hn as <- <-.
    (* [comment removed for export] *)
    set (s := bv_unsigned (edenot E (EVar sv))) in *.
    pose proof (xhi_sound SEGS E M (kn cs) (EVar sv) shi HK Hshi) as Shi.
    destruct (kentails_word_sound E M (kn cs) ob ok 1 (escale 2 (EVar sv)) HK ltac:(lia) Hkw0) as [_ RDb].
    fold o in RDb.
    assert (Hw0 : bv_unsigned w0 mod 256 = 2 * s).
    { pose proof (SumsLib.StartupAux.rdn_low_bytes SEGS M objw w0 1 ltac:(lia) RD8) as H1.
      rewrite Hobjw, RDb in H1. apply some_inj in H1.
      apply (f_equal bytes_le_to_Z) in H1. rewrite !bytes_le_N in H1. change (2 ^ (8 * Z.of_nat 1)) with 256 in H1.
      rewrite escale_u in H1. fold s in H1.
      pose proof (u64_range (edenot E (EVar sv))). fold s in H.
      rewrite (Z.mod_small (2 * s) (2 ^ 64)) in H1 by lia.
      rewrite (Z.mod_small (2 * s) 256) in H1 by lia. lia. }
    destruct (Z.le_gt_cases n 22) as [Hle|Hgt].
    + (* [comment removed for export] *)
      destruct (Z.leb 23 nlo) eqn:Hdead1; [apply Z.leb_le in Hdead1; exfalso; clear -Hdead1 Hle Nlo; lia|]. rewrite mark_dead_false in Hk1.
      destruct (KS fx R M objw spw (Z_to_bv 64 ret) w0 (edenot E (reg cs 12)) s n RD8 Hw0 ltac:(pose proof (u64_range (edenot E (EVar sv))); lia) ltac:(lia)
                  ltac:(rewrite Hou; lia) Hsp80 ltac:(rewrite Hou; lia) STF STO Hretok R1
                  R2 R10 R11n R12)
        as (r' & M' & RUN & A10 & KEPT & FR & GROWS & RDb' & NUL).
      set (E1 := ext_call E (nxt cs) r').
      pose proof (ext_call_agree E (nxt cs) r') as Hag1. fold E1 in Hag1.
      assert (DEF' : forall a : word, M' a <> M a -> M' a <> None).
      { intros a Ha. destruct (M a) as [b|] eqn:HMa; [apply GROWS; rewrite HMa; discriminate | exact Ha]. }
      assert (Hne11 : edenot E1 (reg cs 11) = edenot E (reg cs 11)) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Hnv]).
      assert (Hobv : AP.expr_vars_lt (nxt cs) ob = true).
      { eapply split_lit_vars; [exact Hob|]. apply (nth_sr_vars_lt _ _ 10 Fsr). lia. }
      assert (Hne10 : edenot E1 ob = edenot E ob) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Hobv]).
      assert (Ho1 : estart E1 (SA ob ok) = o) by (unfold o; rewrite !estart_SA, Hne10; reflexivity).
      lazymatch type of Hk1 with context [with_ss cs (mk_ss _ ?sr ?kk ?nx)] =>
        eapply (gcall_core SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps
                  cs E E1 fx fx R M model T ret sr kk nx r' M' HC Hfresh Hag1) end.
      * rewrite Hpc. exact RUN.
      * exact (co_fx HC).
      * intros a Ha. split; [|exact (DEF' a Ha)]. destruct (FR a Ha) as [Hx|Hx].
        -- apply OOWN. rewrite Hou in Hx. exact Hx.
        -- right. right. left. unfold MSTK in *. lia.
      * (* [comment removed for export] *)
        change (regs_ok E1 (sr_upd (sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)) 10 (eaddz ob ok)) r').
        rewrite <- (ridx_lit 10) by lia. apply regs_ok_pin.
        -- apply (regs_after_call E (s_regs (a_ss cs)) R r' (nxt cs) None HR Fsr (kept15_kept_ok R r' KEPT) I).
        -- transitivity objw; [rewrite <- A10; f_equal; apply bv_eq; reflexivity|].
           rewrite Hobjw. unfold eaddz. rewrite mkAlu_denot, alu_add. cbn [edenot]. rewrite Hne10. unfold v_add, o.
           rewrite estart_SA. apply bv_eq. rewrite !Z_to_bv_unsigned. symmetry. apply bv_wrap_add_idemp_r.
      * (* [comment removed for export] *)
        assert (Hsc : edenot E1 (escale 2 (reg cs 11)) = Z_to_bv 64 (2 * n)).
        { apply bv_eq. rewrite escale_u, Hne11. fold n. rewrite Z_to_bv_unsigned. reflexivity. }
        assert (Hnul : estart E1 (SA (eadd (eaddz ob (ok + 1)) (reg cs 11)) 0) = o + 1 + n).
        { rewrite estart_SA, eadd_u, eaddz_u, Hne10, Hne11. fold n. unfold o in *. rewrite estart_SA in *.
          pose proof (u64_range (edenot E ob)). rewrite (Z.mod_small (_ + (ok + 1))) by lia. rewrite Z.mod_small by lia. lia. }
        unfold know_ok.
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply (proj2 (Forall_app _ _ _)); split]]]];
          cbn [kentry_ok].
        -- unfold uE. rewrite Hne11. fold n. lia.
        -- split; [lia|]. split; [unfold flat; rewrite Ho1; cbn; lia|].
           rewrite adenot_SA, Ho1, <- Hobjw, RDb'. rewrite Hsc. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
           rewrite u64_lit by (unfold SMAXR in *; lia). reflexivity.
        -- split; [lia|]. split; [unfold flat; rewrite Hnul; cbn; lia|].
           rewrite adenot_SA, Hnul. rewrite <- Hou. rewrite (rdn1_overlay _ _ _ _ NUL). cbn [edenot]. reflexivity.
        -- rewrite Ho1.
           rewrite (elenZ_lit E1) by lia.
           split.
           { unfold flat. rewrite ?Ho1.
             repeat split; [exact Of1 | exact Of3 | lia | exact Of2]. }
           intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
           apply store_ok_of_all; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
           apply store_ok1_wview. apply defined_store_ok; [lia|]. apply GROWS. apply ODEF. lia.
        -- destruct (kn_readable_x (kn cs) ob ok (ELit 24)); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
           cbn [kentry_ok]. rewrite Ho1, (elenZ_lit E1) by lia. split; [unfold flat; rewrite Ho1; lia|].
           intros i Hi. apply GROWS. apply ODEF. rewrite u64_lit by lia. lia.
        -- (* [comment removed for export] *)
          apply (know_ok_agree' SEGS (nxt cs) E E1); [exact Hag1 | apply str_keep_vars |].
          eapply (str_keep_sound E M M' (kn cs) (a_vis cs) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk ob ok None (nxt cs)
                    HK Hflat (co_perm HC) (co_top HC) Hsp).
          ++ pose proof (u64_range spw). lia.
          ++ exact (co_floor HC).
          ++ intros a Hka Hno _. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
             destruct (FR a Hne) as [Hx|Hx]; [apply Hno; fold o; rewrite <- Hou; exact Hx|].
             subst spw o. destruct Hka as [[_ Hns]|[[Hro _]|[Hab Hspt]]]; [apply Hns; unfold MSTK; lia | unfold MSTK in *; lia | lia].
          ++ intros a Ha. subst spw.
             assert (D : M' a <> None).
             { apply GROWS. eapply (store_ok_defined SEGS G SEGS_out); [unfold MSTK in *; lia | apply Hstk; exact Ha]. }
             split; [exact D | apply defined_store_ok; [unfold MSTK in *; lia | exact D]].
          ++ intros a Ha. subst spw o. cbn [old_lo old_n]. split; [|lia].
             rewrite estart_SA in Hosc'. pose proof (u64_range (edenot E spb)). unfold MSTK in *. lia.
      * (* [comment removed for export] *)
        intros fx'' R' M'' model' HC' Hfs'. apply (Hk1 E1 fx'' R' M'' model'); [| exact HC' | exact Hfs'].
        split; [eapply env_agree_le; [exact Hag1 | exact Fle] | exact Hag1].
    + (* [comment removed for export] *)
      destruct (Z.leb nhi 22) eqn:Hdead2; [apply Z.leb_le in Hdead2; exfalso; clear -Hdead2 Hgt Nhi; lia|]. rewrite mark_dead_false in Hk2.
      pose proof (galloc_facts n 22 ltac:(lia)) as (Ga1 & Ga2 & Ga3 & Ga8).
      set (g := galloc n 22) in *.
      set (Lc := blocks_den E (a_vis cs)).
      destruct (cost_hi_sound SEGS E M (kn cs) (a_vis cs) ch HK Hch) as [Hcost Hcost0].
      assert (Hobv : AP.expr_vars_lt (nxt cs) ob = true).
      { eapply split_lit_vars; [exact Hob|]. apply (nth_sr_vars_lt _ _ 10 Fsr). lia. }
      unfold cfgF. rewrite Hpc.
      apply (GS fx R M model Lc (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs)) ret (bv_unsigned spw) objw w0 (edenot E (reg cs 12)) s n T
               (co_halt HC) (co_lazy HC) (co_mat HC) (co_fx HC) (co_ainv HC) HT0 R1 Rr Re R10 R11n R12).
      * rewrite R2. reflexivity.
      * exact Hal.
      * exact Hsplo.
      * exact Hsptop.
      * exact R4.
      * exact Hstk.
      * split; [rewrite Hou; lia|]. split; [rewrite Hou; exact Of2|]. split; [exact STO|].
        intros a Ha. apply OOWN. rewrite Hou in Ha. exact Ha.
      * exact RD8.
      * exact Hw0.
      * pose proof (u64_range (edenot E (EVar sv))). lia.
      * lia.
      * unfold NMAX, SMAXR in *. lia.
      * fold g. unfold mcost in *.
        pose proof (Z.div_mod (Z.max nhi 23 + 52) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max nhi 23 + 52) 8 ltac:(lia)). lia.
      * unfold GPS.bcount. lia.
      * (* [comment removed for export] *)
        intros fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk Hdisj Hperm Hblk RD0' RD1' RD2' NUL Hfr Hscr Hobj' HAINV' Hh' Hlz' Hmat' Hfs' Hfds'.
        fold g in Hpblk, Hdisj, Hperm, Hblk, RD0', HAINV'.
        pose proof Hpblk as (Hplo & Hphi & Hpimg). unfold GlzConst.PTRLO in Hplo.
        rewrite Hobjw in RD0'. rewrite Hou in RD1', RD2', Hobj'. rewrite Hobjw in Ha0. pose proof (u64_range p) as Hpr.
        pose proof (Z.div_mod (Z.max nlo 23 + 8) 8 ltac:(lia)) as Dv1. pose proof (Z.mod_pos_bound (Z.max nlo 23 + 8) 8 ltac:(lia)) as Md1.
        pose proof (Z.div_mod (Z.max nhi 23 + 52) 8 ltac:(lia)) as Dv2. pose proof (Z.mod_pos_bound (Z.max nhi 23 + 52) 8 ltac:(lia)) as Md2.
        pose proof (Z.div_mod g 8 ltac:(lia)) as Dv3.
        assert (HgAlo : 8 * Z.max 6 ((Z.max nlo 23 + 8) / 8) <= g) by (first [ (clear Md2 Dv2 Hpal Hw0 Hosc' Hal Re Hbc Hobnd; lia) | lia ]).
        assert (HgAhi : g <= 8 * ((Z.max nhi 23 + 52) / 8)) by (first [ (clear Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk1 Hobnd; lia) | lia ]).
        destruct (long_post_sound cs E fx fx' R R' M M' model mdl' ret ob ok (Z.max nlo 23) nhi
                    (Z.max 6 ((Z.max nlo 23 + 8) / 8)) ((Z.max nhi 23 + 52) / 8) None bnd (a_vis cs)
                    (str_keep G (kn cs) (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) ob ok None (nxt cs)) spb spk (fst (split_lit (a_brk cs))) (snd (split_lit (a_brk cs))) p g o n
                    HC Hfresh eq_refl Hobjw Hobv eq_refl Hnv Of1 Of2 ltac:((first [ (clear HgAhi HgAlo Dv3 Md2 Dv2 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])) ltac:((first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])) Ga8 HgAlo HgAhi ltac:((first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])) ltac:((first [ (clear HgAhi Dv3 Md2 Dv2 Hpimg Hperm Hdisj Hpal Ga8 Hw0 Hosc' Hal Re Hbc Hobnd; lia) | lia ])) ltac:((first [ (clear HgAhi Dv3 Md2 Dv2 Hpimg Hperm Hdisj Hpal Ga8 Ga3 Hw0 Hosc' Hal Re Hbc Hobnd; lia) | lia ]))
                    Hpblk Hpal Hblk NUL RD0' RD1' RD2' Hobj' Hdisj Hperm Hflat ltac:(intros x Hx; exact Hx)
                    Hsp Hspv Hsplo Hsptop (surjective_pairing _) (call_ok_top_ok nx0 G _ _ _ Hco))
          as (E' & HagA & HagB & Hfs2 & HC').
        -- (* [comment removed for export] *)
          intros E' HagE Hpv Hav.
          assert (Hne11' : edenot E' (reg cs 11) = edenot E (reg cs 11)) by (symmetry; eapply edenot_agree'; [exact HagE | exact Hnv]).
          assert (Hlen' : bv_unsigned (edenot E' (escale 8 (EVar (S (nxt cs))))) = g).
          { rewrite escale_u, Hav, u64_lit by (unfold CEIL in *; (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])). rewrite Z.mod_small by (unfold CEIL in *; (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])). (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ]). }
          unfold know_ok. apply (proj2 (Forall_app _ _ _)); split.
          ++ (* [comment removed for export] *)
             unfold grow_bound in Hgb. destruct obnd as [b|].
             ** destruct (xhi2 (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
                match type of Hgb with (if ?c then _ else _) = _ => destruct c eqn:Hbc2; [|discriminate] end.
                apply andb_prop in Hbc2 as [Hlin Hbv]. injection Hgb as <-.
                apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
                pose proof (lin_ge0_sound SEGS E M (kn cs) [(b, 0)] [(eaddz (reg cs 11) 52, 0)] HK Hlin) as Hl. cbn [xt_den] in Hl.
                rewrite eaddz_u in Hl. fold n in Hl. rewrite Z.mod_small in Hl by (unfold SMAXR in *; (first [ (clear Hav HgAhi HgAlo Dv3 Md2 Dv2 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])).
                pose proof (xhi2_sound SEGS E M (kn cs) b bh HK Hbh) as Hbhi.
                rewrite esub_u, Hlen'. rewrite <- (edenot_agree' (nxt cs) E E' b HagE Hbv).
                rewrite Z.mod_small by (pose proof (u64_range (edenot E b)); (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hal Re Hbc; lia) | lia ])). (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hal Re Hbc; lia) | lia ]).
             ** injection Hgb as <-. apply Forall_nil.
          ++ repeat apply Forall_cons; [| |apply Forall_nil]; cbn [kentry_ok].
             ** rewrite Hne11'. fold n. (first [ (clear Hav HgAlo Dv3 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Hw0 Hosc' Hal Re Hk1 Hobnd; lia) | lia ]).
             ** rewrite esub_u, eaddz_u, Hne11', Hlen'. fold n. rewrite (Z.mod_small (n + 52)) by (unfold SMAXR in *; (first [ (clear Hav HgAhi HgAlo Dv3 Md2 Dv2 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ])).
                rewrite Z.mod_small by (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ]). (first [ (clear Md2 Dv2 Md1 Dv1 Hpal Hw0 Hosc' Hal Re Hk2 Hk1 Hbc Hobnd; lia) | lia ]).
        -- (* [comment removed for export] *)
          eapply (str_keep_sound E M M' (kn cs) (a_vis cs) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk ob ok None (nxt cs)
                    HK Hflat (co_perm HC) (co_top HC) Hsp).
          ++ pose proof (u64_range spw). (first [ (clear HgAhi HgAlo Dv3 Md2 Dv2 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Ga3 Hw0 Hal Re Hbc Hobnd; lia) | lia ]).
          ++ exact (co_floor HC).
          ++ intros a Hka Hno _. apply Hfr; [exact Hka|]. rewrite Hou. exact Hno.
          ++ exact Hscr.
          ++ intros a Ha. subst spw o. cbn [old_lo old_n]. split; [|lia].
             rewrite estart_SA in Hosc'. pose proof (u64_range (edenot E spb)). unfold MSTK in *. (first [ (clear HgAhi HgAlo Dv3 Md2 Dv2 Md1 Dv1 Hpimg Hperm Hdisj Hpal Ga8 Ga3 Hw0 Re Hbc Hobnd; lia) | lia ]).
        -- apply str_keep_vars.
        -- exact Hkept.
        -- exact Ha0.
        -- exact HFX'.
        -- exact HAINV'.
        -- exact Hh'.
        -- exact Hlz'.
        -- exact Hmat'.
        -- exact Hfs'.
        -- exact Hfds'.
        -- apply (Hk2 E' fx' R' M' mdl'); [split; [exact HagA | exact HagB] | exact HC' | exact Hfs'].
  - (* [comment removed for export] *)
    destruct args1 as [|a2 args2]; [discriminate|]. destruct a2 as [|dv| | | | | |]; try discriminate.
    destruct args2 as [|a3 args3]; [discriminate|]. destruct a3 as [|Av| | | | | |]; try discriminate.
    destruct args3 as [|sz rest]; [discriminate|].
    destruct (match rest with [] => Some None | [b] => Some (Some b) | _ :: _ :: _ => None end) as [obnd|] eqn:Hobnd; [|discriminate].
    match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hlc; [|discriminate] end. cbn [negb] in Hn.
    apply andb_prop in Hlc as [Hlc Hszle]. apply andb_prop in Hlc as [Hlc Hkws]. apply andb_prop in Hlc as [Hlc Hszv].
    apply andb_prop in Hlc as [Hkw0 Hkwd].
    destruct (remove_block (EVar dv) (a_vis cs)) as [[olen live']|] eqn:Hrb; [|discriminate].
    destruct (xlo (kn cs) (EVar Av)) as [Alo|] eqn:HAlo; [|discriminate].
    destruct (xhi (kn cs) (EVar Av)) as [Ahi|] eqn:HAhi; [|discriminate].
    match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hbc; [|discriminate] end. cbn [negb] in Hn.
    apply andb_prop in Hbc as [Hbc Hdsc]. apply andb_prop in Hbc as [Hbc Hdob]. apply andb_prop in Hbc as [Hbc Hdwr].
    apply andb_prop in Hbc as [Hbc HAhiS]. apply andb_prop in Hbc as [Holen HAlo3].
    apply expr_eqb_eq in Holen. subst olen. apply Z.leb_le in HAlo3. apply Z.leb_le in HAhiS.
    change (SMAXR / 8) with (2 ^ 33) in HAhiS.
    (* [comment removed for export] *)
    destruct (remove_block_split _ _ _ _ Hrb) as (L1' & L2' & Hvis & ->).
    set (A := bv_unsigned (edenot E (EVar Av))) in *.
    pose proof (xlo_sound SEGS E M (kn cs) (EVar Av) Alo HK HAlo) as HA1. pose proof (xhi_sound SEGS E M (kn cs) (EVar Av) Ahi HK HAhi) as HA2.
    fold A in HA1, HA2.
    set (cap := 8 * A - 1).
    set (d := edenot E (EVar dv)).
    set (s := bv_unsigned (edenot E sz)) in *.
    assert (HvisV : pairs_vars_lt (nxt cs) (a_vis cs) = true) by exact (pairs_vars_lt_app_l _ _ _ Fallow).
    pose proof (proj1 (forallb_forall _ _) HvisV (EVar dv, escale 8 (EVar Av)) ltac:(rewrite Hvis; apply in_app_iff; right; left; reflexivity)) as Hbv.
    apply andb_prop in Hbv as [Hdvv Holv]. cbn [fst snd] in Hdvv, Holv.
    (* [comment removed for export] *)
    destruct (kentails_word_sound E M (kn cs) ob ok 8 (eaddz (escale 8 (EVar Av)) 1) HK ltac:(lia) Hkw0) as [_ RDw0]. fold o in RDw0.
    destruct (kentails_word_sound E M (kn cs) ob (ok + 16) 8 (EVar dv) HK ltac:(lia) Hkwd) as [_ RDd].
    destruct (kentails_word_sound E M (kn cs) ob (ok + 8) 8 sz HK ltac:(lia) Hkws) as [_ RDs].
    assert (Ho8 : estart E (SA ob (ok + 8)) = o + 8) by (unfold o; rewrite !estart_SA; lia).
    assert (Ho16 : estart E (SA ob (ok + 16)) = o + 16) by (unfold o; rewrite !estart_SA; lia).
    rewrite Ho8 in RDs. rewrite Ho16 in RDd. fold d in RDd.
    assert (Holu : bv_unsigned (edenot E (escale 8 (EVar Av))) = 8 * A) by (rewrite escale_u; fold A; apply Z.mod_small; unfold SMAXR in *; lia).
    assert (Hw0u : bv_unsigned (edenot E (eaddz (escale 8 (EVar Av)) 1)) = cap + 2).
    { rewrite eaddz_u, Holu. subst cap. rewrite Z.mod_small by (unfold SMAXR in *; lia). lia. }
    clear RD8 w0 RDH Hhlen hbs.
    set (w0 := edenot E (eaddz (escale 8 (EVar Av)) 1)) in *.
    assert (RD8 : rdn SEGS M objw 8 = Some (W8 w0)) by (rewrite Hobjw; exact RDw0).
    assert (Hszw : edenot E sz = Z_to_bv 64 s) by (symmetry; apply Z_to_bv_bv_unsigned).
    rewrite Hszw in RDs.
    (* [comment removed for export] *)
    pose proof (lin_ge0_sound SEGS E M (kn cs) [(escale 8 (EVar Av), (-1))] [(sz, 0)] HK Hszle) as Hsle. cbn [xt_den] in Hsle.
    rewrite Holu in Hsle. fold s in Hsle.
    (* [comment removed for export] *)
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) (EVar dv) 0 (escale 8 (EVar Av)) HK HK Hdwr) as (DW & Dfl1 & Dfl2).
    rewrite estart_SA, Z.add_0_r in DW, Dfl1, Dfl2. unfold elenZ in DW, Dfl2. rewrite Holu in DW, Dfl2. fold d in DW, Dfl1, Dfl2.
    rewrite Z_to_bv_bv_unsigned in DW.
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) (EVar dv) 0 (escale 8 (EVar Av)) ob ok (ELit 24) HK Hdob) as Hdob'.
    rewrite estart_SA, Z.add_0_r in Hdob'. unfold elenZ in Hdob'. rewrite Holu in Hdob'. cbn [edenot] in Hdob'. rewrite (u64_lit 24) in Hdob' by lia.
    fold d o in Hdob'.
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) (EVar dv) 0 (escale 8 (EVar Av)) spb (spk - MSTK) (ELit MSTK) HK Hdsc) as Hdsc'.
    rewrite !estart_SA, Z.add_0_r in Hdsc'. unfold elenZ in Hdsc'. rewrite Holu in Hdsc'. cbn [edenot] in Hdsc'. rewrite (u64_lit MSTK) in Hdsc' by (unfold MSTK; lia).
    fold d in Hdsc'.
    (* [comment removed for export] *)
    assert (HLc : blocks_den E (a_vis cs) = blocks_den E L1' ++ (bv_unsigned d, cap + 1) :: blocks_den E L2').
    { rewrite Hvis, blocks_den_app. cbn [blocks_den map app fst snd]. unfold uE. rewrite Holu. fold d. subst cap.
      replace (8 * A - 1 + 1) with (8 * A) by lia. reflexivity. }
    change (ev E dv) with d in Hdob', Hdsc'.
    destruct (cost_hi (kn cs) (L1' ++ L2')) as [ch'|] eqn:Hch'; [|discriminate].
    match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hbc'; [|discriminate] end. cbn [negb] in Hn.
    apply Z.leb_le in Hbc'.
    destruct (grow_bound (kn cs) (eaddz (escale 2 (reg cs 11)) 8) obnd (nxt cs)) as [bnd|] eqn:Hgb; [|discriminate].
    injection Hn as <- <-.
    assert (Hs0 : 0 <= s) by (pose proof (u64_range (edenot E sz)); lia).
    assert (Hcap8 : (cap + 1) mod 8 = 0) by (subst cap; replace (8 * A - 1 + 1) with (A * 8) by lia; apply Z_mod_mult).
    assert (Hcap2 : (cap + 1) mod 2 = 0) by (subst cap; replace (8 * A - 1 + 1) with (4 * A * 2) by lia; apply Z_mod_mult).
    assert (STD : store_ok SEGS M d (Z.to_nat (cap + 1)) = true) by (apply DW; (first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])).
    assert (DST1 : forall a : word, bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> store_ok SEGS M a 1 = true).
    { intros a Ha. eapply (store_ok_bytes SEGS M d (Z.to_nat (cap + 1))); [(first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | exact STD | (first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])]. }
    pose proof (u64_range d) as Hdr.
    rewrite <- Hou in RDs, RDd.
    assert (Hsub : forall x, In x (L1' ++ L2') -> In x (a_vis cs)).
    { intros x Hx. rewrite Hvis. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
    assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((L1' ++ L2') ++ a_ghost cs) = true).
    { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hflat x).
      apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hsub x Hx) | right; exact Hx]. }
    assert (Hobv : AP.expr_vars_lt (nxt cs) ob = true).
    { eapply split_lit_vars; [exact Hob|]. apply (nth_sr_vars_lt _ _ 10 Fsr). lia. }
    assert (Hinold : In (bv_unsigned d, cap + 1) (blocks_den E (a_vis cs))) by (rewrite HLc; apply in_app_iff; right; left; reflexivity).
    assert (OOWN' : forall a : word, o <= bv_unsigned a < o + 24 -> owned SWIN PERMc SPTOPc (blocks_den E L1' ++ blocks_den E L2') a).
    { intros a Ha. destruct (OOWN a Ha) as [Hb|Hrest]; [|right; exact Hrest]. left.
      destruct Hb as (b & m & Hin & Hbz). rewrite HLc in Hin. apply in_app_iff in Hin as [Hin|[Heq|Hin]].
      - exists b, m. split; [apply in_app_iff; left; exact Hin | exact Hbz].
      - exfalso. injection Heq as <- <-. lia.
      - exists b, m. split; [apply in_app_iff; right; exact Hin | exact Hbz]. }
    destruct (Z.le_gt_cases n cap) as [Hle|Hgt].
    + (* [comment removed for export] *)
      destruct (lin_ge0 (kn cs) [(reg cs 11, 0)] [(escale 8 (EVar Av), 0)]) eqn:Hdead1.
      { exfalso. pose proof (lin_ge0_sound SEGS E M (kn cs) [(reg cs 11, 0)] [(escale 8 (EVar Av), 0)] HK Hdead1) as Hl. cbn [xt_den] in Hl.
        rewrite Holu in Hl. fold n in Hl. clear -Hl Hle. subst cap. lia. }
      rewrite mark_dead_false in Hk1.
      destruct (KL fx R M objw spw (Z_to_bv 64 ret) d w0 (edenot E (reg cs 12)) cap s n RD8 Hw0u Hcap2 RDs RDd
                  ltac:((first [ (clear Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:((first [ (clear Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:((first [ (clear Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:(rewrite Hou; (first [ (clear Hcap2 Hcap8 Hdsc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:((first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) Hsp80
                  ltac:(rewrite Hou; unfold MSTK in *; (first [ (clear Hcap2 Hcap8 Hdsc' Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:(unfold MSTK in *; (first [ (clear Hosc' Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])) ltac:(rewrite Hou; (first [ (clear Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]))
                  STF STO STD Hretok R1 R2 R10 R11n R12)
        as (r' & M' & RUN & A10 & KEPT & FR & GROWS & RD0' & RD1' & RD2' & NUL).
      set (E1 := ext_call E (nxt cs) r').
      pose proof (ext_call_agree E (nxt cs) r') as Hag1. fold E1 in Hag1.
      assert (DEF' : forall a : word, M' a <> M a -> M' a <> None).
      { intros a Ha. destruct (M a) as [b|] eqn:HMa; [apply GROWS; rewrite HMa; discriminate | exact Ha]. }
      assert (Hne11 : edenot E1 (reg cs 11) = edenot E (reg cs 11)) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Hnv]).
      assert (Hne10 : edenot E1 ob = edenot E ob) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Hobv]).
      assert (Hned : edenot E1 (EVar dv) = d) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Hdvv]).
      assert (HneA : edenot E1 (escale 8 (EVar Av)) = edenot E (escale 8 (EVar Av))) by (symmetry; eapply edenot_agree'; [exact Hag1 | exact Holv]).
      assert (Ho1 : estart E1 (SA ob ok) = o) by (unfold o; rewrite !estart_SA, Hne10; reflexivity).
      assert (Ho1b : forall z, estart E1 (SA ob (ok + z)) = o + z) by (intros z; unfold o; rewrite !estart_SA, Hne10; lia).
      assert (HlenA : elenZ E1 (escale 8 (EVar Av)) = 8 * A) by (unfold elenZ; rewrite HneA; exact Holu).
      assert (Hd1 : estart E1 (SA (EVar dv) 0) = bv_unsigned d) by (rewrite estart_SA, Hned; lia).
      assert (Hn11 : edenot E (reg cs 11) = Z_to_bv 64 n) by (unfold n; symmetry; apply Z_to_bv_bv_unsigned).
      lazymatch type of Hk1 with context [ACS (mk_ss _ ?sr ?kk ?nx) _ _ _ _ _ _ _ _ _ _] =>
        eapply (gcall_core SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps
                  cs E E1 fx fx R M model T ret sr kk nx r' M' HC Hfresh Hag1) end.
      * rewrite Hpc. exact RUN.
      * exact (co_fx HC).
      * intros a Ha. split; [|exact (DEF' a Ha)]. destruct (FR a Ha) as [Hx|[Hx|Hx]].
        -- apply OOWN. rewrite Hou in Hx. lia.
        -- left. exists (bv_unsigned d), (cap + 1). split; [exact Hinold | lia].
        -- right. right. left. unfold MSTK in *. (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]).
      * (* [comment removed for export] *)
        change (regs_ok E1 (sr_upd (sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)) 10 (eaddz ob ok)) r').
        rewrite <- (ridx_lit 10) by lia. apply regs_ok_pin.
        -- apply (regs_after_call E (s_regs (a_ss cs)) R r' (nxt cs) None HR Fsr (kept15_kept_ok R r' KEPT) I).
        -- transitivity objw; [rewrite <- A10; f_equal; apply bv_eq; reflexivity|].
           rewrite Hobjw. unfold eaddz. rewrite mkAlu_denot, alu_add. cbn [edenot]. rewrite Hne10. unfold v_add, o.
           rewrite estart_SA. apply bv_eq. rewrite !Z_to_bv_unsigned. symmetry. apply bv_wrap_add_idemp_r.
      * (* [comment removed for export] *)
        unfold know_ok.
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
          [|apply (proj2 (Forall_app _ _ _)); split]]]]]]]]; cbn [kentry_ok].
        -- rewrite esub_u, HneA, Hne11, Holu. fold n. rewrite Z.mod_small by (first [ (clear FR Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]). (first [ (clear FR Hcap2 Hcap8 Hosc' Hal Re Hk2 Hobnd; lia) | lia ]).
        -- split; [lia|]. split; [unfold flat; rewrite Ho1; cbn; lia|].
           rewrite adenot_SA, Ho1, <- Hobjw, RD0'. f_equal. f_equal. apply bv_eq. unfold w0. rewrite !eaddz_u, HneA. reflexivity.
        -- split; [lia|]. split; [unfold flat; rewrite (Ho1b 8); cbn; lia|].
           rewrite adenot_SA, (Ho1b 8), <- Hou, RD1', Hne11, Hn11. reflexivity.
        -- split; [lia|]. split; [unfold flat; rewrite (Ho1b 16); cbn; lia|].
           rewrite adenot_SA, (Ho1b 16), <- Hou, RD2', Hned. reflexivity.
        -- rewrite HlenA, Hd1. split; [unfold flat; rewrite ?Hd1, ?HlenA; (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])|].
           intros dd m Hdd Hdm. eapply store_ok_mono; [exact GROWS|].
           destruct m as [|m']; [reflexivity|].
           eapply (store_ok_sub SEGS M d _ (Z.to_nat (cap + 1))); [(first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | exact STD | rewrite u64_lit by (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]); (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | rewrite u64_lit by (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]); (first [ (clear Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])].
        -- assert (Hdn : estart E1 (SA (eadd (EVar dv) (reg cs 11)) 0) = bv_unsigned d + n).
           { rewrite estart_SA, eadd_u, Hned, Hne11. fold n. rewrite Z.mod_small by (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]). lia. }
           split; [lia|]. split; [unfold flat; rewrite Hdn; change (Z.of_nat 1) with 1; (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])|].
           rewrite adenot_SA, Hdn. rewrite (rdn1_overlay _ _ _ _ NUL). cbn [edenot]. reflexivity.
        -- rewrite Ho1, (elenZ_lit E1) by lia. split; [unfold flat; rewrite Ho1; cbn; lia|].
           intros dd m Hdd Hdm. eapply store_ok_mono; [exact GROWS|].
           destruct m as [|m']; [reflexivity|]. rewrite <- Hou.
           eapply (store_ok_sub SEGS M objw _ 24); [cbn; (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | exact STO | rewrite u64_lit by (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]); (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | rewrite u64_lit by (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]); cbn; (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])].
        -- rewrite Ho1, (elenZ_lit E1) by lia. split; [unfold flat; rewrite Ho1; cbn; lia|].
           intros i Hi. apply GROWS. apply ODEF. rewrite u64_lit by (first [ (clear FR Hcap2 Hcap8 Hdsc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]). lia.
        -- destruct (kn_readable_x (kn cs) (EVar dv) 0 (escale 8 (EVar Av))) eqn:Hrdx; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
           cbn [kentry_ok]. rewrite HlenA, Hd1. split; [unfold flat; rewrite ?Hd1, ?HlenA; (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ])|].
           intros i Hi. apply GROWS.
           destruct (GlzCall.kn_readable_x_sound SEGS E M (kn cs) (EVar dv) 0 (escale 8 (EVar Av)) HK Hrdx) as (_ & _ & Hrd).
           rewrite estart_SA, Z.add_0_r in Hrd. unfold elenZ in Hrd. rewrite Holu in Hrd. apply Hrd. lia.
        -- (* [comment removed for export] *)
          apply (know_ok_agree' SEGS (nxt cs) E E1); [exact Hag1 | apply str_keep_vars |].
          eapply (str_keep_sound E M M' (kn cs) (L1' ++ L2') (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk ob ok (Some (EVar dv, escale 8 (EVar Av))) (nxt cs)
                    HK Hflat' (co_perm HC) (co_top HC) Hsp).
          ++ pose proof (u64_range spw). (first [ (clear FR Hcap2 Hcap8 Hdob' Hal Re Hbc' Hobnd; lia) | lia ]).
          ++ exact (co_floor HC).
          ++ intros a Hka Hno Hnold. cbn [old_lo old_n split_lit] in Hnold. rewrite estart_SA, Z.add_0_r in Hnold. unfold elenZ in Hnold. rewrite Holu in Hnold.
             change (edenot E (EVar dv)) with d in Hnold.
             destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
             destruct (FR a Hne) as [Hx|[Hx|Hx]]; [apply Hno; fold o; rewrite <- Hou; (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) | apply Hnold; (first [ (clear Hcap2 Hcap8 Hosc' Hal Re Hk2 Hk1 Hbc' Hobnd; lia) | lia ]) |].
             subst spw o. destruct Hka as [[_ Hns]|[[Hro _]|[Hab Hspt]]]; [apply Hns; unfold MSTK; (first [ (clear Hcap2 Hcap8 Re Hbc' Hobnd; lia) | lia ]) | unfold MSTK in *; lia | lia].
          ++ intros a Ha. subst spw.
             assert (D : M' a <> None).
             { apply GROWS. eapply (store_ok_defined SEGS G SEGS_out); [unfold MSTK in *; (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hbc' Hobnd; lia) | lia ]) | apply Hstk; exact Ha]. }
             split; [exact D | apply defined_store_ok; [unfold MSTK in *; (first [ (clear Hcap2 Hcap8 Hdsc' Hdob' Hosc' Hal Re Hbc' Hobnd; lia) | lia ]) | exact D]].
          ++ intros a Ha. subst spw o. cbn [old_lo old_n split_lit]. rewrite !estart_SA, Z.add_0_r. unfold elenZ. rewrite Holu.
             change (edenot E (EVar dv)) with d.
             rewrite estart_SA in Hosc'. pose proof (u64_range (edenot E spb)). unfold MSTK in *. split; lia.
      * (* [comment removed for export] *)
        intros fx'' R' M'' model' HC' Hfs'. apply (Hk1 E1 fx'' R' M'' model'); [| exact HC' | exact Hfs'].
        split; [eapply env_agree_le; [exact Hag1 | exact Fle] | exact Hag1].
    + (* [comment removed for export] *)
      destruct (lin_ge0 (kn cs) [(escale 8 (EVar Av), (-1)%Z)] [(reg cs 11, 0)]) eqn:Hdead2.
      { exfalso. pose proof (lin_ge0_sound SEGS E M (kn cs) [(escale 8 (EVar Av), (-1)%Z)] [(reg cs 11, 0)] HK Hdead2) as Hl. cbn [xt_den] in Hl.
        rewrite Holu in Hl. fold n in Hl. clear -Hl Hgt. subst cap. lia. }
      rewrite mark_dead_false in Hk2.
      pose proof (galloc_facts n cap ltac:(clear -HA1 HAlo3; lia)) as (Ga1 & Ga2 & Ga3 & Ga8).
      set (g := galloc n cap) in *.
      destruct (cost_hi_sound SEGS E M (kn cs) (L1' ++ L2') ch' HK Hch') as [Hcost Hcost0].
      assert (HB : GPS.bcost E (a_vis cs) = GPS.bcost E (L1' ++ L2') + mcost (cap + 1)).
      { rewrite Hvis, !bcost_app. cbn [GPS.bcost snd]. unfold GPS.uE. rewrite Holu. subst cap. unfold mcost, GPS.MBLK, GlzIface.MBLK. clear; lia. }
      assert (HCn : GPS.bcount (a_vis cs) = GPS.bcount (L1' ++ L2') + MCNT).
      { rewrite Hvis, !bcount_app. unfold GPS.bcount, MCNT. cbn [length]. clear; lia. }
      pose proof (bcost_nonneg E (L1' ++ L2')) as HB0.
      assert (X1 : 0 <= n) by (clear -Nlo Hn0; lia).
      assert (X2 : 1 <= g) by (clear -Ga1 Nlo Hn0; lia).
      assert (X3 : n + 1 <= g) by (clear -Ga1; lia).
      assert (Hg2n : g <= 2 * n + 8) by (clear -Ga3 Hgt HA1 HAlo3; lia).
      pose proof (Z.div_mod (nlo + 8) 8 ltac:(clear; lia)) as Dv1. pose proof (Z.mod_pos_bound (nlo + 8) 8 ltac:(clear; lia)) as Md1.
      pose proof (Z.div_mod (2 * nhi + 8) 8 ltac:(clear; lia)) as Dv2. pose proof (Z.mod_pos_bound (2 * nhi + 8) 8 ltac:(clear; lia)) as Md2.
      pose proof (Z.div_mod g 8 ltac:(clear; lia)) as Dv3.
      assert (HgAlo : 8 * Z.max Alo ((nlo + 8) / 8) <= g) by (clear -Dv1 Md1 Dv3 Ga8 Ga1 Nlo HA1 Hgt; lia).
      assert (HgAhi : g <= 8 * ((2 * nhi + 8) / 8)) by (clear -Dv2 Md2 Dv3 Ga8 Hg2n Nhi; lia).
      assert (X4 : 0 <= Z.max Alo ((nlo + 8) / 8)) by (clear -HAlo3; lia).
      unfold cfgF. rewrite Hpc.
      apply (GL fx R M model (blocks_den E L1') (blocks_den E L2') (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs)) ret (bv_unsigned spw) objw d w0
               (edenot E (reg cs 12)) cap s n T (co_halt HC) (co_lazy HC) (co_mat HC) (co_fx HC) ltac:(rewrite <- HLc; exact (co_ainv HC))
               HT0 R1 Rr Re R10 R11n R12).
      * rewrite R2. reflexivity.
      * exact Hal.
      * exact Hsplo.
      * exact Hsptop.
      * exact R4.
      * exact Hstk.
      * split; [rewrite Hou; clear -Hosp'; lia|]. split; [rewrite Hou; exact Of2|]. split; [exact STO|].
        intros a Ha. apply OOWN'. rewrite Hou in Ha. exact Ha.
      * exact RD8.
      * exact Hw0u.
      * exact Hcap8.
      * clear -HA1 HAlo3. lia.
      * exact RDs.
      * exact RDd.
      * clear -Hs0 Hsle. lia.
      * exact Hgt.
      * clear -Nhi HnS X1. unfold NMAX, SMAXR in *. lia.
      * clear -HA1 HA2 HAlo3 HAhiS. unfold NMAX. lia.
      * rewrite Hou. subst cap. destruct Hdob'; [left | right]; clear -H; lia.
      * exact DST1.
      * fold g. rewrite HB. clear -Hcost Hbc' HgAhi Hgt HA1 HA2 Nhi X1. unfold mcost in *. lia.
      * clear -Hcc. unfold GPS.bcount. lia.
      * (* [comment removed for export] *)
        intros fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk Hdisj Hperm Hblk RD0' RD1' RD2' NUL Hfr Hscr Hobj' HAINV' Hh' Hlz' Hmat' Hfs' Hfds'.
        fold g in Hpblk, Hdisj, Hperm, Hblk, RD0', HAINV'.
        pose proof Hpblk as (Hplo & Hphi & Hpimg). unfold GlzConst.PTRLO in Hplo.
        rewrite Hobjw in RD0'. rewrite Hou in RD1', RD2', Hobj'. rewrite Hobjw in Ha0. pose proof (u64_range p) as Hpr.
        rewrite <- blocks_den_app in Hdisj, HAINV'.
        destruct (long_post_sound cs E fx fx' R R' M M' model mdl' ret ob ok nlo nhi
                    (Z.max Alo ((nlo + 8) / 8)) ((2 * nhi + 8) / 8) (Some (EVar Av)) bnd (L1' ++ L2')
                    (str_keep G (kn cs) ((L1' ++ L2') ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) ob ok (Some (EVar dv, escale 8 (EVar Av))) (nxt cs)) spb spk (fst (split_lit (a_brk cs))) (snd (split_lit (a_brk cs))) p g o n
                    HC Hfresh eq_refl Hobjw Hobv eq_refl Hnv Of1 Of2 X1 X2 Ga8 HgAlo HgAhi X3 Nlo X4
                    Hpblk Hpal Hblk NUL RD0' RD1' RD2' Hobj' Hdisj Hperm Hflat Hsub
                    Hsp Hspv Hsplo Hsptop (surjective_pairing _) (call_ok_top_ok nx0 G _ _ _ Hco))
          as (E' & HagA & HagB & Hfs2 & HC').
        -- (* [comment removed for export] *)
          intros E' HagE Hpv Hav.
          assert (Hne11' : edenot E' (reg cs 11) = edenot E (reg cs 11)) by (symmetry; eapply edenot_agree'; [exact HagE | exact Hnv]).
          assert (HneA' : edenot E' (escale 8 (EVar Av)) = edenot E (escale 8 (EVar Av))) by (symmetry; eapply edenot_agree'; [exact HagE | exact Holv]).
          assert (H16 : bv_unsigned (edenot E' (escale 16 (EVar Av))) = 16 * A).
          { rewrite escale_u. pose proof (escale_u E' 8 (EVar Av)) as H8. rewrite HneA', Holu in H8.
            replace (16 * bv_unsigned (edenot E' (EVar Av))) with (2 * (8 * bv_unsigned (edenot E' (EVar Av)))) by (clear; lia).
            rewrite <- (Z.mul_mod_idemp_r 2 (8 * bv_unsigned (edenot E' (EVar Av))) (2 ^ 64)) by (clear; lia). rewrite <- H8.
            rewrite Z.mod_small by (clear -HA1 HA2 HAlo3 HAhiS; lia). clear -HA1; lia. }
          assert (Hg64 : g < 2 ^ 40) by (clear -Hg2n Nhi HnS; unfold SMAXR in *; lia).
          assert (Hlen' : bv_unsigned (edenot E' (escale 8 (EVar (S (nxt cs))))) = g).
          { rewrite escale_u, Hav, u64_lit by (clear -Hg64 X2 Dv3 Ga8; lia). rewrite Z.mod_small by (clear -Hg64 X2 Dv3 Ga8; lia). clear -Dv3 Ga8; lia. }
          unfold know_ok. apply (proj2 (Forall_app _ _ _)); split.
          ++ (* [comment removed for export] *)
             unfold grow_bound in Hgb. destruct obnd as [b|].
             ** destruct (xhi2 (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
                match type of Hgb with (if ?c then _ else _) = _ => destruct c eqn:Hbc2; [|discriminate] end.
                apply andb_prop in Hbc2 as [Hlin Hbv]. injection Hgb as <-.
                apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
                pose proof (lin_ge0_sound SEGS E M (kn cs) [(b, 0)] [(eaddz (escale 2 (reg cs 11)) 8, 0)] HK Hlin) as Hl. cbn [xt_den] in Hl.
                rewrite eaddz_u, escale_u in Hl. fold n in Hl. rewrite (Z.mod_small (2 * n)) in Hl by (clear -X1 Nhi HnS; unfold SMAXR in *; lia).
                rewrite Z.mod_small in Hl by (clear -X1 Nhi HnS; unfold SMAXR in *; lia).
                pose proof (xhi2_sound SEGS E M (kn cs) b bh HK Hbh) as Hbhi.
                rewrite esub_u, Hlen'. rewrite <- (edenot_agree' (nxt cs) E E' b HagE Hbv).
                pose proof (u64_range (edenot E b)) as Hbr.
                rewrite Z.mod_small by (clear -Hbr Hl Hg2n X2; lia). clear -Hbr Hl Hg2n X2 Hbhi. lia.
             ** injection Hgb as <-. apply Forall_nil.
          ++ repeat apply Forall_cons; [| | |apply Forall_nil]; cbn [kentry_ok].
             ** rewrite esub_u, Hne11', HneA', Holu. fold n. rewrite Z.mod_small by (clear -Hgt Nhi HnS HA1 HAlo3; unfold SMAXR in *; lia).
                clear -Hgt Nhi HnS HA1 HAlo3. lia.
             ** rewrite esub_u, eaddz_u, eadd_u, Hne11', Hlen', H16. fold n.
                rewrite (Z.mod_small (n + 16 * A)) by (clear -X1 Nhi HnS HA1 HA2 HAlo3 HAhiS; unfold SMAXR in *; lia).
                rewrite (Z.mod_small (n + 16 * A + 6)) by (clear -X1 Nhi HnS HA1 HA2 HAlo3 HAhiS; unfold SMAXR in *; lia).
                change (SMAXR / 8) with (2 ^ 33). rewrite Z.mod_small by (clear -X1 X3 Ga3 Hgt Nhi HnS HA1 HA2 HAlo3 HAhiS; unfold SMAXR in *; lia).
                clear -X1 X3 Ga3 Hgt Nhi HnS HA1 HA2 HAlo3 HAhiS. lia.
             ** rewrite esub_u, eaddz_u, escale_u, Hne11', Hlen'. fold n. rewrite (Z.mod_small (2 * n)) by (clear -X1 Nhi HnS; unfold SMAXR in *; lia).
                rewrite (Z.mod_small (2 * n + 8)) by (clear -X1 Nhi HnS; unfold SMAXR in *; lia). rewrite Z.mod_small by (clear -X1 X3 Hg2n Nhi HnS; unfold SMAXR in *; lia).
                clear -X1 X3 Hg2n Nhi. lia.
        -- (* [comment removed for export] *)
          eapply (str_keep_sound E M M' (kn cs) (L1' ++ L2') (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk ob ok (Some (EVar dv, escale 8 (EVar Av))) (nxt cs)
                    HK Hflat' (co_perm HC) (co_top HC) Hsp).
          ++ pose proof (u64_range spw) as Hswr. clear -Hswr Hspv. lia.
          ++ exact (co_floor HC).
          ++ intros a Hka Hno Hnold. cbn [old_lo old_n split_lit] in Hnold. rewrite estart_SA, Z.add_0_r in Hnold. unfold elenZ in Hnold. rewrite Holu in Hnold.
             change (edenot E (EVar dv)) with d in Hnold.
             apply Hfr; [|rewrite Hou; exact Hno]. rewrite <- blocks_den_app. exact Hka.
          ++ exact Hscr.
          ++ intros a Ha. cbn [old_lo old_n split_lit]. rewrite !estart_SA, Z.add_0_r. unfold elenZ. rewrite Holu.
             change (edenot E (EVar dv)) with d. fold o.
             pose proof (u64_range (edenot E spb)) as Hsbr. unfold o in Hosc'. rewrite estart_SA in Hosc'. subst spw.
             clear -Hosc' Hdsc' Hspv Ha Hsbr Hsp80. unfold MSTK in *. split; lia.
        -- apply str_keep_vars.
        -- exact Hkept.
        -- exact Ha0.
        -- exact HFX'.
        -- eapply AINV_mono; [exact HAINV' | rewrite HB; clear -HB0 X2; unfold mcost, GlzIface.MBLK, GPS.MBLK in *; lia | rewrite HCn; clear; unfold GPS.bcount, MCNT; lia].
        -- exact Hh'.
        -- exact Hlz'.
        -- exact Hmat'.
        -- exact Hfs'.
        -- exact Hfds'.
        -- apply (Hk2 E' fx' R' M' mdl'); [split; [exact HagA | exact HagB] | exact HC' | exact Hfs'].
Qed.
End Sound.
