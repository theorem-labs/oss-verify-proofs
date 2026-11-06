(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv APrimSpec APrimLem APrimPop AFrame F_prim_popf.
Import ListNotations.
Open Scope Z_scope.

Lemma sh_off : forall A x, A mod 8 = 0 -> x mod 8 = 0 -> sh (A + x) = sh A + x / 8.
Proof. intros A x HA Hx. unfold sh. Z.div_mod_to_equations. lia. Qed.
Lemma mm16 : forall a b, b mod 16 = 0 -> (a * b) mod 16 = 0.
Proof. intros a b Hb. rewrite Z.mul_mod, Hb, Z.mul_0_r by lia. reflexivity. Qed.
Lemma sh_off8 : forall A x8, A mod 8 = 0 -> sh (A + 8 * x8) = sh A + x8.
Proof. intros A x8 HA. unfold sh. Z.div_mod_to_equations. lia. Qed.
Lemma sh_le : forall A B, A <= B -> sh A <= sh B.
Proof. intros A B H. unfold sh. Z.div_mod_to_equations. lia. Qed.

Lemma sw_exact : forall a n, a mod 32768 = 0 -> n mod 32768 = 0 -> swlo a = sh a /\ swhi a n = sh (a + n) /\ sh (a + n) = sh a + n / 8.
Proof. intros a n Ha Hn. unfold swlo, swhi, sh, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

Section R8.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
#[using="HC AO"] Lemma REG_mod8 : forall c, region AL c mod 8 = 0.
Proof.
  intros c. layout_facts AO 0%nat SPF. destruct SPF as (_ & _ & SP3 & _). unfold region.
  clear - SP3. Z.div_mod_to_equations. lia.
Qed.
#[using="HC AO"] Lemma REG_mod32768 : forall c, region AL c mod 32768 = 0.
Proof.
  intros c. pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & _). unfold region.
  clear - SPAL. Z.div_mod_to_equations. lia.
Qed.
End R8.

Section PR.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Variables (c r : Z) (k : pclass).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hr : 1 <= r <= 8.
Hypothesis WF : pclass_wf c k.
Hypothesis BUD1 : p_mu k + r * class_size c + K_MAP <= FA_OFF.
Hypothesis BUD2 : 4 * (p_nf k + (p_mu k + r * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.
Notation SZ := (class_size c).
Notation REG := (region AL c).
Notation FA := (fa_base AL c).
Notation mu' := (pop_mu k c r).
Notation newc := (pop_new k c r).

Definition pop_clear (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z =>
       (snd iv <= REG \/ REG + mu' <= fst iv)
    /\ (snd iv <= sh REG \/ sh (REG + mu') <= fst iv)
    /\ (snd iv <= pcl_addr AL c \/ pcl_addr AL c + 80 <= fst iv)) W.

#[using="Type"] Lemma pop_clear_user : forall W A n, pop_clear W -> REG <= A -> A + n <= REG + mu' -> disjoint_from W A n.
Proof.
  intros W A n F H1 H2. apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F].
  intros [lo' hi'] Hiv. cbn in Hiv |- *. lia.
Qed.
#[using="Type"] Lemma pop_clear_shadow : forall W A n, pop_clear W -> sh REG <= A -> A + n <= sh (REG + mu') -> disjoint_from W A n.
Proof.
  intros W A n F H1 H2. apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F].
  intros [lo' hi'] Hiv. cbn in Hiv |- *. lia.
Qed.
#[using="Type"] Lemma pop_clear_pcl : forall W A n, pop_clear W -> pcl_addr AL c <= A -> A + n <= pcl_addr AL c + 80 -> disjoint_from W A n.
Proof.
  intros W A n F H1 H2. apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F].
  intros [lo' hi'] Hiv. cbn in Hiv |- *. lia.
Qed.

#[using="HC AO Hc Hr WF BUD1 BUD2"] Lemma cls_open_populate : forall (m1 m' : mem) (inited : bool) (W : list (Z * Z)) (ws2 : list word) (nb nsh : nat) (jt : list byte)
    (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte),
  munch W m1 m' -> wmono asegs m1 m' -> pop_clear W ->
  rw_cells asegs m' (ri_addr AL c) (ri_cells KWL (populate k c r) j8 j64 j88 j96 j104 j112 jpad) ->
  pcl_rep AL m1 inited c k ->
  u32arr asegs m' FA (LF c (p_au k) (p_nf k + newc) ws2 (Z.to_nat newc)) ->
  4 * Z.of_nat (length ws2) = p_mfa (populate k c r) ->
  firstn (length (p_fa k)) ws2 = map wz (p_fa k) ->
  rw_cells asegs m1 (REG + p_au k) [CB nb jt] -> Z.of_nat nb = mu' - p_au k ->
  rw_cells asegs m1 (sh (REG + p_au k)) [CB nsh (repeat (Z_to_bv 8 250) nsh)] -> 8 * Z.of_nat nsh = mu' - p_au k ->
  (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m1 c v) ->
  cls_open AL m' inited c (populate k c r).
Proof.
  intros m1 m' inited W ws2 nb nsh jt j8 j64 j88 j96 j104 j112 jpad MU WM PC RIC PCL FAA LEN FX TL Hnb TSH Hnsh FCH.
  pose proof (SZ_facts c r k Hc Hr) as (CS & CS16 & RS & RS8).
  pose proof (pop_mu_facts c r k Hc Hr WF BUD1) as (M1 & M2 & M3 & M4 & M5 & _).
  pose proof (pop_new_facts c r k Hc Hr WF BUD1) as (N0 & N1 & N2 & N3).
  pose proof (populate_shape c r k) as (S_nf & S_au & S_mu & S_fa & S_cnt & S_ch & _ & _ & S_mfa).
  pose proof (populate_wf c r k Hc Hr WF BUD1 BUD2) as WF'.
  pose proof WF as WF0. unfold pclass_wf in WF0.
  destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
  pose proof (au_mod16 c r k Hc Hr WF) as AU16.
  pose proof (REG_mod8 AL AO c) as R8.
  assert (TLn : (Z.to_nat (p_nf k + newc) <= length ws2)%nat).
  { pose proof (efa_new_facts c r k (mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) (p_nf k + newc)
                  ltac:(cbn; lia) ltac:(cbn; exact MFAM) ltac:(lia) ltac:(lia)) as (F1 & _).
    rewrite <- S_mfa, <- LEN in F1. lia. }
  clear BUD2 N3 M3 GAP AUS MFAM MFA NF4.

  assert (EZ : exists z8, SZ = 8 * z8) by (exists (SZ / 8); Z.div_mod_to_equations; lia). destruct EZ as [z8 Hz8].
  assert (EA : exists a8, p_au k = 8 * a8) by (exists (p_au k / 8); Z.div_mod_to_equations; lia). destruct EA as [a8 Ha8].
  assert (EM : exists m8, mu' = 8 * m8) by (exists (mu' / 8); Z.div_mod_to_equations; lia). destruct EM as [m8 Hm8].
  assert (SZD : SZ / 8 = z8) by (rewrite Hz8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  clear CS16 AU16 M4 MUM.
  assert (NSZ : newc * SZ = 8 * (newc * z8)) by (rewrite Hz8; ring).
  assert (NZ0 : 0 <= newc * z8) by (apply Z.mul_nonneg_nonneg; lia).
  assert (N1' : newc * SZ <= mu' - p_au k) by lia.
  set (cn := Z.to_nat newc) in *. set (sn := Z.to_nat SZ). set (s8 := Z.to_nat (SZ / 8)).
  set (rest := Z.to_nat (mu' - p_au k - newc * SZ)).
  set (rest8 := Z.to_nat ((mu' - p_au k - newc * SZ) / 8)).
  assert (Hcn : Z.of_nat cn = newc) by (subst cn; lia).
  assert (Hsn : Z.of_nat sn = SZ) by (subst sn; lia).
  assert (Hs8 : Z.of_nat s8 = z8) by (subst s8; rewrite SZD; lia).
  assert (Hrest : Z.of_nat rest = mu' - p_au k - newc * SZ) by (subst rest; lia).
  assert (Hrest8 : Z.of_nat rest8 = m8 - a8 - newc * z8).
  { subst rest8. replace (mu' - p_au k - newc * SZ) with ((m8 - a8 - newc * z8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Enb : nb = (cn * sn + rest)%nat).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Hcn, Hsn, Hrest, Hnb. lia. }
  assert (Ensh : nsh = (cn * s8 + rest8)%nat).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Hcn, Hs8, Hrest8. lia. }
  rewrite Enb in TL. rewrite Ensh in TSH.
  destruct (CB_tiles _ _ _ _ _ _ TL) as [TT [jr TR]].
  destruct (CB_tiles_repeat _ _ _ _ _ _ TSH) as [ST SR].
  clear TL TSH Enb Ensh Hnb Hnsh.

  assert (SHA : forall x8, sh (REG + 8 * x8) = sh REG + x8) by (intros x8; apply sh_off8; exact R8).
  assert (SHM : sh (REG + mu') = sh REG + m8) by (rewrite Hm8; apply SHA).
  assert (SHU : sh (REG + p_au k) = sh REG + a8) by (rewrite Ha8; apply SHA).

  assert (TI : forall i : nat, (i < cn)%nat -> 0 <= Z.of_nat i * z8 /\ Z.of_nat i * z8 + z8 <= newc * z8 /\ Z.of_nat i * SZ = 8 * (Z.of_nat i * z8)).
  { intros i Hi. split; [apply Z.mul_nonneg_nonneg; lia|]. split; [| rewrite Hz8; ring].
    replace (Z.of_nat i * z8 + z8) with ((Z.of_nat i + 1) * z8) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  unfold cls_open. split; [exact WF'|]. split; [exists j8, j64, j88, j96, j104, j112, jpad; exact RIC|].
  split; [| split; [| split]].
  -
    destruct PCL as [PC1 (wsc & PA & PL & PX)]. unfold pcl_rep. rewrite S_cnt, S_ch. split.
    + eapply rw_cells_transport; [exact PC1| exact MU| exact WM|]. apply pop_clear_pcl; [exact PC| lia| cbn; lia].
    + exists wsc. split; [| split; assumption].
      eapply u32arr_transport; [exact PA| exact MU| exact WM|]. apply pop_clear_pcl; [exact PC| lia| rewrite PL; lia].
  -
    unfold fa_rep. exists (LF c (p_au k) (p_nf k + newc) ws2 (Z.to_nat newc)).
    split; [exact FAA|]. split.
    + rewrite LF_length by lia. exact LEN.
    + rewrite S_fa, length_app, carve_length. fold cn.
      rewrite (LF_firstn c (p_au k) (p_nf k + newc) ws2 (length (p_fa k)) cn) by lia.
      rewrite FX, map_app. reflexivity.
  -
    unfold tail_rep. rewrite S_au, S_mu. split.
    + exists jr. replace (REG + (p_au k + newc * SZ)) with (REG + p_au k + Z.of_nat cn * Z.of_nat sn) by lia.
      replace (Z.to_nat (mu' - (p_au k + newc * SZ))) with rest by lia.
      eapply rw_cells_transport; [exact TR| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply pop_clear_user; [exact PC| lia| lia].
    + replace (p_au k + newc * SZ) with (8 * (a8 + newc * z8)) by lia. rewrite SHA.
      replace (Z.to_nat ((mu' - 8 * (a8 + newc * z8)) / 8)) with rest8 by (subst rest8; f_equal; f_equal; lia).
      replace (sh REG + (a8 + newc * z8)) with (sh (REG + p_au k) + Z.of_nat cn * Z.of_nat s8) by lia.
      eapply rw_cells_transport; [exact SR| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply pop_clear_shadow; [exact PC| lia| lia].
  -
    intros v Hv. rewrite S_fa, S_ch in Hv. rewrite <- app_assoc in Hv. apply in_app_or in Hv.
    assert (OLD : In v (p_fa k ++ p_chunks k) -> free_chunk AL m' c v).
    { intros Hin. pose proof (proj1 (Forall_forall _ _) FB v Hin) as (V0 & V1 & _). cbv beta in V0, V1.
      eapply free_chunk_frame; [apply FCH; exact Hin| exact MU| exact WM| exact Hc| |].
      - apply pop_clear_user; [exact PC| lia| lia].
      - replace (16 * v) with (8 * (2 * v)) by lia. rewrite SHA, SZD. apply pop_clear_shadow; [exact PC| lia| lia]. }
    destruct Hv as [Hv|Hv]; [apply OLD; apply in_or_app; left; exact Hv|].
    apply in_app_or in Hv. destruct Hv as [Hv|Hv]; [| apply OLD; apply in_or_app; right; exact Hv].
    apply in_carve in Hv. destruct Hv as (i & Hi & ->). fold cn in Hi.
    pose proof (carve_val c r k Hc Hr WF i) as CV. unfold free_chunk. rewrite CV.
    destruct (TI i Hi) as (I0 & I1 & I2).
    split.
    + destruct (TT i Hi) as [j Hj]. exists j. fold sn.
      replace (REG + (p_au k + Z.of_nat i * SZ)) with (REG + p_au k + Z.of_nat i * Z.of_nat sn) by lia.
      eapply rw_cells_transport; [exact Hj| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply pop_clear_user; [exact PC| lia| lia].
    + fold s8. replace (p_au k + Z.of_nat i * SZ) with (8 * (a8 + Z.of_nat i * z8)) by lia. rewrite SHA.
      replace (sh REG + (a8 + Z.of_nat i * z8)) with (sh (REG + p_au k) + Z.of_nat i * Z.of_nat s8) by lia.
      eapply rw_cells_transport; [exact (ST i Hi)| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply pop_clear_shadow; [exact PC| lia| lia].
Qed.
End PR.

Section FCF2.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Variables (c : Z) (k : pclass).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis WF : pclass_wf c k.
Notation REG := (region AL c).

Definition carved_clear (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => (snd iv <= REG \/ REG + p_au k <= fst iv) /\ (snd iv <= sh REG \/ sh (REG + p_au k) <= fst iv)) W.

#[using="HC AO Hc WF"] Lemma free_chunks_frame : forall W m m',
  munch W m m' -> wmono asegs m m' -> carved_clear W ->
  (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m c v) ->
  forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m' c v.
Proof.
  intros W m m' MU WM CC FCH v Hin. unfold carved_clear in CC.
  pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
  pose proof WF as WF0. unfold pclass_wf in WF0.
  destruct WF0 as (_ & _ & _ & _ & _ & _ & AU & _ & _ & AUS & _ & _ & FB & _).
  pose proof (proj1 (Forall_forall _ _) FB v Hin) as (V0 & V1 & _). cbv beta in V0, V1.
  pose proof (REG_mod8 AL AO c) as R8.
  assert (EZ : exists z8, class_size c = 8 * z8) by (exists (class_size c / 8); Z.div_mod_to_equations; lia). destruct EZ as [z8 Hz8].
  assert (EA : exists a8, p_au k = 8 * a8).
  { exists (p_au k / 8). assert (X : p_au k mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (class_size c)); apply Z.mod_divide; lia. }
    Z.div_mod_to_equations. lia. }
  destruct EA as [a8 Ha8].
  assert (SZD : class_size c / 8 = z8) by (rewrite Hz8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  clear CS16 AUS FB.
  eapply free_chunk_frame; [apply FCH; exact Hin| exact MU| exact WM| exact Hc| |].
  - apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CC]. intros [lo' hi'] Hiv. cbn in Hiv |- *. lia.
  - replace (16 * v) with (8 * (2 * v)) by lia. rewrite (sh_off8 _ _ R8), SZD.
    rewrite Ha8, (sh_off8 _ _ R8) in CC.
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CC]. intros [lo' hi'] Hiv. cbn in Hiv |- *. lia.
Qed.
End FCF2.
