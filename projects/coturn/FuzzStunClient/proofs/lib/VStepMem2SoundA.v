(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VState2 VStepMem2 VGamma2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma frame_mod_mem0_ext (m0 m0' mem : word -> option byte) rs :
  (forall a, m0 a = m0' a) -> frame_mod m0 mem rs -> frame_mod m0' mem rs.
Proof.
  intros Heq [H1 H2]. split.
  - intros a Ha. rewrite <- Heq. apply H1, Ha.
  - intros x Hx. apply H2. rewrite Heq. exact Hx.
Qed.

Lemma gamma_mem0_ext SEGS P E (m0 m0' : word -> option byte) A nu regs mem :
  (forall a, m0 a = m0' a) ->
  gamma SEGS P E m0 A nu regs mem -> gamma SEGS P E m0' A nu regs mem.
Proof.
  intros Heq (HE&HM&REST). split; [exact HE|]. split; [|exact REST].
  destruct HM as (M1&M2&M3&M4). split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  eapply frame_mod_mem0_ext; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fake_size_eq cid : 0 <= cid -> fake_size cid = 64 * 2 ^ cid.
Proof. intros H. unfold fake_size. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma fake_size_bounds cid : 0 <= cid <= 4 -> 64 <= fake_size cid <= 1024.
Proof.
  intros H. rewrite fake_size_eq by lia.
  assert (2 ^ 0 <= 2 ^ cid) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ cid <= 2 ^ 4) by (apply Z.pow_le_mono_r; lia).
  replace (2 ^ 0) with 1 in * by reflexivity. replace (2 ^ 4) with 16 in * by reflexivity. lia.
Qed.

Lemma fake_size_mod64 cid : 0 <= cid -> fake_size cid mod 64 = 0.
Proof. intros H. rewrite fake_size_eq by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Lemma class_span cid : 0 <= cid <= 14 -> fake_size cid * fs_nframes cid = 2 ^ 20.
Proof.
  intros H. rewrite fake_size_eq by lia. unfold fs_nframes.
  replace 64 with (2 ^ 6) by reflexivity. rewrite <- !Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma frame_in_class fs cid pos :
  0 <= cid -> cid <= 14 -> 0 <= pos < fs_nframes cid ->
  fs + FS_FRAMES + cid * 2 ^ 20 <= frame_addr fs cid pos
  /\ frame_addr fs cid pos + fake_size cid <= fs + FS_FRAMES + (cid + 1) * 2 ^ 20.
Proof.
  intros H0 H1 Hp. unfold frame_addr, FS_SSL. pose proof (class_span cid ltac:(lia)) as SP.
  pose proof (fake_size_eq cid H0). assert (0 < 2 ^ cid) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= fake_size cid * pos) by nia.
  assert (fake_size cid * pos + fake_size cid <= fake_size cid * fs_nframes cid) by nia.
  nia.
Qed.

Lemma frames_disjoint fs c1 p1 c2 p2 :
  0 <= c1 <= 14 -> 0 <= p1 < fs_nframes c1 -> 0 <= c2 <= 14 -> 0 <= p2 < fs_nframes c2 ->
  (c1 <> c2 \/ p1 <> p2) ->
  frame_addr fs c1 p1 + fake_size c1 <= frame_addr fs c2 p2 \/ frame_addr fs c2 p2 + fake_size c2 <= frame_addr fs c1 p1.
Proof.
  intros Hc1 Hp1 Hc2 Hp2 NE.
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - assert (p1 <> p2) by lia. unfold frame_addr.
    pose proof (fake_size_eq c1 ltac:(lia)). assert (0 < 2 ^ c1) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.lt_ge_cases p1 p2).
    + left. assert (fake_size c1 * p1 + fake_size c1 <= fake_size c1 * p2) by nia. lia.
    + right. assert (fake_size c1 * p2 + fake_size c1 <= fake_size c1 * p1) by nia. lia.
  - pose proof (frame_in_class fs c1 p1 ltac:(lia) ltac:(lia) Hp1) as [A1 B1].
    pose proof (frame_in_class fs c2 p2 ltac:(lia) ltac:(lia) Hp2) as [A2 B2].
    destruct (Z.lt_ge_cases c1 c2).
    + left. assert ((c1 + 1) * 2 ^ 20 <= c2 * 2 ^ 20) by nia. lia.
    + right. assert ((c2 + 1) * 2 ^ 20 <= c1 * 2 ^ 20) by nia. lia.
Qed.

Lemma frame_addr_inj fs c1 p1 c2 p2 :
  0 <= c1 <= 14 -> 0 <= p1 < fs_nframes c1 -> 0 <= c2 <= 14 -> 0 <= p2 < fs_nframes c2 ->
  frame_addr fs c1 p1 = frame_addr fs c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
  intros Hc1 Hp1 Hc2 Hp2 EQ.
  destruct (Z.eq_dec c1 c2) as [E1|N1]; [destruct (Z.eq_dec p1 p2) as [E2|N2]; [auto|]|];
  exfalso; pose proof (fake_size_bounds c1) as B1; pose proof (fake_size_bounds c2) as B2.
  - destruct (frames_disjoint fs c1 p1 c2 p2 Hc1 Hp1 Hc2 Hp2 ltac:(lia)); rewrite ?fake_size_eq in * by lia;
      assert (0 < 2 ^ c1) by (apply Z.pow_pos_nonneg; lia); assert (0 < 2 ^ c2) by (apply Z.pow_pos_nonneg; lia); lia.
  - destruct (frames_disjoint fs c1 p1 c2 p2 Hc1 Hp1 Hc2 Hp2 ltac:(lia)); rewrite ?fake_size_eq in * by lia;
      assert (0 < 2 ^ c1) by (apply Z.pow_pos_nonneg; lia); assert (0 < 2 ^ c2) by (apply Z.pow_pos_nonneg; lia); lia.
Qed.

Lemma frame_addr_mod64 fs cid pos : fs mod 4096 = 0 -> 0 <= cid -> frame_addr fs cid pos mod 64 = 0.
Proof.
  intros Hfs Hc. unfold frame_addr, FS_FRAMES, FS_SSL. rewrite fake_size_eq by lia.
  replace (fs + (4096 + 32768) + cid * 2 ^ 20 + 64 * 2 ^ cid * pos)
    with (fs + 64 * (576 + cid * 2 ^ 14 + 2 ^ cid * pos)) by lia.
  rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Z.add_0_r by lia.
  rewrite Z.mod_mod by lia. apply Z.mod_divide; [lia|].
  apply Z.mod_divide in Hfs; [|lia]. destruct Hfs as [k ->]. exists (k * 64). lia.
Qed.

(* [comment removed for export] *)
Lemma fs_flags_off_S n : fs_flags_off_nat (S n) = fs_flags_off_nat n + fs_nframes (Z.of_nat n).
Proof. reflexivity. Qed.

Lemma fs_flags_off_step cid : 0 <= cid -> fs_flags_off (cid + 1) = fs_flags_off cid + fs_nframes cid.
Proof.
  intros H. unfold fs_flags_off. replace (Z.to_nat (cid + 1)) with (S (Z.to_nat cid)) by lia.
  rewrite fs_flags_off_S, Z2Nat.id by lia. reflexivity.
Qed.

Lemma fs_nframes_pos cid : cid <= 14 -> 0 < fs_nframes cid.
Proof. intros H. unfold fs_nframes. apply Z.pow_pos_nonneg; lia. Qed.

Lemma fs_flags_off_mono c1 c2 : 0 <= c1 -> c1 < c2 -> c2 <= 14 -> fs_flags_off c1 + fs_nframes c1 <= fs_flags_off c2.
Proof.
  intros H0 Hlt H14.
  assert (GEN : forall n : nat, Z.of_nat n <= c2 - c1 - 1 -> fs_flags_off c1 + fs_nframes c1 <= fs_flags_off (c1 + 1 + Z.of_nat n)).
  { induction n as [|n IH]; intros Hn.
    - rewrite Z.add_0_r, fs_flags_off_step by lia. lia.
    - replace (c1 + 1 + Z.of_nat (S n)) with ((c1 + 1 + Z.of_nat n) + 1) by lia.
      rewrite fs_flags_off_step by lia. pose proof (fs_nframes_pos (c1 + 1 + Z.of_nat n) ltac:(lia)).
      specialize (IH ltac:(lia)). lia. }
  specialize (GEN (Z.to_nat (c2 - c1 - 1)) ltac:(lia)).
  replace (c1 + 1 + Z.of_nat (Z.to_nat (c2 - c1 - 1))) with c2 in GEN by lia. exact GEN.
Qed.

Lemma flag_addr_range fs cid pos :
  0 <= cid <= 4 -> 0 <= pos < fs_nframes cid ->
  fs + FS_FLAGS <= flag_addr fs cid pos < fs + FS_FRAMES.
Proof.
  intros Hc Hp. unfold flag_addr, FS_FLAGS, FS_FRAMES.
  pose proof (fs_flags_off_mono cid 5 ltac:(lia) ltac:(lia) ltac:(lia)) as M.
  replace (fs_flags_off 5) with 31744 in M by reflexivity.
  assert (0 <= fs_flags_off cid).
  { destruct (Z.eq_dec cid 0) as [->|]; [replace (fs_flags_off 0) with 0 by reflexivity; lia|].
    pose proof (fs_flags_off_mono 0 cid ltac:(lia) ltac:(lia) ltac:(lia)) as M0.
    replace (fs_flags_off 0) with 0 in M0 by reflexivity. pose proof (fs_nframes_pos 0 ltac:(lia)). lia. }
  lia.
Qed.

Lemma flag_addr_inj fs c1 p1 c2 p2 :
  0 <= c1 <= 4 -> 0 <= p1 < fs_nframes c1 -> 0 <= c2 <= 4 -> 0 <= p2 < fs_nframes c2 ->
  flag_addr fs c1 p1 = flag_addr fs c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
  intros Hc1 Hp1 Hc2 Hp2 EQ. unfold flag_addr in EQ.
  destruct (Z.lt_trichotomy c1 c2) as [L|[E|G]].
  - pose proof (fs_flags_off_mono c1 c2 ltac:(lia) L ltac:(lia)). lia.
  - subst. lia.
  - pose proof (fs_flags_off_mono c2 c1 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Section A.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Lemma PO1 : params_ok SEGS P1.
  Proof. exact (proj1 PO2). Qed.
  (* [comment removed for export] *)
  Lemma PO2_shoff : 0 <= vp_shoff P.
  Proof. pose proof PO2 as (_ & H & _). exact H. Qed.
  Lemma PO2_frame16 : vp_frame (p1 P) mod 16 = 0.
  Proof. pose proof PO2 as (_ & _ & H & _). exact H. Qed.
  Lemma PO2_kcells : forall a w v, In (a, (w, v)) (vp_kcells P) ->
          0 <= a /\ 0 < w /\ a + w <= vp_splo (p1 P) - vp_frame (p1 P)
          /\ (forall c, In c (vp_fcells (p1 P)) -> a + w <= fst c \/ fst c + snd c <= a).
  Proof. pose proof PO2 as (_ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_kruns : forall c, In c (vp_kruns P) ->
          forall f, In f (vp_fcells (p1 P)) -> fst (snd c) <= fst f \/ fst f + snd f <= fst c.
  Proof. pose proof PO2 as (_ & _ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_wrgn : forall i lo hi, In (i, (lo, hi)) (vp_wrgn P) -> 0 <= i < 8 /\ lo <= hi.
  Proof. pose proof PO2 as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_fs : vp_fs P <> None -> vp_shoff P = 0x7fff8000 /\ forall c, In c (vp_fcells (p1 P)) -> fst c + snd c <= 0x7fff7000.
  Proof. pose proof PO2 as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_nozones : vp_fs P = None -> vp_fzones P = [].
  Proof. pose proof PO2 as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_zsyms : forallb fzone_syms_ok (vp_fzones P) = true.
  Proof. pose proof PO2 as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma PO2_img : vp_fs P <> None -> 0 <= vp_imgend P <= 0x7fff7000
          /\ (forall c, In c (vp_fcells (p1 P)) -> fst c + snd c <= vp_imgend P)
          /\ (forall a w v, In (a, (w, v)) (vp_kcells P) -> a + w <= vp_imgend P \/ 0x7fff8000 <= a)
          /\ (forall lo hi, In (lo, hi) (vp_pristine (p1 P)) -> hi <= vp_imgend P).
  Proof. pose proof PO2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Lemma fs_range len ssl : env_ok2 P E -> vp_fs P = Some (len, ssl) ->
    0 <= e_fs E /\ e_fs E + len <= HIGH_MEM_END /\ vp_imgend P <= e_fs E /\ off_band (e_fs E) len.
  Proof.
    intros HE Hfs. pose proof HE as (_ & _ & HF & _). unfold env_fs in HF. rewrite Hfs in HF.
    destruct HF as (_ & Hob & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIE).
    destruct (PO2_img ltac:(rewrite Hfs; discriminate)) as (IE0 & _). destruct Hob as [Hf0 Hob]. repeat split; auto; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma in_zoneb_spec a z : in_zoneb E a z = true <-> in_zone E a z.
  Proof. unfold in_zoneb, in_zone. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

  Lemma in_rw_zones_in a : in_rw_zones P E a = true -> exists z, In z (vp_fzones P) /\ fz_rw z = true /\ in_zone E a z.
  Proof.
    unfold in_rw_zones, rw_zones. rewrite existsb_exists. intros (z & Hz & Hb).
    apply filter_In in Hz as [Hin Hrw]. apply in_zoneb_spec in Hb. eauto.
  Qed.

  Lemma in_any_zone_in a : in_any_zone P E a = true -> exists z, In z (vp_fzones P) /\ in_zone E a z.
  Proof.
    unfold in_any_zone. rewrite existsb_exists. intros (z & Hz & Hb). apply in_zoneb_spec in Hb. eauto.
  Qed.

  Lemma in_rng_Z a b n : in_rng (wordZ a) (wordZ b) n -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a < b + n.
  Proof. unfold in_rng. intros [H1 H2] Ha Hb. rewrite !u_wordZ in H1, H2 by lia. lia. Qed.

  (* [comment removed for export] *)
  Lemma outside_unit_regions a :
    env_ok P1 E1 -> 0 <= a < 2 ^ 64 ->
    ~ (e_sp0 E1 - vp_frame P1 <= a < e_sp0 E1) ->
    (forall c, In c (vp_fcells P1) -> ~ (fst c <= a < fst c + snd c)) ->
    outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Ha Hfr Hfc.
    pose proof PO1 as (POfr & POsphi & _ & POfc & POwc & POws & _).
    destruct HE as (_ & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & Hfrsp).
    unfold unit_regions. apply outside_app. split.
    - (* [comment removed for export] *)
      assert (G : forall l, (forall r, In r l -> - vp_frame P1 <= fst r /\ snd r <= 0) ->
                 outside (wordZ a) (map (fun r : Z * Z => (wordZ (e_sp0 E1 + fst r), snd r - fst r)) l)).
      { induction l as [|[lo hi] t IH]; simpl; intros Hl; [exact I|]. split.
        - intros Hr. pose proof (Hl (lo, hi) (or_introl eq_refl)) as W. simpl in W.
          destruct (Z.le_gt_cases lo 0) as [Hlo|Hlo]; [|exfalso; destruct Hr as [Hr1 Hr2]; lia].
          assert (Rb : 0 <= e_sp0 E1 + lo < 2 ^ 64) by (unfold P1, E1 in *; lia).
          pose proof (in_rng_Z _ _ _ Hr Ha Rb) as X. apply Hfr. unfold P1, E1 in *. lia.
        - apply IH. intros r Hr'. apply Hl. auto. }
      apply G. exact POws.
    - (* [comment removed for export] *)
      unfold cells_regions.
      assert (G : forall l, (forall c, In c l -> exists f, In f (vp_fcells P1) /\ fst f <= fst c /\ fst c + snd c <= fst f + snd f) ->
                 outside (wordZ a) (map (fun c : Z * Z => (wordZ (fst c), snd c)) l)).
      { induction l as [|c t IH]; simpl; intros Hl; [exact I|]. split.
        - intros Hr. destruct (Hl c (or_introl eq_refl)) as (f & Hf & F1 & F2).
          pose proof (POfc f Hf) as (F0 & F3 & _).
          destruct (Z.le_gt_cases (snd c) 0) as [Hn|Hn]; [exfalso; destruct Hr as [Hr1 Hr2]; lia|].
          assert (Rb : 0 <= fst c < 2 ^ 64) by (unfold P1, E1 in *; lia).
          pose proof (in_rng_Z _ _ _ Hr Ha Rb) as X. apply (Hfc f Hf). lia.
        - apply IH. intros c' Hc'. apply Hl. auto. }
      apply G. exact POwc.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma env2_env1 : env_ok2 P E -> env_ok P1 E1.
  Proof. intros H; exact (proj1 H). Qed.

  Lemma zone_byte_outside z a :
    env_ok2 P E -> In z (vp_fzones P) -> in_zone E a z -> outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Hz Ha. pose proof HE as (HE1 & _ & _ & [Zwf Zap] & _).
    destruct (Zwf z Hz) as (Z0 & Z1 & Z2). destruct (Zap z a Hz Ha) as (A1 & A2 & _).
    apply outside_unit_regions; auto. unfold in_zone in Ha. lia.
  Qed.

  Lemma rw_zone_byte_outside a :
    env_ok2 P E -> in_rw_zones P E a = true -> outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Ha. destruct (in_rw_zones_in _ Ha) as (z & Hz & _ & Hin). eapply zone_byte_outside; eauto.
  Qed.

  Lemma any_zone_byte_outside a :
    env_ok2 P E -> in_any_zone P E a = true -> outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Ha. destruct (in_any_zone_in _ Ha) as (z & Hz & Hin). eapply zone_byte_outside; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_same_outside mem mem' R a n :
    frame_mod mem mem' R -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat n -> outside (wordZ (a + i)) R) ->
    rdn SEGS mem' (wordZ a) n = rdn SEGS mem (wordZ a) n.
  Proof.
    intros FM Ha Hn Ho.
    destruct n as [|n']. { reflexivity. }
    apply (frame_mod_rdn SEGS mem mem' R (S n') (wordZ a) FM).
    - intros i Hi. unfold wordZ. rewrite u_wordZ. 2:{ lia. } apply Ho. lia.
    - unfold wordZ. rewrite u_wordZ. lia. lia.
  Qed.

  Lemma rdn1_same_outside mem mem' R a :
    frame_mod mem mem' R -> 0 <= a < 2 ^ 64 -> outside (wordZ a) R ->
    rdn SEGS mem' (wordZ a) 1 = rdn SEGS mem (wordZ a) 1.
  Proof.
    intros FM Ha Ho. apply (rdn_same_outside mem mem' R a 1%nat FM); [lia|simpl; lia|].
    intros i Hi. replace (a + i) with a by (simpl in Hi; lia). exact Ho.
  Qed.

  Lemma zpatch_same mem mem' :
    env_ok2 P E -> frame_mod mem mem' (unit_regions P1 E1) ->
    forall a, zpatch P E mem0 mem' a = zpatch P E mem0 mem a.
  Proof.
    intros HE FM a. unfold zpatch. destruct (in_rw_zones P E (bv_unsigned a)) eqn:Z; [|reflexivity].
    pose proof (rw_zone_byte_outside _ HE Z) as Ho. rewrite wordZ_u in Ho. exact (frame_mod_byte _ _ _ _ FM Ho).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fs_nframes_le cid : 0 <= cid -> 0 <= fs_nframes cid <= 16384.
  Proof.
    intros H. unfold fs_nframes.
    destruct (Z.le_gt_cases cid 14).
    - replace 16384 with (2 ^ 14) by reflexivity. split; [apply Z.pow_nonneg; lia|]. apply Z.pow_le_mono_r; lia.
    - rewrite Z.pow_neg_r by lia. lia.
  Qed.

  Lemma fs_flags_off_bound cid : 0 <= cid <= 4 -> 0 <= fs_flags_off cid <= 30720.
  Proof.
    intros H. unfold fs_flags_off.
    assert (E0 : cid = 0 \/ cid = 1 \/ cid = 2 \/ cid = 3 \/ cid = 4) by lia.
    destruct E0 as [E0|[E0|[E0|[E0|E0]]]]; rewrite E0;
      [ replace (fs_flags_off_nat (Z.to_nat 0)) with 0 by reflexivity
      | replace (fs_flags_off_nat (Z.to_nat 1)) with 16384 by reflexivity
      | replace (fs_flags_off_nat (Z.to_nat 2)) with 24576 by reflexivity
      | replace (fs_flags_off_nat (Z.to_nat 3)) with 28672 by reflexivity
      | replace (fs_flags_off_nat (Z.to_nat 4)) with 30720 by reflexivity ]; lia.
  Qed.

  Lemma fs_byte_outside len ssl a :
    env_ok2 P E -> vp_fs P = Some (len, ssl) -> e_fs E <= a < e_fs E + len ->
    outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Hfs Ha. pose proof HE as (HE1 & _ & HF & _).
    unfold env_fs in HF. rewrite Hfs in HF. destruct HF as (_ & Hlo & Hhi & _ & _ & _ & _ & Hapart & _ & _ & _ & _ & _ & _ & _ & HIE).
    pose proof PO2_fs as FL.
    destruct (FL ltac:(rewrite Hfs; discriminate)) as [_ FCL].
    destruct (PO2_img ltac:(rewrite Hfs; discriminate)) as (_ & FCI & _).
    destruct (PO2_img ltac:(rewrite Hfs; discriminate)) as (IE0 & _).
    apply outside_unit_regions; auto.
    - unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END in *. lia.
    - unfold P1, E1 in *. lia.
    - intros c Hc X. specialize (FCI c Hc). lia.
  Qed.

  Lemma flag_byte_outside len ssl cid pos :
    env_ok2 P E -> vp_fs P = Some (len, ssl) -> 0 <= cid <= 4 -> 0 <= pos < fs_nframes cid ->
    outside (wordZ (flag_addr (e_fs E) cid pos)) (unit_regions P1 E1)
    /\ e_fs E <= flag_addr (e_fs E) cid pos < e_fs E + len.
  Proof.
    intros HE Hfs Hc Hp.
    pose proof HE as (_ & _ & HF & _). unfold env_fs in HF. rewrite Hfs in HF. destruct HF as (_ & _ & _ & _ & Hlen & _).
    pose proof (fs_flags_off_bound cid Hc). pose proof (fs_nframes_le cid ltac:(lia)).
    assert (R : e_fs E <= flag_addr (e_fs E) cid pos < e_fs E + len).
    { unfold flag_addr, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia. }
    split; [|exact R]. eapply fs_byte_outside; eauto.
  Qed.

  Lemma shadow_byte_outside a :
    env_ok2 P E -> vp_fs P <> None -> vp_shoff P <= a < HIGH_MEM_BEG ->
    outside (wordZ a) (unit_regions P1 E1).
  Proof.
    intros HE Hfs Ha. pose proof HE as (HE1 & _ & HF & _).
    unfold env_fs in HF. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|congruence].
    destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
    pose proof PO2_fs as FL.
    destruct (FL ltac:(rewrite Efs; discriminate)) as [SH FCL].
    pose proof PO2_shoff as SH0.
    apply outside_unit_regions; auto.
    - unfold HIGH_MEM_BEG in *. lia.
    - unfold P1, E1 in *. lia.
    - intros c Hc X. specialize (FCL c Hc). lia.
  Qed.

  Lemma krun_byte_outside c x :
    env_ok2 P E -> In c (vp_kruns P) -> fst c <= x < fst (snd c) ->
    outside (wordZ x) (unit_regions P1 E1).
  Proof.
    intros HE Hc Hx. pose proof HE as (HE1 & _ & _ & _ & [_ KR]).
    destruct (KR c x Hc Hx) as (XR & _ & NF).
    pose proof PO2_kruns as KP. destruct c as [lo [hi b]]. simpl in *.
    apply outside_unit_regions; auto.
    intros f Hf X. destruct (KP _ Hc f Hf); simpl in *; lia.
  Qed.

  Lemma kcell_byte_outside c x :
    env_ok2 P E -> In c (vp_kcells P) -> fst c <= x < fst c + fst (snd c) ->
    outside (wordZ x) (unit_regions P1 E1).
  Proof.
    intros HE Hc Hx. pose proof HE as (HE1 & _ & _ & _ & [KC _]).
    destruct (KC c x Hc Hx) as [_ NF].
    pose proof PO2_kcells as KP. destruct c as [a [w v]]. simpl in *.
    destruct (KP a w v Hc) as (A0 & W0 & AW & APART).
    pose proof PO1 as (POfr & POsphi & _). destruct HE1 as (_ & Hsp & _).
    apply outside_unit_regions; auto.
    - destruct HE as (HE1' & _). exact HE1'.
    - unfold P1, E1 in *. lia.
    - intros f Hf X. destruct (APART f Hf); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fix_val2_fixed s z : fix_val2 E s = Some z -> (s <= 75)%positive.
  Proof.
    unfold fix_val2. destruct (fix_val (ev1 E) s) eqn:F.
    - intros _. pose proof (fix_val_fixed _ _ _ F). unfold LAST_FIXED in *. lia.
    - unfold SP8, DATA8, FSB, FS8.
      destruct (Pos.eqb_spec s 64); [intros; lia|]. destruct (Pos.eqb_spec s 65); [intros; lia|].
      destruct (Pos.eqb_spec s 66); [intros; lia|]. destruct (Pos.eqb_spec s 67); [intros; lia|].
      destruct (Pos.leb_spec 19 s); destruct (Pos.leb_spec s 26); simpl; intros Hx; try discriminate. lia.
  Qed.

  Lemma gamma_fix2_ext b nu nu' : (75 < b)%positive -> ext b nu nu' -> gamma_fix2 E nu -> gamma_fix2 E nu'.
  Proof.
    intros Hb X HF s z Hs. rewrite X; [exact (HF _ _ Hs)|]. pose proof (fix_val2_fixed _ _ Hs) as Hle. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rt_byte_outside a w x :
    env_ok2 P E -> rt_apart P E a w -> a <= x < a + w -> 0 <= x < 2 ^ 64 -> outside (wordZ x) (unit_regions P1 E1).
  Proof.
    intros HE RA Hx X64. destruct (RA x Hx) as (_ & NF & NC). apply outside_unit_regions; auto. exact (proj1 HE).
  Qed.

  Lemma rt_cell_frame mem mem' a w v :
    env_ok2 P E -> rt_cell SEGS P E mem a w v -> frame_mod mem mem' (unit_regions P1 E1) -> rt_cell SEGS P E mem' a w v.
  Proof.
    intros HE (A0 & W0 & AW & RA & RD) FM. split; [exact A0|]. split; [exact W0|]. split; [exact AW|]. split; [exact RA|].
    rewrite <- RD. apply (rdn_same_outside mem mem' _ a (Z.to_nat w) FM); [lia|rewrite Z2Nat.id; lia|].
    intros i Hi. apply (rt_byte_outside a w); auto; rewrite Z2Nat.id in Hi; lia.
  Qed.

  Lemma rt_readable_frame mem mem' a w :
    env_ok2 P E -> rt_readable SEGS P E mem a w -> frame_mod mem mem' (unit_regions P1 E1) -> rt_readable SEGS P E mem' a w.
  Proof.
    intros HE (A0 & AW & RA & RD) FM. split; [exact A0|]. split; [exact AW|]. split; [exact RA|].
    intros i Hi. destruct (RD i Hi) as [b Hb]. exists b. rewrite <- Hb.
    apply (rdn1_same_outside mem mem' _ _ FM); [lia|]. apply (rt_byte_outside a w); auto; lia.
  Qed.

  Lemma rtctx_frame mem mem' :
    env_ok2 P E -> rtctx_ok SEGS P E mem -> frame_mod mem mem' (unit_regions P1 E1) -> rtctx_ok SEGS P E mem'.
  Proof.
    intros HE RT FM. unfold rtctx_ok in *. destruct (vp_fs P); [|exact I].
    destruct RT as (tsd & ctx & thr & db & beg & C1 & C2 & C3 & C4 & C5 & N5 & C6 & N6 & R7 & C8 & N8 & N8' & C9 & N9).
    exists tsd, ctx, thr, db, beg.
    destruct N9 as [N9 N9'].
    repeat match goal with |- _ /\ _ => split end;
      try (eapply rt_cell_frame; eassumption); try (eapply rt_readable_frame; eassumption); assumption.
  Qed.

  #[using="PO2"] Lemma MC2_frame mem mem' :
    env_ok2 P E -> MC2 SEGS P E mem0 mem -> frame_mod mem mem' (unit_regions P1 E1) -> MC2 SEGS P E mem0 mem'.
  Proof.
    intros HE (K & Zo & DS & LF & RT & KR) FM. split; [|split; [|split; [|split; [|split; [eapply rtctx_frame; eauto|]]]]].
    - (* [comment removed for export] *)
      intros a w v Hin. destruct (K a w v Hin) as (A0 & W0 & AW & bs & Hr & Hv). split; [lia|]. split; [lia|]. split; [lia|].
      exists bs. split; [|exact Hv]. rewrite <- Hr. apply (rdn_same_outside mem mem' _ a (Z.to_nat w) FM); [lia| rewrite Z2Nat.id; lia|].
      intros i Hi. apply (kcell_byte_outside (a, (w, v)) (a + i)); auto. simpl. rewrite Z2Nat.id in Hi; lia.
    - (* [comment removed for export] *)
      intros z a Hz Ha. destruct (Zo z a Hz Ha) as [[b Hb] Hw].
      pose proof HE as (_ & _ & _ & [Zwf _] & _). destruct (Zwf z Hz) as (Z0 & Z1 & Z2). unfold in_zone in Ha.
      split.
      + exists b. rewrite <- Hb. apply (rdn1_same_outside mem mem' _ a FM); [lia|]. eapply zone_byte_outside; eauto; unfold in_zone; lia.
      + intros Hrw. eapply frame_mod_store_ok; eauto.
    - (* [comment removed for export] *)
      intros Hal Hfs. destruct (DS Hal Hfs) as (D1 & D2 & D3).
      pose proof HE as (HE1 & _ & HF & _). unfold env_fs in HF.
      destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|congruence].
      destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & Hdat & _).
      pose proof PO2_fs as FL. destruct (FL ltac:(rewrite Efs; discriminate)) as [SH _].
      destruct HE1 as (_ & _ & Hsz & Hd0 & Hdpos & _).
      split.
      + intros g Hg. destruct (D1 g Hg) as (k & Hk & K1 & K2). exists k. split; [|auto].
        rewrite <- Hk. apply (rdn1_same_outside mem mem' _ _ FM).
        * unfold shadow_byte. unfold HIGH_MEM_BEG, HIGH_MEM_END, E1 in *.
          assert (0 <= e_data (ev1 E) / 8) by (apply Z.div_pos; lia).
          assert (e_data (ev1 E) / 8 <= (2 ^ 47 - 64) / 8) by (apply Z.div_le_mono; lia). lia.
        * apply shadow_byte_outside; auto; [congruence|]. unfold shadow_byte, HIGH_MEM_BEG, HIGH_MEM_END, E1 in *.
          assert (0 <= e_data (ev1 E) / 8) by (apply Z.div_pos; lia).
          assert (e_data (ev1 E) / 8 <= (2 ^ 47 - 64) / 8) by (apply Z.div_le_mono; lia). lia.
      + split.
        * intros a Ha Hpos. destruct (D2 a Ha Hpos) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD1 HD2].
          assert (R : vp_shoff P <= a < HIGH_MEM_BEG).
          { unfold shadow_byte, HIGH_MEM_BEG, HIGH_MEM_END, E1 in *.
            assert (2 <= e_data (ev1 E) / 8) by (apply Z.div_le_lower_bound; lia).
            assert ((e_data (ev1 E) + e_size (ev1 E) - 1) / 8 <= (2 ^ 47 - 65) / 8) by (apply Z.div_le_mono; (ltac2:(LK.k [@D3; @Hsz; @Hdpos; @Hdat; @Hpos; @Hd0]); lia)). lia. }
          apply (rdn1_same_outside mem mem' _ _ FM); [unfold HIGH_MEM_BEG in *; pose proof PO2_shoff; lia|].
          apply shadow_byte_outside; auto. congruence.
        * intros Hpos a Ha. destruct (D3 Hpos a Ha) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD1 HD2].
          assert (R : vp_shoff P <= a < HIGH_MEM_BEG).
          { unfold shadow_byte, HIGH_MEM_BEG, HIGH_MEM_END, E1 in *.
            pose proof (Z.div_mod (vp_shoff P + e_data (ev1 E) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (vp_shoff P + e_data (ev1 E) / 8) 8 ltac:(lia)).
            pose proof (Z.div_mod (vp_shoff P + (e_data (ev1 E) + e_size (ev1 E) - 1) / 8) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (vp_shoff P + (e_data (ev1 E) + e_size (ev1 E) - 1) / 8) 8 ltac:(lia)).
            assert (2 <= e_data (ev1 E) / 8) by (apply Z.div_le_lower_bound; (ltac2:(LK.k [@D3; @Hsz; @Hdpos; @Hdat; @Hpos; @H0; @H2; @Hd0]); lia)).
            assert ((e_data (ev1 E) + e_size (ev1 E) - 1) / 8 <= (2 ^ 47 - 65) / 8) by (apply Z.div_le_mono; (ltac2:(LK.k [@D3; @Hsz; @Hdpos; @Hdat; @Hpos; @H0; @H2; @Hd0]); lia)).
            pose proof PO2_shoff. (ltac2:(LK.k [@D3; @Hsz; @Hd0; @Hdpos; @Hdat; @SH; @Hpos; @Ha; @HD1; @HD2; @H0; @H2; @H3]); lia). }
          apply (rdn1_same_outside mem mem' _ _ FM); [unfold HIGH_MEM_BEG in *; pose proof PO2_shoff; lia|].
          apply shadow_byte_outside; auto. congruence.
    - (* [comment removed for export] *)
      intros cp Hcp. destruct (LF cp Hcp) as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite <- Hb.
      pose proof HE as (_ & _ & HF & _). unfold env_fs in HF.
      destruct (vp_fs P) as [[len ssl]|] eqn:Efs.
      + destruct HF as (_ & Hlo & Hhi & _ & _ & HV & _). rewrite Forall_forall in HV. destruct (HV cp Hcp) as [C1 C2].
        destruct (flag_byte_outside len ssl (fst cp) (snd cp) HE Efs C1 C2) as [O R].
        pose proof (fs_range len ssl HE Efs) as (F0 & _).
        apply (rdn1_same_outside mem mem' _ _ FM); [|exact O].
        unfold HIGH_MEM_BEG, HIGH_MEM_END in *. lia.
      + destruct HF as [HL _]. rewrite HL in Hcp. destruct Hcp.
    - (* [comment removed for export] *)
      intros lo hi b Hin. destruct (KR lo hi b Hin) as (L0 & H64 & Hb). split; [lia|]. split; [lia|].
      intros a Ha. destruct (Hb a Ha) as (k & Hk & Hv). exists k. split; [|exact Hv]. rewrite <- Hk.
      apply (rdn1_same_outside mem mem' _ _ FM); [lia|].
      apply (krun_byte_outside (lo, (hi, b)) a); auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cell_bytes_outside nu mem r off w v :
    env_ok2 P E -> region_ok SEGS P E nu (mkVS2 (vstate_init 0) [] [] pm_empty []) mem r \/ True ->
    region_perm_ok SEGS P E nu mem r -> is_data_shadow r = false ->
    In (off, (w, v)) (vr_cells r) -> region_cells_ok SEGS nu mem r ->
    forall i, 0 <= i < w -> outside (wordZ (rbase nu r + off + i)) (unit_regions P1 E1).
  Proof.
    intros HE _ PERM ND Hin CELLS i Hi.
    destruct (CELLS _ _ _ Hin) as (L1 & L2 & L3 & _).
    destruct (PERM ND) as [RD _]. destruct (RD (off + i) ltac:(lia)) as [Z _].
    replace (rbase nu r + off + i) with (rbase nu r + (off + i)) by lia.
    eapply any_zone_byte_outside; eauto.
  Qed.

  Lemma run_holds_frame mem mem' a w b :
    frame_mod mem mem' (unit_regions P1 E1) -> 0 <= a -> a + w <= 2 ^ 64 ->
    (forall i, 0 <= i < w -> outside (wordZ (a + i)) (unit_regions P1 E1)) ->
    run_holds SEGS mem a w b -> run_holds SEGS mem' a w b.
  Proof.
    intros FM Ha Hw Ho RH i Hi. destruct (RH i Hi) as (k & Hk & Hb). exists k. split; [|exact Hb].
    rewrite <- Hk. apply (rdn1_same_outside mem mem' _ _ FM); [lia|]. apply Ho. lia.
  Qed.

  Lemma cell_holds_frame nu nu' mem mem' a w v b :
    frame_mod mem mem' (unit_regions P1 E1) -> 0 <= a -> a + w <= 2 ^ 64 -> 0 < w ->
    (forall i, 0 <= i < w -> outside (wordZ (a + i)) (unit_regions P1 E1)) ->
    ext b nu nu' -> (match v with Some e => lin_below e b = true | None => True end) ->
    cell_holds SEGS nu mem a w v -> cell_holds SEGS nu' mem' a w v.
  Proof.
    intros FM Ha Hw Hw0 Ho X Hb CH. destruct v as [e|]; [|exact I]. cbn [cell_holds] in *.
    destruct CH as (bs & Hr & Hv). exists bs. split.
    - rewrite <- Hr. apply (rdn_same_outside mem mem' _ a (Z.to_nat w) FM); [lia|rewrite Z2Nat.id; lia|].
      intros i Hi. apply Ho. rewrite Z2Nat.id in Hi; lia.
    - rewrite (eval_ext_below _ _ _ _ X Hb). exact Hv.
  Qed.

  Lemma region_ok_frame A A1' nu nu' mem mem' r :
    env_ok2 P E ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    ext (vs_next (v1 A)) nu nu' ->
    state_below2 A -> In r (vs_rgn A) ->
    region_ok SEGS P E nu A mem r -> region_ok SEGS P E nu' (with_v1 A A1') mem' r.
  Proof.
    intros HE FM X BEL Hr (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
    destruct BEL as (BF & BR & BL & BD & BM). destruct (BR r Hr) as (Bb & Bc & Bk).
    assert (RB : rbase nu' r = rbase nu r) by (unfold rbase; rewrite X by exact Bb; reflexivity).
    unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok, kind_ok. rewrite !RB.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact DS|].
    split; [|split; [|split]].
    3:{ (* [comment removed for export] *)
      intros lo hi Hin. destruct (NUL lo hi Hin) as (off & b & R1 & R2 & Hrd & Hb0).
      exists off, b. split; [exact R1|]. split; [exact R2|]. split; [|exact Hb0]. rewrite <- Hrd.
      destruct (is_data_shadow r) eqn:ND.
      { destruct (DS eq_refl) as (_ & _ & N0). rewrite N0 in Hin. destruct Hin. }
      destruct (PERM ND) as [RD _]. destruct (RD off R2) as [Zb _].
      apply (rdn1_same_outside mem mem' _ _ FM); [lia|]. eapply any_zone_byte_outside; eauto. }
    - (* [comment removed for export] *)
      intros off w v Hin. destruct (CELLS _ _ _ Hin) as (L1 & L2 & L3 & RC). split; [lia|]. split; [lia|]. split; [lia|].
      destruct (is_data_shadow r) eqn:ND.
      { destruct (DS eq_refl) as [C0 _]. rewrite C0 in Hin. destruct Hin. }
      assert (OUT : forall i, 0 <= i < w -> outside (wordZ (rbase nu r + off + i)) (unit_regions P1 E1)).
      { eapply cell_bytes_outside; eauto. }
      unfold rcell_holds in *. destruct v as [e|]; [|exact I].
      destruct (is_shadow r && lin_is_const e).
      + eapply run_holds_frame; eauto; lia.
      + eapply cell_holds_frame; eauto; try lia; cbn; try exact (Bc _ _ _ Hin).
    - (* [comment removed for export] *)
      intros ND. destruct (PERM ND) as [RD WR]. split.
      + intros off Hoff. destruct (RD off Hoff) as [Z1 [b Hb]]. split; [exact Z1|]. exists b. rewrite <- Hb.
        apply (rdn1_same_outside mem mem' _ _ FM); [lia|]. eapply any_zone_byte_outside; eauto.
      + intros lo hi off Hlh Hoff. destruct (WR lo hi off Hlh Hoff) as (W1 & W2 & W3 & W4).
        split; [exact W1|]. split; [exact W2|]. split; [eapply frame_mod_store_ok; eauto|exact W4].
    - (* [comment removed for export] *)
      unfold kind_ok in KIND. destruct (vr_kind r) as [cid fl| |owner|s|] eqn:K; try exact KIND.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & pos & P1' & P2 & P3 & P4 & P5 & P6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        exists pos. rewrite X by exact Bk. split; [exact P1'|]. split; [exact P2|]. split; [exact P3|]. split; [|split; [exact P5|exact P6]].
        destruct P4 as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite <- Hb.
        destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|exfalso; apply F1; reflexivity].
        destruct (flag_byte_outside len ssl cid pos HE Efs F2 P1') as [O R]. rewrite P3.
        apply (rdn1_same_outside mem mem' _ _ FM); [|exact O].
        pose proof HE as (_ & _ & HF & _). unfold env_fs in HF. rewrite Efs in HF. destruct HF as (_ & Hlo & Hhi & _).
        unfold HIGH_MEM_BEG, HIGH_MEM_END in *. lia.
      + (* [comment removed for export] *)
        destruct KIND as (S1 & S2 & S3 & S4 & S5 & S6).
        split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
        intros N1 N2 N3. destruct (S6 N1 N2 N3) as (ro & G & B8 & M). exists ro.
        cbn [vs_rgn with_v1]. split; [exact G|]. split; [exact B8|].
        destruct (rgn_get_in _ _ _ G) as [Gin _]. destruct (BR ro Gin) as (Bro & _ & _).
        assert (RBo : rbase nu' ro = rbase nu ro) by (unfold rbase; rewrite X by exact Bro; reflexivity).
        rewrite RBo. rewrite X by exact Bb. exact M.
  Qed.

  (* [comment removed for export] *)
  Lemma flags_inv_step A A' nu nu' mem mem' :
    flags_inv P E A nu mem -> flags_step P E A A' nu nu' mem mem' -> flags_inv P E A' nu' mem'.
  Proof.
    intros FI FS Hfs c p Hc Hp NL NO.
    assert (FZ : in_flags_zone P E (flag_addr (e_fs E) c p)).
    { unfold in_flags_zone. destruct (vp_fs P) as [[len ssl]|]; [|exact (Hfs eq_refl)].
      pose proof (flag_addr_range (e_fs E) c p Hc Hp). unfold FS_FLAGS, FS_FRAMES in *. lia. }
    destruct (FS _ FZ) as [[E1' M]|[(I2 & N1 & Zb)|(I1 & N2 & Zb)]].
    - rewrite M. apply FI; auto. intros X. apply NO. apply (proj1 E1'). exact X.
    - exfalso. exact (NO I2).
    - exact Zb.
  Qed.

  (* [comment removed for export] *)
  Lemma nodup_map_inj {X Y : Type} (f : X -> Y) (l : list X) a b :
    List.NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
  Proof.
    induction l as [|x t IH]; simpl; [tauto|]. intros ND Ha Hb EQ. apply List.NoDup_cons_iff in ND as [Hy Ht].
    destruct Ha as [<-|Ha], Hb as [<-|Hb]; [reflexivity| | |exact (IH Ht Ha Hb EQ)].
    - exfalso. apply Hy. rewrite EQ. apply in_map. exact Hb.
    - exfalso. apply Hy. rewrite <- EQ. apply in_map. exact Ha.
  Qed.

  Lemma live_ok_base_inj nu A r1 r2 :
    live_ok nu A -> In r1 (vs_rgn A) -> In r2 (vs_rgn A) -> vr_base r1 = vr_base r2 -> r1 = r2.
  Proof. intros (_ & _ & _ & ND) H1 H2 EQ. exact (nodup_map_inj vr_base _ _ _ ND H1 H2 EQ). Qed.

  Lemma live_ok_frame A A1' nu nu' :
    ext (vs_next (v1 A)) nu nu' -> state_below2 A ->
    live_ok nu A -> live_ok nu' (with_v1 A A1').
  Proof.
    intros X (BF & BR & BL & BD & BM) (L1 & L2 & L3 & L4). split; [exact L1|]. split; [exact L2|]. split; [|exact L4].
    intros r1 r2 H1 H2. specialize (L3 r1 r2 H1 H2).
    destruct (vr_kind r1); try exact I. destruct (vr_kind r2); try exact I.
    intros Hne. unfold rbase in *. rewrite !X; [exact (L3 Hne)| |]; apply BR; auto.
  Qed.

  Lemma cells_syms_below_mono m b b' : (b <= b')%positive -> cells_syms_below m b -> cells_syms_below m b'.
  Proof. intros Hle H k w e Hin. eapply lin_below_mono; eauto. Qed.

  Lemma state_below2_next A A1' :
    (vs_next (v1 A) <= vs_next A1')%positive -> state_below2 A -> state_below2 (with_v1 A A1').
  Proof.
    intros Hle (BF & BR & BL & BD & BM). unfold state_below2; cbn [v1 vs_rgn vs_live vs_divdef vs_memo with_v1].
    split; [lia|]. split; [|split; [|split]].
    - intros r Hr. destruct (BR r Hr) as (B1 & B2 & B3). split; [lia|]. split; [eapply cells_syms_below_mono; eauto|].
      destruct (vr_kind r); try exact I. lia.
    - intros s Hs. pose proof (BL s Hs). lia.
    - intros q x m Hq. destruct (BD q x m Hq) as [D1 D2]. split; [lia|]. eapply lin_below_mono; eauto.
    - intros a n v Hin. destruct (BM a n v Hin) as [D1 D2]. split; eapply lin_below_mono; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma state_below2_nextc A A1' :
    (vs_next (v1 A) <= vs_next A1')%positive -> state_below2 A -> state_below2 (with_v1c A A1').
  Proof.
    intros Hle HB. pose proof (state_below2_next A A1' Hle HB) as (BF & BR & BL & BD & BM).
    split; [exact BF|]. split; [exact BR|]. split; [exact BL|]. split; [exact BD|]. intros a n v [].
  Qed.

  (* [comment removed for export] *)
  Lemma gamma2_clear_memo A nu regs mem :
    gamma2 SEGS P E mem0 A nu regs mem -> gamma2 SEGS P E mem0 (clear_memo A) nu regs mem.
  Proof.
    intros (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & (BF & BR & BL & BD & BM) & GL & FI2 & MEM2).
    split; [exact G1|]. split; [exact HE2|]. split; [exact HMC2|]. split; [exact FIX2|]. split; [exact DIV|].
    split; [exact RGN|]. split; [exact LIVE|]. split; [|split; [exact GL|split; [exact FI2|intros a n v []]]].
    split; [exact BF|]. split; [exact BR|]. split; [exact BL|]. split; [exact BD|]. intros a n v [].
  Qed.

  (* [comment removed for export] *)
  Lemma memo_ok_ext A nu nu' mem :
    ext (vs_next (v1 A)) nu nu' -> state_below2 A -> memo_ok SEGS nu mem A -> memo_ok SEGS nu' mem A.
  Proof.
    intros X (BF & BR & BL & BD & BM) HM a n v Hin. destruct (HM a n v Hin) as [N CH]. split; [exact N|].
    destruct (BM a n v Hin) as [Ba Bv].
    rewrite (eval_ext_below _ _ _ _ X Ba). cbn [cell_holds] in CH |- *. rewrite (eval_ext_below _ _ _ _ X Bv). exact CH.
  Qed.

  Lemma own_flags_ext A nu nu' :
    ext (vs_next (v1 A)) nu nu' -> state_below2 A -> own_flags A nu' = own_flags A nu.
  Proof.
    intros X (BF & BR & BL & BD & BM). unfold own_flags.
    assert (G : forall l, (forall r, In r l -> In r (vs_rgn A)) ->
      flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu' fl] | _ => [] end) l =
      flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu fl] | _ => [] end) l).
    { induction l as [|r t IH]; simpl; intros Hl; [reflexivity|].
      rewrite IH by (intros; apply Hl; auto). destruct (BR r (Hl r (or_introl eq_refl))) as (_ & _ & Bk).
      destruct (vr_kind r); try reflexivity. rewrite X by exact Bk. reflexivity. }
    apply G. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma globs_in_fcells_sound A : globs_in_fcells P A = true -> globs_ok2 P A.
  Proof.
    unfold globs_in_fcells, globs_ok2. intros H AM. rewrite AM in H. cbn [negb orb] in H.
    rewrite forallb_forall in H. intros a w v Hin.
    specialize (H _ Hin). cbn beta iota in H. apply in_cells_sound in H as (f & Hf & F1 & F2). exists f. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma in_cells_complete l a n c : In c l -> fst c <= a -> a + n <= fst c + snd c -> in_cells l a n = true.
  Proof.
    intros Hin H1 H2. unfold in_cells. rewrite existsb_exists. exists c. split; [exact Hin|].
    destruct c as [b m]. cbn in *. rewrite andb_true_iff, Z.leb_le, Z.leb_le. lia.
  Qed.

  Lemma globs_ok2_in_fcellsb A : globs_ok2 P A -> globs_in_fcells P A = true.
  Proof.
    unfold globs_in_fcells, globs_ok2. intros H. destruct (asan_mode P); [|reflexivity]. cbn [negb orb].
    rewrite forallb_forall. intros [a [w v]] Hin. destruct (H eq_refl a w v Hin) as (f & Hf & F1 & F2).
    eapply in_cells_complete; eauto.
  Qed.

  Lemma gamma2_globs_in_fcells A nu regs mem : gamma2 SEGS P E mem0 A nu regs mem -> globs_in_fcells P A = true.
  Proof. intros HG. apply globs_ok2_in_fcellsb. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HG))))))))). Qed.

  (* [comment removed for export] *)
  Lemma check_globs_next r l :
    check_globs P r = VR2_next l -> r = VR2_next l /\ forallb (globs_in_fcells P) l = true.
  Proof.
    unfold check_globs. destruct r as [l0|m]; [|discriminate].
    destruct (forallb (globs_in_fcells P) l0) eqn:F; [|discriminate]. intros H; injection H as ->. auto.
  Qed.

  Lemma vstep2_of_raw A i l :
    vstep2_raw P A i = VR2_next l -> forallb (globs_in_fcells P) l = true -> vstep2 P A i = VR2_next l.
  Proof. intros H F. unfold vstep2. rewrite H. cbn [check_globs]. rewrite F. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma globs_in_fcells_same A B : vs_globs (v1 B) = vs_globs (v1 A) -> globs_in_fcells P B = globs_in_fcells P A.
  Proof. intros H. unfold globs_in_fcells. rewrite H. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition memo_kept (A : vstate2) (m : list (lin * (Z * lin))) (mem mem' : word -> option byte) : Prop :=
    (m = vs_memo A /\ mem' = mem) \/ m = [].

  Lemma memo_kept_keep A mem : memo_kept A (vs_memo A) mem mem.
  Proof. left; auto. Qed.
  Lemma memo_kept_nil A mem mem' : memo_kept A [] mem mem'.
  Proof. right; auto. Qed.
  Lemma memo_kept_with_v1 A mem mem' : mem' = mem \/ vs_memo A = [] -> memo_kept A (vs_memo A) mem mem'.
  Proof. intros [H|H]; [left; auto|right; auto]. Qed.

  Lemma gamma2_transfer_gen A A1' m nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next A1')%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1' nu' regs' mem' ->
    globs_ok2 P (with_v1 A A1') ->
    memo_kept A m mem mem' ->
    gamma2 SEGS P E mem0 (mkVS2 A1' (vs_rgn A) (vs_live A) (vs_divdef A) m) nu' regs' mem'.
  Proof.
    intros (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & MEM2) X Hle FM G1' GL' MK.
    split.
    { eapply gamma_mem0_ext; [|exact G1']. intros a. symmetry. apply zpatch_same; auto. }
    split; [exact HE2|]. split; [eapply MC2_frame; eauto|].
    split; [eapply gamma_fix2_ext; [|exact X|exact FIX2]; destruct BEL2 as [BF _]; unfold LAST_FIXED2 in BF; lia|].
    split.
    { intros q x mm Hq. cbn [vs_divdef] in Hq. destruct (DIV q x mm Hq) as [D1 D2]. split; [exact D1|].
      destruct BEL2 as (_ & _ & _ & BD & _). destruct (BD q x mm Hq) as [Q1 Q2].
      rewrite X by exact Q1. rewrite (eval_ext_below _ _ _ _ X Q2). exact D2. }
    split.
    { intros r Hr. cbn [vs_rgn] in Hr. eapply (region_ok_frame A A1'); eauto. }
    split; [eapply (live_ok_frame A A1'); eauto|]. split.
    { destruct MK as [[-> MM]| ->]; [eapply (state_below2_next A A1'); eauto|eapply (state_below2_nextc A A1'); eauto]. }
    split; [exact GL'|]. split.
    { (* [comment removed for export] *)
      intros Hfs c p Hc Hp NL NO.
      change (own_flags _ nu') with (own_flags A nu') in NO. rewrite (own_flags_ext A nu nu' X BEL2) in NO.
      destruct (FI2 Hfs c p Hc Hp NL NO) as (b & Hb & Hb0). exists b. split; [|exact Hb0]. rewrite <- Hb.
      destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|exfalso; exact (Hfs eq_refl)].
      destruct (flag_byte_outside len ssl c p HE2 Efs Hc Hp) as [O _]. exact (frame_mod_byte _ _ _ _ FM O). }
    (* [comment removed for export] *)
    destruct MK as [[-> ->]| ->]; [|intros a n v []].
    exact (memo_ok_ext A nu nu' mem X BEL2 MEM2).
  Qed.

  Lemma gamma2_transfer A A1' nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next A1')%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1' nu' regs' mem' ->
    globs_ok2 P (with_v1 A A1') ->
    mem' = mem \/ vs_memo A = [] ->
    gamma2 SEGS P E mem0 (with_v1 A A1') nu' regs' mem'.
  Proof. intros HG X Hle FM G1' GL' MM. apply (gamma2_transfer_gen A A1' (vs_memo A) nu nu' regs regs' mem mem'); auto. apply memo_kept_with_v1; exact MM. Qed.

  Lemma gamma2_transferc A A1' nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next A1')%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1' nu' regs' mem' ->
    globs_ok2 P (with_v1 A A1') ->
    gamma2 SEGS P E mem0 (with_v1c A A1') nu' regs' mem'.
  Proof. intros HG X Hle FM G1' GL'. apply (gamma2_transfer_gen A A1' [] nu nu' regs regs' mem mem'); auto. apply memo_kept_nil. Qed.

  (* [comment removed for export] *)
  Lemma step_post_lift_gen (f : vstate -> vstate2) A nu l regs mem pc rom :
    gamma2 SEGS P E mem0 A nu regs mem ->
    (forall x, In x l -> globs_ok2 P (with_v1 A x)) ->
    (forall x, exists m, f x = mkVS2 x (vs_rgn A) (vs_live A) (vs_divdef A) m /\
        forall regs' pc' mem', RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom) ->
          memo_kept A m mem mem') ->
    step_post SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu l regs mem pc rom ->
    step_post2 SEGS P E mem0 A nu (map f l) regs mem pc rom.
  Proof.
    intros HG2 GL HF (regs' & pc' & mem' & A1' & nu' & ST & IN & PC' & X & LE & FM & G1').
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & _ & _).
    destruct (HF A1') as (m & EF & MK). specialize (MK _ _ _ ST).
    exists regs', pc', mem', (f A1'), nu'. rewrite EF.
    split; [exact ST|]. split; [rewrite <- EF; apply in_map; exact IN|]. split; [exact PC'|]. split; [exact X|]. split; [exact LE|].
    split; [|split].
    - eapply frame_mod_weaken; [|exact FM]. intros a Ha. unfold unit_regions2 in Ha. apply outside_app in Ha. tauto.
    - (* [comment removed for export] *)
      intros a Ha. left. split.
      + change (own_flags _ nu') with (own_flags A nu'). rewrite (own_flags_ext A nu nu' X BEL2). tauto.
      + unfold in_flags_zone in Ha. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|destruct Ha].
        eapply frame_mod_byte; [exact FM|]. eapply fs_byte_outside; eauto.
        pose proof HE2 as (_ & _ & HF' & _). unfold env_fs in HF'. rewrite Efs in HF'. destruct HF' as (_ & _ & _ & _ & Hlen & _).
        unfold FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia.
    - eapply gamma2_transfer_gen; eauto.
  Qed.

  Lemma step_post_lift A nu l regs mem pc rom :
    gamma2 SEGS P E mem0 A nu regs mem ->
    (forall x, In x l -> globs_ok2 P (with_v1 A x)) ->
    (forall regs' pc' mem', RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom) ->
        mem' = mem \/ vs_memo A = []) ->
    step_post SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu l regs mem pc rom ->
    step_post2 SEGS P E mem0 A nu (map (with_v1 A) l) regs mem pc rom.
  Proof.
    intros HG GL NM SP. apply (step_post_lift_gen (with_v1 A)); auto.
    intros x. exists (vs_memo A). split; [reflexivity|]. intros regs' pc' mem' ST. apply memo_kept_with_v1. eauto.
  Qed.

  Lemma step_post_liftc A nu l regs mem pc rom :
    gamma2 SEGS P E mem0 A nu regs mem ->
    (forall x, In x l -> globs_ok2 P (with_v1 A x)) ->
    step_post SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu l regs mem pc rom ->
    step_post2 SEGS P E mem0 A nu (map (with_v1c A) l) regs mem pc rom.
  Proof.
    intros HG GL SP. apply (step_post_lift_gen (with_v1c A)); auto.
    intros x. exists []. split; [reflexivity|]. intros; apply memo_kept_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma gamma2_lift_gen A (B : vstate) m nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) B nu' regs' mem' ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next B)%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    globs_ok2 P (with_v1 A B) ->
    memo_kept A m mem mem' ->
    gamma2 SEGS P E mem0 (mkVS2 B (vs_rgn A) (vs_live A) (vs_divdef A) m) nu' regs' mem'
    /\ frame_mod mem mem' (unit_regions2 P E)
    /\ flags_step P E A (mkVS2 B (vs_rgn A) (vs_live A) (vs_divdef A) m) nu nu' mem mem'.
  Proof.
    intros HG2 G1' X LE FM GL MK. pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & _ & _).
    split; [eapply gamma2_transfer_gen; eauto|]. split.
    - eapply frame_mod_weaken; [|exact FM]. intros a Ha. unfold unit_regions2 in Ha. apply outside_app in Ha. tauto.
    - intros a Ha. left. split.
      + change (own_flags _ nu') with (own_flags A nu'). rewrite (own_flags_ext A nu nu' X BEL2). tauto.
      + unfold in_flags_zone in Ha. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|destruct Ha].
        eapply frame_mod_byte; [exact FM|]. eapply fs_byte_outside; eauto.
        pose proof HE2 as (_ & _ & HF & _). unfold env_fs in HF. rewrite Efs in HF. destruct HF as (_ & _ & _ & _ & Hlen & _).
        unfold FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia.
  Qed.

  Lemma gamma2_lift A (B : vstate) nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) B nu' regs' mem' ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next B)%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    globs_ok2 P (with_v1 A B) ->
    mem' = mem \/ vs_memo A = [] ->
    gamma2 SEGS P E mem0 (with_v1 A B) nu' regs' mem'
    /\ frame_mod mem mem' (unit_regions2 P E)
    /\ flags_step P E A (with_v1 A B) nu nu' mem mem'.
  Proof. intros HG G1' X LE FM GL MM. apply (gamma2_lift_gen A B (vs_memo A) nu nu' regs regs' mem mem'); auto. apply memo_kept_with_v1; exact MM. Qed.

  Lemma gamma2_liftc A (B : vstate) nu nu' regs regs' mem mem' :
    gamma2 SEGS P E mem0 A nu regs mem ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) B nu' regs' mem' ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next B)%positive ->
    frame_mod mem mem' (unit_regions P1 E1) ->
    globs_ok2 P (with_v1 A B) ->
    gamma2 SEGS P E mem0 (with_v1c A B) nu' regs' mem'
    /\ frame_mod mem mem' (unit_regions2 P E)
    /\ flags_step P E A (with_v1c A B) nu nu' mem mem'.
  Proof. intros HG G1' X LE FM GL. apply (gamma2_lift_gen A B [] nu nu' regs regs' mem mem'); auto. apply memo_kept_nil. Qed.

  (* [comment removed for export] *)
  Definition not_store (i : instr) : Prop := match i with Store _ _ _ _ => False | _ => True end.

  Lemma step_nonstore_mem X l regs pc mem rom w i regs' pc' mem' :
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    vstep P1 X i = VR_next l -> not_store i ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom) -> mem' = mem.
  Proof.
    intros Hf He Hd Hv NS ST.
    assert (INJ : forall r1 p1 m1, MachineOk (mkst r1 p1 m1 rom) = MachineOk (mkst regs' pc' mem' rom) -> mem' = m1)
      by (intros r1 p1 m1 H; injection H; auto).
    destruct i; try discriminate Hv; try (destruct NS; fail).
    - erewrite step_lui in ST by eauto. eauto.
    - erewrite step_auipc in ST by eauto. eauto.
    - erewrite SeqExec.step_jal_link in ST by eauto. eauto.
    - erewrite step_jalr_gen in ST by eauto. eauto.
    - destruct (Sem.branch_taken c (getr regs rs1) (getr regs rs2)) eqn:BT.
      + erewrite step_branch_tk_gen in ST by eauto. eauto.
      + erewrite step_branch_ft_gen in ST by eauto. eauto.
    - (* [comment removed for export] *) revert ST. destruct sz, signed; step_pipeline Hf He Hd.
      all: rewrite ?ov_rdn.
      all: match goal with |- context [rdn ?s ?m ?a ?n] => destruct (rdn s m a n) end; cbv beta iota; intros ST; try discriminate.
      all: injection ST; intros; congruence.
    - erewrite step_opimm_gen in ST by eauto. eauto.
    - erewrite step_shiftimm_gen in ST by eauto. eauto.
    - erewrite step_op_gen in ST by eauto. eauto.
    - erewrite step_opimm32_gen in ST by eauto. eauto.
    - erewrite step_shiftimm32_gen in ST by eauto. eauto.
    - erewrite step_op32_gen in ST by eauto. eauto.
    - erewrite step_mul_gen in ST by eauto. eauto.
    - erewrite step_mul32_gen in ST by eauto. eauto.
  Qed.

  (* [comment removed for export] *)
  Theorem lift1_sound A nu regs mem pc rom w i l :
    gamma2 SEGS P E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    vstep P1 (v1 A) i = VR_next l ->
    (forall x, In x l -> globs_in_fcells P (with_v1 A x) = true) ->
    not_store i ->
    step_post2 SEGS P E mem0 A nu (map (with_v1 A) l) regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hv GL NS. eapply step_post_lift; [exact HG2|intros x Hx; apply globs_in_fcells_sound; apply GL; exact Hx| |].
    - intros regs' pc' mem' ST. left. eapply step_nonstore_mem; eauto.
    - eapply (vstep_sound SEGS P1 E1 (zpatch P E mem0 mem) PO1); eauto. exact (proj1 HG2).
  Qed.
End A.

(* [comment removed for export] *)
Lemma rt_apart_env (P P' : vparams2) (E E' : venv2) a w :
  vp_frame (p1 P') = vp_frame (p1 P) -> vp_fcells (p1 P') = vp_fcells (p1 P) ->
  e_sp0 (ev1 E') = e_sp0 (ev1 E) ->
  (forall x, in_rw_zones P' E' x = in_rw_zones P E x) ->
  rt_apart P E a w -> rt_apart P' E' a w.
Proof.
  intros HF HC HS HZ RA x Hx. destruct (RA x Hx) as (Z1 & Z2 & Z3).
  rewrite HZ, HF, HC, HS. auto.
Qed.

Lemma rtctx_ok_env SEGS (P P' : vparams2) (E E' : venv2) mem :
  vp_fs P' = vp_fs P -> vp_frame (p1 P') = vp_frame (p1 P) -> vp_fcells (p1 P') = vp_fcells (p1 P) ->
  vp_tp P' = vp_tp P -> e_fs E' = e_fs E -> e_sp0 (ev1 E') = e_sp0 (ev1 E) ->
  (forall x, in_rw_zones P' E' x = in_rw_zones P E x) ->
  rtctx_ok SEGS P E mem -> rtctx_ok SEGS P' E' mem.
Proof.
  intros HFS HF HC HT HE HS HZ RT. unfold rtctx_ok in *. rewrite HFS. destruct (vp_fs P); [|exact I].
  rewrite HT, HE.
  assert (RC : forall a w v, rt_cell SEGS P E mem a w v -> rt_cell SEGS P' E' mem a w v).
  { intros a w v (A0 & W0 & AW & RA & RD). repeat (split; [assumption|]). split; [eapply rt_apart_env; eauto|exact RD]. }
  assert (RR : forall a w, rt_readable SEGS P E mem a w -> rt_readable SEGS P' E' mem a w).
  { intros a w (A0 & AW & RA & RD). repeat (split; [assumption|]). split; [eapply rt_apart_env; eauto|exact RD]. }
  destruct RT as (tsd & ctx & thr & db & beg & C1 & C2 & C3 & C4 & C5 & N5 & C6 & N6 & R7 & C8 & N8 & N8' & C9 & [N9 N9']).
  exists tsd, ctx, thr, db, beg.
  repeat match goal with |- _ /\ _ => split end; auto.
Qed.
