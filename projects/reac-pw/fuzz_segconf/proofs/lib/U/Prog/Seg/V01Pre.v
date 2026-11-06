(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/CellsX.v; 657 of its 685 lines of code are new or changed and 29 lines of the source are left out. *)
(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd): the
    PREFIX stretch of the inner walk, [v01_pre] : V01D.V01_INNER from V01D.V01_HEAD and V01D.V01_TAIL.

    Code (UBSan binary):
      0x13e90 beqz s1 / 0x13e98 beqz a0 -> abort: dead (tab, mt >= 4096); s4 = mt          [inner]
      0x13e9c-0x13ea8 a0 = 18 cap, a1 = ~tab, bltu a1,a0 -> trap: dead (tab + 18 (cap + 1) <= lo)
      0x13eac-0x13eb8 memset(tab + 18 cap, 0x5a, 18): the guard entry
      0x13ebc-0x13ecc a0 = flags & 1; *n = 0 (sw 0x5c); 0(sp) = tab; beqz a0 -> 0x13f38   [at_ebc]
      0x13ed0-0x13ef0 a0 = cap (0x20(sp)); beqz -> 0x13f38; tab & 1 trap (dead); memcpy(tab, "enp1s0", 7)  [at_flag]
      0x13ef4-0x13f34 s0 = 33; sh tab[0].vid; mt & 3 trap (dead); memcpy(mt, "enp1s0", 7); sw mt[0].vid;
                      0x40(sp) = 1, *n = 1, 0x28(sp) = 1; j 0x13f48                  [at_ef4]
      0x13f38-0x13f44 0x28(sp) = 0; 0x40(sp) = (mt & 3 == 0) = 1                     [at_else]
      0x13f48-0x13f54 a0 = m->n (lw 0(s11)); s3 = m; 0x18(sp) = mt; blez a0 -> 0x141a8  [at48]
      0x141a8         0x20(sp) = 0, then V01_TAIL with want = 0 (m->n = 0: m_declared's first clause)
      0x13f58-0x13f94 the loop prologue, then V01_HEAD at turn 0 (V01_inv is m_declared's definition)
    The memory the prefix writes is main's frame [sp, sp + 96) and the two tables ([WPL]); every other fact of
    V01_env is carried across by munch (env_frame).
    Part of the proof of LLVMFuzzerTestOneInput: this file is one stretch of segment V01 of its walk; no released
    proof of fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import MainBPure.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D MainB.
Import ListNotations.
Open Scope Z_scope.

(** ** Build-independent facts (the plain twin may Require them) *)
Module V01PrePure.

(** *** Cells *)
Lemma wr_at_app : forall segs m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_addr : forall segs m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_cs : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_conv : forall segs m A A' cs cs', rw_cells segs m A cs -> A = A' -> cs = cs' ->
  rw_cells segs m A' cs'.
Proof. intros; subst; assumption. Qed.

Lemma rw_CB_resize : forall segs m A A' n n' bs, rw_cells segs m A [CB n bs] -> A = A' -> n = n' ->
  rw_cells segs m A' [CB n' bs].
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_wn : forall segs m A n bs (w v : word), rw_cells segs m A [CB n bs] ->
  bv_unsigned w = A -> Z.to_nat (bv_unsigned v) = n ->
  rw_cells segs m (bv_unsigned w) [CB (Z.to_nat (bv_unsigned v)) bs].
Proof. intros segs m A n bs w v H E1 E2. rewrite E1, E2. exact H. Qed.

Lemma bytes_at_w : forall segs m A bs (w : word), bytes_at segs m A bs -> bv_unsigned w = A ->
  bytes_at segs m (bv_unsigned w) bs.
Proof. intros segs m A bs w H E. rewrite E. exact H. Qed.

(** calloc's zeros, read through bytes_at, with the writability of the block. *)
Lemma rw_of_bytes : forall segs m A bs n j, bytes_at segs m A bs -> rw_cells segs m A [CB n j] ->
  length bs = n -> rw_cells segs m A [CB n bs].
Proof.
  intros segs m A bs n j HB [_ HW] HL. split; [split|].
  - cbn. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact HW.
Qed.

Lemma rw_bytes1 : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros segs m A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma rw_bytesC2 : forall segs m A v, rw_cells segs m A [C2 v] -> bytes_at segs m A (le2 v).
Proof. intros segs m A v [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma rw_bytesC4 : forall segs m A v, rw_cells segs m A [C4 v] -> bytes_at segs m A (le4 v).
Proof. intros segs m A v [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma bat_cat : forall segs m a b (l1 l2 : list byte), bytes_at segs m a l1 -> bytes_at segs m b l2 ->
  b = a + Z.of_nat (length l1) -> bytes_at segs m a (l1 ++ l2).
Proof. intros segs m a b l1 l2 H1 H2 ->. apply (proj2 (bytes_at_app segs m a l1 l2)). split; assumption. Qed.

Lemma rw_CB_app : forall segs m A (a b : list byte),
  rw_cells segs m A [CB (length a + length b) (a ++ b)] -> rw_cells segs m A [CB (length a) a; CB (length b) b].
Proof.
  intros segs m A a b [[_ HB] HW]. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in HB. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize] in *. replace (length a + (length b + 0))%nat with (length a + length b + 0)%nat by lia.
    exact HW.
Qed.

(** Cut a block of n copies of x at n1. *)
Lemma rw_rep_cut : forall segs m A (x : byte) n n1 n2 A2, n = (n1 + n2)%nat -> A2 = A + Z.of_nat n1 ->
  rw_cells segs m A [CB n (repeat x n)] ->
  rw_cells segs m A [CB n1 (repeat x n1)] /\ rw_cells segs m A2 [CB n2 (repeat x n2)].
Proof.
  intros segs m A x n n1 n2 A2 En EA H. subst n.
  assert (H' : rw_cells segs m A [CB (length (repeat x n1) + length (repeat x n2)) (repeat x n1 ++ repeat x n2)])
    by (rewrite !repeat_length, <- repeat_app; exact H).
  apply rw_CB_app in H'. rewrite !repeat_length in H'.
  change [CB n1 (repeat x n1); CB n2 (repeat x n2)] with ([CB n1 (repeat x n1)] ++ [CB n2 (repeat x n2)]) in H'.
  apply rw_cells_app in H' as [H1 H2]. split; [exact H1|].
  eapply rw_cells_addr; [exact H2|]. cbn [cells_size csize]. lia.
Qed.

Lemma cells_eq11 : forall a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : word,
  a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 -> a4 = b4 -> a5 = b5 -> a6 = b6 -> a7 = b7 -> a8 = b8 -> a9 = b9 ->
  a10 = b10 ->
  [C8 a0; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7; C8 a8; C8 a9; C8 a10] =
  [C8 b0; C8 b1; C8 b2; C8 b3; C8 b4; C8 b5; C8 b6; C8 b7; C8 b8; C8 b9; C8 b10].
Proof. intros; subst; reflexivity. Qed.

(** *** Words *)
Lemma land1_16 : forall t, t mod 16 = 0 -> Z.land t 1 = 0.
Proof.
  intros t H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land3_16 : forall t, t mod 16 = 0 -> Z.land t 3 = 0.
Proof.
  intros t H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

(** *** The model *)
Lemma flags_rng : forall inp, 0 <= seg_flags inp < 256.
Proof.
  intros inp. pose proof (mb_bytes_ok inp) as H. revert H. unfold seg_flags, seg_pay, decode.
  destruct (seg_in inp) as [|b0 [|b1 r]]; cbn; intros H; try lia.
  apply Forall_inv_tail, Forall_inv in H. destruct (fuzz_u8 r) as [b2 i3]. exact H.
Qed.

Lemma tab0_nil : forall inp, Z.land (seg_flags inp) 1 = 0 \/ seg_cap inp = 0 -> seg_tab0 inp = [].
Proof.
  intros inp H. unfold seg_tab0, vlan_init.
  change (p_flags (seg_pay inp)) with (seg_flags inp). change (p_cap (seg_pay inp)) with (seg_cap inp).
  destruct H as [H|H]; rewrite H; [reflexivity|].
  destruct (negb (Z.land (seg_flags inp) 1 =? 0)); reflexivity.
Qed.

Lemma tab0_one : forall inp, Z.land (seg_flags inp) 1 <> 0 -> 0 < seg_cap inp -> seg_tab0 inp = [(S_enp, 33)].
Proof.
  intros inp H1 H2. unfold seg_tab0, vlan_init.
  change (p_flags (seg_pay inp)) with (seg_flags inp). change (p_cap (seg_pay inp)) with (seg_cap inp).
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.

Lemma tab0_len : forall inp, (length (seg_tab0 inp) <= 1)%nat.
Proof. intros inp. unfold seg_tab0, vlan_init. destruct (_ && _); cbn; lia. Qed.

Lemma tab0_cap : forall inp, Z.of_nat (length (seg_tab0 inp)) <= seg_cap inp.
Proof. intros inp. apply vlan_init_len. pose proof (mb_cap inp) as H. unfold seg_cap in H. lia. Qed.

Lemma enp_nulfree : ~ In 0 S_enp.
Proof. intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.

(** The 18 and 20 bytes of the one entry (S_enp, 33): the 7 copied bytes, calloc's zeros, then the vid. *)
Lemma rvlan_one : rvlan_enc (S_enp, 33) (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)).
Proof.
  unfold rvlan_enc, cstr_enc. cbn [fst snd].
  split; [reflexivity|].
  split; [split; [reflexivity|]; split; [apply Nat.ltb_lt; reflexivity|]; split; [exact enp_nulfree | reflexivity]|].
  split; [lia | reflexivity].
Qed.

Lemma mvlan_one : mvlan_enc (S_enp, 33) (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)).
Proof.
  unfold mvlan_enc, cstr_enc, u32_enc. cbn [fst snd].
  split; [reflexivity|].
  split; [split; [reflexivity|]; split; [apply Nat.ltb_lt; reflexivity|]; split; [exact enp_nulfree | reflexivity]|].
  split; [lia | reflexivity].
Qed.

Lemma rtab_one : rtab_enc [(S_enp, 33)] (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)).
Proof.
  split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
  exact rvlan_one.
Qed.

Lemma mtab_one : mtab_enc [(S_enp, 33)] (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)).
Proof.
  split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
  exact mvlan_one.
Qed.

Lemma rtab_nil : rtab_enc [] [].
Proof. split; [reflexivity|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma mtab_nil : mtab_enc [] [].
Proof. split; [reflexivity|]. intros i Hi. cbn in Hi. lia. Qed.

(** m->n: the four bytes at m + 0x2000 are the number of segments, at most 32. *)
Lemma read_n : forall segs m a mc, mconf_at segs m a mc ->
  ov_read_bytes segs m (wa (a + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc))))) /\
  (length (mc_seg mc) <= 32)%nat.
Proof.
  intros segs m a mc (bs & HB & HL & H32 & _ & (_ & HN) & _).
  split; [|exact H32]. rewrite <- HN. unfold fldz, fld.
  rewrite <- (Z2Nat.id MC_N) at 1 by (unfold MC_N; lia).
  change (Z.to_nat 4) with 4%nat.
  apply bytes_at_ov_read; [exact HB|]. unfold SEG_M_SIZE, MC_N in *. lia.
Qed.

End V01PrePure.
Import V01PrePure.

(** ** Tactics *)
(** A dead branch: the condition contradicts the context. *)
Ltac v1_refute K :=
  exfalso; zify_cond K;
  try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
         ?Z.eqb_neq in K);
  try (rewrite zb_lxor_ones in K by lia);
  lia.
(** [v1_ntk]: the branch is not taken; [v1_tkn]: it is taken. *)
Ltac v1_ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota; [ v1_refute K | clear K ]
  end.
Ltac v1_tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota; [ clear K | v1_refute K ]
  end.
(** A word the code computed is the word a cut names. *)
Ltac weq := first
  [ reflexivity
  | f_equal; lia
  | rewrite ?zb_lxor_ones by lia; f_equal; lia
  | (repeat match goal with H : Z.land _ _ = 0 |- _ => progress rewrite H end); reflexivity
  | apply bv_eq; vm_compute; reflexivity ].
(** After a callee's contract: its post, the hypotheses carried across its footprint, the return pc. *)
Ltac v1_post :=
  let ms' := fresh "ms'" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
  destruct PO as [E [MUc [WMc [MIc PO]]]]; subst ms';
  repeat (rewrite unsigned_lit in MUc by lia);
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call rsegs m m' MUc WMc; clear MUc WMc;
      repeat match goal with H : mem_inv rsegs m |- _ => clear H end
  end;
  rename MIc into MI;
  rewrite ret_pc_even by (try lia; reflexivity).

(** ** The walk *)
Section Walk.
Variable X : vctx.
Hypothesis HG : V01_geo X.
Hypothesis HMS : memset_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HH : V01_HEAD X.
Hypothesis HT : V01_TAIL X.

(** The bytes the prefix writes: main's frame below the int n and the mvlan buffer, and the two tables. *)
Local Abbreviation WPL := [(v_sp X, v_sp X + 96); (v_tab X, v_tab X + v_ntab X); (v_mt X, v_mt X + v_nmt X)].

Ltac geo_destr := destruct HG as (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & g14 & g15 &
  g16 & g17 & g18 & g19 & g20 & g21 & g22 & g23 & g24 & g25 & g26 & g27 & g28 & g29 & g30 & g31 & g32 & g33 & g34 &
  g35).

(** The numbers of the context, without a disjunction (lia case-splits every one). *)
Lemma geo_ar :
  v_sp X = v_S X - 240 /\ v_lo X = v_S X - 65536 /\ 0x60000 < v_lo X /\ v_S X <= 2 ^ 47 /\
  0 <= v_cap X < 40 /\ v_ntab X = 18 * (v_cap X + 1) /\ v_nmt X = 20 * (v_cap X + 1) /\
  4096 <= v_tab X /\ v_tab X + v_ntab X <= v_lo X /\ 4096 <= v_mt X /\ v_mt X + v_nmt X <= v_lo X /\
  4096 <= v_mm X /\ v_mm X + 9236 <= v_lo X /\ 4096 <= v_c X /\ v_c X + 16616 <= v_lo X /\
  v_buf X = v_sp X + 96 /\ Z.land (v_tab X) 1 = 0 /\ Z.land (v_mt X) 3 = 0 /\ 0 <= v_flags X < 256.
Proof.
  geo_destr.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact g2|]. split; [exact g3|]. split; [exact g5|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact g12|]. split; [exact g14|]. split; [exact g15|].
  split; [exact g17|]. split; [exact g9|]. split; [exact g11|]. split; [exact g6|]. split; [exact g8|].
  split; [reflexivity|]. split; [apply land1_16; exact g13|]. split; [apply land3_16; exact g16|].
  exact (flags_rng (v_inp X)).
Qed.

Ltac geo := pose proof geo_ar as (Esp & Elo & LO & SH & CAP & Entab & Enmt & TB0 & TBL & MT0 & MTL & MM0 & MML &
  CC0 & CCL & Ebuf & T1 & M3 & FLG).

Lemma ap_ct : apart (v_c X) SEG_C_SIZE (v_tab X) (v_tab X + v_ntab X). Proof. geo_destr. exact g19. Qed.
Lemma ap_cm : apart (v_c X) SEG_C_SIZE (v_mt X) (v_mt X + v_nmt X). Proof. geo_destr. exact g20. Qed.
Lemma ap_mt : apart (v_mm X) SEG_M_SIZE (v_tab X) (v_tab X + v_ntab X). Proof. geo_destr. exact g21. Qed.
Lemma ap_mm : apart (v_mm X) SEG_M_SIZE (v_mt X) (v_mt X + v_nmt X). Proof. geo_destr. exact g22. Qed.
Lemma ap_tm : v_tab X + v_ntab X <= v_mt X \/ v_mt X + v_nmt X <= v_tab X. Proof. geo_destr. exact g23. Qed.
Lemma ap_et : apart V01_ERRNO 4 (v_tab X) (v_tab X + v_ntab X). Proof. geo_destr. exact g26. Qed.
Lemma ap_em : apart V01_ERRNO 4 (v_mt X) (v_mt X + v_nmt X). Proof. geo_destr. exact g27. Qed.
Lemma ap_gt : apart (sa_guard SA) 8 (v_tab X) (v_tab X + v_ntab X). Proof. geo_destr. exact g28. Qed.
Lemma ap_gm : apart (sa_guard SA) 8 (v_mt X) (v_mt X + v_nmt X). Proof. geo_destr. exact g29. Qed.
Lemma ap_ggt : apart (sa_got_guard SA) 8 (v_tab X) (v_tab X + v_ntab X). Proof. geo_destr. exact g30. Qed.
Lemma ap_ggm : apart (sa_got_guard SA) 8 (v_mt X) (v_mt X + v_nmt X). Proof. geo_destr. exact g31. Qed.
Lemma ap_nt : V01_ENP + 7 <= v_tab X \/ v_tab X + v_ntab X <= V01_ENP. Proof. geo_destr. exact g32. Qed.
Lemma ap_nm : V01_ENP + 7 <= v_mt X \/ v_mt X + v_nmt X <= V01_ENP. Proof. geo_destr. exact g33. Qed.

Lemma dj3 : forall a n, (a + n <= v_sp X \/ v_sp X + 96 <= a) -> (a + n <= v_tab X \/ v_tab X + v_ntab X <= a) ->
  (a + n <= v_mt X \/ v_mt X + v_nmt X <= a) -> disjoint_from WPL a n.
Proof. intros a n H1 H2 H3. cbn [disjoint_from]. tauto. Qed.

(** Every fact of the environment survives the prefix's writes. *)
Lemma env_frame : forall ms m, V01_env X ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  V01_env X m.
Proof.
  intros ms m (MI0 & ST & ROM & GG & (gv & GV) & (ev & EV) & ENP & (bsc & BC & EC) & (bsm & BM & EM)) MU WM MI.
  geo.
  pose proof EC as (LC & _). pose proof EM as (LM & _).
  unfold V01_env. split; [exact MI|].
  split.
  { eapply stk_transport_disjoint; [exact ST | exact MU | exact WM |]. apply dj3; lia. }
  split; [exact ROM|].
  split.
  { eapply bytes_at_transport; [exact GG | exact MU |]. rewrite length_le8.
    apply dj3; [unfold SA, SEG_UBSAN; cbn [sa_got_guard]; lia | exact ap_ggt | exact ap_ggm]. }
  split.
  { exists gv. eapply bytes_at_transport; [exact GV | exact MU |]. rewrite length_le8.
    apply dj3; [unfold SA, SEG_UBSAN; cbn [sa_guard]; lia | exact ap_gt | exact ap_gm]. }
  split.
  { exists ev. eapply rw_cells_transport; [exact EV | exact MU | exact WM |]. cbn [cells_size csize].
    apply dj3; [unfold V01_ERRNO; lia | exact ap_et | exact ap_em]. }
  split.
  { eapply bytes_at_transport; [exact ENP | exact MU |].
    change (Z.of_nat (length (zb (S_enp ++ [0])))) with 7.
    apply dj3; [unfold V01_ENP; lia | exact ap_nt | exact ap_nm]. }
  split.
  { exists bsc. split; [|exact EC]. eapply bytes_at_transport; [exact BC | exact MU |]. rewrite LC.
    apply dj3; [unfold SEG_C_SIZE; lia | exact ap_ct | exact ap_cm]. }
  exists bsm. split; [|exact EM]. eapply bytes_at_transport; [exact BM | exact MU |]. rewrite LM.
  apply dj3; [unfold SEG_M_SIZE; lia | exact ap_mt | exact ap_mm].
Qed.

(** The memory at the entry the prefix never writes: the environment, the write set against m0 and the buffer. *)
Definition PK (ms : word -> option byte) : Prop :=
  V01_env X ms /\ munch (V01_W X) (v_m0 X) ms /\ wmono rsegs (v_m0 X) ms /\
  (exists jb : list byte, rw_cells rsegs ms (v_buf X) [CB 20 jb]).

(** The two tables as the interface points want them, over the model's initial table. *)
Definition TABS (m : word -> option byte) : Prop :=
  rtab_at rsegs m (v_tab X) (v_tab0 X) /\ guard_at rsegs m (v_tab X) (v_cap X) /\
  (exists ft : list byte, rw_cells rsegs m (v_tab X + RVLAN_SIZE * Z.of_nat (v_n0 X))
     [CB (Z.to_nat (RVLAN_SIZE * (v_cap X - Z.of_nat (v_n0 X)))) ft]) /\
  mtab_at rsegs m (v_mt X) (v_tab0 X) /\
  (exists fm : list byte, rw_cells rsegs m (v_mt X + MVLAN_SIZE * Z.of_nat (length (v_tab0 X)))
     [CB (Z.to_nat (MVLAN_SIZE * (v_cap X + 1 - Z.of_nat (length (v_tab0 X))))) fm]).

Lemma tabs_xport : forall m m', TABS m -> munch [(v_sp X, v_sp X + 96)] m m' -> wmono rsegs m m' -> TABS m'.
Proof.
  intros m m' ((bt & BT & ET) & GU & (ft & FT) & (bm & BM & EM) & (fm & FM)) MU WM.
  geo.
  pose proof (tab0_cap (v_inp X)) as TC. pose proof (tab0_len (v_inp X)) as TL.
  change (seg_tab0 (v_inp X)) with (v_tab0 X) in TC, TL. change (seg_cap (v_inp X)) with (v_cap X) in TC.
  pose proof ET as (LT & _). pose proof EM as (LMt & _).
  unfold TABS, v_n0 in *.
  split.
  { exists bt. split; [|exact ET]. eapply bytes_at_transport; [exact BT | exact MU |].
    cbn [disjoint_from]. rewrite LT. split; [lia | exact I]. }
  split.
  { unfold guard_at in *. eapply bytes_at_transport; [exact GU | exact MU |].
    change (Z.of_nat (length GUARD_BYTES)) with 18. cbn [disjoint_from]. unfold RVLAN_SIZE.
    split; [lia | exact I]. }
  split.
  { exists ft. eapply rw_cells_transport; [exact FT | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. unfold RVLAN_SIZE. split; [lia | exact I]. }
  split.
  { exists bm. split; [|exact EM]. eapply bytes_at_transport; [exact BM | exact MU |].
    cbn [disjoint_from]. rewrite LMt. split; [lia | exact I]. }
  exists fm. eapply rw_cells_transport; [exact FM | exact MU | exact WM |].
  cbn [disjoint_from cells_size csize]. unfold MVLAN_SIZE. split; [lia | exact I].
Qed.

(** The memory of an interface point, from the entry's untouched facts, the frame and the tables. *)
Lemma mk_mem : forall ms m (w8 w30 w38 : word) (added : Z),
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X) (V01_cells X w8 w30 w38 added (Z.of_nat (v_n0 X))) ->
  (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (v_n0 X)))]) ->
  TABS m -> V01_mem X w8 w30 w38 added (v_tab0 X) m.
Proof.
  intros ms m w8 w30 w38 added (ENV & MU0 & WM0 & (jb & JB)) MU WM MI FR NC (RT & GU & FT & MTB & FM).
  geo.
  unfold V01_mem.
  split; [exact (env_frame ms m ENV MU WM MI)|].
  split; [exact FR|].
  split; [exact NC|].
  split.
  { exists jb. eapply rw_cells_transport; [exact JB | exact MU | exact WM |]. cbn [cells_size csize].
    apply dj3; lia. }
  split; [exact RT|]. split; [exact GU|]. split; [exact FT|]. split; [exact MTB|]. split; [exact FM|].
  split; [exact (tab0_cap (v_inp X))|].
  split.
  { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
    unfold sub_fp, V01_W, V01_ERRNO. cbn [outside]. intros x (H1 & H2 & H3 & H4 & _).
    split; [lia | split; [exact H2 | split; [exact H3 | exact I]]]. }
  eapply wmono_trans; eassumption.
Qed.

(** The tables of the else path: nothing appended. *)
Lemma tabs_nil : forall m, v_tab0 X = [] ->
  rw_cells rsegs m (v_tab X) [CB (Z.to_nat (18 * v_cap X)) (repeat ZERO (Z.to_nat (18 * v_cap X)))] ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) (repeat ZERO (Z.to_nat (v_nmt X)))] ->
  TABS m.
Proof.
  intros m E0 T0 TG M0. geo.
  unfold TABS, v_n0. rewrite E0. cbn [length Z.of_nat].
  split. { exists []. split; [apply bytes_at_nil; lia | exact rtab_nil]. }
  split. { unfold guard_at, RVLAN_SIZE. exact (rw_bytes1 _ _ _ _ _ TG). }
  split. { eexists. eapply rw_CB_resize; [exact T0 | unfold RVLAN_SIZE; lia | unfold RVLAN_SIZE; lia]. }
  split. { exists []. split; [apply bytes_at_nil; lia | exact mtab_nil]. }
  eexists. eapply rw_CB_resize; [exact M0 | unfold MVLAN_SIZE; lia | unfold MVLAN_SIZE; lia].
Qed.

(** The tables of the flags path: entry 0 is ("enp1s0", 33) in both. *)
Lemma tabs_one : forall m (w2 w4 : word) (nr nr' : nat),
  v_tab0 X = [(S_enp, 33)] ->
  rw_cells rsegs m (v_tab X) [CB 7 (zb (S_enp ++ [0]))] ->
  rw_cells rsegs m (v_tab X + 7) [CB 9 (repeat ZERO 9)] ->
  rw_cells rsegs m (v_tab X + 16) [C2 w2] -> w2 = Z_to_bv 64 33 ->
  rw_cells rsegs m (v_tab X + 18) [CB nr (repeat ZERO nr)] -> nr = Z.to_nat (18 * (v_cap X - 1)) ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB 7 (zb (S_enp ++ [0]))] ->
  rw_cells rsegs m (v_mt X + 7) [CB 9 (repeat ZERO 9)] ->
  rw_cells rsegs m (v_mt X + 16) [C4 w4] -> w4 = Z_to_bv 64 33 ->
  rw_cells rsegs m (v_mt X + 20) [CB nr' (repeat ZERO nr')] -> nr' = Z.to_nat (20 * v_cap X) ->
  TABS m.
Proof.
  intros m w2 w4 nr nr' E0 T7 T9 T2 E2 TR ER TG M7 M9 M4 E4 MR ER'. subst w2 w4 nr nr'. geo.
  assert (LZ : length (zb (S_enp ++ [0])) = 7%nat) by reflexivity.
  unfold TABS, v_n0. rewrite E0. cbn [length Z.of_nat].
  split.
  { exists (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)). split; [|exact rtab_one].
    apply (bat_cat _ _ _ (v_tab X + 7)); [exact (rw_bytes1 _ _ _ _ _ T7) | | rewrite LZ; lia].
    apply (bat_cat _ _ _ (v_tab X + 16)); [exact (rw_bytes1 _ _ _ _ _ T9) | exact (rw_bytesC2 _ _ _ _ T2) |].
    rewrite repeat_length. lia. }
  split. { unfold guard_at, RVLAN_SIZE. exact (rw_bytes1 _ _ _ _ _ TG). }
  split. { eexists. eapply rw_CB_resize; [exact TR | unfold RVLAN_SIZE; lia | unfold RVLAN_SIZE; lia]. }
  split.
  { exists (zb (S_enp ++ [0]) ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)). split; [|exact mtab_one].
    apply (bat_cat _ _ _ (v_mt X + 7)); [exact (rw_bytes1 _ _ _ _ _ M7) | | rewrite LZ; lia].
    apply (bat_cat _ _ _ (v_mt X + 16)); [exact (rw_bytes1 _ _ _ _ _ M9) | exact (rw_bytesC4 _ _ _ _ M4) |].
    rewrite repeat_length. lia. }
  eexists. eapply rw_CB_resize; [exact MR | unfold MVLAN_SIZE; lia | unfold MVLAN_SIZE; lia].
Qed.

(** V01_HEAD at turn 0, with the registers in the forms the prologue leaves. *)
Lemma head0 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 : word)
    (w9 w18 w19 w20 w22 w25 w26 w27 : word),
  w9 = Z_to_bv 64 (v_mm X) -> w18 = Z_to_bv 64 (18446744073709551615 - v_mm X) -> w19 = Z_to_bv 64 (v_mm X) ->
  w20 = Z_to_bv 64 18446744073709551615 -> w22 = Z_to_bv 64 (0 - v_mm X) -> w25 = Z_to_bv 64 0 ->
  w26 = Z_to_bv 64 4094 -> w27 = Z_to_bv 64 (v_mm X + MC_N) ->
  V01_lmem X 0 (v_tab0 X) m -> (0 < length (v_segs X))%nat ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 w9 x10 x11 x12 x13 x14 x15 x16 x17
             w18 w19 w20 x21 w22 x23 x24 w25 w26 w27 x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13f98) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 w9 w18 w19 w20 w22 w25 w26 w27
    E9 E18 E19 E20 E22 E25 E26 E27 LM LT.
  subst w9 w18 w19 w20 w22 w25 w26 w27.
  pose proof (HH 0%nat (v_tab0 X) 0 m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 LM)
    as H.
  replace (v_mm X + 256 * Z.of_nat 0) with (v_mm X) in H by lia.
  change (Z.of_nat 0) with 0 in H.
  apply H; [|exact LT].
  split; [lia|]. split; [lia|]. reflexivity.
Qed.

(** V01_TAIL with want = 0 when the model has no segment. *)
Lemma tail0 : forall m (w8 w30 w38 : word)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 w19 : word),
  w19 = Z_to_bv 64 (v_mm X) -> mc_seg (v_mc X) = [] -> V01_mem X w8 w30 w38 0 (v_tab0 X) m ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 w19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x141ac) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m w8 w30 w38 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 w19 E19 ES LM.
  subst w19.
  apply (HT 0 (v_tab0 X) m w8 w30 w38 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
           x27 x28 x29 x30 x31); [|lia|exact LM].
  unfold m_declared. rewrite ES. reflexivity.
Qed.

(** 0x13f48: m->n, s3 = m, 0x18(sp) = mt, then the tail (m->n = 0) or the loop prologue and the head. *)
Lemma at48 : forall m ms (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30
                          x31 : word) (w8 w18 w20 w28 w30 w38 w40 wn : word) (jn : list byte),
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X)
    [C8 (Z_to_bv 64 (v_tab X)); C8 w8; C8 (Z_to_bv 64 (v_cap X)); C8 w18; C8 w20; C8 w28; C8 w30; C8 w38; C8 w40;
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
  w28 = Z_to_bv 64 (Z.of_nat (v_n0 X)) -> w40 = Z_to_bv 64 1 ->
  rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 wn] -> wn = Z_to_bv 64 (Z.of_nat (v_n0 X)) ->
  TABS m ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - v_mm X)) x19 (Z_to_bv 64 (v_mt X)) x21 x22 x23 x24 x25 x26
             (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13f48) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m ms x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    w8 w18 w20 w28 w30 w38 w40 wn jn PKm MP WMP MI FR E28 E40 NC En TB.
  subst w28 w40 wn. geo.
  destruct (env_frame ms m (proj1 PKm) MP WMP MI) as (_ & _ & _ & _ & _ & _ & _ & _ & MC).
  destruct (read_n rsegs m (v_mm X) (v_mc X) MC) as [RN NL]. clear MC.
  pose proof (munch_refl [(v_sp X, v_sp X + 96)] m) as MPf. pose proof (wmono_refl rsegs m) as WMf.
  zstep. clear RN. rewrite (sx32_small (Z.of_nat (length (mc_seg (v_mc X))))) by lia.
  zstep. zstep.
  zstep.
  destruct (Nat.eq_dec (length (mc_seg (v_mc X))) 0) as [N0|N0].
  - (* 0x141a8: added = 0 and the tail *)
    v1_tkn. zstep.
    eapply tail0; [weq | apply length_zero_iff_nil; exact N0 |].
    eapply mk_mem; [exact PKm | exact MP | exact WMP | exact MI | | | eapply tabs_xport; [exact TB | exact MPf | exact WMf]].
    + eapply rw_cells_cs; [exact FR|]. unfold V01_cells. apply cells_eq11; weq.
    + eexists; exact NC.
  - (* 0x13f58 - 0x13f94: the loop prologue *)
    v1_ntk.
    do 16 zstep.
    eapply head0; [weq | weq | weq | weq | weq | weq | weq | weq | | unfold v_segs; lia].
    unfold V01_lmem.
    eapply mk_mem; [exact PKm | exact MP | exact WMP | exact MI | | | eapply tabs_xport; [exact TB | exact MPf | exact WMf]].
    + eapply rw_cells_cs; [exact FR|]. unfold V01_cells. apply cells_eq11; weq.
    + eexists; exact NC.
Qed.

(** 0x13f38: the else path (no initial entry): mn = 0, 0x40(sp) = 1. *)
Lemma at_else : forall m ms (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30
                             x31 : word) (w8 w18 w20 w28 w30 w38 w40 wn : word) (jn : list byte),
  v_tab0 X = [] ->
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X)
    [C8 (Z_to_bv 64 (v_tab X)); C8 w8; C8 (Z_to_bv 64 (v_cap X)); C8 w18; C8 w20; C8 w28; C8 w30; C8 w38; C8 w40;
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
  rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 wn] -> wn = Z_to_bv 64 0 ->
  rw_cells rsegs m (v_tab X) [CB (Z.to_nat (18 * v_cap X)) (repeat ZERO (Z.to_nat (18 * v_cap X)))] ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) (repeat ZERO (Z.to_nat (v_nmt X)))] ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - v_mm X)) x19 (Z_to_bv 64 (v_mt X)) x21 x22 x23 x24 x25 x26
             (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13f38) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m ms x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    w8 w18 w20 w28 w30 w38 w40 wn jn E0 PKm MP WMP MI FR NC En T0 TG M0.
  subst wn. geo.
  zstep. zstep. zstep. zstep.
  eapply at48; [exact PKm | exact MP | exact WMP | exact MI | exact FR | | | exact NC | |
                eapply tabs_nil; [exact E0 | exact T0 | exact TG | exact M0]].
  - unfold v_n0. rewrite E0. reflexivity.
  - weq.
  - unfold v_n0. rewrite E0. reflexivity.
Qed.

(** 0x13ef4, after memcpy(tab, "enp1s0", 7): tab[0].vid, memcpy(mt, "enp1s0", 7), mt[0].vid, mn = n = 1. *)
Lemma at_ef4 : forall m ms (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30
                            x31 : word) (w8 w18 w20 w28 w30 w38 w40 wn : word) (jn : list byte) (nr : nat),
  v_tab0 X = [(S_enp, 33)] -> 1 <= v_cap X ->
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X)
    [C8 (Z_to_bv 64 (v_tab X)); C8 w8; C8 (Z_to_bv 64 (v_cap X)); C8 w18; C8 w20; C8 w28; C8 w30; C8 w38; C8 w40;
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
  rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 wn] -> wn = Z_to_bv 64 0 ->
  rw_cells rsegs m (v_tab X) [CB 7 (zb (S_enp ++ [0]))] ->
  rw_cells rsegs m (v_tab X + 7) [CB 9 (repeat ZERO 9)] ->
  rw_cells rsegs m (v_tab X + 16) [CB 2 (repeat ZERO 2)] ->
  rw_cells rsegs m (v_tab X + 18) [CB nr (repeat ZERO nr)] -> nr = Z.to_nat (18 * (v_cap X - 1)) ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) (repeat ZERO (Z.to_nat (v_nmt X)))] ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 (Z_to_bv 64 (v_tab X)) x10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 (18446744073709551615 - v_mm X)) x19 (Z_to_bv 64 (v_mt X)) x21 x22 x23 x24 x25 x26
             (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13ef4) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m ms x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    w8 w18 w20 w28 w30 w38 w40 wn jn nr E0 C1 PKm MP WMP MI FR NC En T7 T9 T2 TR ER TG M0.
  subst wn nr. geo. pose proof ap_tm as TM.
  destruct (rw_rep_cut rsegs m (v_mt X) ZERO (Z.to_nat (v_nmt X)) 7 (Z.to_nat (v_nmt X) - 7) (v_mt X + 7) ltac:(lia) ltac:(lia) M0)
    as [M7 M0']. clear M0.
  destruct (rw_rep_cut rsegs m (v_mt X + 7) ZERO (Z.to_nat (v_nmt X) - 7) 9 (Z.to_nat (v_nmt X) - 7 - 9) (v_mt X + 16) ltac:(lia) ltac:(lia)
              M0') as [M9 M0'']. clear M0'.
  destruct (rw_rep_cut rsegs m (v_mt X + 16) ZERO (Z.to_nat (v_nmt X) - 7 - 9) 4 (Z.to_nat (v_nmt X) - 7 - 9 - 4) (v_mt X + 20) ltac:(lia)
              ltac:(lia) M0'') as [M4 MR]. clear M0''.
  zstep.                     (* 0x13ef4 addi s0, zero, 0x21 *)
  zstep.                     (* 0x13ef8 andi a0, s4, 3 *)
  zstep.                     (* 0x13efc sh s0, 0x10(s1) *)
  zstep. v1_ntk.             (* 0x13f00 bnez a0 -> trap *)
  zstep. zstep. zstep. zstep. (* a1 = "enp1s0", a2 = 7, a0 = mt *)
  zstep.                     (* 0x13f14 jal memcpy *)
  destruct (env_frame ms _ (proj1 PKm) MP WMP MI) as (_ & _ & _ & _ & _ & _ & ENP & _ & _).
  eapply evt_cut.
  { eapply HMC with (src := zb (S_enp ++ [0])) (junk := repeat ZERO 7).
    - eapply bytes_at_w; [exact ENP | rewrite unsigned_lit by lia; reflexivity].
    - rewrite unsigned_lit by lia. reflexivity.
    - eapply rw_cells_wn; [exact M7 | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit by lia; reflexivity].
    - rewrite !unsigned_lit by lia. pose proof ap_nm as AP. unfold V01_ENP in AP. lia.
    - exact MI. }
  clear ENP.
  v1_post.
  destruct PO as [M7' ENP']. clear ENP'.
  lazymatch type of M7' with rw_cells _ ?M _ _ =>
    assert (M7 : rw_cells rsegs M (v_mt X) [CB 7 (zb (S_enp ++ [0]))])
      by (eapply rw_cells_conv; [exact M7' | rewrite unsigned_lit by lia; reflexivity |
                                 rewrite unsigned_lit by lia; reflexivity])
  end.
  clear M7'.
  zstep.                     (* 0x13f18 sw s0, 0x10(s4) *)
  zstep. zstep.              (* a1 = 1, a0 = 1 *)
  zstep.                     (* 0x13f24 sd a0, 0x40(sp) *)
  zstep.                     (* 0x13f28 sw a1, 0x5c(sp) *)
  zstep.                     (* a0 = 1 *)
  zstep.                     (* 0x13f30 sd a0, 0x28(sp) *)
  zstep.                     (* 0x13f34 j 0x13f48 *)
  eapply at48; [exact PKm | exact MP | exact WMP | exact MI | exact FR | | | exact NC | |].
  - unfold v_n0. rewrite E0. reflexivity.
  - weq.
  - unfold v_n0. rewrite E0. reflexivity.
  - eapply tabs_one; [exact E0 | exact T7 | exact T9 | exact T2 | weq | exact TR | reflexivity | exact TG |
                      exact M7 | exact M9 | exact M4 | weq | exact MR | lia].
Qed.

(** 0x13ed0, flags & 1 set: cap = 0 goes to the else path; else memcpy(tab, "enp1s0", 7). *)
Lemma at_flag : forall m ms (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30
                             x31 : word) (w8 w18 w20 w28 w30 w38 w40 wn : word) (jn : list byte),
  Z.land (v_flags X) 1 <> 0 ->
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X)
    [C8 (Z_to_bv 64 (v_tab X)); C8 w8; C8 (Z_to_bv 64 (v_cap X)); C8 w18; C8 w20; C8 w28; C8 w30; C8 w38; C8 w40;
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
  w20 = Z_to_bv 64 (v_cap X) ->
  rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 wn] -> wn = Z_to_bv 64 0 ->
  rw_cells rsegs m (v_tab X) [CB (Z.to_nat (18 * v_cap X)) (repeat ZERO (Z.to_nat (18 * v_cap X)))] ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) (repeat ZERO (Z.to_nat (v_nmt X)))] ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 (Z_to_bv 64 (v_tab X)) x10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 (18446744073709551615 - v_mm X)) x19 (Z_to_bv 64 (v_mt X)) x21 x22 x23 x24 x25 x26
             (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13ed0) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m ms x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    w8 w18 w20 w28 w30 w38 w40 wn jn KF PKm MP WMP MI FR E20 NC En T0 TG M0.
  subst w20. geo.
  zstep.                     (* 0x13ed0 ld a0, 0x20(sp) = cap *)
  zstep.                     (* 0x13ed4 beqz a0 -> 0x13f38 *)
  destruct (Z.eq_dec (v_cap X) 0) as [CZ|CZ].
  - v1_tkn.
    eapply at_else; [apply tab0_nil; right; exact CZ | exact PKm | exact MP | exact WMP | exact MI | exact FR |
                     exact NC | exact En | exact T0 | exact TG | exact M0].
  - v1_ntk.
    assert (E0 : v_tab0 X = [(S_enp, 33)])
      by (apply tab0_one; [exact KF | change (seg_cap (v_inp X)) with (v_cap X); lia]).
    pose proof ap_tm as TM.
    destruct (rw_rep_cut rsegs m (v_tab X) ZERO (Z.to_nat (18 * v_cap X)) 7 (Z.to_nat (18 * v_cap X) - 7) (v_tab X + 7) ltac:(lia) ltac:(lia)
                T0) as [T7 T0']. clear T0.
    destruct (rw_rep_cut rsegs m (v_tab X + 7) ZERO (Z.to_nat (18 * v_cap X) - 7) 9 (Z.to_nat (18 * v_cap X) - 7 - 9) (v_tab X + 16) ltac:(lia)
                ltac:(lia) T0') as [T9 T0'']. clear T0'.
    destruct (rw_rep_cut rsegs m (v_tab X + 16) ZERO (Z.to_nat (18 * v_cap X) - 7 - 9) 2 (Z.to_nat (18 * v_cap X) - 7 - 9 - 2) (v_tab X + 18)
                ltac:(lia) ltac:(lia) T0'') as [T2 TR]. clear T0''.
    zstep.                   (* 0x13ed8 andi a0, s1, 1 *)
    zstep. v1_ntk.           (* 0x13edc bnez a0 -> trap *)
    zstep. zstep. zstep. zstep. (* a1 = "enp1s0", a2 = 7, a0 = tab *)
    zstep.                   (* 0x13ef0 jal memcpy *)
    destruct (env_frame ms _ (proj1 PKm) MP WMP MI) as (_ & _ & _ & _ & _ & _ & ENP & _ & _).
    eapply evt_cut.
    { eapply HMC with (src := zb (S_enp ++ [0])) (junk := repeat ZERO 7).
      - eapply bytes_at_w; [exact ENP | rewrite unsigned_lit by lia; reflexivity].
      - rewrite unsigned_lit by lia. reflexivity.
      - eapply rw_cells_wn; [exact T7 | rewrite unsigned_lit by lia; reflexivity |
                             rewrite unsigned_lit by lia; reflexivity].
      - rewrite !unsigned_lit by lia. pose proof ap_nt as AP. unfold V01_ENP in AP. lia.
      - exact MI. }
    clear ENP.
    v1_post.
    destruct PO as [T7' ENP']. clear ENP'.
    lazymatch type of T7' with rw_cells _ ?M _ _ =>
      assert (T7 : rw_cells rsegs M (v_tab X) [CB 7 (zb (S_enp ++ [0]))])
        by (eapply rw_cells_conv; [exact T7' | rewrite unsigned_lit by lia; reflexivity |
                                   rewrite unsigned_lit by lia; reflexivity])
    end.
    clear T7'.
    eapply at_ef4; [exact E0 | lia | exact PKm | exact MP | exact WMP | exact MI | exact FR | exact NC | exact En |
                    exact T7 | exact T9 | exact T2 | exact TR | lia | exact TG | exact M0].
Qed.

(** 0x13ebc, after the guard memset: flags & 1, *n = 0, 0(sp) = tab, then the flags test. *)
Lemma at_ebc : forall m ms (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30
                            x31 : word) (w0 w8 w18 w20 w28 w30 w38 w40 : word) (jn j58 : list byte),
  PK ms -> munch WPL ms m -> wmono rsegs ms m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X)
    [C8 w0; C8 w8; C8 (Z_to_bv 64 (v_cap X)); C8 w18; C8 w20; C8 w28; C8 w30; C8 w38; C8 w40;
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
  w8 = Z_to_bv 64 (v_flags X) -> w20 = Z_to_bv 64 (v_cap X) ->
  rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; CB 4 j58] ->
  rw_cells rsegs m (v_tab X) [CB (Z.to_nat (18 * v_cap X)) (repeat ZERO (Z.to_nat (18 * v_cap X)))] ->
  rw_cells rsegs m (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES] ->
  rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) (repeat ZERO (Z.to_nat (v_nmt X)))] ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 (Z_to_bv 64 (v_tab X)) x10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 (18446744073709551615 - v_mm X)) x19 (Z_to_bv 64 (v_mt X)) x21 x22 x23 x24 x25 x26
             (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 0x13ebc) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m ms x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    w0 w8 w18 w20 w28 w30 w38 w40 jn j58 PKm MP WMP MI FR E8 E20 NC T0 TG M0.
  subst w8 w20. geo.
  zstep.                     (* 0x13ebc ld a0, 8(sp) = flags *)
  zstep.                     (* 0x13ec0 andi a0, a0, 1 *)
  zstep.                     (* 0x13ec4 sw zero, 0x5c(sp) *)
  zstep.                     (* 0x13ec8 sd s1, 0(sp) *)
  zstep.                     (* 0x13ecc beqz a0 -> 0x13f38 *)
  let K := fresh "K" in if_cases K; cbv iota; zify_cond K.
  - eapply at_else; [apply tab0_nil; left; exact K | exact PKm | exact MP | exact WMP | exact MI | exact FR |
                     exact NC | weq | exact T0 | exact TG | exact M0].
  - eapply at_flag; [exact K | exact PKm | exact MP | exact WMP | exact MI | exact FR | reflexivity | exact NC | weq |
                     exact T0 | exact TG | exact M0].
Qed.

(** 0x13e90: the NULL tests, the guard's address and memset. *)
Lemma inner : V01_INNER X.
Proof.
  unfold V01_INNER, V01_PC_IN.
  intros m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    fcell0 fcell8 fcell18 fcell20 fcell28 fcell30 fcell38 fcell40 j58 ENV MU WM FR E8 E20 (jn & NC) JB BT BM RT RM.
  subst fcell8 fcell20. geo. pose proof ap_tm as TM.
  assert (PKm : PK m) by exact (conj ENV (conj MU (conj WM JB))).
  pose proof (proj1 ENV) as MI. clear ENV MU WM JB.
  destruct RT as (ft & RT). destruct RM as (fm & RM).
  pose proof (rw_of_bytes rsegs m (v_tab X) _ _ _ BT RT (repeat_length _ _)) as T. clear BT RT.
  pose proof (rw_of_bytes rsegs m (v_mt X) _ _ _ BM RM (repeat_length _ _)) as M0. clear BM RM.
  destruct (rw_rep_cut rsegs m (v_tab X) ZERO (Z.to_nat (v_ntab X)) (Z.to_nat (18 * v_cap X)) 18 (v_tab X + 18 * v_cap X) ltac:(lia)
              ltac:(lia) T) as [T0 TG0]. clear T.
  pose proof (munch_refl WPL m) as MP. pose proof (wmono_refl rsegs m) as WMP.
  zstep. v1_ntk.             (* 0x13e90 beqz s1 -> abort *)
  zstep.                     (* 0x13e94 mv s4, a0 *)
  zstep. v1_ntk.             (* 0x13e98 beqz a0 -> abort *)
  zstep. zstep. zstep.       (* a0 = 18 cap, a1 = ~tab *)
  zstep. v1_ntk.             (* 0x13ea8 bltu a1, a0 -> trap *)
  zstep. zstep. zstep.       (* a0 = tab + 18 cap, a1 = 0x5a, a2 = 18 *)
  zstep.                     (* 0x13eb8 jal memset *)
  eapply evt_cut.
  { eapply HMS with (junk := repeat ZERO 18); [|exact MI].
    eapply rw_cells_wn; [exact TG0 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; reflexivity]. }
  v1_post.
  lazymatch type of PO with rw_cells _ ?M _ _ =>
    assert (TG : rw_cells rsegs M (v_tab X + 18 * v_cap X) [CB 18 GUARD_BYTES])
      by (eapply rw_cells_conv; [exact PO | rewrite unsigned_lit by lia; lia | vm_compute; reflexivity])
  end.
  clear PO.
  eapply at_ebc; [exact PKm | exact MP | exact WMP | exact MI | exact FR | reflexivity | reflexivity | exact NC |
                  exact T0 | exact TG | exact M0].
Qed.

End Walk.

Lemma v01_pre : forall X : V01D.vctx, V01D.V01_geo X -> MainB.K_V01 -> V01D.V01_HEAD X -> V01D.V01_TAIL X ->
  V01D.V01_INNER X.
Proof.
  intros X HG HK HH HT. destruct HK as (HMS & HMC & _).
  exact (inner X HG HMS HMC HH HT).
Qed.
