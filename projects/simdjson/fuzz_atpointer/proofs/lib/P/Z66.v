(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Z9o Z44.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma land_shiftl_small : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_small : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_small b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_small b2 b3 8) by lia.
  rewrite (lor_shiftl_small (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.

Lemma land64_shl_small : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma sbs_byte : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.

  Definition sbuf_bytes (o l : Z) : list byte := firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) (ae_sbs E))).
  Lemma sbuf_bytes_at : forall m o l, bytes_at psegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) -> 0 <= o -> 0 <= l -> o + 4 + l < ae_sn E ->
    bytes_at psegs m (ae_SBUF E + o + 4) (sbuf_bytes o l) /\ length (sbuf_bytes o l) = Z.to_nat l.
  Proof.
    intros m o l HB Ho Hl Hol. unfold sbuf_bytes. split.
    - replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. lia.
  Qed.

  Lemma obj_key_loop1 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e spv Kp L : Z) (kb : list byte)
      (x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    bytes_at psegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    bytes_at psegs m Kp kb -> Z.of_nat (length kb) = L -> 0 <= Kp -> Kp + L < 2^63 ->
    rw_cells psegs m (spv + 64) [C8 (Z_to_bv 64 4294967295)] ->
    e + 1 <= ae_n E - 1 -> mem_inv psegs m -> 0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling ->
    (forall (it j' : Z) (x1 x10 x11 x12 x13 x14 x23 : word),
       is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 it) (Z_to_bv 64 72057594037927935)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 Kp) (Z_to_bv 64 L)
                          (Z_to_bv 64 (ae_TAPE E)) x23 (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x2832c) fc None m (seg_rom psegs))) ->
    (forall (x1 x8 x10 x11 x12 x13 x14 x23 : word),
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 Kp) (Z_to_bv 64 L)
                          (Z_to_bv 64 (ae_TAPE E)) x23 (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x2830c) fc None m (seg_rom psegs))) ->
    forall (n : nat) (it c' : Z) (x1 x10 x11 x12 x13 x14 x23 : word),
      tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 it) (Z_to_bv 64 72057594037927935)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 Kp) (Z_to_bv 64 L)
                         (Z_to_bv 64 (ae_TAPE E)) x23 (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x28268) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc e spv Kp L kb x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 TAPEB SBUFB KB KL KP0 KPL M64 EN MI SR XFOUND XNF.
    pose proof alloc_ceiling_range as CR.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' x1 x10 x11 x12 x13 x14 x23 TI NE I0 FUEL.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').
    pose proof (key_word_range _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDK.

    astep. astep. step. astep. rewrite KM. astep.

    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byte o ltac:(lia)) as B0. pose proof (sbs_byte (o + 1) ltac:(lia)) as B1.
    pose proof (sbs_byte (o + 2) ltac:(lia)) as B2. pose proof (sbs_byte (o + 3) ltac:(lia)) as B3.

    astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.

    assert (NEXT : forall (x1' x10' x11' x12' x13' x14' : word),
      evt psegs K (MS (mkR x1' (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 it) (Z_to_bv 64 72057594037927935)
                         x10' x11' x12' x13' x14' x15 x16 x17 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 Kp) (Z_to_bv 64 L)
                         (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (8 * it)) (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x282bc) fc None m (seg_rom psegs))).
    { intros x1' x10' x11' x12' x13' x14'.
      pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB ltac:(lia)) as RDV.
      pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
      assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).

      astep. step. astep. astep.

      assert (LT : forall (pc : Z) (x10'' x11'' x12'' : word), (pc = 0x282e0 \/ pc = 0x282fc \/ pc = 0x28308) ->
        evt psegs K (MS (mkR x1' (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 j') (Z_to_bv 64 72057594037927935)
                           x10'' x11'' x12'' x13' x14' x15 x16 x17 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 Kp) (Z_to_bv 64 L)
                           (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (ae_TAPE E + 8 + 8 * it)) (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E))
                           x28 x29 x30 x31)
                      F (Z_to_bv 64 pc) fc None m (seg_rom psegs))).
      { intros pc x10'' x11'' x12'' [-> |[-> | ->]]; (step; if_cases KLT; zify_cond KLT;
          [ eapply (IH j' (c' - 1)); [exact TI'| exact KLT| lia| lia]
          | first [apply XNF | step; apply XNF] ]). }
      destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
        as [TY Ej|TY Ej|TY Ej STR2|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
      -
        unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
          (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
           eapply evt_eq; [| eapply (LT 0x28308)]; [atp_st_eq| do 2 right; reflexivity]).
      -
        unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
          (step; if_false; astep; astep; step; if_false; astep;
           eapply evt_eq; [| eapply (LT 0x282e0)]; [atp_st_eq| left; reflexivity]).
      -
        unfold t_str in TY. rewrite TY.
        step. if_true. astep.
        eapply evt_eq; [| eapply (LT 0x28308)]; [atp_st_eq| do 2 right; reflexivity].
      -
        unfold t_arr in TY. rewrite TY.
        step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. step. astep.
        rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x282fc)]; [atp_st_eq| right; left; reflexivity].
      -
        unfold t_obj in TY. rewrite TY.
        step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. step. astep.
        rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x282fc)]; [atp_st_eq| right; left; reflexivity]. }

    step. if_cases KEQ; zify_cond KEQ.
    { eapply evt_eq; [| eapply NEXT]; [atp_st_eq]. }

    destruct (sbuf_bytes_at m o l SBUFB ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    astep. step. step. step.
    eapply evt_cut.
    { eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m Kp (ae_SBUF E + o + 4) kb (sbuf_bytes o l));
        [reflexivity| f_equal; lia| f_equal; lia| rewrite QL; lia| lia| lia| lia| lia| exact KB| exact QB| exact MI]. }
    cbv beta. intros ms' (r & a1' & a2' & a3' & a4' & -> & HR).
    replace (ret_pc (Z_to_bv 64 0x282b8)) with (Z_to_bv 64 0x282b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact STR| exact EL| lia| lia]. }
    eapply evt_eq; [| eapply NEXT]; [atp_st_eq].
  Qed.

  Lemma obj_key_loop2 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e spv Kp L : Z) (kb : list byte)
      (x3 x5 x6 x7 x8 x15 x16 x17 x28 x29 x30 x31 : word),
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    bytes_at psegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    bytes_at psegs m Kp kb -> Z.of_nat (length kb) = L -> 0 <= Kp -> Kp + L < 2^63 ->
    rw_cells psegs m (spv + 64) [C8 (Z_to_bv 64 4294967297)] -> rw_cells psegs m (spv + 32) [C8 (Z_to_bv 64 4294967295)] ->
    e + 1 <= ae_n E - 1 -> mem_inv psegs m -> 0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling ->
    (forall (it j' : Z) (x1 x10 x11 x12 x13 x14 x27 : word),
       is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 it) (Z_to_bv 64 Kp) (Z_to_bv 64 67240448) (Z_to_bv 64 e) (Z_to_bv 64 L)
                          (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 32) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 (ae_TAPE E + 8)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x28600) fc None m (seg_rom psegs))) ->
    (forall (x1 x10 x11 x12 x13 x14 x18 x27 : word),
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                          x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 Kp) (Z_to_bv 64 67240448) (Z_to_bv 64 e) (Z_to_bv 64 L)
                          (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 32) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 (ae_TAPE E + 8)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x285e0) fc None m (seg_rom psegs))) ->
    forall (n : nat) (it c' : Z) (x1 x10 x11 x12 x13 x14 x27 : word),
      tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 it) (Z_to_bv 64 Kp) (Z_to_bv 64 67240448) (Z_to_bv 64 e) (Z_to_bv 64 L)
                         (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 32) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 (ae_TAPE E + 8)) x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x28538) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc e spv Kp L kb x3 x5 x6 x7 x8 x15 x16 x17 x28 x29 x30 x31 TAPEB SBUFB KB KL KP0 KPL M64 M32 EN MI SR XFOUND XNF.
    pose proof alloc_ceiling_range as CR.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' x1 x10 x11 x12 x13 x14 x27 TI NE I0 FUEL.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').
    pose proof (key_word_range _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDK.

    astep. astep. step. astep. rewrite KM. astep.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byte o ltac:(lia)) as B0. pose proof (sbs_byte (o + 1) ltac:(lia)) as B1.
    pose proof (sbs_byte (o + 2) ltac:(lia)) as B2. pose proof (sbs_byte (o + 3) ltac:(lia)) as B3.

    astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.

    assert (NEXT : forall (x1' x10' x11' x12' x13' x14' : word),
      evt psegs K (MS (mkR x1' (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                         x10' x11' x12' x13' x14' x15 x16 x17 (Z_to_bv 64 it) (Z_to_bv 64 Kp) (Z_to_bv 64 67240448) (Z_to_bv 64 e) (Z_to_bv 64 L)
                         (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 32) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (8 * it)) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x2858c) fc None m (seg_rom psegs))).
    { intros x1' x10' x11' x12' x13' x14'.
      pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB ltac:(lia)) as RDV.
      pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
      assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).

      astep. step. astep. astep.
      assert (LT : forall (pc : Z) (x11'' x12'' : word), (pc = 0x285b0 \/ pc = 0x285d0 \/ pc = 0x285dc) ->
        evt psegs K (MS (mkR x1' (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 72057594037927935)
                           (Z_to_bv 64 (ae_T E (it + 1))) x11'' x12'' x13' x14' x15 x16 x17 (Z_to_bv 64 j') (Z_to_bv 64 Kp) (Z_to_bv 64 67240448) (Z_to_bv 64 e) (Z_to_bv 64 L)
                           (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 32) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_TAPE E + 8 + 8 * it))
                           x28 x29 x30 x31)
                      F (Z_to_bv 64 pc) fc None m (seg_rom psegs))).
      { intros pc x11'' x12'' [-> |[-> | ->]]; (step; if_cases KLT; zify_cond KLT;
          [ eapply (IH j' (c' - 1)); [exact TI'| exact KLT| lia| lia]
          | first [apply XNF | step; apply XNF] ]). }
      destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
        as [TY Ej|TY Ej|TY Ej STR2|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
      - unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
          (step; if_false; astep; astep; step; if_true; step; astep; astep; step; if_true; astep;
           eapply evt_eq; [| eapply (LT 0x285dc)]; [atp_st_eq| do 2 right; reflexivity]).
      - unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
          (step; if_false; astep; astep; step; if_false; astep;
           eapply evt_eq; [| eapply (LT 0x285b0)]; [atp_st_eq| left; reflexivity]).
      - unfold t_str in TY. rewrite TY.
        step. if_true. astep.
        eapply evt_eq; [| eapply (LT 0x285dc)]; [atp_st_eq| do 2 right; reflexivity].
      - unfold t_arr in TY. rewrite TY.
        step. if_false. astep. astep. step. if_true. step. astep. astep. step. if_false. step. astep.
        rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x285d0)]; [atp_st_eq| right; left; reflexivity].
      - unfold t_obj in TY. rewrite TY.
        step. if_false. astep. astep. step. if_true. step. astep. astep. step. if_false. step. astep.
        rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x285d0)]; [atp_st_eq| right; left; reflexivity]. }

    step. if_cases KEQ; zify_cond KEQ.
    { eapply evt_eq; [| eapply NEXT]; [atp_st_eq]. }

    destruct (sbuf_bytes_at m o l SBUFB ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    astep. step. step. step.
    eapply evt_cut.
    { eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m Kp (ae_SBUF E + o + 4) kb (sbuf_bytes o l));
        [reflexivity| f_equal; lia| f_equal; lia| rewrite QL; lia| lia| lia| lia| lia| exact KB| exact QB| exact MI]. }
    cbv beta. intros ms' (r & a1' & a2' & a3' & a4' & -> & HR).
    replace (ret_pc (Z_to_bv 64 0x28588)) with (Z_to_bv 64 0x28588) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact STR| exact EL| lia| lia]. }
    eapply evt_eq; [| eapply NEXT]; [atp_st_eq].
  Qed.

End Obj.
End WithCeiling0.
