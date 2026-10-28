(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl F_strncasecmp.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Lemma land_shiftl_small_ci : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_small_ci : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_small_ci; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small_ci; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4_ci : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_small_ci b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_small_ci b2 b3 8) by lia.
  rewrite (lor_shiftl_small_ci (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.

Lemma land64_shl_small_ci : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Definition ATKEYCI : Z := 0x3fac4.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section ObjKci.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma sbs_byte_ci : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.

  Definition sbuf_bytes_ci (o l : Z) : list byte := firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) (ae_sbs E))).
  Lemma sbuf_bytes_at_ci : forall m o l, bytes_at usegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) -> 0 <= o -> 0 <= l -> o + 4 + l < ae_sn E ->
    bytes_at usegs m (ae_SBUF E + o + 4) (sbuf_bytes_ci o l) /\ length (sbuf_bytes_ci o l) = Z.to_nat l.
  Proof.
    intros m o l HB Ho Hl Hol. unfold sbuf_bytes_ci. split.
    - replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. lia.
  Qed.

  Definition kinv_ci (mL : mem) (spv lo : Z) (m : mem) : Prop :=
    mem_inv usegs m /\ stk usegs m lo spv /\ munch [(spv - 48, spv)] mL m /\ wmono usegs mL m.

  Lemma kinv_step_ci : forall mL spv lo m m', kinv_ci mL spv lo m ->
    munch [(spv - 48, spv)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' lo spv -> kinv_ci mL spv lo m'.
  Proof.
    intros mL spv lo m m' (MI & ST & MU & WM) MU' WM' MI' ST'. split; [exact MI'|]. split; [exact ST'|].
    split; [eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']].
  Qed.

  Lemma kinv_refl_ci : forall mL spv lo, mem_inv usegs mL -> stk usegs mL lo spv -> kinv_ci mL spv lo mL.
  Proof. intros mL spv lo MI ST. split; [exact MI|]. split; [exact ST|]. split; [apply munch_refl| apply wmono_refl]. Qed.

  Lemma kinv_facts_ci : forall mL spv lo m Kp L kb,
    bytes_at usegs mL (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    bytes_at usegs mL (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    rw_cells usegs mL (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    bytes_at usegs mL Kp kb -> Z.of_nat (length kb) = L -> rw_cells usegs mL (spv + 16) [C8 (Z_to_bv 64 Kp)] ->
    ae_TAPE E + 8 * ae_n E <= spv - 48 -> ae_SBUF E + ae_sn E <= spv - 48 -> spv <= ae_DOC E -> (Kp + L <= spv - 48 \/ L = 0) ->
    kinv_ci mL spv lo m ->
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) /\ bytes_at usegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) /\
    rw_cells usegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] /\
    bytes_at usegs m Kp kb /\ rw_cells usegs m (spv + 16) [C8 (Z_to_bv 64 Kp)] /\ mem_inv usegs m /\ stk usegs m lo spv.
  Proof.
    intros mL spv lo m Kp L kb TB SB DC KB KL K16 TR SR DS KR (MI & ST & MU & WM).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [| split; [| split; [| split; [| split; [| split; [exact MI| exact ST]]]]]].
    - eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia.
    - eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. lia.
    - eapply rw_cells_agree; [exact AG| exact DC|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
    - eapply bytes_at_agree; [exact AG| exact KB|]. intros a Ha. cbn [outside]. lia.
    - eapply rw_cells_agree; [exact AG| exact K16|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
  Qed.

  Lemma atkeyci_loop : forall (K : machine_state -> Prop) (mL : mem) (F : bvmap 5 word) (fc : bv 32) (e spv lo Kp L : Z) (kb : list byte)
      (x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
    bytes_at usegs mL (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    bytes_at usegs mL (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    rw_cells usegs mL (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    bytes_at usegs mL Kp kb -> Z.of_nat (length kb) = L -> 0 <= Kp -> Kp + L < 2^63 ->
    rw_cells usegs mL (spv + 16) [C8 (Z_to_bv 64 Kp)] ->
    ae_TAPE E + 8 * ae_n E <= spv - 48 -> ae_SBUF E + ae_sn E <= spv - 48 -> spv <= ae_DOC E -> (Kp + L <= spv - 48 \/ L = 0) ->
    e + 1 <= ae_n E - 1 -> 0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling ->
    0 < ae_TAPE E -> ae_TAPE E + 8 * ae_n E < 2^63 -> ae_TAPE E mod 8 = 0 -> 0 < ae_DOC E -> ae_DOC E + 16 < 2^64 -> 0 <= spv -> spv + 24 < 2^63 ->
    lo + 48 <= spv ->
    (forall (it j' : Z) (m : mem) (x1 x10 x11 x12 x13 x14 x21 : word),
       is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e ->
       kinv_ci mL spv lo m ->
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) x21 (Z_to_bv 64 e)
                          (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x3fd50) fc None m (seg_rom usegs))) ->
    (forall (m : mem) (x1 x10 x11 x12 x13 x14 x20 x21 : word),
       kinv_ci mL spv lo m ->
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) x20 x21 (Z_to_bv 64 e)
                          (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x3fbac) fc None m (seg_rom usegs))) ->
    forall (n : nat) (it c' : Z) (m : mem) (x1 x10 x11 x12 x13 x14 x21 : word),
      tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      kinv_ci mL spv lo m ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) x21 (Z_to_bv 64 e)
                         (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x3fc44) fc None m (seg_rom usegs)).
  Proof.
    intros K mL F fc e spv lo Kp L kb x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 TBL SBL DCL KBL KL KP0 KPL K16L TRS SRS DCS KRS
      EN SR T0 TN T8 D0 D16 SP0 SP24 LOSP XFOUND XNF.
    pose proof alloc_ceiling_range as CR.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' m x1 x10 x11 x12 x13 x14 x21 TI NE I0 FUEL KI.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    destruct (kinv_facts_ci mL spv lo m Kp L kb TBL SBL DCL KBL KL K16L TRS SRS DCS KRS KI) as (TAPEB & SBUFB & DOCC & KB & K16 & MI & ST).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').
    pose proof (key_word_range _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDK.

    step. if_false. step. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it) (RA := 0x3fc54);
      [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. if_false. step. step. astep. rewrite KM. astep. step. if_lia.

    astep. astep.
    replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
    first [ replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (o + ae_SBUF E <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
    cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false. step. if_lia.

    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byte_ci o ltac:(lia)) as B0. pose proof (sbs_byte_ci (o + 1) ltac:(lia)) as B1.
    pose proof (sbs_byte_ci (o + 2) ltac:(lia)) as B2. pose proof (sbs_byte_ci (o + 3) ltac:(lia)) as B3.
    astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small_ci by lia. rewrite le32_of_lbu4_ci by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.

    assert (NEXT : forall (m1 : mem) (x1' x10' x11' x12' x13' x14' : word), kinv_ci mL spv lo m1 ->
      evt usegs K (MS (mkR x1' (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                         x10' x11' x12' x13' x14' x15 x16 x17 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) x21 (Z_to_bv 64 e)
                         (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x3fce8) fc None m1 (seg_rom usegs))).
    { intros m1 x1' x10' x11' x12' x13' x14' KI1.
      clear MU WM.
      destruct (kinv_facts_ci mL spv lo m1 Kp L kb TBL SBL DCL KBL KL K16L TRS SRS DCS KRS KI1) as (TAPEB1 & SBUFB1 & DOCC1 & KB1 & K161 & MI1 & ST1).
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB1 ltac:(lia)) as RDV.
      pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
      pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) (it + 1) TAPEB1 ltac:(lia) TIR) as RDB.
      assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).

      astep. step. step. step.
      eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it + 1) (RA := 0x3fcf8);
        [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
      intros za1 za2 za3 za4.

      assert (LT : forall (pc : Z) (w1 w10 w11 w12 w13 w14 : word), (pc = 0x3fd14 \/ pc = 0x3fd3c \/ pc = 0x3fd48) ->
        evt usegs K (MS (mkR w1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                           w10 w11 w12 w13 w14 x15 x16 x17 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 j') (Z_to_bv 64 (it + 1)) (Z_to_bv 64 e)
                           (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) x28 x29 x30 x31)
                      F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs))).
      { intros pc w1 w10 w11 w12 w13 w14 [-> |[-> | ->]]; (step; if_cases KLT; zify_cond KLT;
          [ eapply evt_eq; [| eapply (IH j' (c' - 1))]; [atp_st_eq| exact TI'| exact KLT| lia| lia| exact KI1]
          | step; eapply evt_eq; [| eapply XNF]; [atp_st_eq| exact KI1] ]). }
      destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
        as [TY Ej|TY Ej|TY Ej STR2|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
      -
        unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY in RDB;
          (astep; astep; step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
           eapply evt_eq; [| eapply (LT 0x3fd48)]; [atp_st_eq| do 2 right; reflexivity]).
      -
        unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY in RDB;
          (astep; astep; step; if_false; astep; astep; step; if_false; astep;
           eapply evt_eq; [| eapply (LT 0x3fd14)]; [atp_st_eq| left; reflexivity]).
      -
        unfold t_str in TY. rewrite TY in RDB.
        astep. astep. step. if_true. astep.
        eapply evt_eq; [| eapply (LT 0x3fd48)]; [atp_st_eq| do 2 right; reflexivity].
      -
        unfold t_arr in TY. rewrite TY in RDB.
        astep. astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.
        step. step. step.
        eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it + 1) (RA := 0x3fd34);
          [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
        intros wa1 wa2 wa3 wa4.
        step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x3fd3c)]; [atp_st_eq| right; left; reflexivity].
      -
        unfold t_obj in TY. rewrite TY in RDB.
        astep. astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.
        step. step. step.
        eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it + 1) (RA := 0x3fd34);
          [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
        intros wa1 wa2 wa3 wa4.
        step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
        eapply evt_eq; [| eapply (LT 0x3fd3c)]; [atp_st_eq| right; left; reflexivity]. }

    step. if_cases KEQ; zify_cond KEQ.
    { eapply evt_eq; [| eapply NEXT]; [atp_st_eq| exact KI]. }

    step. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it) (RA := 0x3fcb8);
      [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros yb1 yb2 yb3 yb4.
    step. step. if_lia. step. astep. rewrite KM. astep. astep. step. if_lia. step. if_lia.

    destruct (sbuf_bytes_at_ci m o l SBUFB ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    step. step. step.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (sncc_spec_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m spv lo Kp (ae_SBUF E + o + 4) kb (sbuf_bytes_ci o l)
                                  ltac:(rewrite QL; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Z_to_bv 64 0))];
        [atp_st_eq| | exact KB| exact QB| exact MI| exact ST].
      destruct KRS as [KR'|KR']; [right; split; lia| left; lia]. }
    cbv beta. intros ms' (r & a1' & a2' & m' & -> & MU' & WM' & MI' & ST').
    replace (ret_pc (Z_to_bv 64 0x3fce4)) with (Z_to_bv 64 0x3fce4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kinv_step_ci _ _ _ _ _ KI MU' WM' MI' ST') as KI'.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl usegs m') as WM.

    step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact STR| exact EL| lia| lia| exact KI']. }
    eapply evt_eq; [| eapply NEXT]; [atp_st_eq| exact KI'].
  Qed.

  Definition atkeyci_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo out e : Z) (od : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (r0 : word) (it code : Z),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(q - 176, q); (out, out + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
      /\ rw_cells usegs m' out [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 od]
      /\ ((code = 0 /\ r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= it /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' /\ j' <= e)
          \/ (code = 20 /\ r0 = Z_to_bv 64 0 /\ it = 0)).

  Lemma atkeyci_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo out N2 i e c Kp L : Z) (kb : list byte) (oa ob oc od : list byte),
    rw_cells usegs m N2 [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= N2 -> N2 + 16 < 2^63 ->
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    bytes_at usegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    rw_cells usegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    bytes_at usegs m Kp kb -> Z.of_nat (length kb) = L -> (0 < L -> 0 < Kp) -> Kp + L < 2^63 -> (Kp + L <= q - 176 \/ L = 0) -> (Kp + L <= out \/ out + 24 <= Kp) ->
    rw_cells usegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> q <= out -> out + 24 < 2^63 ->
    (0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling) -> (0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling) ->
    stk usegs m lo q -> lo <= q - 176 -> ae_lo E <= lo -> mem_inv usegs m -> 0 <= q -> q <= ae_DOC E ->
    evt usegs (atkeyci_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 N2) (Z_to_bv 64 Kp) (Z_to_bv 64 L) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATKEYCI) fc None m (seg_rom usegs)).
  Proof.
    intros until od. intros N2C QN N63 TAPEB SBUFB DOCC TY NXT TILES I0 EN KB KL KP0 KPL KDJ KO OUT QO O63 TR SR ST LO LOLO MI Q0 QD.
    unfold ATKEYCI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    unfold GLOBALS_TOP in GLO.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.
    assert (L0 : 0 <= L) by lia. assert (KPN : 0 <= Kp) by (destruct KB as [KPN _]; exact KPN).
    pose proof (munch_refl [(q - 176, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

    hide TAPEB. hide SBUFB. hide KB.
    step. carve_frame 128%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 128 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 13 step. hstep. name_mem m1.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -128 + Z.of_nat 8) with (q + -120) in FR by lia.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FROUT FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -120 + Z.of_nat 8) with (q + -112) in FR by lia.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FRKP FRHI]. cbn [cells_size csize Nat.add] in FRHI.
    replace (q + -112 + Z.of_nat 8) with (q + -104) in FRHI by lia.

    assert (VIEWS : forall mx, munch [(q - 176, q); (out, out + 24)]%Z m mx -> wmono usegs m mx ->
              bytes_at usegs mx (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) /\ bytes_at usegs mx (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E))
              /\ bytes_at usegs mx Kp kb).
    { intros mx MUx WMx. unhide TAPEB. unhide SBUFB. unhide KB.
      pose proof (agree_on_of_munch _ _ _ MUx WMx) as AG.
      split; [| split].
      - eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha. cbn [outside]. lia.
      - eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha. cbn [outside]. lia.
      - eapply bytes_at_agree; [exact AG| exact KB|]. intros a Ha. cbn [outside]. lia. }
    destruct (VIEWS m1 MU WM) as (TAPEB1 & SBUFB1 & KB1).

    step. step. if_lia. step. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false.
    step. step. step. step. step.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia)) as RDT.
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia) TIR) as RDB. rewrite TY in RDB. unfold t_obj in RDB.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := i) (RA := 0x3fb28);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    astep. astep. astep. hstep. name_mem m2.
    step. if_false. astep. astep. astep. astep. step. if_true.

    astep. astep. astep. astep. astep. step. if_false.
    step. step. if_lia. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false. step. step.
    destruct (VIEWS m2 MU WM) as (TAPEB2 & SBUFB2 & KB2).
    pose proof (tape_read_lo32 E m2 i TAPEB2 ltac:(lia)) as RDL.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := i) (RA := 0x3fb8c);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros xb1 xb2 xb3 xb4.

    step. rewrite zx32_tnext by lia. rewrite NXT. step. step. astep. astep.

    assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m3 : mem)
                         (r0 : word) (it code : Z),
      rw_cells usegs m3 (q + -128) [CB 8 (firstn 8 junk)] -> rw_cells usegs m3 (q + -120) [C8 (Z_to_bv 64 out)] -> rw_cells usegs m3 (q + -112) [C8 (Z_to_bv 64 Kp)] ->
      rw_cells usegs m3 (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv usegs m3 -> stk usegs m3 lo (q + -128) -> munch [(q - 176, q); (out, out + 24)] m m3 -> wmono usegs m m3 ->
      rw_cells usegs m3 out [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 od] ->
      ((code = 0 /\ r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= it /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' /\ j' <= e)
          \/ (code = 20 /\ r0 = Z_to_bv 64 0 /\ it = 0)) ->
      evt usegs (atkeyci_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
        (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3fbc4) fc None m3 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m3 r0 it code
             EFR0 EFROUT EFRKP EFRHI EMI EST EMU EWM EOUT ERES.
      do 13 step. step.
      destruct (rw_cells_forget _ _ _ _ EFROUT) as [j1 EFROUT']. destruct (rw_cells_forget _ _ _ _ EFRKP) as [j2 EFRKP'].
      cbn [cells_size csize Nat.add] in EFROUT', EFRKP'.
      release_frame EFR0 EST (q + -120). release_frame EFROUT' EST (q + -112). release_frame EFRKP' EST (q + -104). release_frame EFRHI EST q.
      step.
      apply evt_done. unfold atkeyci_post. do 16 eexists. exists r0, it, code.
      split; [atp_st_eq_goal|]. split; [exact EMU|]. split; [exact EWM|]. split; [exact EMI|]. split; [exact EST|]. split; [exact EOUT| exact ERES]. }
    assert (XNF : forall (mx : mem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      kinv_ci m2 (q + -128) lo mx ->
      evt usegs (atkeyci_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
        (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3fbac) fc None mx (seg_rom usegs))).
    { intros mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (MIx & STx & MUx & WMx).
      transport_after_call usegs m2 mx MUx WMx. clear MUx WMx.

      step. step. if_lia. astep. hstep. hstep. hstep. name_mem m3.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -128) _ |- _ => rename H into EFR0 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -120) _ |- _ => rename H into EFROUT end.
      lazymatch goal with H : rw_cells usegs m3 (q + -112) _ |- _ => rename H into EFRKP end.
      lazymatch goal with H : rw_cells usegs m3 (q + -104) _ |- _ => rename H into EFRHI end.
      lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : munch _ m m3 |- _ => rename H into MU3 end.
      lazymatch goal with H : wmono usegs m m3 |- _ => rename H into WM3 end.
      eapply EPI; [exact EFR0| exact EFROUT| exact EFRKP| exact EFRHI| exact MI3| exact ST3| exact MU3| exact WM3| exact OUT3|].
      right. split; [reflexivity|]. split; reflexivity. }

    step. if_cases KE; zify_cond KE; [| eapply XNF; apply kinv_refl_ci; assumption].

    step. astep. astep. astep. astep.
    astep. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. astep. astep. astep. astep. astep.
    replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (ae_DOC E <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z Z.ltb Z.land Z.lor Z.compare Pos.compare].
    astep. astep. astep. astep. astep.

    assert (XFOUND : forall (it j' : Z) (mx : mem) (x1 x10 x11 x12 x13 x14 x21 : word),
       is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e ->
       kinv_ci m2 (q + -128) lo mx ->
       evt usegs (atkeyci_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
         (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 67240448) (Z_to_bv 64 L)
                  x10 x11 x12 x13 x14 (Z_to_bv 64 1) a6 a7 (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) x21 (Z_to_bv 64 e)
                  (Z_to_bv 64 32) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 72057594037927935) (Z_to_bv 64 4294967295) t3 t4 t5 t6)
             F (Z_to_bv 64 0x3fd50) fc None mx (seg_rom usegs))).
    { intros it j' mx x1 x10 x11 x12 x13 x14 x21 STR EL IT0 JE (MIx & STx & MUx & WMx).
      transport_after_call usegs m2 mx MUx WMx. clear MUx WMx.
      step. step. if_lia. astep. hstep. hstep. hstep. name_mem m3. step.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -128) _ |- _ => rename H into EFR0 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -120) _ |- _ => rename H into EFROUT end.
      lazymatch goal with H : rw_cells usegs m3 (q + -112) _ |- _ => rename H into EFRKP end.
      lazymatch goal with H : rw_cells usegs m3 (q + -104) _ |- _ => rename H into EFRHI end.
      lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : munch _ m m3 |- _ => rename H into MU3 end.
      lazymatch goal with H : wmono usegs m m3 |- _ => rename H into WM3 end.
      eapply EPI; [exact EFR0| exact EFROUT| exact EFRKP| exact EFRHI| exact MI3| exact ST3| exact MU3| exact WM3| exact OUT3|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. exists j'. split; [exact EL| lia]. }
    eapply evt_eq; [| eapply (atkeyci_loop _ m2 F fc e (q + -128) lo Kp L kb _ _ _ _ _ _ _ _ _ _ _ TAPEB2 SBUFB2 DOCC KB2 KL ltac:(lia) KPL
                                ltac:(lazymatch goal with H : rw_cells usegs m2 (q + -112) _ |- _ => replace (q + -128 + 16) with (q + -112) by lia; exact H end)
                                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct KDJ as [KD|KD]; [left| right]; lia)
                                EN SR ltac:(lia) ltac:(lia) AL8T ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                                ltac:(intros it_ j_ mm y1 y10 y11 y12 y13 y14 y21 A1 A2 A3 A4 A5; apply (XFOUND it_ j_ mm y1 y10 y11 y12 y13 y14 y21 A1 A2 A3 A4 A5))
                                ltac:(intros; eapply XNF; eassumption) (S (Z.to_nat (e - (i + 1)))) (i + 1) c m2)];
      [atp_st_eq| exact TILES| exact KE| lia| lia| apply kinv_refl_ci; assumption].
  Qed.
End ObjKci.
End WithCeiling0.
