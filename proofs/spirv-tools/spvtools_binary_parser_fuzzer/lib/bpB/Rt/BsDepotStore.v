(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsAtomics BsDepotInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition IMEMCPY : Z := 0xcbcd4.

Definition imc_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S cnt : Z) (src : list byte) (n0 : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + cnt)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists bs', u8arr asegs m' D bs' /\ length bs' = n0)
    /\ bytes_at asegs m' S src.

Section IMC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D S cnt : Z) (src : list byte) (n0 : nat) (m : word -> option byte).
  Hypothesis LEN : Z.of_nat (length src) = cnt.
  Hypothesis N0  : Z.of_nat n0 = cnt.
  Hypothesis SEP : S + cnt <= D \/ D + cnt <= S.
  Hypothesis DR  : 0 <= D /\ D + cnt <= 2^64.
  Hypothesis SR  : 0 <= S /\ S + cnt <= 2^64.

  Notation POST := (imc_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc D S cnt src n0 m).

  Lemma imc_loop : forall (K : nat) (P : Z) (m1 : word -> option byte) (bs1 : list byte) (xa4 : word),
    Z.to_nat (cnt - P) = K -> 0 <= P < cnt ->
    u8arr asegs m1 D bs1 -> length bs1 = n0 -> bytes_at asegs m1 S src -> mem_inv asegs m1 ->
    munch [(D, D + cnt)] m m1 -> wmono asegs m m1 ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz (S + P)) (wz (D + cnt)) (wz (D + P)) xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcbce0) fc None m1 (seg_rom asegs)).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros P m1 bs1 xa4 HK HP DST L1 SRC MI MU WM. unfold wz.
    destruct (nth_error src (Z.to_nat P)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    pose proof (bytes_at_read1 asegs m1 S src P b (wa (S + P)) SRC NB ltac:(lia) eq_refl) as HR.
    step.
    pose proof (u8arr_store_ok_n asegs m1 D bs1 P 1 (wa (D + P)) DST ltac:(lia) ltac:(cbn; lia) eq_refl) as HS.
    step. rewrite le1_zxb.
    pose proof (u8arr_write asegs m1 D bs1 P b DST ltac:(lia)) as DST'. clear DST. store_done.

    zstep. zstep. step. if_cases K1; zify_cond K1.
    - replace (D + P + 1) with (D + (P + 1)) by lia. replace (S + P + 1) with (S + (P + 1)) by lia.
      eapply (IH (Z.to_nat (cnt - (P + 1))) ltac:(lia) (P + 1)); try eassumption; try lia.
      rewrite upd_length. exact L1.
    -
      step. apply evt_done. unfold imc_post. do 5 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact SRC].
      eexists. split; [exact DST'|]. rewrite upd_length. exact L1.
  Qed.

  Lemma imemcpy_body : forall (xa3 xa4 : word) (bs : list byte),
    u8arr asegs m D bs -> length bs = n0 -> bytes_at asegs m S src -> mem_inv asegs m -> 0 <= cnt ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz cnt) xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IMEMCPY) fc None m (seg_rom asegs)).
  Proof.
    intros xa3 xa4 bs DST L SRC MI C0. unfold IMEMCPY, wz.
    pose proof (munch_refl [(D, D + cnt)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K0; zify_cond K0.
    -   step. apply evt_done. unfold imc_post. do 5 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact SRC]. eexists. split; [exact DST|exact L].
    - zstep. step.
      pose proof (imc_loop (Z.to_nat cnt) 0 m bs xa4) as L0. unfold wz in L0. rewrite !Z.add_0_r in L0.
      eapply L0; try eassumption; try lia.
  Qed.
End IMC.

Lemma imemcpy_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S cnt : Z) (src bs : list byte),
  a1 = wz S -> a2 = wz cnt ->
  u8arr asegs m D bs -> Z.of_nat (length bs) = cnt -> bytes_at asegs m S src -> Z.of_nat (length src) = cnt ->
  (S + cnt <= D \/ D + cnt <= S) -> mem_inv asegs m ->
  evt asegs (imc_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc D S cnt src (length bs) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IMEMCPY) fc None m (seg_rom asegs)).
Proof.
  intros until bs. intros -> -> DST LB SRC LS SEP MI.
  pose proof (u8arr_bound _ _ _ _ DST) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  eapply imemcpy_body; try eassumption; try lia.
Qed.

Definition SS_ALLOC : Z := 0xd83dc.

Definition alloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo IDXP Fr count SB : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (SB + 8 * Fr)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (SSB, SSB + 8); (IDXP, IDXP + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' SSB [C8 (wz (Fr + count))]
    /\ rw_cells asegs m' IDXP [C8 (wz Fr)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma shl44_shr41 : forall F, 0 <= F < 2^20 -> Z.shiftr ((Z.shiftl F 44) mod 18446744073709551616) 41 = 8 * F.
Proof.
  intros F HF. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^20 * 2^44); nia).
  change (2^44) with (8 * 2^41). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Section ALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo IDXP Fr count SB : Z) (m : word -> option byte).
  Hypothesis LO   : lo + 16 <= bv_unsigned sp.
  Hypothesis IDXR : bv_unsigned sp <= IDXP /\ IDXP + 8 <= 2^64.
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis FR_  : 0 <= Fr /\ 1 <= count /\ Fr + count <= LIM_FRAMES.
  Hypothesis SBR  : 0 < SB /\ SB + 8 * LIM_FRAMES <= 2^64.

  Theorem alloc_spec : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ij : word),
    a1 = wz count -> a2 = wz IDXP ->
    rw_cells asegs m SSB [C8 (wz Fr)] ->
    rw_cells asegs m SSB_DATA [C8 (wz SB)] ->
    rw_cells asegs m IDXP [C8 ij] ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo IDXP Fr count SB m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SSB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SS_ALLOC) fc None m (seg_rom asegs)).
  Proof.
    intros until ij. intros -> -> TF DATA IDX ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp); (SSB, SSB + 8); (IDXP, IDXP + 8)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold SS_ALLOC, AIMG_TOP, wz in *.
    carve_frame 16%nat ST.

    step. step. step. step. step.

    astep.

    zstep. zstep. rewrite (Z.shiftr_div_pow2 Fr 20), (Z.div_small Fr (2^20)) by lia.
    zstep. zstep. rewrite Z.shiftr_div_pow2, Z.div_small by lia.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }

    zstep. rewrite Z.shiftr_div_pow2, Z.div_small by lia.
    step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }

    step. zstep. zstep. step. step. if_cases K2; zify_cond K2. { exfalso. lia. }

    zstep. zstep. rewrite shl44_shr41 by lia. zstep.

    step. step. step. release_frame FR ST (bv_unsigned sp). step.
    finish.
  Qed.
End ALLOC.

Definition SS_STORE : Z := 0xd82b8.

Definition store_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo PK SB Fr n : Z) (nj : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (Fr + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (SSB, SSB + 8); (SSB_STORED, SSB_STORED + 4); (PK, PK + 8); (SB + 8 * Fr, SB + 8 * Fr + 8 * (n + 1))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' SSB [C8 (wz (Fr + n + 1))]
    /\ rw_cells asegs m' SSB_STORED [C4 (wz (Fr + n + 1))]
    /\ rw_cells asegs m' PK [C8 (wz 0)]
    /\ (exists junk', u8arr asegs m' (SB + 8 * Fr) junk' /\ length junk' = nj)
    /\ stk asegs m' lo (bv_unsigned sp).

Section STORE.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo ARGS PK TR SB Fr n : Z) (src junk : list byte) (m : word -> option byte).
  Hypothesis LO   : lo + 80 <= bv_unsigned sp.
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis ARGSR: bv_unsigned sp <= ARGS /\ ARGS + 16 <= 2^64.
  Hypothesis PKR  : bv_unsigned sp <= PK /\ PK + 8 <= 2^64.
  Hypothesis APK  : ARGS + 16 <= PK \/ PK + 8 <= ARGS.
  Hypothesis NR   : 1 <= n <= 254.
  Hypothesis FR_  : 0 <= Fr /\ Fr + n + 1 <= LIM_FRAMES.
  Hypothesis SBR  : AIMG_TOP <= SB /\ SB + 8 * LIM_FRAMES <= lo.
  Hypothesis TRR  : bv_unsigned sp <= TR /\ PK + 8 <= TR /\ ARGS + 16 <= TR.
  Hypothesis LSRC : Z.of_nat (length src) = 8 * n.
  Hypothesis LJ   : Z.of_nat (length junk) = 8 * (LIM_FRAMES - Fr).

  Theorem store_spec : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pj : word),
    rw_cells asegs m ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)] ->
    rw_cells asegs m PK [C8 pj] ->
    bytes_at asegs m TR src ->
    rw_cells asegs m SSB [C8 (wz Fr)] ->
    rw_cells asegs m SSB_DATA [C8 (wz SB)] ->
    rw_cells asegs m SSB_STORED [C4 (wz Fr)] ->
    u8arr asegs m (SB + 8 * Fr) junk ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (store_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo PK SB Fr n (length junk) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SSB) (wz ARGS) (wz PK) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SS_STORE) fc None m (seg_rom asegs)).
  Proof.
    intros until pj. intros ARGC PKC SRC TF DATA STO SPACE ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp); (SSB, SSB + 8); (SSB_STORED, SSB_STORED + 4); (PK, PK + 8); (SB + 8 * Fr, SB + 8 * Fr + 8 * (n + 1))] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold SS_STORE, AIMG_TOP, wz in *.
    carve_frame 64%nat ST.

    do 8 step. step.

    step. step. rewrite ?sx32_wz by lia. unfold wz. zstep. rewrite Z.lor_0_r.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }

    step. step. step. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
    step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. }

    st1. st1. zstep. step. step. step. step.

    step.
    apply (proj1 (rw_cells_app _ _ _ [C8 (Z_to_bv 64 0)] _)) in FR. destruct FR as [IDX FR1].
    cbn [cells_size csize Nat.add] in FR1. change (Z.of_nat 8) with 8 in FR1.
    replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FR1 by lia.
    callU (alloc_spec _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo (bv_unsigned sp + -64) Fr (n + 1) SB).
    all: try (rewrite ?unsigned_lit by lia; unfold AIMG_TOP; first [eassumption | reflexivity | lia]).
    unfold wz in *.

    step. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. }
    zstep. step. zstep. change (Z.lor 0 n) with n.

    pose proof (u8arr_store_ok_n asegs _ _ _ 0 8 (wa (SB + 8 * Fr)) SPACE ltac:(lia) ltac:(cbn; lia) ltac:(f_equal; lia)) as HS.
    step.
    pose proof (u8arr_write_n asegs _ _ _ 0 (le8 (Z_to_bv 64 n)) SPACE ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as SPACE'.
    rewrite Z.add_0_r in SPACE'. clear SPACE. store_done.

    zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. step.

    destruct (list_split3 (upd_bytes junk (Z.to_nat 0) (le8 (Z_to_bv 64 n))) 8 (Z.to_nat (8 * n))) as (j1 & j2 & j3 & EJ & L1 & L2).
    { rewrite upd_bytes_length by (rewrite length_le8; lia). lia. }
    assert (L3 : Z.of_nat (length j3) = 8 * (32768 - Fr) - 8 - 8 * n).
    { apply (f_equal (@length byte)) in EJ. rewrite upd_bytes_length, !length_app in EJ by (rewrite length_le8; lia). lia. }
    rewrite EJ in SPACE'. apply u8arr_app in SPACE'. destruct SPACE' as [U1 U23]. rewrite L1 in U23. change (Z.of_nat 8) with 8 in U23.
    apply u8arr_app in U23. destruct U23 as [U2 U3].
    replace (SB + 8 * Fr + 8 + Z.of_nat (length j2)) with (SB + 8 * Fr + 8 + 8 * n) in U3 by lia.
    callU (imemcpy_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc _ (SB + 8 * Fr + 8) TR (8 * n) src j2).
    all: try (rewrite ?unsigned_lit by lia; unfold AIMG_TOP; first [eassumption | reflexivity | lia]).
    { f_equal. lia. }
    destruct PC1 as (j2' & U2 & L2'). unfold wz in *.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SPACE : u8arr asegs mm (SB + 8 * Fr) (j1 ++ j2' ++ j3)) end.
    { apply u8arr_app. split; [exact U1|]. rewrite L1. change (Z.of_nat 8) with 8. apply u8arr_app. split; [exact U2|].
      replace (SB + 8 * Fr + 8 + Z.of_nat (length j2')) with (SB + 8 * Fr + 8 + 8 * n) by lia. exact U3. }
    assert (LSP : length (j1 ++ j2' ++ j3) = length junk).
    { apply (f_equal (@length byte)) in EJ. rewrite upd_bytes_length in EJ by (rewrite length_le8; lia). rewrite !length_app in *. lia. }
    clear U1 U2 U3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FR : rw_cells asegs mm (bv_unsigned sp + -64) ([C8 (Z_to_bv 64 Fr)] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) end.
    { apply rw_cells_app. split; [exact PC0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
      replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by lia. exact FR1. }
    clear PC0 FR1. cbn [app] in FR.

    step. zstep. rewrite (Z.shiftr_div_pow2 Fr 16), (Z.div_small Fr (2^16)) by lia. zstep. zstep. zstep.

    astep. rewrite ?sx32_wz by lia. rewrite unsigned_lit, low32_lit in STO by lia.
    apply (proj1 (rw_cells_C8_C4C4 asegs _ _ [] Fr _ ltac:(lia))) in FR. cbn [app] in FR.
    rewrite (Z.shiftr_div_pow2 Fr 32), (Z.div_small Fr (2^32)) in FR by lia. unfold wz in *.

    step. zstep. zstep. rewrite (Z.mod_small Fr 4294967296) by lia. zstep. step. zstep. step. rewrite ?sx32_wz by lia. unfold wz in *. zstep.
    replace (Z.lxor (n + 1 + Fr) 1048576 <? 1) with false.
    2:{ symmetry. apply Z.ltb_ge. assert (NE : Z.lxor (n + 1 + Fr) 1048576 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
        pose proof (Z.lxor_nonneg (n + 1 + Fr) 1048576). lia. }
    cbn [Z.b2z]. zstep. st1. zstep. rewrite (swrap32_small (Fr + 1)) by lia.

    do 8 step. release_frame FR POST (bv_unsigned sp). step.
    replace (Fr + (n + 1)) with (Fr + n + 1) in * by lia.
    finish.
    { eexists. split; [exact SPACE|exact LSP]. }
  Qed.
End STORE.

Definition NODE_STORE : Z := 0xda5cc.

Definition nstore_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo ND SB Fr n h : Z) (j2 : word) (nj : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (SSB, SSB + 8); (SSB_STORED, SSB_STORED + 4); (ND, ND + 16); (SB + 8 * Fr, SB + 8 * Fr + 8 * (n + 1))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' ND [C8 (wz h); C4 j2; C4 (wz (Fr + 1))]
    /\ rw_cells asegs m' SSB [C8 (wz (Fr + n + 1))]
    /\ rw_cells asegs m' SSB_STORED [C4 (wz (Fr + n + 1))]
    /\ (exists junk', u8arr asegs m' (SB + 8 * Fr) junk' /\ length junk' = nj)
    /\ stk asegs m' lo (bv_unsigned sp).

Section NSTORE.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo ARGS ND TR SB Fr n h : Z) (src junk : list byte) (m : word -> option byte).
  Hypothesis LO   : lo + 112 <= bv_unsigned sp.
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis ARGSR: bv_unsigned sp <= ARGS /\ ARGS + 16 <= TR /\ TR + 8 * n <= 2^64.
  Hypothesis NDR  : AIMG_TOP <= ND /\ ND + 16 <= lo.
  Hypothesis NDSB : ND + 16 <= SB + 8 * Fr \/ SB + 8 * LIM_FRAMES <= ND.
  Hypothesis NR   : 1 <= n <= 254.
  Hypothesis FR_  : 0 <= Fr /\ Fr + n + 1 <= LIM_FRAMES.
  Hypothesis SBR  : AIMG_TOP <= SB /\ SB + 8 * LIM_FRAMES <= lo.
  Hypothesis HR   : 0 <= h < 2^64.
  Hypothesis LSRC : Z.of_nat (length src) = 8 * n.
  Hypothesis LJ   : Z.of_nat (length junk) = 8 * (LIM_FRAMES - Fr).

  Theorem nstore_spec : forall (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 j1 j2 j3 : word),
    rw_cells asegs m ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)] ->
    rw_cells asegs m ND [C8 j1; C4 j2; C4 j3] ->
    bytes_at asegs m TR src ->
    rw_cells asegs m SSB [C8 (wz Fr)] ->
    rw_cells asegs m SSB_DATA [C8 (wz SB)] ->
    rw_cells asegs m SSB_STORED [C4 (wz Fr)] ->
    u8arr asegs m (SB + 8 * Fr) junk ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (nstore_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo ND SB Fr n h j2 (length junk) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ND) a1 (wz ARGS) (wz h) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NODE_STORE) fc None m (seg_rom asegs)).
  Proof.
    intros until j3. intros ARGC NDC SRC TF DATA STO SPACE ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp); (SSB, SSB + 8); (SSB_STORED, SSB_STORED + 4); (ND, ND + 16); (SB + 8 * Fr, SB + 8 * Fr + 8 * (n + 1))] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold NODE_STORE, AIMG_TOP, wz in *.
    carve_frame 32%nat ST.

    step. step. step. step. step. step. st1. step. step. zstep.

    step.
    apply (proj1 (rw_cells_app _ _ _ [CB 8 _] _)) in FR. destruct FR as [FR0 FR1].
    cbn [cells_size csize Nat.add] in FR1. change (Z.of_nat 8) with 8 in FR1.
    apply (proj1 (rw_cells_app _ _ _ [C8 _] _)) in FR1. destruct FR1 as [PKC FR2].
    cbn [cells_size csize Nat.add] in FR2. change (Z.of_nat 8) with 8 in FR2.
    replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) in FR2 by lia.
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in PKC by lia.
    callU (store_spec _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo ARGS (bv_unsigned sp + -24) TR SB Fr n src junk).
    all: try (rewrite ?unsigned_lit by lia; unfold AIMG_TOP; first [eassumption | reflexivity | lia]).
    destruct PC2 as (junk' & SPACE' & LSP). unfold wz in *.

    step. step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FR : rw_cells asegs mm (bv_unsigned sp + -32) ([CB 8 (firstn 8 (firstn 16 (firstn 24 junk0)))] ++ [C8 (Z_to_bv 64 0)] ++ [C8 s0; C8 ra])) end.
    { apply rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
      apply rw_cells_app. split; [replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia; exact PC1|].
      cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
      replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) by lia. exact FR2. }
    clear FR0 PC1 FR2. cbn [app] in FR.

    step. step. step. release_frame FR POST (bv_unsigned sp). step.
    finish.
    { eexists. split; [exact SPACE'|exact LSP]. }
  Qed.
End NSTORE.
