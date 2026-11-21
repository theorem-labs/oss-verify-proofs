(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit U2AObj U2ABlob.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface InfB_pro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

From Stdlib Require Import FunctionalExtensionality.

Section CANSEC1. Context {rc : runConstT}.
Lemma inf_byte_of_c1 : forall m s b, rw_cells bsegs m s [C1 b] -> 0x67f000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.
Lemma inf_mem_eq_single : forall (mp m' : amem) A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> m' = write_to_mem mp (wa A) [b].
Proof.
  intros mp m' A b HA HB MU Hb. apply functional_extensionality. intros x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Definition ibx (P : Prop) : Prop := P.

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 704.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = (SP - 672) - (SP - 672) mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Variables (F FLG : Z).
  Hypothesis F64 : F mod 64 = 0.
  Hypothesis FB : ablk F (F + 64).
  Hypothesis FTOP : F + 64 <= ATOP.
  Hypothesis GB : ablk FLG (FLG + 1).
  Hypothesis GTOP : FLG + 1 <= ATOP.
  Hypothesis GF : FLG + 1 <= F \/ F + 64 <= FLG.
  Hypothesis RF : rng RNG F 64.
  Hypothesis RSF : rng RNG (Z.shiftr F 3 + 2147450880) 8.
  Hypothesis RG : rng RNG FLG 1.

  Notation SHF := (Z.shiftr F 3 + 2147450880).

  Lemma inf_epi : forall (r : Z) (x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) m
      (jB : list byte) (h0 h1 h2 : word) (jk : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 : bv 8),
    stk bsegs m lo SPA -> stk bsegs m (SPA + 568) (SP + -104) -> mem_inv bsegs m ->
    rw_cells bsegs m SPA [CB 568 jB] ->
    rw_cells bsegs m (SP + -104) (inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m F [C8 h0; C8 h1; C8 h2; CB 32 jk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m SHF [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7] ->
    evtF bsegs RNG (fun ms' => exists (mp m' : amem) (q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 (Z_to_bv 64 r) q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SHF, SHF + 8); (F, F + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR (Z_to_bv 64 F) x2 gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x24 x21 x26 x23 (Z_to_bv 64 SHF) x25 (Z_to_bv 64 r) (Z_to_bv 64 F) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x93a38) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until c7. intros STL STG MI FRA FRB FH FLC FSH.
    unfold inf_SAVED in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    assert (SPAB : SP - 688 <= SPA <= SP - 672 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (F8 : F mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (BSF : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (DSF : SHF + 8 <= F \/ F + 64 <= SHF)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ablk, AIMG_HI, KLS in FB; Z.div_mod_to_equations; lia).
    assert (DSG : SHF + 8 <= FLG \/ FLG + 1 <= SHF)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ablk, AIMG_HI, KLS in FB, GB; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SHF, SHF + 8); (F, F + 8)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zrunb [0x93a74].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (ibx (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (ibx T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (ibx T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zs.
    zs.
    zs. zs. zs.
    do 13 zs. zs. zs.
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRA2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -104) _ |- _ => rename H into FRB2 end.
    lazymatch goal with H : stk bsegs _ lo SPA |- _ => rename H into STL2 end.
    lazymatch goal with H : stk bsegs _ (SPA + 568) (SP + -104) |- _ => rename H into STG2 end.
    eapply stk_release in FRA2; [| exact STL2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 568) (SP + -104) FRA2 STG2 ltac:(lia)) as ST2 end.
    release_frame FRB2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold ibx in MU1, WM1, MIp.
    replace (Z.shiftr F 3 + 2147450888) with (SHF + 8) by lia.
    eexists _, _. do 14 eexists. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| eassumption].
  Qed.
End S.
End CANSEC1.
