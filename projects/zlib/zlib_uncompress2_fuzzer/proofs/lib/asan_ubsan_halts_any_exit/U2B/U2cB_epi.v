(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B-unc2] A2 2026-11-12: carried to unc2's combined image by tools/merge3_u2.sh: ours = my unc text (U1B, built at unc c31)
   moved by tools/t12.py (the measured unc -> unc2 combined image map), base = G's unc ASan twin moved the same
   way, theirs = G2's unc2 ASan twin moved by tools/g2b_u2.py.
   Any comment above or below that names the unc merge describes the unc text this one was carried from. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh): the view's text
   (1.3.1 combined, moved), the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/U2cA_epi
   moved to the combined image by tools/g2b.py; conflicts resolved by hand (marked [U14B]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memset.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface U2BIfaceS U2cB_pre U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Definition bxu (P : Prop) : Prop := P.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (F1 Fu FLG lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Variable SL : Z.
  Hypothesis ESL : SL = SP + 8.
  Notation DL := (SP + 16).
  Notation Zs := (Fu + 32).
  Notation SHF := (Z.shiftr Fu 3 + 2147450880).
  Hypothesis LOS : lo <= SP - UC_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = SP - 160 - SP mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RFRM : rng RNG SPA 56.
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis RFU : rng RNG Fu 256.
  Hypothesis RSFU : rng RNG SHF 32.
  Hypothesis GB : ablk FLG (FLG + 1).
  Hypothesis GF : FLG + 1 <= Fu \/ Fu + 256 <= FLG.
  Hypothesis RG : rng RNG FLG 1.

  Notation BODY pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v2 v3 v4 v5 v6 v10 v11 x28 x29 x30 x31 mm :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             v2 v3 v4 v5 v6 (Z_to_bv 64 Zs) (Z_to_bv 64 SHF) (Z_to_bv 64 Fu) v10 v11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* 1.4 return-code select at 0x8d22c (after inflateEnd): err, len + avail_in in s11.
     [U14B] A2: in the COMBINED 1.4 image err is in s6 (0x8d1ec mv s6,a0; 0x8d230 beq s6,a1); the ASan image has it in s5 *)
  Lemma uc_sel : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v2 v3 v4 v5 v10 v11 x28 x29 x30 x31 : word) m (rcw : word),
    evtF bsegs RNG (fun ms' => exists (av y11 : word),
        ms' = BODY 0x8cf84 x1 x5 x6 x7 av y11 x12 x13 x14 x15 x16 x17 v2 v3 v4 v5 rcw v10 v11 x28 x29 x30 x31 m)
      (BODY 0x8d1f4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v2 v3 v4 v5 rcw v10 v11 x28 x29 x30 x31 m).
  Proof using All.
    intros until rcw.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    zrung [0x8cf84]. if_cases K1.
    - zrung [0x8cf84]. apply evtF_done. eexists _, _. reflexivity.
    - zrung [0x8cf84]. if_cases K2.
      + zrung [0x8cf84]. apply evtF_done. eexists _, _. reflexivity.
      + zrung [0x8cf84]. if_cases K3.
        * zrung [0x8cf84]. apply evtF_done. eexists _, _. reflexivity.
        * zrung [0x8cf84]. if_cases K4.
          -- zrung [0x8cf84]. apply evtF_done. eexists _, _. reflexivity.
          -- zrung [0x8cf84]. apply evtF_done. eexists _, _. reflexivity.
  Qed.

  Lemma uc_epi : forall (x1 x5 x6 x7 av x11 x12 x13 x14 x15 x16 x17 v3 v4 v5 v6 v10 v11 x28 x29 x30 x31 : word) m (j8 j16 : list byte),
    stk bsegs m lo SPA -> stk bsegs m (SPA + 56) (SP + -104) -> mem_inv bsegs m ->
    rw_cells bsegs m SPA (UFRA sp SL Fu j8 j16) ->   (* [U14B] A2: the combined 1.4 UFRA (U2cB_pre) *)
    rw_cells bsegs m (SP + -104) (UFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m Fu UFHD ->
    rw_cells bsegs m (Fu + 248) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m SHF UFSH ->
    evtF bsegs RNG (fun ms' => exists (mp m' : amem) (q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 av q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SHF, SHF + 32); (Fu, Fu + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (BODY 0x8cf84 x1 x5 x6 x7 av x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Fu) v3 v4 v5 v6 v10 v11 x28 x29 x30 x31 m).
  Proof using All.
    intros until j16. intros STL STG MI FRA FRB FH FFL FLC FSH.
    unfold UFRA, UFRB, UFHD, UFSH, UC_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    assert (SPAB : SP - 176 <= SPA <= SP - 160 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (BSF : 2147450880 <= SHF /\ SHF + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    band_ind FUB bU. band_ind GB bG.
    destruct (sepI FLG 1 Fu 256 GF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (cG & CG0 & CG1 & CG2). clear GF.
    pose proof (munch_refl [(SHF, SHF + 32); (Fu, Fu + 8)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zrung [0x8d054].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bxu (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bxu T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bxu T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zs.
    zs.
    zs. zs.
    do 13 zs. zs. zs.
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRA2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -104) _ |- _ => rename H into FRB2 end.
    lazymatch goal with H : stk bsegs _ lo SPA |- _ => rename H into STL2 end.
    lazymatch goal with H : stk bsegs _ (SPA + 56) (SP + -104) |- _ => rename H into STG2 end.
    eapply stk_release in FRA2; [| exact STL2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 56) (SP + -104) FRA2 STG2 ltac:(lia)) as ST2 end.
    release_frame FRB2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold bxu in MU1, WM1, MIp.
    replace (Z.shiftr Fu 3 + 2147450912) with (SHF + 32) by lia.
    eexists _, _. do 14 eexists. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| eassumption].
  Qed.
End S.
End CANSEC1.
