(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BSysStep BExec BellsX BacX BMem BMState BLFrame BZBridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma xpres_SHAD : forall LB SP X m m' A sbs,
    xpres H LB SP X m m' -> SHAD m A sbs -> xclient_range H LB SP X (sh A) (Z.of_nat (length sbs)) -> SHAD m' A sbs.
  Proof.
    intros LB SP X m m' A sbs XP (A0 & A8 & [UB UW]) XC. split; [exact A0|]. split; [exact A8|].
    split; [eapply xpres_bytes_at; eauto| eapply xpres_wr_at; eauto].
  Qed.

  Lemma xpres_addressable : forall LB SP X m m' A n,
    xpres H LB SP X m m' -> addressable m A n -> xclient_range H LB SP X (sh A) (nsh n) -> addressable m' A n.
  Proof.
    intros LB SP X m m' A n XP [Hn SH] XC. split; [exact Hn|]. eapply xpres_SHAD; eauto. rewrite shadow_of_length by lia. exact XC.
  Qed.

  Lemma aconst_ok_hi : forall lo hi, AHI_LO <= lo -> aconst_ok (lo, hi).
  Proof.
    intros lo hi L1. apply aconst_ok_high; cbn; [| unfold AHI_LO in *; lia].
    pose proof (sh_below_app AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)). apply (Z.le_trans _ AHI_LO); [| exact L1].
    unfold sh, AIMG_TOP, AHI_LO. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
  Qed.

  Lemma aconst_ok_aapp : forall A n lo hi, aapp A n -> A <= lo -> hi <= A + n -> aconst_ok (lo, hi).
  Proof.
    intros A n lo hi AP L1 L2. destruct AP as [[P1 P2]|[P1 P2]]; [| apply aconst_ok_hi; lia].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ALOWSH_LO in *; rewrite ?ASHADOW_BASE_val; try lia.
  Qed.

End K.

Definition amove_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SP Dst Src N : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dst, Dst + N); (SP - 4096, SP)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src
    /\ ACONST m'.

Section Calls.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma amemcpy_specZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (SP Dst Src N : Z) (src junk : list byte) (lo : Z),
    bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
    (Src + N <= Dst \/ Dst + N <= Src) -> 0 <= N <= 2^40 -> 0 <= Src -> 0 <= Dst ->
    accessible m Src N -> accessible m Dst N -> shvis m Src (Src + N) -> shvis m Dst (Dst + N) ->
    in_app_mem Src (Src + N) -> in_app_mem Dst (Dst + N) -> aconst_ok (Dst, Dst + N) ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2^64 ->
    (Dst + N <= lo \/ SP <= Dst) -> (Src + N <= lo \/ SP <= Src) ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (amove_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP Dst Src N src lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMEMCPY_STUB) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros SRC LEN DST SEP HN HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC.
    pose proof ACS as (_ & SH' & _). pose proof ACD as (_ & DH' & _). unfold AAPP_HI in SH', DH'.
    assert (SP0 : 0 <= SP) by (destruct ST as [? _]; lia).
    eapply evt_mono.
    { eapply (ah_memcpy_icpt H HH) with (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; unfold AINTRIN_STACK; lia. }
    intros ms' PO. cbv beta in PO. unfold amemcpy_post in PO. unfold amove_post.
    rewrite !(unsigned_lit Dst), !(unsigned_lit Src), !(unsigned_lit N), !(unsigned_lit SP) in PO by lia. unfold AINTRIN_STACK in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & D' & S' & AC').
    do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact AC'.
  Qed.

End Calls.
