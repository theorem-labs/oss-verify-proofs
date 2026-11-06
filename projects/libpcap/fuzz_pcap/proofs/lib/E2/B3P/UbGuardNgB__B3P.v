(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF Shadow StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UbGuardNgB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land4_0 : forall x, x mod 8 = 0 -> Z.land x 4 = 0.
Proof.
  intros x Hx. assert (E : x = 8 * (x / 8)) by (Z.div_mod_to_equations; lia). rewrite E.
  change 8 with (2^3). rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 2) as [->|NE]; [rewrite Z.shiftl_spec_low by lia; reflexivity|].
  replace (Z.testbit 4 n) with false; [apply andb_false_r|]. symmetry. change 4 with (2^2). apply Z.pow2_bits_false. lia.
Qed.

(* [comment removed for export] *)
Ltac ub_uns X :=
  first [ rewrite (unsigned_lit X) by lia
        | rewrite <- (Z_to_bv_mod64 X);
          let v := eval vm_compute in (X mod 2^64) in (change (X mod 2^64) with v; rewrite (unsigned_lit v) by lia) ].

(* [comment removed for export] *)
Ltac ub_ovf :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)) then _ else _) _ _ _ _) =>
      replace (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) with true
        by (symmetry; unfold bv_ltu; ub_uns a; ub_uns b; apply Z.ltb_lt; lia);
      cbn [negb]; cbv iota
  | |- evtF _ _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) then _ else _) _ _ _ _) =>
      replace (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) with false
        by (symmetry; unfold bv_ltu; ub_uns a; ub_uns b; apply Z.ltb_ge; lia);
      cbv iota
  end.
End UbGuardNgB.

(* [comment removed for export] *)
Module F_gfbdB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.UbGuardNgB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Definition GFBD_ENTRY : Z := 0x8c1dc.
Definition GFBD_SNPRINTF_RA : Z := 0x8c244.
Definition GFBD_FMT : Z := 0x22520.

Section CANSEC1. Context {rc : runConstT}.
Section Gfbd.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (lo CUR : Z).
  Hypothesis LO : (lo <= bv_unsigned sp - 16)%Z.
  Hypothesis KLO : (17594333495296 <= lo)%Z.           (* [comment removed for export] *)
  Hypothesis CLO : (17594333495296 <= CUR)%Z.          (* [comment removed for export] *)
  Hypothesis CHI : (CUR + 24 <= 2^47)%Z.
  Hypothesis C8A : (CUR mod 8 = 0)%Z.
  Hypothesis CSEP : (CUR + 24 <= lo \/ bv_unsigned sp <= CUR)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RCUR : rng RNG CUR 24.
  Hypothesis RCSH : rng RNG (shad CUR) (nshad 24).

  Definition gfbd_ok__stmt : Prop := forall (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (D R BT N : Z) (cpad : list byte),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> artcells m ->
    rw_cells asegs m CUR [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 R); C4 (Z_to_bv 64 BT); CB 4 cpad] ->
    unpoisoned m CUR (CUR + 24) ->
    (0 <= N)%Z -> (N <= R < 2^64)%Z -> (0 < D)%Z -> (D + N < 2^64)%Z ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (CUR, CUR + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 (D + N)); C8 (Z_to_bv 64 (R - N)); C4 (Z_to_bv 64 BT); CB 4 cpad]
        /\ unpoisoned m' CUR (CUR + 24))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CUR) (Z_to_bv 64 N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 GFBD_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 D R BT N cpad : ltac2:(SecDiet.SzSec.tyM 'gfbd_ok__stmt "vvvvvvvvvvvvvvvvvvv" @m).
  #[using="LO KLO CLO CHI C8A CSEP RSTK RIMG RCUR RCSH"] Lemma gfbd_ok__body : ltac2:(SecDiet.SzSec.bodyP 'gfbd_ok__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI ST RT CC CUNP HN HR HD HDN.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct RT as (_ & GOT & _ & _ & SHB & _).
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (CUR, CUR + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold GFBD_ENTRY.
    carve_frame 16%nat ST.
    zstep. zstep.
    zstep. ub_al 7%Z ltac:(exact C8A). zstep. if_false.
    do 4 zstep.
    ck0 CUNP; ck_go.
    zstep. zstep.
    replace (bv_ltu (Z_to_bv 64 R) (Z_to_bv 64 N)) with false
      by (symmetry; unfold bv_ltu; rewrite (unsigned_lit R), (unsigned_lit N) by lia; apply Z.ltb_ge; lia).
    cbn [negb]; cbv iota.
    ck0 CUNP; ck_go.
    zstep. zstep. zstep.
    ub_ovf.   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (0 <? D)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    replace (N + D <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z Z.lxor Pos.lxor]. if_false.
    ck0_at CUNP CUR. zstep. zstep. if_false.
    zstep.
    ck0_at CUNP (CUR + 8)%Z. zstep. zstep. if_false.
    do 3 zstep.
    do 2 zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    replace (N + D)%Z with (D + N)%Z in CC by lia.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact CC | assumption].
  Qed.
  End Sz1.
  #[using="LO KLO CLO CHI C8A CSEP RSTK RIMG RCUR RCSH"] Lemma gfbd_ok : ltac:(let t := eval cbv delta [gfbd_ok__stmt] in gfbd_ok__stmt in exact t).
  Proof. intros m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 D R BT N cpad. ltac2:(SecDiet.SzSec.closeP 'gfbd_ok__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition gfbd_short_pre__stmt : Prop := forall (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (D R BT N : Z) (cpad : list byte),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> artcells m ->
    rw_cells asegs m CUR [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 R); C4 (Z_to_bv 64 BT); CB 4 cpad] ->
    unpoisoned m CUR (CUR + 24) ->
    (0 <= N < 2^64)%Z -> (0 <= R < N)%Z ->
    evtF asegs RNG (fun ms' => exists (a4' a5' a6' : word) (jk : list byte) (m' : mem),
        ms' = MS (mkR (Z_to_bv 64 GFBD_SNPRINTF_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                      a2 (Z_to_bv 64 256) (Z_to_bv 64 GFBD_FMT) (sx32 (Z_to_bv 64 BT)) a4' a5' a6' a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x44518) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -16)
        /\ rw_cells asegs m' (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 R); C4 (Z_to_bv 64 BT); CB 4 cpad]
        /\ unpoisoned m' CUR (CUR + 24))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CUR) (Z_to_bv 64 N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 GFBD_ENTRY) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 D R BT N cpad : ltac2:(SecDiet.SzSec.tyM 'gfbd_short_pre__stmt "vvvvvvvvvvvvvvvvvvv" @m).
  #[using="LO KLO CLO CHI C8A CSEP RSTK RIMG RCUR RCSH"] Lemma gfbd_short_pre__body : ltac2:(SecDiet.SzSec.bodyP 'gfbd_short_pre__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI ST RT CC CUNP HN HR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct RT as (_ & GOT & _ & _ & SHB & _).
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold GFBD_ENTRY, GFBD_SNPRINTF_RA, GFBD_FMT.
    carve_frame 16%nat ST.
    zstep. zstep.
    zstep. ub_al 7%Z ltac:(exact C8A). zstep. if_false.
    do 4 zstep.
    ck0 CUNP; ck_go.
    zstep. zstep.
    replace (bv_ltu (Z_to_bv 64 R) (Z_to_bv 64 N)) with true
      by (symmetry; unfold bv_ltu; rewrite (unsigned_lit R), (unsigned_lit N) by lia; apply Z.ltb_lt; lia).
    cbn [negb]; cbv iota.
    zstep.
    ck0 CUNP; ck_go.
    do 6 zstep. zstep.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact CC | assumption].
  Qed.
  End Sz2.
  #[using="LO KLO CLO CHI C8A CSEP RSTK RIMG RCUR RCSH"] Lemma gfbd_short_pre : ltac:(let t := eval cbv delta [gfbd_short_pre__stmt] in gfbd_short_pre__stmt in exact t).
  Proof. intros m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 D R BT N cpad. ltac2:(SecDiet.SzSec.closeP 'gfbd_short_pre__body "vvvvvvvvvvvvvvvvvvv"). Qed.

End Gfbd.

(* [comment removed for export] *)
Section GfbdPost.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (lo : Z).
  Hypothesis LO : (lo <= bv_unsigned sp - 16)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition gfbd_short_post__stmt : Prop := forall (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jk : list byte),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -16) ->
    rw_cells asegs m (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    evtF asegs RNG (fun ms' => exists (a1' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m (seg_rom asegs)
        /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 GFBD_SNPRINTF_RA) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 jk : ltac2:(SecDiet.SzSec.tyM 'gfbd_short_post__stmt "vvvvvvvvvvvvvvvvvv" @m).
  #[using="LO RSTK"] Lemma gfbd_short_post__body : ltac2:(SecDiet.SzSec.bodyP 'gfbd_short_post__stmt "vvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI ST FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold GFBD_SNPRINTF_RA.
    do 3 zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    apply evtF_done. eexists. split; [reflexivity | exact ST].
  Qed.
  End Sz3.
  #[using="LO RSTK"] Lemma gfbd_short_post : ltac:(let t := eval cbv delta [gfbd_short_post__stmt] in gfbd_short_post__stmt in exact t).
  Proof. intros m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 jk. ltac2:(SecDiet.SzSec.closeP 'gfbd_short_post__body "vvvvvvvvvvvvvvvvvv"). Qed.
End GfbdPost.
End CANSEC1.
End F_gfbdB.
