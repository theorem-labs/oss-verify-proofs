(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_sd4P U0_sd4D U0_sd4E U0_sd4F.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable m0 : word -> option byte.
  Variable nG : Z.
  Hypothesis VW : sd_vw cx e P m0.
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cP := (Z_to_bv 64 P). Notation cE := (Z_to_bv 64 E).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation DX L := (L cx g e Q gp tp F fc P CX SEP Gmtf Gbs Gzb Hnb CEP PHI LIM HLIM m0 nG VW).
  Variables (A nSel : Z).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef (e_inUse e) k = true /\ (0 <= zget (e_inUse e) k < 256)%Z.
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef (e_selectorMtf e) i = true /\ (0 <= zget (e_selectorMtf e) i < nG)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef (e_len e) (258 * t + v) = true /\ (1 <= zget (e_len e) (258 * t + v) <= 17)%Z.
  Variable in160 : zarr.
  Hypothesis OK0 : bw_ok (e_bw e).

  Definition IN16 : zarr := sm_in16 16 in160 (e_inUse e) 0.
  Definition BA : bw := sm_put_in16 16 (e_bw e) IN16 0.
  Definition BB : bw := sm_put_inuse 16 BA IN16 (e_inUse e) 0.
  Definition BC3 : bw := bsW BB 3 nG.
  Definition BC : bw := bsW BC3 15 nSel.
  Definition BD : bw := sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0.
  Definition BE : bw := sm_put_lens (Z.to_nat nG) BD (e_len e) A 0.
  Hypothesis NLE : (bw_numZ BE <= LIM)%Z.

  Lemma IN16R : forall k, (0 <= k < 16)%Z -> zget IN16 k = ROW16 (e_inUse e) k.
  Proof using. intros k Hk. unfold IN16. apply smD_in16_row. exact Hk. Qed.

  Lemma NZ_chain : (bw_numZ (e_bw e) <= bw_numZ BA /\ bw_numZ BA <= bw_numZ BB /\ bw_numZ BB <= bw_numZ BC3 /\ bw_numZ BC3 <= bw_numZ BC /\
                    bw_numZ BC <= bw_numZ BD /\ bw_numZ BD <= bw_numZ BE)%Z.
  Proof using.
    repeat split.
    - exact (put_in16_NZM 16 (e_bw e) IN16 0).
    - exact (put_inuse_NZM 16 BA IN16 (e_inUse e) 0).
    - exact (bsW_NZM BB 3 nG).
    - exact (bsW_NZM BC3 15 nSel).
    - exact (put_sels_NZM (Z.to_nat nSel) BC (e_selectorMtf e) 0).
    - exact (put_lens_NZM (Z.to_nat nG) BD (e_len e) A 0).
  Qed.
  Lemma BB_unfold : sm_put_inuse 16 BA IN16 (e_inUse e) 0 = BB.
  Proof using. unfold BB. reflexivity. Qed.
  #[local] Opaque IN16 BA BB BC3 BC BD BE.

  Lemma U0_sd4_seg : forall (H0 : sdw) (i16 : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    h928 H0 = Z_to_bv 64 nG -> h944 H0 = Z_to_bv 64 nSel -> h976 H0 = Z_to_bv 64 nSel ->
    h960 H0 = Z_to_bv 64 (E + 37708) -> h968 H0 = Z_to_bv 64 A ->
    Z.of_nat (length i16) = 16%Z ->
    MD H0 i16 (e_bw e) m0 ->
    (forall m' (i16' : list byte) (s2' s4' s5' s6' s8' s10' t4' t5' t6' : word),
        MD H0 i16' BE m' -> Z.of_nat (length i16') = 16%Z -> bw_ok BE ->
        evt s0segs Q (MS (mkR ra cP gp tp (Z_to_bv 64 257) (Z_to_bv 64 A) (Z_to_bv 64 2) cE (Z_to_bv 64 3) (Z_to_bv 64 (bw_numZ BD)) (Z_to_bv 64 nG)
                              (Z_to_bv 64 6) (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) (Z_to_bv 64 31) s2' (Z_to_bv 64 (bw_numZ BE))
                              s4' s5' s6' s7 s8' (NOT (E + 37708)) s10' s11 (Z_to_bv 64 nG) t4' t5' t6')
                          F (Z_to_bv 64 0x1c198) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1b670) fc None m0 (seg_rom s0segs)).
  Proof using All.
    intros H0 i16 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 HS28 HS44 HS76 HS60 HS68 Li16 MEM K.
    cps_pose NZ_chain as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5).
    cps_pose OK0 as (OKb & OKl & OKn).
    eapply (DX U0_in16_pre INUF ra s1 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t5 t6 H0 i16 (e_bw e) m0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4); [exact MEM|].
    eapply (DX U0_in16_outer INUF ra s1 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t5 t6 16%nat 0%Z H0 i16 (e_bw e) m0 t0 t1 t2 t3 t4);
      [lia| lia| lia| exact Li16| intros; lia| exact MEM|].
    clear MEM. intros m1 bs1 t0_1 t1_1 t2_1 t3_1 t4_1 MEM L1 ROWS1.
    eapply (DX U0_pin16_pre INUF ra s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 H0 bs1 (e_bw e) m1 _ _ _ _ _ _ t0_1 t1_1 t2_1 t3_1 t4_1 t5 t6 s1 s2);
      [exact OK0| lia| exact MEM|].
    eapply (DX U0_pin16_loop INUF ra s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 16%nat 0%Z IN16 H0 bs1 (e_bw e) m1 _ t4_1 t5 t6 s1 s2);
      [lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OK0| change (sm_put_in16 16 (e_bw e) IN16 0) with BA; lia| exact MEM|].
    change (sm_put_in16 16 (e_bw e) IN16 0) with BA. clear MEM.
    intros m2 t4_2 t5_2 t6_2 s1_2 s2_2 MEM OKA.
    eapply (DX U0_pinuse_pre INUF ra s6 s7 s8 (NOT (E + 37708)) s10 s11 m2 _ _ t4_2 t5_2 t6_2 s1_2 s2_2 s3 s4 s5).
    eapply (DX U0_pinuse_outer INUF ra s6 s7 s8 (NOT (E + 37708)) s10 s11 16%nat 0%Z IN16 H0 bs1 BA m2 _ t5_2 t6_2 s1_2 s2_2 s3 s4 s5);
      [lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OKA| rewrite BB_unfold; lia| exact MEM|].
    rewrite BB_unfold. clear MEM.
    intros m3 t5_3 t6_3 s1_3 s2_3 s3_3 s4_3 s5_3 MEM OKB.
    eapply (DX U0_bsw3 nSel HG HNS ra s5_3 s6 s7 s8 (NOT (E + 37708)) s10 s11 H0 bs1 BB m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [exact HS28| exact HS44| exact OKB| change (bsW BB 3 nG) with BC3; lia| exact MEM|].
    clear MEM. intros m4 a2_4 a5_4 a6_4 a7_4 bB1 EbB1 MEM X4.
    cps_pose OKB as (OKBb & OKBl & OKBn).
    cps_pose (bs_needw_post BS_FUEL BB OKB ltac:(change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OKB1 & MB1 & _). rewrite <- EbB1 in OKB1, MB1.
    pose proof (Z.mod_pos_bound (bw_live BB) 8 ltac:(lia)) as MB8.
    assert (OKC3 : bw_ok (bsW BB 3 nG)) by (apply bw_ok_bsW; [exact OKB| lia| lia]).
    assert (LC3 : bw_live (bsW BB 3 nG) = (bw_live bB1 + 3)%Z) by (unfold bsW; rewrite <- EbB1; reflexivity).
    eapply (DX U0_bsw15 nSel HG HNS ra s5_3 s6 s7 s8 (NOT (E + 37708)) s10 s11 H0 bs1 (bsW BB 3 nG) (bw_live bB1) m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [exact HS76| exact OKC3| exact LC3| cps_destruct OKB1 as (?&?&?); lia| change (bsW (bsW BB 3 nG) 15 nSel) with BC; lia| exact X4| exact MEM|].
    change (bsW (bsW BB 3 nG) 15 nSel) with BC. clear MEM.
    intros m5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t2_5 MEM OKC X5.
    eapply (DX U0_sels nSel HG HNS ra s5_3 s6 s7 s8 (NOT (E + 37708)) s10 s11 SLMF H0 bs1 BC m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [exact OKC| change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD; lia| exact X5| exact MEM|].
    change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD. clear MEM.
    intros m6 t2_6 t6_6 s1_6 s2_6 s3_6 s4_6 MEM OKD X6.
    eapply (DX U0_lens A HA HG LENF ra s7 s11 H0 bs1 BD m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [exact HS28| exact HS60| exact HS68| exact OKD| change (sm_put_lens (Z.to_nat nG) BD (e_len e) A 0) with BE; lia| exact MEM|].
    change (sm_put_lens (Z.to_nat nG) BD (e_len e) A 0) with BE. clear MEM.
    intros m7 s2_7 s4_7 s5_7 s6_7 s8_7 s10_7 t4_7 t5_7 t6_7 MEM OKE.
    enter_with (K m7 bs1 _ _ _ _ _ _ _ _ _); [st_eq| exact MEM| exact L1| exact OKE].
  Qed.
End SDZ.
End ACeilS1.
