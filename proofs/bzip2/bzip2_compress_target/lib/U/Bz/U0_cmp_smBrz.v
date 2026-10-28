(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpFsKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_smBr1 U0_cmp_smBr2 U0_cmp_smBr3.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section FR.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation S6 := (Z_to_bv 64 (4 * A)).
  Notation RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_fr : cctx_ok cx -> (3 <= A <= 258)%Z -> (2 <= nG <= 6)%Z -> (1 <= nMTF <= (NBLOCKMAX + 20))%Z -> zbok arr1 ->
    forall (rf0 : zarr) (gs bt B : Z) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs)%Z -> (gs + 50 <= nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + 50 <= 2000000000)%Z ->
    (forall k, (0 <= k < 50)%Z -> (0 <= QV arr1 gs k < A)%Z) ->
    u32arr s0segs m (E + 45448) (ovw rf0 (jseg J 45448 6192) 1548) -> RFrow rf0 bt A B ->
    mem_inv s0segs m -> munch Wrf me m -> wmono s0segs me m ->
    (forall m', munch Wrf me m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    frdW s0segs Wrf me (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] -> frdW s0segs Wrf me (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wrf me (SP + 1024) [C8 (Z_to_bv 64 (gs + 50))] -> frdW s0segs Wrf me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (rf' : zarr) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) ->
      rf' = sm_rfreq_inc 50 rf0 arr1 bt gs -> RFrow rf' bt A (B + 50) ->
      mem_inv s0segs m' -> munch Wrf me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b310) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) (Z_to_bv 64 (1032 * bt)) a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x199fc) fc None m (seg_rom s0segs)).
  Proof.
    intros CX HA HNG HM ZB rf0 gs bt B m me ra t0 t1 t2 a0 a1 a2 a3 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6
      Hgs HgsM Hbt HB HBM QB RFQ RFF MI MU WM VAR1 V952 V1016 V1024 V1032 K.
    assert (HnG : (nG <= 6)%Z) by lia. assert (HM6 : (nMTF <= (NBLOCKMAX + 20))%Z) by lia.
    assert (ERF : rf0 = sm_rfreq_inc 0 rf0 arr1 bt gs) by reflexivity.
    replace B with (B + 0)%Z in RFF by lia.
    eapply U0_fr1 with (cx := cx) (e := e) (Q := Q) (SP := SP) (rf0 := rf0) (gs := gs) (bt := bt) (B := B) (me := me).
    all: first [ eassumption | idtac ].
    clear RFQ ERF RFF MI MU WM. intros m1 rf1 y0 y2 y3 RFQ ERF RFF MI MU WM.
    eapply U0_fr2 with (cx := cx) (e := e) (Q := Q) (SP := SP) (rf0 := rf0) (gs := gs) (bt := bt) (B := B) (me := me).
    all: first [ eassumption | idtac ].
    clear RFQ ERF RFF MI MU WM. intros m2 rf2 z0 z2 z3 RFQ ERF RFF MI MU WM.
    eapply U0_fr3 with (cx := cx) (e := e) (Q := Q) (SP := SP) (rf0 := rf0) (gs := gs) (bt := bt) (B := B) (me := me).   (* [comment removed for export] *)
    all: first [ eassumption | idtac ].
    clear RFQ ERF RFF MI MU WM. intros m3 rf3 w0 w1 w2 w3 w5 w6 RFQ ERF RFF MI MU WM.
    eapply K; eassumption.
  Qed.
End FR.
End ACeilS1.
