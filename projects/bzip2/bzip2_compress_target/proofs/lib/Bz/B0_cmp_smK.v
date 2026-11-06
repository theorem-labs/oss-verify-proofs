(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdV.


(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
(* [comment removed for export] *)
Ltac openCX_a CX :=
  let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in
  let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let ME := ident:(ME) in let MA1 := ident:(MA1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in
  let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA1 MA2 MF Mb Mf LJb; lin16 ME.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SMK.
  Variables (cx : cctx) (Q : machine_state -> Prop) (P nG A : Z).
  Notation E := (c_E cx).
  Hypothesis CX : cctx_ok cx.
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  (* [comment removed for export] *)
  Notation HK v00 v32 v48 v56 v72 v88 v20 v28 :=
    (sd_hi cx nG (SDW v00 (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 v72 v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Ltac openHK H := unfold sd_hi in H; cbv zeta in H; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in H.

  Lemma B0_sm_mklA : forall (m : word -> option byte) (t : Z) (v00 v32 v48 v56 v72 v88 v20 v28 : word)
      (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    rw_cells b0segs m (P + 1384) (HK v00 v32 v48 v56 v72 v88 v20 v28) -> (0 <= t < 6)%Z ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 0x939e0) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 (E + 45448 + 1032 * t)) (Z_to_bv 64 A) (Z_to_bv 64 17)
                          a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (258 * t - 1548)) s5 s6 s7 s8 s9 (Z_to_bv 64 (1032 * t)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa7e6c) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (258 * t - 1548)) s5 s6 s7 s8 s9 (Z_to_bv 64 (1032 * t)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9399c) fc None m (seg_rom b0segs)).
  Proof.
    intros m t v00 v32 v48 v56 v72 v88 v20 v28 ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc HI Ht K.
    openCX_a CX. openHK HI.
    brun_to 0xa7e6c%Z.
    enter_with K; st_eq.
  Qed.

  Lemma B0_sm_mklB : forall (m : word -> option byte) (t : Z) (v00 v32 v48 v56 v72 v88 v20 v28 : word)
      (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    rw_cells b0segs m (P + 1384) (HK v00 v32 v48 v56 v72 v88 v20 v28) -> (0 <= t < nG)%Z -> (nG <= 6)%Z ->
    (* [comment removed for export] *)
    ((t + 1 <> nG)%Z ->
     evt b0segs Q (MS (mkR (Z_to_bv 64 A) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 (1032 * nG)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (258 * (t + 1) - 1548)) s5 s6 s7 s8 s9
                           (Z_to_bv 64 (1032 * (t + 1))) s11 t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9)))
                      F (Z_to_bv 64 0x9399c) fc None m (seg_rom b0segs))) ->
    (* [comment removed for export] *)
    ((t + 1 = nG)%Z ->
     evt b0segs Q (MS (mkR (Z_to_bv 64 A) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 (1032 * nG)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (258 * (t + 1) - 1548)) s5 s6 s7 s8 s9
                           (Z_to_bv 64 (1032 * (t + 1))) s11 t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9)))
                      F (Z_to_bv 64 0x939fc) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (258 * t - 1548)) s5 s6 s7 s8 s9 (Z_to_bv 64 (1032 * t)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x939e0) fc None m (seg_rom b0segs)).
  Proof.
    intros m t v00 v32 v48 v56 v72 v88 v20 v28 ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc HI Ht HnG KM KD.
    openHK HI.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (KM ltac:(lia)); st_eq.
    - enter_with (KD ltac:(lia)); st_eq.
  Qed.
End SMK.
End ACeilS1.
