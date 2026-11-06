(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition shcB (b : byte) : list cell := Eval cbv [repeat] in repeat (C1 b) 32.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).

  Lemma A0_bs_E2 : forall (m : word -> option byte) (v200 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (P + 200) [C8 v200; C8 (Z_to_bv 64 (SHF + 362))] -> mem_inv a0segs m ->
    (evt a0segs Q (MS (mkR (Z_to_bv 64 0x9a278) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x559e4) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9a26c) fc None m (seg_rom a0segs)).
  Proof.
    intros m v200 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SL MI K.
    (* [comment removed for export] *)
    wstep. wstep. wstep. exact K.
  Qed.

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.

  Lemma A0_bs_E3 : forall (me m : word -> option byte) (b : byte) (v104 v112 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (SHF + 322) (shcB b) -> mem_inv a0segs m -> munch [(SHF + 322, SHF + 354)]%Z me m -> wmono a0segs me m ->
    frdW a0segs [(SHF + 322, SHF + 354)]%Z me (P + 104) [C8 v104; C8 v112; C8 (Z_to_bv 64 (SHF + 178))] ->
    (forall m', rw_cells a0segs m' (SHF + 322) (shcB f8b) -> mem_inv a0segs m' -> munch [(SHF + 322, SHF + 354)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x9a308) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9a278) fc None m (seg_rom a0segs)).
  Proof.
    intros me m b v104 v112 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 SH MI MU WMo V K.
    unfold shcB in SH.
    (* [comment removed for export] *)
    wstep. do 32 sbf8. wstep.
    pose proof (V _ MU) as RO_. wstep. clear RO_. wstep.
    apply K; [unfold shcB; exact SH| exact MI| exact MU| exact WMo].
  Qed.

  Lemma A0_bs_E4 : forall (m : word -> option byte) (SHn b : Z) (v120 s5v v384 : word) (sq : scq)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    saddr (E + 108) SHn -> (-2147483648 < b < 2147483648)%Z ->
    rw_cells a0segs m (P + 104) [C8 (Z_to_bv 64 SHn); C8 (Z_to_bv 64 (E + 108)); C8 v120; C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 FB); C8 s5v] ->
    rw_cells a0segs m (P + 216) (scq_cells Y sq) -> rw_cells a0segs m (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] ->
    rw_cells a0segs m (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> mem_inv a0segs m ->
    shzW a0segs [] m E (E + 55768) ->
    (* [comment removed for export] *)
    (forall (y10 y11 : word), (0 <= b)%Z ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (E + 108)) cSB x20 s5v x22 (Z_to_bv 64 FT) (Z_to_bv 64 FB) (Z_to_bv 64 E) x26 (Z_to_bv 64 SHn) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x9a37c) fc None m (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    ((b < 0)%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x9a37c) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 n) (Z_to_bv 64 0) x15 x16 x17
                            (Z_to_bv 64 (E + 108)) cSB x20 s5v x22 (Z_to_bv 64 FT) (Z_to_bv 64 FB) (Z_to_bv 64 E) x26 (Z_to_bv 64 SHn) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x9aa30) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 x22 (Z_to_bv 64 FT) x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9a308) fc None m (seg_rom a0segs)).
  Proof.
    intros m SHn b v120 s5v v384 sq x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
           ASN Hb SL SCQ SCC BUD EC MI SHE KB KF.
    msenv_open XOK. amenv_open YOK. open_scq_in SCQ.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. astep. astep.
    (* [comment removed for export] *)
    wstep. rewrite (sx32_of_Z_signed b) by lia.
    wstep; if_cases Kb; [apply bgez_taken in Kb; [|lia] | apply bgez_not_taken in Kb; [|lia]].
    - eapply KB. exact Kb.
    - (* [comment removed for export] *)
      astep. astep. astep.
      arun_to 0x9a378%Z. wstep.
      eapply KF. exact Kb.
  Qed.
End A0MS.

End ACeilS1.
