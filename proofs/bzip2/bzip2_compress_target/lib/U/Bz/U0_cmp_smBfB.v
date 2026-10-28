(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
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
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
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
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.
Local Ltac lia ::= CmpRel.lia_cr.
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_smBfV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section FCWB.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 s1 s3 s4 s9 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z) (cb : zarr) (gs : Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx).
  Notation arr1 := (e_arr1 e).
  Ltac openCX CX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by lia
    | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Ltac fstep := let R := u_regs in u_zstep_nofb; bzl; u_flags R; u_try_lit_branch; u_try_guard.
  Ltac frun_to p := first [ u_at_pc p | u_pc_is_lit; fstep; frun_to p | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "STUCKAT" pc end; fail 1 "frun_to: stuck before" p ].
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac RDQ VAR1 QB ZB k :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let AR1v := fresh "AR1v" in let RD := fresh "RD" in
      pose proof (VAR1 mm MU') as AR1v;
      pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1v ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD;
      clear AR1v;
      change (rd16 arr1 (2 * (gs + k))) with (QV arr1 gs k) in RD;
      pose proof (QB k ltac:(lia)) as ?QBk;
      lstep; clear RD; rewrite (zx16_lit (QV arr1 gs k)) by lia end.
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; lstep; clear RO end.
  Ltac SST := lstep; lit_store.
  Ltac cl_cell :=
    lazymatch goal with
    | |- rw_cells ?sg ?mm ?A [C8 ?v] =>
        match goal with Hc : rw_cells sg mm A [C8 ?w] |- _ => replace v with w; [exact Hc | f_equal; lia] end
    end.

  Lemma U0_fc_it25 : FCI25 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99024%Z. RDV V1032.
    frun_to 99040%Z. RDV V1032.
    frun_to 99080%Z. RDQ VAR1 QB ZB 25%Z.
    frun_to 99088%Z. RDV V1000.
    frun_to 99096%Z. SST.
    frun_to 99136%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it26 : FCI26 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99152%Z. RDV V1032.
    frun_to 99168%Z. RDV V1032.
    frun_to 99208%Z. RDQ VAR1 QB ZB 26%Z.
    frun_to 99216%Z. RDV V1000.
    frun_to 99224%Z. SST.
    frun_to 99264%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it27 : FCI27 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99280%Z. RDV V1032.
    frun_to 99296%Z. RDV V1032.
    frun_to 99336%Z. RDQ VAR1 QB ZB 27%Z.
    frun_to 99344%Z. RDV V1000.
    frun_to 99352%Z. SST.
    frun_to 99392%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it28 : FCI28 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99408%Z. RDV V1032.
    frun_to 99424%Z. RDV V1032.
    frun_to 99464%Z. RDQ VAR1 QB ZB 28%Z.
    frun_to 99472%Z. RDV V1000.
    frun_to 99480%Z. SST.
    frun_to 99520%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it29 : FCI29 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99536%Z. RDV V1032.
    frun_to 99552%Z. RDV V1032.
    frun_to 99592%Z. RDQ VAR1 QB ZB 29%Z.
    frun_to 99600%Z. RDV V1000.
    frun_to 99608%Z. SST.
    frun_to 99648%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it30 : FCI30 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x832 x840 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99664%Z. RDV V1032.
    frun_to 99680%Z. RDV V1032.
    frun_to 99720%Z. RDQ VAR1 QB ZB 30%Z.
    frun_to 99728%Z. RDV V1000.
    frun_to 99736%Z. SST.
    frun_to 99776%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it31 : FCI31 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99792%Z. RDV V1032.
    frun_to 99808%Z. RDV V1032.
    frun_to 99848%Z. RDQ VAR1 QB ZB 31%Z.
    frun_to 99856%Z. RDV V1000.
    frun_to 99864%Z. SST.
    frun_to 99904%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it32 : FCI32 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 99920%Z. RDV V1032.
    frun_to 99936%Z. RDV V1032.
    frun_to 99976%Z. RDQ VAR1 QB ZB 32%Z.
    frun_to 99984%Z. RDV V1000.
    frun_to 99992%Z. SST.
    frun_to 100032%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it33 : FCI33 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100048%Z. RDV V1032.
    frun_to 100064%Z. RDV V1032.
    frun_to 100104%Z. RDQ VAR1 QB ZB 33%Z.
    frun_to 100112%Z. RDV V1000.
    frun_to 100120%Z. SST.
    frun_to 100160%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it34 : FCI34 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100176%Z. RDV V1032.
    frun_to 100192%Z. RDV V1032.
    frun_to 100232%Z. RDQ VAR1 QB ZB 34%Z.
    frun_to 100240%Z. RDV V1000.
    frun_to 100248%Z. SST.
    frun_to 100288%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it35 : FCI35 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100304%Z. RDV V1032.
    frun_to 100320%Z. RDV V1032.
    frun_to 100360%Z. RDQ VAR1 QB ZB 35%Z.
    frun_to 100368%Z. RDV V1000.
    frun_to 100376%Z. SST.
    frun_to 100416%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it36 : FCI36 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100432%Z. RDV V1032.
    frun_to 100448%Z. RDV V1032.
    frun_to 100488%Z. RDQ VAR1 QB ZB 36%Z.
    frun_to 100496%Z. RDV V1000.
    frun_to 100504%Z. SST.
    frun_to 100544%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it37 : FCI37 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100560%Z. RDV V1032.
    frun_to 100576%Z. RDV V1032.
    frun_to 100616%Z. RDQ VAR1 QB ZB 37%Z.
    frun_to 100624%Z. RDV V1000.
    frun_to 100664%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it38 : FCI38 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 x520 x584 x592 x600 x832 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100680%Z. RDV V1032.
    frun_to 100696%Z. RDV V1032.
    frun_to 100736%Z. RDQ VAR1 QB ZB 38%Z.
    frun_to 100744%Z. RDV V1000.
    frun_to 100752%Z. SST.
    frun_to 100792%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it39 : FCI39 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 x520 x584 x592 x600 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100808%Z. RDV V1032.
    frun_to 100824%Z. RDV V1032.
    frun_to 100864%Z. RDQ VAR1 QB ZB 39%Z.
    frun_to 100872%Z. RDV V1000.
    frun_to 100908%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it40 : FCI40 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a7 s5 s6 s7 s11 t4 x520 x584 x592 x600 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 100924%Z. RDV V1032.
    frun_to 100940%Z. RDV V1032.
    frun_to 100980%Z. RDQ VAR1 QB ZB 40%Z.
    frun_to 100988%Z. RDV V1000.
    frun_to 101024%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it41 : FCI41 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a7 s5 s6 s11 t4 x520 x584 x592 x600 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101040%Z. RDV V1032.
    frun_to 101056%Z. RDV V1032.
    frun_to 101096%Z. RDQ VAR1 QB ZB 41%Z.
    frun_to 101104%Z. RDV V1000.
    frun_to 101112%Z. SST.
    frun_to 101152%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it42 : FCI42 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a7 s5 s6 s11 t4 x520 x584 x592 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101168%Z. RDV V1032.
    frun_to 101184%Z. RDV V1032.
    frun_to 101224%Z. RDQ VAR1 QB ZB 42%Z.
    frun_to 101232%Z. RDV V1000.
    frun_to 101268%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it43 : FCI43 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a7 s6 s11 t4 x520 x584 x592 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101284%Z. RDV V1032.
    frun_to 101300%Z. RDV V1032.
    frun_to 101340%Z. RDQ VAR1 QB ZB 43%Z.
    frun_to 101348%Z. RDV V1000.
    frun_to 101384%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it44 : FCI44 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 s6 s11 t4 x520 x584 x592 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101400%Z. RDV V1032.
    frun_to 101416%Z. RDV V1032.
    frun_to 101456%Z. RDQ VAR1 QB ZB 44%Z.
    frun_to 101464%Z. RDV V1000.
    frun_to 101472%Z. SST.
    frun_to 101512%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it45 : FCI45 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 s6 s11 t4 x520 x584 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101528%Z. RDV V1032.
    frun_to 101544%Z. RDV V1032.
    frun_to 101584%Z. RDQ VAR1 QB ZB 45%Z.
    frun_to 101592%Z. RDV V1000.
    frun_to 101600%Z. SST.
    frun_to 101640%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it46 : FCI46 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 s6 s11 t4 x520 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101656%Z. RDV V1032.
    frun_to 101672%Z. RDV V1032.
    frun_to 101712%Z. RDQ VAR1 QB ZB 46%Z.
    frun_to 101720%Z. RDV V1000.
    frun_to 101760%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it47 : FCI47 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a3 a5 s6 s11 t4 x520 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101776%Z. RDV V1032.
    frun_to 101792%Z. RDV V1032.
    frun_to 101832%Z. RDQ VAR1 QB ZB 47%Z.
    frun_to 101840%Z. RDV V1000.
    frun_to 101876%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it48 : FCI48 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a3 a5 s6 s11 x520 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 101892%Z. RDV V1032.
    frun_to 101908%Z. RDV V1032.
    frun_to 101948%Z. RDQ VAR1 QB ZB 48%Z.
    frun_to 101956%Z. RDV V1000.
    frun_to 101992%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it49 : FCI49 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra a0 a1 a3 a5 s6 s11 x520 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 102008%Z. RDV V1032.
    frun_to 102024%Z. RDV V1032.
    frun_to 102064%Z. RDQ VAR1 QB ZB 49%Z.
    frun_to 102072%Z. RDV V1000.
    frun_to 102108%Z. SST.
    frun_to 102112%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

End FCWB.
End ACeilS1.
