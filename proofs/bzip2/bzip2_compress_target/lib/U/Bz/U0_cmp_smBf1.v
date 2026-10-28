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

Section FCW1.
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

  Lemma U0_fc_it0 : FCI0 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 95884%Z. RDV V1032.
    frun_to 95896%Z. RDV V1016.
    frun_to 95908%Z. RDV V1032.
    frun_to 95936%Z. RDV V1032.
    frun_to 95960%Z. RDQ VAR1 QB ZB 0%Z.
    frun_to 95968%Z. RDV V1000.
    frun_to 96004%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it1 : FCI1 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96020%Z. RDV V1032.
    frun_to 96036%Z. RDV V1032.
    frun_to 96076%Z. RDQ VAR1 QB ZB 1%Z.
    frun_to 96084%Z. RDV V1000.
    frun_to 96120%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it2 : FCI2 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t1 t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96136%Z. RDV V1032.
    frun_to 96152%Z. RDV V1032.
    frun_to 96192%Z. RDQ VAR1 QB ZB 2%Z.
    frun_to 96200%Z. RDV V1000.
    frun_to 96236%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it3 : FCI3 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96252%Z. RDV V1032.
    frun_to 96268%Z. RDV V1032.
    frun_to 96308%Z. RDQ VAR1 QB ZB 3%Z.
    frun_to 96316%Z. RDV V1000.
    frun_to 96352%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it4 : FCI4 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96368%Z. RDV V1032.
    frun_to 96384%Z. RDV V1032.
    frun_to 96424%Z. RDQ VAR1 QB ZB 4%Z.
    frun_to 96432%Z. RDV V1000.
    frun_to 96440%Z. SST.
    frun_to 96480%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it5 : FCI5 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x832 x840 x848 x856 x864 x872 x880 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96496%Z. RDV V1032.
    frun_to 96512%Z. RDV V1032.
    frun_to 96552%Z. RDQ VAR1 QB ZB 5%Z.
    frun_to 96560%Z. RDV V1000.
    frun_to 96568%Z. SST.
    frun_to 96608%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it6 : FCI6 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x832 x840 x848 x856 x864 x872 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96624%Z. RDV V1032.
    frun_to 96640%Z. RDV V1032.
    frun_to 96680%Z. RDQ VAR1 QB ZB 6%Z.
    frun_to 96688%Z. RDV V1000.
    frun_to 96696%Z. SST.
    frun_to 96736%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it7 : FCI7 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x832 x840 x848 x856 x864 x872 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96752%Z. RDV V1032.
    frun_to 96768%Z. RDV V1032.
    frun_to 96808%Z. RDQ VAR1 QB ZB 7%Z.
    frun_to 96816%Z. RDV V1000.
    frun_to 96824%Z. SST.
    frun_to 96864%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it8 : FCI8 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x832 x840 x848 x856 x864 x872 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 96880%Z. RDV V1032.
    frun_to 96896%Z. RDV V1032.
    frun_to 96936%Z. RDQ VAR1 QB ZB 8%Z.
    frun_to 96944%Z. RDV V1000.
    frun_to 96952%Z. SST.
    frun_to 96992%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it9 : FCI9 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x832 x840 x848 x856 x864 x872 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97008%Z. RDV V1032.
    frun_to 97024%Z. RDV V1032.
    frun_to 97064%Z. RDQ VAR1 QB ZB 9%Z.
    frun_to 97072%Z. RDV V1000.
    frun_to 97080%Z. SST.
    frun_to 97120%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it10 : FCI10 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97136%Z. RDV V1032.
    frun_to 97152%Z. RDV V1032.
    frun_to 97192%Z. RDQ VAR1 QB ZB 10%Z.
    frun_to 97200%Z. RDV V1000.
    frun_to 97236%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it11 : FCI11 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97252%Z. RDV V1032.
    frun_to 97268%Z. RDV V1032.
    frun_to 97308%Z. RDQ VAR1 QB ZB 11%Z.
    frun_to 97316%Z. RDV V1000.
    frun_to 97324%Z. SST.
    frun_to 97364%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it12 : FCI12 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97380%Z. RDV V1032.
    frun_to 97396%Z. RDV V1032.
    frun_to 97436%Z. RDQ VAR1 QB ZB 12%Z.
    frun_to 97444%Z. RDV V1000.
    frun_to 97452%Z. SST.
    frun_to 97492%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it13 : FCI13 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97508%Z. RDV V1032.
    frun_to 97524%Z. RDV V1032.
    frun_to 97564%Z. RDQ VAR1 QB ZB 13%Z.
    frun_to 97572%Z. RDV V1000.
    frun_to 97608%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it14 : FCI14 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97624%Z. RDV V1032.
    frun_to 97640%Z. RDV V1032.
    frun_to 97680%Z. RDQ VAR1 QB ZB 14%Z.
    frun_to 97688%Z. RDV V1000.
    frun_to 97696%Z. SST.
    frun_to 97736%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it15 : FCI15 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97752%Z. RDV V1032.
    frun_to 97768%Z. RDV V1032.
    frun_to 97808%Z. RDQ VAR1 QB ZB 15%Z.
    frun_to 97816%Z. RDV V1000.
    frun_to 97824%Z. SST.
    frun_to 97864%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it16 : FCI16 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 97880%Z. RDV V1032.
    frun_to 97896%Z. RDV V1032.
    frun_to 97936%Z. RDQ VAR1 QB ZB 16%Z.
    frun_to 97944%Z. RDV V1000.
    frun_to 97952%Z. SST.
    frun_to 97992%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it17 : FCI17 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x832 x840 x848 x856 x864 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98008%Z. RDV V1032.
    frun_to 98024%Z. RDV V1032.
    frun_to 98064%Z. RDQ VAR1 QB ZB 17%Z.
    frun_to 98072%Z. RDV V1000.
    frun_to 98080%Z. SST.
    frun_to 98120%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it18 : FCI18 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x832 x840 x848 x856 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98136%Z. RDV V1032.
    frun_to 98152%Z. RDV V1032.
    frun_to 98192%Z. RDQ VAR1 QB ZB 18%Z.
    frun_to 98200%Z. RDV V1000.
    frun_to 98208%Z. SST.
    frun_to 98248%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it19 : FCI19 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x832 x840 x848 x856 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98264%Z. RDV V1032.
    frun_to 98280%Z. RDV V1032.
    frun_to 98320%Z. RDQ VAR1 QB ZB 19%Z.
    frun_to 98328%Z. RDV V1000.
    frun_to 98336%Z. SST.
    frun_to 98376%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it20 : FCI20 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x832 x840 x848 x856 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98392%Z. RDV V1032.
    frun_to 98408%Z. RDV V1032.
    frun_to 98448%Z. RDQ VAR1 QB ZB 20%Z.
    frun_to 98456%Z. RDV V1000.
    frun_to 98464%Z. SST.
    frun_to 98504%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it21 : FCI21 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x832 x840 x848 x856 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98520%Z. RDV V1032.
    frun_to 98536%Z. RDV V1032.
    frun_to 98576%Z. RDQ VAR1 QB ZB 21%Z.
    frun_to 98584%Z. RDV V1000.
    frun_to 98592%Z. SST.
    frun_to 98632%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it22 : FCI22 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x832 x840 x848 x856 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98648%Z. RDV V1032.
    frun_to 98664%Z. RDV V1032.
    frun_to 98704%Z. RDQ VAR1 QB ZB 22%Z.
    frun_to 98712%Z. RDV V1000.
    frun_to 98720%Z. SST.
    frun_to 98760%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it23 : FCI23 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t5 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98776%Z. RDV V1032.
    frun_to 98792%Z. RDV V1032.
    frun_to 98832%Z. RDQ VAR1 QB ZB 23%Z.
    frun_to 98840%Z. RDV V1000.
    frun_to 98880%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

  Lemma U0_fc_it24 : FCI24 cx e Q gp tp s0 s1 s3 s4 s9 F fc SP cb gs.
  Proof.
    intros m me Jlo ra t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 s7 s11 t4 t6 x520 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x832 x840 x848 H LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 SC MI MU WM VAR1 V1000 V1016 V1032 K.
    destruct H as (CX & CEP & PHI & HA & Hgs & HgsM & HM & ZB & QB).
    openCX CX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP.
    frun_to 98896%Z. RDV V1032.
    frun_to 98912%Z. RDV V1032.
    frun_to 98952%Z. RDQ VAR1 QB ZB 24%Z.
    frun_to 98960%Z. RDV V1000.
    frun_to 98968%Z. SST.
    frun_to 99008%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | idtac .. ]; try assumption; try cl_cell.
  Qed.

End FCW1.
End ACeilS1.
