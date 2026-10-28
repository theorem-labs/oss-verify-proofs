(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 BzWalkArith DecCut S0_bzd_out S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1 BzLemmasMtf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop1.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_bzd_loop2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_loop1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop1.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zok :=
    let CX := ident:(CX) in let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj in CS; cbv zeta in CS;
    cps_destruct CS as (D1 & D2 & D3 & _ & _ & _ & _ & IA1 & IA2 & _); unfold img_apart, IHI in IA1, IA2;
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 fmkc] in *.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.

  (* [comment removed for export] *)
  Lemma FWB_sub : forall c, o_cx c = cx -> sub_fp (FWB c) (WBZ z).
  Proof.
    intros c E1. unfold sub_fp, FWB, WBZ. zok. rewrite E1. cbn [outside app]. (intros x; cps_intros (A & B & C & D & _)).
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cf_transport : forall c m1 m cf, o_cx c = cx -> munch (FWB c) m1 m -> wmono s0segs m1 m ->
    u32arr s0segs m1 (S + 1096) cf -> length cf = 257%nat -> u32arr s0segs m (S + 1096) cf.
  Proof.
    intros c m1 m cf E1 MU WM CF CFL. zok. unfold FWB in MU. rewrite E1 in MU.
    eapply u32arr_transport; [exact CF| exact MU| exact WM|]. rewrite CFL. cbn. lia.
  Qed.
  Lemma fheld_transport : forall c m1 m rr,
    o_cx c = cx ->
    munch (FWB c) m1 m -> wmono s0segs m1 m ->
    drest_at s0segs m1 S rr ->
    bytes_at s0segs m1 (b_src cx) (z_payload z) -> rw_cells s0segs m1 0x32098 [C8 (z_sv z)] ->
    rw_cells s0segs m1 uspi (FRM z) -> stk s0segs m1 lo uspi -> munch (WBZ z) (z_m0 z) m1 -> wmono s0segs (z_m0 z) m1 ->
    drest_at s0segs m S rr /\ bytes_at s0segs m (b_src cx) (z_payload z) /\
    rw_cells s0segs m 0x32098 [C8 (z_sv z)] /\ rw_cells s0segs m uspi (FRM z) /\ stk s0segs m lo uspi /\
    munch (WBZ z) (z_m0 z) m /\ wmono s0segs (z_m0 z) m.
  Proof.
    intros c m1 m rr E1 MU WM DR PAY SV FR ST MU0 WM0. zok.
    pose proof (FWB_sub c E1) as SUB.
    unfold FWB in MU. rewrite E1 in MU.
    splits.
    - eapply drest_transport; [exact DR| exact MU| exact WM| | |]; cbn; lia.
    - eapply bytes_at_transport; [exact PAY| exact MU|]. rewrite PAYL. cbn. lia.
    - eapply rw_cells_transport; [exact SV| exact MU| exact WM|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
    - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia.
    - eapply munch_trans; [exact MU0|]. eapply munch_weaken; [exact SUB|]. unfold FWB. rewrite E1. exact MU.
    - eapply wmono_trans; [exact WM0| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fexitF : forall (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) (rr : drest),
    b_small cx = 0%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    u32arr s0segs m1 (S + 1096) (zw32 (d_cftab d) 257) -> drest_at s0segs m1 S rr ->
    bytes_at s0segs m1 (b_src cx) (z_payload z) -> rw_cells s0segs m1 0x32098 [C8 (z_sv z)] ->
    rw_cells s0segs m1 uspi (FRM z) -> stk s0segs m1 lo uspi -> munch (WBZ z) (z_m0 z) m1 -> wmono s0segs (z_m0 z) m1 ->
    FKexit (fmkc z m1 J d s f) (FROf (fmkc z m1 J d s f)).
  Proof.
    intros until rr. intros Hsm DP Err CF DR PAY SV FR ST MU0 WM0.
    unfold FKexit. ofmkc. intros rq0 rq1 rq2 rq3 rq4 rq5 rq6 rq7 rq8 rq9 rq10 rq11 rq12 rq13 rq14 rq15 rq16 rq17 m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest.
    intros DSm DE RO MU WM (Hnu & Hav).
    pose proof (cf_transport (fmkc z m1 J d s f) m1 m _ eq_refl MU WM CF ltac:(rewrite zw32_length_nat; reflexivity)) as CF'.
    cps_destruct (fheld_transport (fmkc z m1 J d s f) m1 m rr eq_refl MU WM DR PAY SV FR ST MU0 WM0)
      as (DR' & PAY' & SV' & FR' & ST' & MU' & WM').
    cps_destruct RO as (SAV & TTA & CRC & RNA & GOT & MI). unfold FGOT in GOT. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    focbn_in Hnu. cbn [K_U Z.eqb].
    eapply (bzd_fepi z ZOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m BZ_DATA_ERROR (jk_set_o J tol toh)
              (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout) dbytes rest FR' ST' MU' WM' MI).
    - eapply dmemF_intro; focbn; try exact_cells HD; try exact_cells NBU; try exact CF'; try exact_cells MID; try exact_cells SAV; try exact_cells SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      + change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d). rewrite Err. exact DR'.
      + change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
        unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
        pose proof (proj1 (proj2 (proj2 DP))) as En. zok.
        split; [exact Hsm| split; [exact TTA| rewrite zw32_length by lia; reflexivity]].
    - exact CRC.
    - unfold FDEST. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - apply dpureF_set8; [exact DP| exact Hnu].
    - unfold BZ_DATA_ERROR. lia.
  Qed.

  Lemma bzd_fexitS : forall (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) (rr : drest),
    b_small cx = 1%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    drest_at s0segs m1 S rr ->
    bytes_at s0segs m1 (b_src cx) (z_payload z) -> rw_cells s0segs m1 0x32098 [C8 (z_sv z)] ->
    rw_cells s0segs m1 uspi (FRM z) -> stk s0segs m1 lo uspi -> munch (WBZ z) (z_m0 z) m1 -> wmono s0segs (z_m0 z) m1 ->
    FKexit (fmkc z m1 J d s f) (FROs (fmkc z m1 J d s f)).
  Proof.
    intros until rr. intros Hsm DP Err DR PAY SV FR ST MU0 WM0.
    unfold FKexit. ofmkc. intros rq0 rq1 rq2 rq3 rq4 rq5 rq6 rq7 rq8 rq9 rq10 rq11 rq12 rq13 rq14 rq15 rq16 rq17 m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest.
    intros DSm DE RO MU WM (Hnu & Hav).
    cps_destruct RO as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI). unfold FGOT in GOT. ofmkc.
    cps_destruct (fheld_transport (fmkc z m1 J d s f) m1 m rr eq_refl MU WM DR PAY SV FR ST MU0 WM0)
      as (DR' & PAY' & SV' & FR' & ST' & MU' & WM').
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    focbn_in Hnu. cbn [K_U Z.eqb].
    eapply (bzd_fepi z ZOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m BZ_DATA_ERROR (jk_set_o J tol toh)
              (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout) dbytes rest FR' ST' MU' WM' MI).
    - eapply dmemF_intro; focbn; try exact_cells HD; try exact_cells NBU; try exact CFA; try exact_cells MID; try exact_cells SAV; try exact_cells SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      + change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d). rewrite Err. exact DR'.
      + change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
        unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
        pose proof (proj1 (proj2 (proj2 DP))) as En. zok.
        split; [exact Hsm| split; [exact L16A| split; [rewrite zh16_length by lia; reflexivity| split; [exact L4A| rewrite zb8_length by lia; reflexivity]]]].
    - exact CRC.
    - unfold FDEST. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - apply dpureF_set8; [exact DP| exact Hnu].
    - unfold BZ_DATA_ERROR. lia.
  Qed.
End BZD.
End ACeilS1.
End S0F_bzd_loop2.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzdFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_loop3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_loop1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s.S0F_bzd_loop2.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma dpureF_rebase : forall cx J0 s0 payload J d s, dpureF cx (bs_of cx J0 s0) payload J d s -> dpureF cx (bs_of cx J s) payload J d s.
Proof.
  intros cx J0 s0 payload J d s DP. unfold dpureF, jk_static in DP |- *. dvF_cbn_in DP. dvF_cbn. decompose [and] DP.
  repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
Lemma dpureF_setcb : forall cx b0 payload J d s a,
  dpureF cx b0 payload J d s -> dpureF cx b0 payload J (d_set_cbcrc d a) s.
Proof. intros. unfold dpureF, drep in *. focbn. exact H. Qed.
Lemma dpureF_setccs : forall cx b0 payload J d s a b e,
  dpureF cx b0 payload J d s -> dpureF cx b0 payload J (d_set_state (d_set_cccrc (d_set_cbcrc d a) b) e) s.
Proof. intros. unfold dpureF, drep in *. focbn. exact H. Qed.
(* [comment removed for export] *)
Lemma cccrc_step2 : forall cc crc, (0 <= cc < 4294967296)%Z -> (0 <= crc < 4294967296)%Z ->
  ((Z.lxor (Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 cc)) * 2) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 cc)) mod 4294967296 / 2147483648))
          (bv_unsigned (sx32 (Z_to_bv 64 crc)))) mod 4294967296
   = Z.lxor (Z.lor (cc * 2) (cc / 2147483648) mod 4294967296) crc)%Z.
Proof. intros cc crc Hcc Hcrc. rewrite cccrc_step by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Hypothesis DEC : dec14F_spec DI_S0.
  Notation cx := (z_cx z).
  Hypothesis N1 : (1 <= b_n (z_cx z))%Z.
  Hypothesis NN0 : b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z.
  Hypothesis NN1 : b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z.
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zlin :=
    let CX := ident:(CX) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    cps_destruct CL as (LS1 & LS2 & LR1 & LR2 & LR3 & LR4 & LD1 & LD2 & LD3 & LD4 & LP1 & LP2 & _ & LSTRM & LSM & LN & LTT & LL16 & LL4);
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    pose proof crc_words_length as CWL; pose proof rnums_words_length as RNL.
  Ltac zsepF TNZ :=
    let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in lazymatch goal with CX : ctx_ok _ |- _ =>
      let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj, DSTATE_SIZE in CS; cbv zeta in CS;
      let D4 := fresh "D4" in
      let IA3 := fresh "IA3" in
      cps_destruct CS as (D1 & D2 & _ & D4 & _ & _ & _ & IA1 & IA2 & IA3 & _); pose proof (IA3 TNZ) as IA3'; clear IA3; unfold img_apart, IHI in IA1, IA2, IA3'; cps_destruct (D4 TNZ) as (D4a & D4b & D4c); clear D4 end.
  Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
  Ltac dlia := BzdFast.dlia_fast.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.
  Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
  (* [comment removed for export] *)
  Ltac djtac := cbn [disjoint_from]; unfold FRM, FRMj; simpl_sizes; repeat split; try exact I; dlia.
  Ltac subfp_tac := BzdFast.subfp_fast.
  Ltac transport14 m m' MUc WMc :=
    let W := lazymatch type of MUc with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at s0segs m ?A ?bs |- _ =>
        first [ apply (bytes_at_transport s0segs W m m' A bs) in H; [| exact MUc| djtac] | clear H ]
    | H : rw_cells s0segs m ?A ?cs |- _ =>
        first [ apply (rw_cells_transport s0segs W m m' A cs) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : u8arr s0segs m ?A ?bs |- _ =>
        first [ apply (u8arr_transport s0segs W m m' A bs) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : u32arr s0segs m ?A ?ws |- _ =>
        first [ apply (u32arr_transport s0segs W m m' A ws) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : stk s0segs m ?lo' ?hi' |- _ =>
        first [ apply (stk_transport_disjoint s0segs W m m' lo' hi') in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : munch ?Wq ?mq m |- _ =>
        apply (munch_trans Wq mq m m') in H; [| eapply (munch_weaken W Wq m m'); [subfp_tac| exact MUc]]
    | H : wmono s0segs ?mq m |- _ => apply (wmono_trans s0segs mq m m') in H; [| exact WMc]
    | H : mem_inv s0segs m |- _ => clear H
    end.

  Ltac zsepS NZ16 NZ4 :=
    let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in lazymatch goal with CX : ctx_ok _ |- _ =>
      let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj, DSTATE_SIZE in CS; cbv zeta in CS;
      let D5 := fresh "D5" in let D6 := fresh "D6" in let D7 := fresh "D7" in
      let IA4 := fresh "IA4" in let IA5 := fresh "IA5" in
      cps_destruct CS as (D1 & D2 & _ & _ & D5 & D6 & D7 & IA1 & IA2 & _ & IA4 & IA5); pose proof (IA4 NZ16) as IA4'; pose proof (IA5 NZ4) as IA5'; clear IA4 IA5; unfold img_apart, IHI in IA1, IA2, IA4', IA5'; cps_destruct (D5 NZ16) as (D5a & D5b & D5c); cps_destruct (D6 NZ4) as (D6a & D6b & D6c);
      pose proof (D7 NZ16 NZ4) as D7a; clear D5 D6 D7 end.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 fmkc] in *.
  (* [comment removed for export] *)
  Ltac trb H MU D := unfold id in H; eapply bytes_at_transport in H; [| exact MU| unfold id in D; BzdFast.cbn_lia].
  Ltac tr8 H MU WM D := unfold id in H; eapply u8arr_transport in H; [| exact MU| exact WM| rewrite ?zh16_length_nat, ?zb8_length_nat; unfold id in D; BzdFast.cbn_lia].
  Ltac tr32 H MU WM D := unfold id in H; eapply u32arr_transport in H; [| exact MU| exact WM| rewrite ?zw32_length_nat; unfold id in D; BzdFast.cbn_lia].
  Ltac tr32n H MU WM := unfold id in H; eapply u32arr_transport in H; [| exact MU| exact WM| rewrite ?zw32_length_nat; BzdFast.cbn_lia].
  Ltac trc H MU WM D := unfold id in H; eapply rw_cells_transport in H; [| exact MU| exact WM| unfold id in D; BzdFast.cbn_lia].
  Ltac trcn H MU WM := unfold id in H; eapply rw_cells_transport in H; [| exact MU| exact WM| unfold FRM, FRMj; BzdFast.cbn_lia].
  Ltac trd H MU WM := unfold id in H; eapply drest_transport in H; [| exact MU| exact WM| BzdFast.cbn_lia| BzdFast.cbn_lia| BzdFast.cbn_lia].
  (* [comment removed for export] *)
  Ltac unhideF MU2 WM2 :=
    lazymatch goal with PAY' : id (bytes_at _ _ _ _), DSTA : id (u8arr _ _ _ _), CRC : id (u32arr _ _ 0x33178 _), RNA : id (u32arr _ _ 0x335b0 _),
                         GOT : id (rw_cells _ _ 0x320e8 _), SV' : id (rw_cells _ _ 0x32098 _), FR' : id (rw_cells _ _ (bv_unsigned _) _),
                         CF' : id (u32arr _ _ (_ + 1096)%Z _), SAV : id (rw_cells _ _ (_ + 64036)%Z _), DR' : id (drest_at _ _ _ _), TTA : id (u32arr _ _ (b_tt _) _),
                         D1 : id (_ <= b_src _ \/ _)%Z, D2 : id (_ <= b_dst _ \/ _)%Z, IA1 : id (_ + 64144 <= 65536 \/ _)%Z, D4a : id (_ + 64144 <= b_tt _ \/ _)%Z |- _ =>
      trb PAY' MU2 D1; tr8 DSTA MU2 WM2 D2; tr32 CRC MU2 WM2 IA1; tr32 RNA MU2 WM2 IA1; trc GOT MU2 WM2 IA1; trc SV' MU2 WM2 IA1;
      trcn FR' MU2 WM2; tr32n CF' MU2 WM2; trcn SAV MU2 WM2; trd DR' MU2 WM2; tr32 TTA MU2 WM2 D4a
    end.
  Ltac unhideS MU2 WM2 :=
    lazymatch goal with PAY' : id (bytes_at _ _ _ _), DSTA : id (u8arr _ _ (b_dst _) _), CRC : id (u32arr _ _ 0x33178 _), RNA : id (u32arr _ _ 0x335b0 _),
                         GOT : id (rw_cells _ _ 0x320e8 _), SV' : id (rw_cells _ _ 0x32098 _), FR' : id (rw_cells _ _ (bv_unsigned _) _),
                         CF' : id (u32arr _ _ (_ + 1096)%Z _), SAV : id (rw_cells _ _ (_ + 64036)%Z _), DR' : id (drest_at _ _ _ _),
                         L16A : id (u8arr _ _ (b_ll16 _) _), L4A : id (u8arr _ _ (b_ll4 _) _),
                         D1 : id (_ <= b_src _ \/ _)%Z, D2 : id (_ <= b_dst _ \/ _)%Z, IA1 : id (_ + 64144 <= 65536 \/ _)%Z,
                         D5a : id (_ + 64144 <= b_ll16 _ \/ _)%Z, D6a : id (_ + 64144 <= b_ll4 _ \/ _)%Z |- _ =>
      trb PAY' MU2 D1; tr8 DSTA MU2 WM2 D2; tr32 CRC MU2 WM2 IA1; tr32 RNA MU2 WM2 IA1; trc GOT MU2 WM2 IA1; trc SV' MU2 WM2 IA1;
      trcn FR' MU2 WM2; tr32n CF' MU2 WM2; trcn SAV MU2 WM2; trd DR' MU2 WM2; tr8 L16A MU2 WM2 D5a; tr8 L4A MU2 WM2 D6a
    end.

  (* [comment removed for export] *)
  Definition mkA (m : word -> option byte) (J : jk) (d : dst) (s : dstrm) (x9 x19 x24 : word) : act14 :=
    ACT (Z_to_bv 64 0x15c94) (z_spi z) (z_gp z) (z_tp z)
        (Z_to_bv 64 S) x9 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1)
        (Z_to_bv 64 2) (Z_to_bv 64 (-1)) x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10)
        (z_F z) (z_fc z) m cx (hd_of cx J d) (bs_of cx J s) lo (z_g1 z) (z_sv z) (z_payload z).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fcallF : forall f, FLK2 z f ->
    forall (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6 : word) (m : word -> option byte)
           (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
      FCH z m J d s dbytes rest ->
      munch (WBZ z) (z_m0 z) m -> wmono s0segs (z_m0 z) m -> mem_inv s0segs m ->
      dpureF cx (bs_of cx J s) (z_payload z) J d s -> d_state d = 14%Z ->
      (0 <= d_cccrc d < 4294967296)%Z -> (0 <= s_avail_out s <= dlen)%Z ->
      (b_len cx / 6 - d_blockNo d <= Z.of_nat f)%Z ->
      b_small cx = 0%Z ->
      evt s0segs (bzd_fpost z (K_call f d s))
          (MS (ZR z rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6) (z_F z) (Z_to_bv 64 0x15c8c) (z_fc z) None m (seg_rom s0segs)).
  Proof.
    intros f IHL. intros until rest. intros CH MU WM MI DP Hst Hcc Hav BND Hsm.
    cps_destruct CH as (DM & CRC & (DSTA & DL & Edb & Lout) & FR & ST).
    pose proof DM as DM'. unfold dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in *.
    zlin. unfold ZR. pose proof (NN0 Hsm) as TNZ. destruct LTT as [X|[LTT1 LTT2]]; [exfalso; exact (TNZ X)|]. clear LL16 LL4.
    zsepF TNZ. hide_disj.
    unfold WBZ, blk_ivls in MU. rewrite Hsm in MU. cbn [Z.eqb app] in MU. unfold DSTATE_SIZE in MU.
    assert (WBZE : WBZ z = ([(S, S + 64144); (STRM, STRM + 44); (DST, DST + dlen); (lo, usp); (b_tt cx, b_tt cx + 400000 * b_n cx)])%Z).
    { unfold WBZ, blk_ivls, DSTATE_SIZE. rewrite Hsm. reflexivity. }
    wstep. wstep.
    pose proof DEC as DEC'. unfold dec14F_spec in DEC'.
    cbn [di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in DEC'.
    eapply evt_cut; [ eapply (DEC' (mkA m J d s x9 x19 x24) J d s) | ].
    - unfold act_okF, mkA. cbn [a_cx a_lo a_sp a_payload]. unfold D14, CEILING. splits; try assumption; try lia.
    - exact DM.
    - exact DP.
    - exact Hst.
    - reflexivity.
    - exact Hav.
    - exact ST.
    - exact MI.
    - clear HD NBU CF MID SAV DR SM BLK PAY GOT SV RNA ST.
      intros ms' [PO PW]. unfold FPOST14 in PO. unfold mkA in PO, PW.
      cbn [a_ra a_sp a_gp a_tp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11 a_F a_fc a_m0 a_cx a_h0 a_b0 a_lo a_g1 a_sv a_payload
           di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in PO.
      pose proof (decompress_frame d s ltac:(rewrite Hst; unfold BZ_X_OUTPUT; lia) ltac:(rewrite Hst; lia)) as DF.
      unfold K_call.
      destruct (decompress d s) as [[rv2 d2] s2].
      cps_destruct DF as (Fout & Fav & Ftout & Fcc & Fbn & Fbn2 & Fst).
      cps_destruct PO as (q0 & q1 & q2 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m' & J' & -> & MUc & WMc & MIc & DMc & STc & DPc & _).
      unfold W14, blk_ivls, D14, DSTATE_SIZE in MUc. rewrite Hsm in MUc.
      cbn [Z.eqb app di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in MUc.
      unfold FIMG in CRC.
      transport14 m m' MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 89236)) with (Z_to_bv 64 89236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (IHL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' rv2 J' d2 s2 dbytes rest).
      + unfold FCH, FDEST, FIMG. rewrite Fout, Fav. splits; assumption.
      + rewrite WBZE. exact MU.
      + exact WM.
      + exact MIc.
      + unfold FFACTS. split; [apply (dpureF_rebase _ _ _ _ _ _ _ DPc)|]. split; [exact Fst|]. split; [rewrite Fcc; exact Hcc|].
        split; [rewrite Fav; exact Hav| exact PW].
      + intros Hst2. specialize (Fbn2 Hst2 ltac:(rewrite Hst; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fjoinF : forall f (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (rr : drest),
    FLK2 z f ->
    b_small cx = 0%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    (0 <= d_cccrc d < 4294967296)%Z -> (0 <= d_sbcrc d < 4294967296)%Z ->
    (b_len cx / 6 - d_blockNo d <= Z.of_nat f)%Z ->
    u32arr s0segs m1 (S + 1096) (zw32 (d_cftab d) 257) -> drest_at s0segs m1 S rr ->
    bytes_at s0segs m1 (b_src cx) (z_payload z) -> rw_cells s0segs m1 0x32098 [C8 (z_sv z)] ->
    rw_cells s0segs m1 uspi (FRM z) -> stk s0segs m1 lo uspi -> munch (WBZ z) (z_m0 z) m1 -> wmono s0segs (z_m0 z) m1 ->
    FKjoin (fmkc z m1 J d s f) (FROf (fmkc z m1 J d s f)).
  Proof.
    intros until rr. intros IHL Hsm DP Err Hcc Hsb BND CF DR PAY SV FR ST MU0 WM0.
    unfold FKjoin. ofmkc. intros rq0 rq1 rq2 rq3 rq4 rq5 rq6 rq7 rq8 rq9 rq10 rq11 rq12 rq13 rq14 rq15 rq16 rq17 rq18 m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest.
    intros DSm DE RO MU WM OJ.
    pose proof (cf_transport z ZOK (fmkc z m1 J d s f) m1 m _ eq_refl MU WM CF ltac:(rewrite zw32_length_nat; reflexivity)) as CF'.
    cps_destruct (fheld_transport z ZOK (fmkc z m1 J d s f) m1 m rr eq_refl MU WM DR PAY SV FR ST MU0 WM0)
      as (DR' & PAY' & SV' & FR' & ST' & MU' & WM'). clear CF DR PAY SV FR ST MU0 WM0 MU WM.
    cps_destruct RO as (SAV & TTA & CRC & RNA & GOT & MI). unfold FGOT in GOT. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    unfold ojoin in OJ. ofmkc. focbn_in OJ. cps_destruct OJ as (Rnu & Rcb & Rol & Roc & Rk0 & Rtp & Rrnd & Rav).
    pose proof (dpureF_set8 z J d s oc ol nu k0 tp rn rt cb out av tout tol toh DP ltac:(lia)) as DP'. cbv zeta in DP'.
    set (J' := jk_set_o J tol toh) in *. set (d' := set8 d oc ol nu k0 tp rn rt cb) in *. set (s' := smod s out av tout) in *.
    cbn [K_U Z.eqb]. unfold K_J.
    assert (Esnb : sv_nblock (d_sv d') = sv_nblock (d_sv d)) by reflexivity.
    assert (Enu : d_nused d' = nu) by reflexivity. assert (Eol : d_out_len d' = ol) by reflexivity.
    assert (Ecb : d_cbcrc d' = cb) by reflexivity. assert (Esb : forall v, d_sbcrc (d_set_cbcrc d' v) = d_sbcrc d) by reflexivity.
    assert (Ecc : forall v, d_cccrc (d_set_cbcrc d' v) = d_cccrc d) by reflexivity.
    rewrite Esnb, Enu, Eol, Ecb, Esb, Ecc.
    (* [comment removed for export] *)
    assert (DMj : dmem DI_S0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J' d' s')).
    { eapply dmemF_intro; cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0]; try exact HD; try exact NBU; try exact CF'; try exact MID; try exact SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      - subst J' d'. focbn. exact_cells SAV.
      - change (r_of d') with (r_of d). rewrite Err. exact DR'.
      - change (blk_of cx d') with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at].
        pose proof (proj1 (proj2 (proj2 DP))) as En. zlin.
        split; [exact Hsm| split; [exact TTA| rewrite zw32_length by lia; reflexivity]]. }
    (* [comment removed for export] *)
    assert (Rav2 : (0 <= av <= dlen)%Z).
    { subst s'. focbn_in Lout. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. lia. }
    unfold DSg in *. subst J' d' s'. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV.
    zlin. unfold ZR. pose proof (NN0 Hsm) as TNZ. destruct LTT as [X|[LTT1 LTT2]]; [exfalso; exact (TNZ X)|]. clear LL16 LL4.
    zsepF TNZ. hide_disj.
    pose proof (proj1 (proj2 (proj2 DP))) as En. pose proof (dpureF_snb _ _ _ _ _ _ DP) as Rsnb. pose proof (zw32_length (d_tt d) (100000 * b_n cx) ltac:(lia)) as TTL.
    unfold WBZ, blk_ivls in MU'. rewrite Hsm in MU'. cbn [Z.eqb app] in MU'. unfold DSTATE_SIZE in MU'.
    assert (WBZE : WBZ z = ([(S, S + 64144); (STRM, STRM + 44); (DST, DST + dlen); (lo, usp); (b_tt cx, b_tt cx + 400000 * b_n cx)])%Z).
    { unfold WBZ, blk_ivls, DSTATE_SIZE. rewrite Hsm. reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. notrap.
    wstep. wstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (nu =? sv_nblock (d_sv d) + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      wstep. wstep. rewrite <- WBZE in MU'.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| exact DMj| exact CRC| | exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    replace (nu =? sv_nblock (d_sv d) + 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
    wstep. wstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      replace (ol =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      wstep. wstep. rewrite <- WBZE in MU'.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| exact DMj| exact CRC| | exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    replace (ol =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv zeta.
    clear DMj.
    remember (crc_final cb) as crc' eqn:Ecrc. pose proof (crc_final_range cb ltac:(lia)) as Rcrc. rewrite <- Ecrc in Rcrc.
    hide PAY'. hide DSTA. hide CRC. hide RNA. hide GOT. hide SV'. hide FR'. hide CF'. hide SAV. hide DR'. hide TTA.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl ([(S + 8, S + 12); (S + 3184, S + 3192)])%Z mm) as MU2; pose proof (wmono_refl s0segs mm) as WM2 end.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (dpureF_verb _ _ _ _ _ _ DP). try rewrite (sx32_of_Z 0) by lia. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. if_false. wstep. if_true.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; C4 ?w; ?c6; ?c7] =>
        apply (C4_recell s0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4] w crc' [c6; c7]) in MID; [cbn [app] in MID| rewrite low32_lit, Ecrc; apply not_crc_final; lia] end end.
    (* [comment removed for export] *)
    wstep. wstep. wstep. if_cases K5; zify_cond K5.
    { (* [comment removed for export] *)
      assert (NE : crc' <> d_sbcrc d) by (intros E; apply K5; rewrite E; reflexivity).
      replace (crc' =? d_sbcrc d) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb].
      wstep. wstep. rewrite <- WBZE in MU'. unhideF MU2 WM2.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| | exact CRC| | apply dpureF_setcb; exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      - eapply dmemF_intro; focbn; [exact_cells HD| exact_cells NBU| exact CF'| exact_cells MID| exact_cells SAV| | exact_cells SM| | exact PAY'| exact GOT| exact SV'| exact RNA].
        + change (r_of (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc')) with (r_of d). rewrite Err. exact DR'.
        + change (blk_of cx (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc')) with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
          split; [exact Hsm| split; [exact TTA| exact TTL]].
      - unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    assert (EQ : crc' = d_sbcrc d).
    { pose proof (sx32_mod32 crc' ltac:(lia)) as X1. pose proof (sx32_mod32 (d_sbcrc d) ltac:(lia)) as X2. clear -K5 X1 X2. rewrite <- X1, <- X2. rewrite K5. reflexivity. }
    replace (crc' =? d_sbcrc d) with true by (symmetry; apply Z.eqb_eq; exact EQ). cbn [negb].
    remember (Z.lxor (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648) mod 4294967296) crc') as cc eqn:Ecc2.
    assert (Rcc2 : (0 <= cc < 4294967296)%Z).
    { subst cc. pose proof (Z.mod_pos_bound (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648)) 4294967296 ltac:(lia)).
      change 4294967296%Z with (2^32)%Z. apply lxor_lt_pow2; lia. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; C4 ?w; ?c7] =>
        apply (C4_recell s0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4; c5] w cc [c7]) in MID; [cbn [app] in MID| rewrite low32_lit, (low32_small cc) by lia; rewrite Ecc2; apply cccrc_step2; lia] end end.
    rewrite <- WBZE in MU'. unhideF MU2 WM2. clear MU2 WM2.
    eapply (bzd_fcallF f IHL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (jk_set_o J tol toh) _ (smod s out av tout) dbytes rest).
    - unfold FCH. split; [| split; [exact CRC| split; [| split; [exact FR'| exact ST']]]].
      + eapply dmemF_intro; focbn; [exact_cells HD| exact_cells NBU| exact CF'| exact_cells MID| exact_cells SAV| | exact_cells SM| | exact PAY'| exact GOT| exact SV'| exact RNA].
        * change (r_of (d_set_state (d_set_cccrc (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc') cc) BZ_X_BLKHDR_1)) with (r_of d). rewrite Err. exact DR'.
        * change (blk_of cx (d_set_state (d_set_cccrc (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc') cc) BZ_X_BLKHDR_1)) with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
          split; [exact Hsm| split; [exact TTA| exact TTL]].
      + unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - exact MU'.
    - exact WM'.
    - exact MI.
    - apply dpureF_setccs. exact DP'.
    - reflexivity.
    - focbn. exact Rcc2.
    - focbn. exact Rav2.
    - focbn. exact BND.
    - exact Hsm.
  Time Qed.
End BZD.
End ACeilS1.
End S0F_bzd_loop3.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s.S0F_bzd_loop2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s.S0F_bzd_loop3.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzdFast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLia.
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
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Hypothesis DEC : dec14F_spec DI_S0.
  Notation cx := (z_cx z).
  Hypothesis N1 : (1 <= b_n (z_cx z))%Z.
  Hypothesis NN0 : b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z.
  Hypothesis NN1 : b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z.
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zlin :=
    let CX := ident:(CX) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    cps_destruct CL as (LS1 & LS2 & LR1 & LR2 & LR3 & LR4 & LD1 & LD2 & LD3 & LD4 & LP1 & LP2 & _ & LSTRM & LSM & LN & LTT & LL16 & LL4);
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    pose proof crc_words_length as CWL; pose proof rnums_words_length as RNL.
  Ltac zsepF TNZ :=
    let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in lazymatch goal with CX : ctx_ok _ |- _ =>
      let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj, DSTATE_SIZE in CS; cbv zeta in CS;
      let D4 := fresh "D4" in
      let IA3 := fresh "IA3" in
      cps_destruct CS as (D1 & D2 & _ & D4 & _ & _ & _ & IA1 & IA2 & IA3 & _); pose proof (IA3 TNZ) as IA3'; clear IA3; unfold img_apart, IHI in IA1, IA2, IA3'; cps_destruct (D4 TNZ) as (D4a & D4b & D4c); clear D4 end.
  Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
  Ltac dlia := BzdFast.dlia_fast.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.
  Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
  (* [comment removed for export] *)
  Ltac djtac := cbn [disjoint_from]; unfold FRM, FRMj; simpl_sizes; repeat split; try exact I; dlia.
  Ltac subfp_tac := BzdFast.subfp_fast.
  Ltac transport14 m m' MUc WMc :=
    let W := lazymatch type of MUc with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at s0segs m ?A ?bs |- _ =>
        first [ apply (bytes_at_transport s0segs W m m' A bs) in H; [| exact MUc| djtac] | clear H ]
    | H : rw_cells s0segs m ?A ?cs |- _ =>
        first [ apply (rw_cells_transport s0segs W m m' A cs) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : u8arr s0segs m ?A ?bs |- _ =>
        first [ apply (u8arr_transport s0segs W m m' A bs) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : u32arr s0segs m ?A ?ws |- _ =>
        first [ apply (u32arr_transport s0segs W m m' A ws) in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : stk s0segs m ?lo' ?hi' |- _ =>
        first [ apply (stk_transport_disjoint s0segs W m m' lo' hi') in H; [| exact MUc| exact WMc| djtac] | clear H ]
    | H : munch ?Wq ?mq m |- _ =>
        apply (munch_trans Wq mq m m') in H; [| eapply (munch_weaken W Wq m m'); [subfp_tac| exact MUc]]
    | H : wmono s0segs ?mq m |- _ => apply (wmono_trans s0segs mq m m') in H; [| exact WMc]
    | H : mem_inv s0segs m |- _ => clear H
    end.

  Ltac zsepS NZ16 NZ4 :=
    let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in lazymatch goal with CX : ctx_ok _ |- _ =>
      let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj, DSTATE_SIZE in CS; cbv zeta in CS;
      let D5 := fresh "D5" in let D6 := fresh "D6" in let D7 := fresh "D7" in
      let IA4 := fresh "IA4" in let IA5 := fresh "IA5" in
      cps_destruct CS as (D1 & D2 & _ & _ & D5 & D6 & D7 & IA1 & IA2 & _ & IA4 & IA5); pose proof (IA4 NZ16) as IA4'; pose proof (IA5 NZ4) as IA5'; clear IA4 IA5; unfold img_apart, IHI in IA1, IA2, IA4', IA5'; cps_destruct (D5 NZ16) as (D5a & D5b & D5c); cps_destruct (D6 NZ4) as (D6a & D6b & D6c);
      pose proof (D7 NZ16 NZ4) as D7a; clear D5 D6 D7 end.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 fmkc] in *.
  (* [comment removed for export] *)
  Ltac trb H MU D := unfold id in H; eapply bytes_at_transport in H; [| exact MU| unfold id in D; BzdFast.cbn_lia].
  Ltac tr8 H MU WM D := unfold id in H; eapply u8arr_transport in H; [| exact MU| exact WM| rewrite ?zh16_length_nat, ?zb8_length_nat; unfold id in D; BzdFast.cbn_lia].
  Ltac tr32 H MU WM D := unfold id in H; eapply u32arr_transport in H; [| exact MU| exact WM| rewrite ?zw32_length_nat; unfold id in D; BzdFast.cbn_lia].
  Ltac tr32n H MU WM := unfold id in H; eapply u32arr_transport in H; [| exact MU| exact WM| rewrite ?zw32_length_nat; BzdFast.cbn_lia].
  Ltac trc H MU WM D := unfold id in H; eapply rw_cells_transport in H; [| exact MU| exact WM| unfold id in D; BzdFast.cbn_lia].
  Ltac trcn H MU WM := unfold id in H; eapply rw_cells_transport in H; [| exact MU| exact WM| unfold FRM, FRMj; BzdFast.cbn_lia].
  Ltac trd H MU WM := unfold id in H; eapply drest_transport in H; [| exact MU| exact WM| BzdFast.cbn_lia| BzdFast.cbn_lia| BzdFast.cbn_lia].
  (* [comment removed for export] *)
  Ltac unhideF MU2 WM2 :=
    lazymatch goal with PAY' : id (bytes_at _ _ _ _), DSTA : id (u8arr _ _ _ _), CRC : id (u32arr _ _ 0x33178 _), RNA : id (u32arr _ _ 0x335b0 _),
                         GOT : id (rw_cells _ _ 0x320e8 _), SV' : id (rw_cells _ _ 0x32098 _), FR' : id (rw_cells _ _ (bv_unsigned _) _),
                         CF' : id (u32arr _ _ (_ + 1096)%Z _), SAV : id (rw_cells _ _ (_ + 64036)%Z _), DR' : id (drest_at _ _ _ _), TTA : id (u32arr _ _ (b_tt _) _),
                         D1 : id (_ <= b_src _ \/ _)%Z, D2 : id (_ <= b_dst _ \/ _)%Z, IA1 : id (_ + 64144 <= 65536 \/ _)%Z, D4a : id (_ + 64144 <= b_tt _ \/ _)%Z |- _ =>
      trb PAY' MU2 D1; tr8 DSTA MU2 WM2 D2; tr32 CRC MU2 WM2 IA1; tr32 RNA MU2 WM2 IA1; trc GOT MU2 WM2 IA1; trc SV' MU2 WM2 IA1;
      trcn FR' MU2 WM2; tr32n CF' MU2 WM2; trcn SAV MU2 WM2; trd DR' MU2 WM2; tr32 TTA MU2 WM2 D4a
    end.
  Ltac unhideS MU2 WM2 :=
    lazymatch goal with PAY' : id (bytes_at _ _ _ _), DSTA : id (u8arr _ _ (b_dst _) _), CRC : id (u32arr _ _ 0x33178 _), RNA : id (u32arr _ _ 0x335b0 _),
                         GOT : id (rw_cells _ _ 0x320e8 _), SV' : id (rw_cells _ _ 0x32098 _), FR' : id (rw_cells _ _ (bv_unsigned _) _),
                         CF' : id (u32arr _ _ (_ + 1096)%Z _), SAV : id (rw_cells _ _ (_ + 64036)%Z _), DR' : id (drest_at _ _ _ _),
                         L16A : id (u8arr _ _ (b_ll16 _) _), L4A : id (u8arr _ _ (b_ll4 _) _),
                         D1 : id (_ <= b_src _ \/ _)%Z, D2 : id (_ <= b_dst _ \/ _)%Z, IA1 : id (_ + 64144 <= 65536 \/ _)%Z,
                         D5a : id (_ + 64144 <= b_ll16 _ \/ _)%Z, D6a : id (_ + 64144 <= b_ll4 _ \/ _)%Z |- _ =>
      trb PAY' MU2 D1; tr8 DSTA MU2 WM2 D2; tr32 CRC MU2 WM2 IA1; tr32 RNA MU2 WM2 IA1; trc GOT MU2 WM2 IA1; trc SV' MU2 WM2 IA1;
      trcn FR' MU2 WM2; tr32n CF' MU2 WM2; trcn SAV MU2 WM2; trd DR' MU2 WM2; tr8 L16A MU2 WM2 D5a; tr8 L4A MU2 WM2 D6a
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fcallS : forall f, FLK2 z f ->
    forall (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6 : word) (m : word -> option byte)
           (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
      FCH z m J d s dbytes rest ->
      munch (WBZ z) (z_m0 z) m -> wmono s0segs (z_m0 z) m -> mem_inv s0segs m ->
      dpureF cx (bs_of cx J s) (z_payload z) J d s -> d_state d = 14%Z ->
      (0 <= d_cccrc d < 4294967296)%Z -> (0 <= s_avail_out s <= dlen)%Z ->
      (b_len cx / 6 - d_blockNo d <= Z.of_nat f)%Z ->
      b_small cx = 1%Z ->
      evt s0segs (bzd_fpost z (K_call f d s))
          (MS (ZR z rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6) (z_F z) (Z_to_bv 64 0x15c8c) (z_fc z) None m (seg_rom s0segs)).
  Proof.
    intros f IHL. intros until rest. intros CH MU WM MI DP Hst Hcc Hav BND Hsm.
    cps_destruct CH as (DM & CRC & (DSTA & DL & Edb & Lout) & FR & ST).
    pose proof DM as DM'. unfold dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in *.
    zlin. unfold ZR. destruct (NN1 Hsm) as [NZ16 NZ4]. destruct LL16 as [X|[LA1 LA2]]; [exfalso; exact (NZ16 X)|]. destruct LL4 as [X|[LB1 LB2]]; [exfalso; exact (NZ4 X)|]. clear LTT.
    zsepS NZ16 NZ4. hide_disj.
    unfold WBZ, blk_ivls in MU. rewrite Hsm in MU. cbn [Z.eqb app] in MU. unfold DSTATE_SIZE in MU.
    assert (WBZE : WBZ z = ([(S, S + 64144); (STRM, STRM + 44); (DST, DST + dlen); (lo, usp); (b_ll16 cx, b_ll16 cx + 200000 * b_n cx); (b_ll4 cx, b_ll4 cx + 50000 * b_n cx)])%Z).
    { unfold WBZ, blk_ivls, DSTATE_SIZE. rewrite Hsm. reflexivity. }
    wstep. wstep.
    pose proof DEC as DEC'. unfold dec14F_spec in DEC'.
    cbn [di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in DEC'.
    eapply evt_cut; [ eapply (DEC' (mkA z m J d s x9 x19 x24) J d s) | ].
    - unfold act_okF, mkA. cbn [a_cx a_lo a_sp a_payload]. unfold D14, CEILING. splits; try assumption; try lia.
    - exact DM.
    - exact DP.
    - exact Hst.
    - reflexivity.
    - exact Hav.
    - exact ST.
    - exact MI.
    - clear HD NBU CF MID SAV DR SM BLK PAY GOT SV RNA ST.
      intros ms' [PO PW]. unfold FPOST14 in PO. unfold mkA in PO, PW.
      cbn [a_ra a_sp a_gp a_tp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11 a_F a_fc a_m0 a_cx a_h0 a_b0 a_lo a_g1 a_sv a_payload
           di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in PO.
      pose proof (decompress_frame d s ltac:(rewrite Hst; unfold BZ_X_OUTPUT; lia) ltac:(rewrite Hst; lia)) as DF.
      unfold K_call.
      destruct (decompress d s) as [[rv2 d2] s2].
      cps_destruct DF as (Fout & Fav & Ftout & Fcc & Fbn & Fbn2 & Fst).
      cps_destruct PO as (q0 & q1 & q2 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m' & J' & -> & MUc & WMc & MIc & DMc & STc & DPc & _).
      unfold W14, blk_ivls, D14, DSTATE_SIZE in MUc. rewrite Hsm in MUc.
      cbn [Z.eqb app di_segs di_dec di_got di_stderrp di_crc di_rnums DI_S0] in MUc.
      unfold FIMG in CRC.
      transport14 m m' MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 89236)) with (Z_to_bv 64 89236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (IHL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' rv2 J' d2 s2 dbytes rest).
      + unfold FCH, FDEST, FIMG. rewrite Fout, Fav. splits; assumption.
      + rewrite WBZE. exact MU.
      + exact WM.
      + exact MIc.
      + unfold FFACTS. split; [apply (dpureF_rebase _ _ _ _ _ _ _ DPc)|]. split; [exact Fst|]. split; [rewrite Fcc; exact Hcc|].
        split; [rewrite Fav; exact Hav| exact PW].
      + intros Hst2. specialize (Fbn2 Hst2 ltac:(rewrite Hst; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fjoinS : forall f (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (rr : drest),
    FLK2 z f ->
    b_small cx = 1%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    (0 <= d_cccrc d < 4294967296)%Z -> (0 <= d_sbcrc d < 4294967296)%Z ->
    (b_len cx / 6 - d_blockNo d <= Z.of_nat f)%Z ->
    drest_at s0segs m1 S rr ->
    bytes_at s0segs m1 (b_src cx) (z_payload z) -> rw_cells s0segs m1 0x32098 [C8 (z_sv z)] ->
    rw_cells s0segs m1 uspi (FRM z) -> stk s0segs m1 lo uspi -> munch (WBZ z) (z_m0 z) m1 -> wmono s0segs (z_m0 z) m1 ->
    FKjoin (fmkc z m1 J d s f) (FROs (fmkc z m1 J d s f)).
  Proof.
    intros until rr. intros IHL Hsm DP Err Hcc Hsb BND DR PAY SV FR ST MU0 WM0.
    unfold FKjoin. ofmkc. intros rq0 rq1 rq2 rq3 rq4 rq5 rq6 rq7 rq8 rq9 rq10 rq11 rq12 rq13 rq14 rq15 rq16 rq17 rq18 m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest.
    intros DSm DE RO MU WM OJ.
    cps_destruct (fheld_transport z ZOK (fmkc z m1 J d s f) m1 m rr eq_refl MU WM DR PAY SV FR ST MU0 WM0)
      as (DR' & PAY' & SV' & FR' & ST' & MU' & WM'). clear DR PAY SV FR ST MU0 WM0 MU WM.
    cps_destruct RO as (SAV & L16A & L4A & CF' & CRC & RNA & GOT & MI). unfold FGOT in GOT. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    unfold ojoin in OJ. ofmkc. focbn_in OJ. cps_destruct OJ as (Rnu & Rcb & Rol & Roc & Rk0 & Rtp & Rrnd & Rav).
    pose proof (dpureF_set8 z J d s oc ol nu k0 tp rn rt cb out av tout tol toh DP ltac:(lia)) as DP'. cbv zeta in DP'.
    set (J' := jk_set_o J tol toh) in *. set (d' := set8 d oc ol nu k0 tp rn rt cb) in *. set (s' := smod s out av tout) in *.
    cbn [K_U Z.eqb]. unfold K_J.
    assert (Esnb : sv_nblock (d_sv d') = sv_nblock (d_sv d)) by reflexivity.
    assert (Enu : d_nused d' = nu) by reflexivity. assert (Eol : d_out_len d' = ol) by reflexivity.
    assert (Ecb : d_cbcrc d' = cb) by reflexivity. assert (Esb : forall v, d_sbcrc (d_set_cbcrc d' v) = d_sbcrc d) by reflexivity.
    assert (Ecc : forall v, d_cccrc (d_set_cbcrc d' v) = d_cccrc d) by reflexivity.
    rewrite Esnb, Enu, Eol, Ecb, Esb, Ecc.
    (* [comment removed for export] *)
    assert (DMj : dmem DI_S0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J' d' s')).
    { eapply dmemF_intro; cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0]; try exact HD; try exact NBU; try exact CF'; try exact MID; try exact SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      - subst J' d'. focbn. exact_cells SAV.
      - change (r_of d') with (r_of d). rewrite Err. exact DR'.
      - change (blk_of cx d') with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at].
        pose proof (proj1 (proj2 (proj2 DP))) as En. zlin.
        split; [exact Hsm| split; [exact L16A| split; [rewrite zh16_length by lia; reflexivity| split; [exact L4A| rewrite zb8_length by lia; reflexivity]]]]. }
    (* [comment removed for export] *)
    assert (Rav2 : (0 <= av <= dlen)%Z).
    { subst s'. focbn_in Lout. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. lia. }
    unfold DSg in *. subst J' d' s'. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV.
    zlin. unfold ZR. destruct (NN1 Hsm) as [NZ16 NZ4]. destruct LL16 as [X|[LA1 LA2]]; [exfalso; exact (NZ16 X)|]. destruct LL4 as [X|[LB1 LB2]]; [exfalso; exact (NZ4 X)|]. clear LTT.
    zsepS NZ16 NZ4. hide_disj.
    pose proof (proj1 (proj2 (proj2 DP))) as En. pose proof (dpureF_snb _ _ _ _ _ _ DP) as Rsnb. pose proof (zh16_length (d_ll16 d) (200000 * b_n cx) ltac:(lia)) as L16L. pose proof (zb8_length (d_ll4 d) (50000 * b_n cx) ltac:(lia)) as L4L.
    unfold WBZ, blk_ivls in MU'. rewrite Hsm in MU'. cbn [Z.eqb app] in MU'. unfold DSTATE_SIZE in MU'.
    assert (WBZE : WBZ z = ([(S, S + 64144); (STRM, STRM + 44); (DST, DST + dlen); (lo, usp); (b_ll16 cx, b_ll16 cx + 200000 * b_n cx); (b_ll4 cx, b_ll4 cx + 50000 * b_n cx)])%Z).
    { unfold WBZ, blk_ivls, DSTATE_SIZE. rewrite Hsm. reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. notrap.
    wstep. wstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (nu =? sv_nblock (d_sv d) + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      wstep. wstep. rewrite <- WBZE in MU'.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| exact DMj| exact CRC| | exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    replace (nu =? sv_nblock (d_sv d) + 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
    wstep. wstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      replace (ol =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      wstep. wstep. rewrite <- WBZE in MU'.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| exact DMj| exact CRC| | exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    replace (ol =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv zeta.
    clear DMj.
    remember (crc_final cb) as crc' eqn:Ecrc. pose proof (crc_final_range cb ltac:(lia)) as Rcrc. rewrite <- Ecrc in Rcrc.
    hide PAY'. hide DSTA. hide CRC. hide RNA. hide GOT. hide SV'. hide FR'. hide CF'. hide SAV. hide DR'. hide L16A. hide L4A.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl ([(S + 8, S + 12); (S + 3184, S + 3192)])%Z mm) as MU2; pose proof (wmono_refl s0segs mm) as WM2 end.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (dpureF_verb _ _ _ _ _ _ DP). try rewrite (sx32_of_Z 0) by lia. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. if_false. wstep. if_true.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; C4 ?w; ?c6; ?c7] =>
        apply (C4_recell s0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4] w crc' [c6; c7]) in MID; [cbn [app] in MID| rewrite low32_lit, Ecrc; apply not_crc_final; lia] end end.
    (* [comment removed for export] *)
    wstep. wstep. wstep. if_cases K5; zify_cond K5.
    { (* [comment removed for export] *)
      assert (NE : crc' <> d_sbcrc d) by (intros E; apply K5; rewrite E; reflexivity).
      replace (crc' =? d_sbcrc d) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb].
      wstep. wstep. rewrite <- WBZE in MU'. unhideS MU2 WM2.
      eapply bzd_fepi; [exact ZOK| exact FR'| exact ST'| exact MU'| exact WM'| exact MI| | exact CRC| | apply dpureF_setcb; exact DP'| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
      - eapply dmemF_intro; focbn; [exact_cells HD| exact_cells NBU| exact CF'| exact_cells MID| exact_cells SAV| | exact_cells SM| | exact PAY'| exact GOT| exact SV'| exact RNA].
        + change (r_of (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc')) with (r_of d). rewrite Err. exact DR'.
        + change (blk_of cx (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc')) with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
          split; [exact Hsm| split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]].
      - unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    assert (EQ : crc' = d_sbcrc d).
    { pose proof (sx32_mod32 crc' ltac:(lia)) as X1. pose proof (sx32_mod32 (d_sbcrc d) ltac:(lia)) as X2. clear -K5 X1 X2. rewrite <- X1, <- X2. rewrite K5. reflexivity. }
    replace (crc' =? d_sbcrc d) with true by (symmetry; apply Z.eqb_eq; exact EQ). cbn [negb].
    remember (Z.lxor (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648) mod 4294967296) crc') as cc eqn:Ecc2.
    assert (Rcc2 : (0 <= cc < 4294967296)%Z).
    { subst cc. pose proof (Z.mod_pos_bound (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648)) 4294967296 ltac:(lia)).
      change 4294967296%Z with (2^32)%Z. apply lxor_lt_pow2; lia. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; C4 ?w; ?c7] =>
        apply (C4_recell s0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4; c5] w cc [c7]) in MID; [cbn [app] in MID| rewrite low32_lit, (low32_small cc) by lia; rewrite Ecc2; apply cccrc_step2; lia] end end.
    rewrite <- WBZE in MU'. unhideS MU2 WM2. clear MU2 WM2.
    eapply (bzd_fcallS f IHL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (jk_set_o J tol toh) _ (smod s out av tout) dbytes rest).
    - unfold FCH. split; [| split; [exact CRC| split; [| split; [exact FR'| exact ST']]]].
      + eapply dmemF_intro; focbn; [exact_cells HD| exact_cells NBU| exact CF'| exact_cells MID| exact_cells SAV| | exact_cells SM| | exact PAY'| exact GOT| exact SV'| exact RNA].
        * change (r_of (d_set_state (d_set_cccrc (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc') cc) BZ_X_BLKHDR_1)) with (r_of d). rewrite Err. exact DR'.
        * change (blk_of cx (d_set_state (d_set_cccrc (d_set_cbcrc (set8 d oc ol nu k0 tp rn rt cb) crc') cc) BZ_X_BLKHDR_1)) with (blk_of cx d). unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_S0].
          split; [exact Hsm| split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]].
      + unfold FDEST. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - exact MU'.
    - exact WM'.
    - exact MI.
    - apply dpureF_setccs. exact DP'.
    - reflexivity.
    - focbn. exact Rcc2.
    - focbn. exact Rav2.
    - focbn. exact BND.
    - exact Hsm.
  Time Qed.
End BZD.
End ACeilS1.
