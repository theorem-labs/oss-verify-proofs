(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AIcp0e6 ARtStmts ARtSscs ARt_fpo ARt_6n0 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module AFreeM0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AIcp0e6 ARtStmts ARtSscs ARt_fpo ARt_6n0 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@Tctx; @Tthr]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- tls_consts _ => unfold tls_consts
  | |- tls_dyn _ _ _ => unfold tls_dyn
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition free_mid0_stmt : Prop :=
  forall (rax gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fp tsd ctx thr top bot lo : Z) (ra0 v s5v s4v s3v s2v s1v j0 j3 : word) (pad j12 jb : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2128) -> lo <= fp - 2128 - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> fp mod 16 = 0 -> fp <= 2^47 ->
    4096 <= bv_unsigned ra0 -> bv_unsigned ra0 <> 0x58994 -> bv_unsigned v <= fp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)] -> ro_cells rsegs m 0x144660 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xb58bc [C4 (wz 30)] ->                                                     (* [comment removed for export] *)
    ro_cells rsegs m 0xa8b60 [C8 (wz 0x1466e8)] -> ro_cells rsegs m (0x1466e8 + 34) [C1 (Z_to_bv 8 1)] ->  (* [comment removed for export] *)
    ro_cells rsegs m 0xb5dc8 [C8 (wz 0)] ->                               (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    (thr + 4096 <= lo \/ fp - 2128 + 2^16 <= thr) ->
    rw_cells rsegs m (fp + -2128) [C8 j0; CB 8 j12; CB 2040 jb; C8 j3] ->                         (* [comment removed for export] *)
    rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->   (* [comment removed for export] *)
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jb1 jrest : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->                                 (* [comment removed for export] *)
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); C8 ra0]
         else rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->
        munch [(fp - 2128 - 224, fp - 2128); (fp + -2128, fp + -2128 + 32); (fp + -2128 + 2056, fp + -2128 + 2064);
               (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2128) ->
        evt rsegs Q (MS (mkR (wz 0x58a04) (wz (fp + -2128)) gp tp t0' t1' t2' (wz fp) (wz 0)
                         (wz 0xb1558) (wz 0) (wz 0) (wz 0) (wz (fp + -2128)) (wz 1) a6' a7'
                         (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz dealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR rax (wz (fp + -2128)) gp tp t0 t1 t2 (wz fp) (wz 0) (wz 0xb5dc0) a1 a2 a3 a4 a5 a6 a7
                     ra0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz free_mid_entry) fc None m (seg_rom rsegs)).


Theorem free_mid0_ok : free_mid0_stmt.
Proof.
  unfold free_mid0_stmt. intros until Q.
  intros MI ST LOLE CEIL TPE FPA FPH RA0 RANE VLE TOPR BOTR THC CINI CGPS CPS CMCS CFL CFU IAM TTB TDT TUNW TDJ OBJ SAV K.
  pose proof alloc_ceiling_val as CV.
  pose proof THC as THC'.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). aobj_lin_all.
  unfold free_mid_entry, dealloc_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, off_th_unwinding in *. aobj_lin_all. unfold TP in TPE. subst tp.
  rewrite unsigned_lit in Ttsd, Btp by lia. change (6192088 - 88) with 6192000 in Ttsd. lit_addrs.
  pose proof (munch_refl [(fp - 2128 - 224, fp - 2128); (fp + -2128, fp + -2128 + 32); (fp + -2128 + 2056, fp + -2128 + 2064); (thr + 3168, thr + 3168 + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  amz. rewrite ?(Z.shiftr_div_pow2 0 47), ?(Z.div_small 0 (2^47)) by lia. change (Z.shiftr 0 47) with 0.
  amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. change (Z.shiftr 0 32) with 0. rewrite ?(Z.shiftl_mul_pow2 0 3) by lia. change (Z.shiftl 0 3) with 0. zsimp.
  amz. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with H : rw_cells rsegs mc (fp + -2128) (?c0 :: C8 (Z_to_bv 64 0) :: ?rest) |- _ =>
      apply (rw_cells_C8_44x mc (fp + -2128) [c0] 0 rest) in H; [cbn [app] in H| plia] end end.
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  rewrite (land_ones64_l fp) by lia.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  pose proof SAV as SAV2. do 6 apply rw_cells_tl in SAV2. apply rw_cells_ro in SAV2.
  cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.add] in SAV2 || idtac.
  lazymatch type of SAV2 with ro_cells _ _ ?a _ => replace a with (fp - 16) in SAV2 by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  replace (fp + -2112) with (fp + -2128 + 16) in OBJ by lia.
  (* [comment removed for export] *)
  pose proof OBJ as OBJc.
  lazymatch type of OBJc with rw_cells _ ?mm ?a (?c0 :: ?c1 :: ?c2 :: ?rest) =>
    destruct (ARt_u2d.rw_cells_app_split mm a [c0] (c1 :: c2 :: rest) OBJc) as [O0 R1];
    destruct (ARt_u2d.rw_cells_app_split mm _ [c1] (c2 :: rest) R1) as [O8 R2];
    destruct (ARt_u2d.rw_cells_app_split mm _ [c2] rest R2) as [O12 R3];
    lazymatch rest with CB ?n ?l :: ?rest4 =>
      apply (rw_cells_split_CB rsegs mm _ [] n l rest4 [16; 2024]%nat) in R3; [| reflexivity]; cbn [app mk_CB_cells] in R3;
      lazymatch type of R3 with rw_cells _ _ _ (?c3 :: ?c4 :: ?rest5) =>
        destruct (ARt_u2d.rw_cells_app_split mm _ [c3] (c4 :: rest5) R3) as [O16x R4]; clear O16x;
        destruct (ARt_u2d.rw_cells_app_split mm _ [c4] rest5 R4) as [O32 R5]; clear R5 end end;
    clear OBJc R1 R2 O8 R3 R4 end.
  lazymatch type of O12 with rw_cells _ _ ?a _ => replace a with (fp + -2128 + 12) in O12 by (cbn; lia) end.
  lazymatch type of O32 with rw_cells _ _ ?a _ => replace a with (fp + -2128 + 32) in O32 by (cbn; lia) end.
  eapply evt_cut; [eapply unwind_ok|].
  all: try exact MI.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  all: try exact OBJ. all: try exact SAV2. all: try exact TTB. all: try exact TDT. all: try exact TUNW.
  all: try exact CINI. all: try exact CGPS. all: try exact CPS. all: try exact RA0. all: try exact RANE. all: try exact FPA.
  all: try reflexivity.
  all: try (unfold thread_cells, kHighMemBeg; rewrite unsigned_lit by lia; change (6192088 - 88) with 6192000; rebundle).
  all: try (rewrite ?unsigned_lit by lia; lia).
  clear OBJ TUNW SAV2.
  intros ms' PO. destruct_exs PO. (first [ dand8 PO as E MUc WMc MIc STc TUNW TFB OBJ2 | destruct PO as (E & MUc & WMc & MIc & STc & TUNW & TFB & OBJ2) ]). aobj_lin_all. subst ms'.
  rewrite ?unsigned_lit in MUc, STc by lia. unfold off_th_unwinding in MUc, TUNW.
  lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs mA m' MUc WMc end.
  clear MUc WMc MI. rename STc into ST. rename MIc into MI.
  replace (ret_pc (Z_to_bv 64 362992)) with (Z_to_bv 64 362992) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  amz. amz. amz. amz. (* [comment removed for export] *)
  do 11 amz. (* [comment removed for export] *)
  eapply K; try eassumption.
Qed.

End CEIL.
End AFreeM0.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@Tctx; @Tthr]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- tls_consts _ => unfold tls_consts
  | |- tls_dyn _ _ _ => unfold tls_dyn
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem free_mid_ok : free_mid_stmt.
Proof.
  unfold free_mid_stmt. intros until Q.
  intros MI ST LOLE CEIL TPE FPA FPH P0 PLO PHI RA0 RANE VLE TOPR BOTR THC CINI CGPS CPS CMCS CFL CFU IAM TTB TDT TUNW TDJ OBJ SAV K.
  pose proof alloc_ceiling_val as CV.
  pose proof THC as THC'.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
  unfold free_mid_entry, dealloc_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, off_th_unwinding in *. aobj_lin_all. unfold TP in TPE. subst tp.
  rewrite unsigned_lit in Ttsd, Btp by lia. change (6192088 - 88) with 6192000 in Ttsd. lit_addrs.
  remember (744904 + 8 * Z.shiftr p 32) as iam eqn:IAME.
  assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
  pose proof (munch_refl [(fp - 2128 - 224, fp - 2128); (fp + -2128, fp + -2128 + 32); (fp + -2128 + 2056, fp + -2128 + 2064); (thr + 3168, thr + 3168 + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  amz. rewrite (Z.shiftr_div_pow2 p 47), (Z.div_small p (2^47)) by lia.
  amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. rewrite (Z.shiftl_mul_pow2 (Z.shiftr p 32) 3) by lia. change (2 ^ 3) with 8.
  replace (744896 + Z.shiftr p 32 * 8) with (iam + -8) by lia.
  amz. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with H : rw_cells rsegs mc (fp + -2128) (?c0 :: C8 (Z_to_bv 64 0) :: ?rest) |- _ =>
      apply (rw_cells_C8_44x mc (fp + -2128) [c0] 0 rest) in H; [cbn [app] in H| plia] end end.
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  rewrite (land_ones64_l fp) by lia.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  pose proof SAV as SAV2. do 6 apply rw_cells_tl in SAV2. apply rw_cells_ro in SAV2.
  cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.add] in SAV2 || idtac.
  lazymatch type of SAV2 with ro_cells _ _ ?a _ => replace a with (fp - 16) in SAV2 by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  replace (fp + -2112) with (fp + -2128 + 16) in OBJ by lia.
  (* [comment removed for export] *)
  pose proof OBJ as OBJc.
  lazymatch type of OBJc with rw_cells _ ?mm ?a (?c0 :: ?c1 :: ?c2 :: ?rest) =>
    destruct (ARt_u2d.rw_cells_app_split mm a [c0] (c1 :: c2 :: rest) OBJc) as [O0 R1];
    destruct (ARt_u2d.rw_cells_app_split mm _ [c1] (c2 :: rest) R1) as [O8 R2];
    destruct (ARt_u2d.rw_cells_app_split mm _ [c2] rest R2) as [O12 R3];
    lazymatch rest with CB ?n ?l :: ?rest4 =>
      apply (rw_cells_split_CB rsegs mm _ [] n l rest4 [16; 2024]%nat) in R3; [| reflexivity]; cbn [app mk_CB_cells] in R3;
      lazymatch type of R3 with rw_cells _ _ _ (?c3 :: ?c4 :: ?rest5) =>
        destruct (ARt_u2d.rw_cells_app_split mm _ [c3] (c4 :: rest5) R3) as [O16x R4]; clear O16x;
        destruct (ARt_u2d.rw_cells_app_split mm _ [c4] rest5 R4) as [O32 R5]; clear R5 end end;
    clear OBJc R1 R2 O8 R3 R4 end.
  lazymatch type of O12 with rw_cells _ _ ?a _ => replace a with (fp + -2128 + 12) in O12 by (cbn; lia) end.
  lazymatch type of O32 with rw_cells _ _ ?a _ => replace a with (fp + -2128 + 32) in O32 by (cbn; lia) end.
  eapply evt_cut; [eapply unwind_ok|].
  all: try exact MI.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  all: try exact OBJ. all: try exact SAV2. all: try exact TTB. all: try exact TDT. all: try exact TUNW.
  all: try exact CINI. all: try exact CGPS. all: try exact CPS. all: try exact RA0. all: try exact RANE. all: try exact FPA.
  all: try reflexivity.
  all: try (unfold thread_cells, kHighMemBeg; rewrite unsigned_lit by lia; change (6192088 - 88) with 6192000; rebundle).
  all: try (rewrite ?unsigned_lit by lia; lia).
  clear OBJ TUNW SAV2.
  intros ms' PO. destruct_exs PO. (first [ dand8 PO as E MUc WMc MIc STc TUNW TFB OBJ2 | destruct PO as (E & MUc & WMc & MIc & STc & TUNW & TFB & OBJ2) ]). subst ms'.
  rewrite ?unsigned_lit in MUc, STc by lia. unfold off_th_unwinding in MUc, TUNW.
  lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs mA m' MUc WMc end.
  clear MUc WMc MI. rename STc into ST. rename MIc into MI.
  replace (ret_pc (Z_to_bv 64 362992)) with (Z_to_bv 64 362992) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  amz. amz. amz. amz. (* [comment removed for export] *)
  do 11 amz. (* [comment removed for export] *)
  eapply K; try eassumption.
Qed.

End CEIL.
