(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac AMallocI.

Module ACallocI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@CFL; @CFU; @CGPS; @CINI; @CMCS; @CPS; @FR1; @Tctx; @Tini; @Tkey; @Tthr; @Ttsd]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition calloc_icpt_entry : Z := 0x58d74.

Section CEIL.
Context {Clg : Ceiling}.

Definition calloc_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cnt sz tsd ctx thr top bot lo : Z) (Q : machine_state -> Prop),
    let fp := bv_unsigned sp in
    mem_inv rsegs m -> stk rsegs m lo fp -> lo <= fp - 2144 - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> fp mod 16 = 0 -> fp <= 2^47 -> a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz < 2^64 ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> 0x58e48 -> bv_unsigned s0 <= fp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)] -> ro_cells rsegs m 0x144e60 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xb60bc [C4 (wz 30)] ->                                                     (* [comment removed for export] *)
    ro_cells rsegs m 0xa9180 [C8 (wz 0x146ee8)] -> ro_cells rsegs m (0x146ee8 + 34) [C1 (Z_to_bv 8 1)] ->  (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    (thr + 4096 <= lo \/ fp + 2^16 <= thr) ->
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad1 pad2 jb1 jrest js0 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2136) [C8 (wz (fp + -2136 + 16))] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2136 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2136 + 16) [C8 (wz 0x58e48); C8 ra]
         else rw_cells rsegs m' (fp + -2136 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2136 + 16) [C8 (wz 0x58e48); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2136 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (fp + -2136 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2136 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (fp + -72) [CB 8 pad1] ->
        rw_cells rsegs m' (fp + -2144) [CB 8 pad2] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' (fp + -2192) [CB 8 js0; C8 (wz 0x58e48); C8 a0; C8 a1; C8 sp; C8 (wz 0x58eb8)] ->
        munch [(fp - 2144 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2192) ->
        evt rsegs Q (MS (mkR (wz 0x37b78) (wz (fp + -2192)) gp tp t0' t1' t2' (wz (cnt * sz)) (wz (fp + -2136))
                         (wz 0xb1d58) (wz (cnt * sz)) (wz 8) (wz (fp + -2136)) (wz 1) (wz 0) a6' a7'
                         (wz 0xb1d58) (wz 1) (wz 1) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz alloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz calloc_icpt_entry) fc None m (seg_rom rsegs)).
End CEIL.

Section Pro.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.

  #[using="UNW"] Theorem calloc_pro_ok : calloc_pro_stmt.
  Proof.
    pose proof alloc_ceiling_val as CE0. unfold calloc_pro_stmt. intros until Q. cbv zeta.
    intros MI ST LOLE CEIL TPE FPA FPH A0 A1 CR SR PR RA0 RANE VLE TOPR BOTR THC CINI CGPS CPS CMCS CFL CFU TTB TDT TUNW TDJ K.
    pose proof alloc_ceiling_val as CV.
    pose proof THC as THC'.
    (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    unfold calloc_icpt_entry, alloc_entry, kHighMemBeg, off_th_unwinding in *. unfold TP in TPE. subst tp a0 a1.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    rewrite unsigned_lit in Ttsd, Btp by lia. change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 224, bv_unsigned sp); (thr + 3168, thr + 3168 + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    carve_frame 64%nat ST.      (* [comment removed for export] *)
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    carve_frame 2056%nat ST.    (* [comment removed for export] *)
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    do 15 amz.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 9 amz. if_false. do 4 amz.
    release_frame FR4 ST (bv_unsigned sp + -2144).
    amz. if_false. (* [comment removed for export] *)
    (* [comment removed for export] *)
    amz. amz. amz. amz. amz.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with H : rw_cells rsegs mc (bv_unsigned sp + -2136) [C8 ?w; C8 _; CB 2040 ?j] |- _ =>
        apply (obj_split_80h mc (bv_unsigned sp + -2136) w j) in H; [| destruct H as [[WF _] _]; cbn in WF; tauto] end end.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    rewrite (land_ones64_l' (bv_unsigned sp)) by lia.
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
    pose proof FR as SAV2. do 6 apply rwc_tl in SAV2. apply rwc_ro in SAV2.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.add] in SAV2 || idtac.
    lazymatch type of SAV2 with ro_cells _ _ ?a _ => replace a with (bv_unsigned sp - 16) in SAV2 by lia end.
    replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) in FR2 by lia.
    obj_join FR1 FR2. rename FR2 into FR1.
    (* [comment removed for export] *)
    pose proof FR1 as OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O0.
    apply rwc_tl in OBJ. apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O12. apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    lazymatch type of OBJ with rw_cells _ _ _ (CB 2040 ?j :: _) =>
      apply (rwc_CB_split _ _ 16 2024 j) in OBJ; [| destruct OBJ as [[[WFj _] _] _]; exact WFj] end.
    apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O32. clear OBJ.
    replace (bv_unsigned sp + -2136 + 8 + 4) with (bv_unsigned sp + -2124) in O12 by lia.
    replace (bv_unsigned sp + -2136 + 8 + 4 + 4 + 16) with (bv_unsigned sp + -2104) in O32 by lia.
    callx UNW cleaning (unfold off_th_unwinding in *).
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    match goal with H : context [unwind_depth2 _ _ _] |- _ => rename H into DEP end.
    destruct (unwind_depth2 top bot (bv_unsigned sp)) eqn:DD; destruct DEP as [D8 D16].
    (* [comment removed for export] *)
    all: do 5 amz. (* [comment removed for export] *)
    all: carve_frame 48%nat ST.
    all: do 6 amz. (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: amz; if_cases Kz; zify_cond Kz;
         [ | amz; replace (Z.shiftr (sz * cnt) 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia);
             amz; br_not_taken ].
    all: do 11 amz.
    all: replace (sz * cnt) with (cnt * sz) by lia. (* [comment removed for export] *)
    all: lazymatch type of O12 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2136 + 12) in O12 by (cbn; lia) end.
    all: lazymatch type of O32 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2136 + 32) in O32 by (cbn; lia) end.
    all: match goal with H : munch _ ?m0 _ |- _ => is_var m0; rename H into MUf; match goal with W : wmono rsegs m0 _ |- _ => rename W into WMf end end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with H : mem_inv rsegs mc |- _ => rename H into MIf end end.
    all: eapply K; try eassumption.
    all: split; [assumption| eassumption].
    Unshelve. all: try exact [].
  Qed.
End Pro.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End ACallocI.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition calloc_epi_entry : Z := 0x37b78.

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Definition calloc_tail_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 c8 c16 c24 c32 : word) (cs16 : list cell) (j32 pad1 pad2 js0 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2192) -> lo <= fp - 2192 -> 0 <= fp - 2192 -> fp <= 2^47 ->
    sp = wz (fp + -2192) ->
    rw_cells rsegs m (fp + -2192) [CB 8 js0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x58eb8)] ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x37bcc) fc None m (seg_rom rsegs)).

Theorem calloc_tail_ok : calloc_tail_stmt.
Proof.
  unfold calloc_tail_stmt. intros until Q. intros MI ST LOLE F0 F1 SP C48 P2 O0 O8 O12 O16 S16 O32 O2056 P1 SAV K.
  subst sp.
  pose proof (munch_refl [(fp - 2192, fp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  replace (fp - 2192) with (fp + -2192) in ST by lia.
  do 6 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  do 11 amz. (* [comment removed for export] *)
  release_frame C48 ST (fp + -2144).
  release_frame P2 ST (fp + -2136).
  release_frame O0 ST (fp + -2128).
  release_frame O8 ST (fp + -2124).
  release_frame O12 ST (fp + -2120).
  eapply stk_release in O16; [| exact ST| lia]. clear ST. rename O16 into ST. rewrite S16 in ST.
  lazymatch type of ST with stk _ _ _ ?h => replace h with (fp + -2104) in ST by (cbn; lia) end.
  release_frame O32 ST (fp + -80).
  release_frame O2056 ST (fp + -72).
  release_frame P1 ST (fp + -64).
  release_frame SAV ST fp.
  apply K. exact ST.
Qed.

(* [comment removed for export] *)
Definition calloc_epi0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 e0 c8 c16 c24 c32 : word) (cs16 : list cell) (j32 pad1 pad2 js0 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2192) -> lo <= fp - 2192 - 16 -> alloc_ceiling <= lo -> fp <= 2^47 ->
    sp = wz (fp + -2192) -> a0 = wz 0 ->
    164 <= bv_unsigned tp -> bv_unsigned tp <= kHighMemBeg ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 e0] ->
    rw_cells rsegs m (fp + -2192) [CB 8 js0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x58eb8)] ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (forall (t0' t1' t2' a1' : word) (m' : word -> option byte),
        stk rsegs m' lo fp -> mem_inv rsegs m' ->
        munch [(fp - 2208, fp - 2192); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' -> wmono rsegs m m' ->
        rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (wz 12)] ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz calloc_epi_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition calloc_epiS_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo r sb : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 c8 c16 c24 c32 : word) (cs16 : list cell) (j32 pad1 pad2 js0 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2192) -> lo <= fp - 2192 -> 0 <= fp - 2192 -> fp <= 2^47 ->
    sp = wz (fp + -2192) -> a0 = wz r -> 0 < r < 2^64 -> s2 = wz 0xb1d58 -> s3 = wz 1 ->
    0 <= sb -> sb + 2^37 < 2^64 -> (r < sb \/ sb + 2^37 <= r) ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->                                          (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2192) [CB 8 js0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x58eb8)] ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (forall (a1' : word),
        stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v (wz r) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz calloc_epi_entry) fc None m (seg_rom rsegs)).

#[using="Clg"] Theorem calloc_epiS_ok : calloc_epiS_stmt.
Proof.
  unfold calloc_epiS_stmt. intros until Q. intros MI ST LOLE F0 F1 SP A0 RR S2 S3 SB0 SB1 NP CSB C48 P2 O0 O8 O12 O16 S16 O32 O2056 P1 SAV K.
  pose proof alloc_ceiling_val as CV0. unfold calloc_epi_entry in *. subst sp a0 s2 s3.
  pose proof (munch_refl [(fp - 2192, fp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    eapply calloc_tail_ok; [ exact MI | exact ST | lia | lia | lia | reflexivity | try eassumption .. | ].
    all: try eassumption. intros ST'. eapply K; exact ST'.
  - amz. amz. (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    eapply calloc_tail_ok; [ exact MI | exact ST | lia | lia | lia | reflexivity | try eassumption .. | ].
    all: try eassumption. intros ST'. eapply K; exact ST'.
Qed.

(* [comment removed for export] *)
Definition calloc_epiP_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo r sb n : Z)
         (w0 w8 w12 w2056 s6v s5v s4v s3v s2v s1v s0v ra0 c8 c16 c24 c32 : word) (cs16 : list cell) (j32 pad1 pad2 js0 uj : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2192) -> lo <= fp - 2192 -> 0 <= fp - 2192 -> fp <= 2^47 ->
    sp = wz (fp + -2192) -> a0 = wz r -> 0 < r -> s0 = wz n -> 0 <= n -> r + n < 2^64 -> s2 = wz 0xb1d58 -> s3 = wz 1 ->
    0 <= sb -> sb + 2^37 < 2^64 -> sb <= r < sb + 2^37 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->                                          (* [comment removed for export] *)
    ro_cells rsegs m 0xa91b0 [C8 (wz 0xab038)] -> ro_cells rsegs m 0xab038 [C8 (wz 0xa25c8)] ->   (* [comment removed for export] *)
    rw_cells rsegs m r [CB (Z.to_nat n) uj] ->                                         (* [comment removed for export] *)
    (fp <= r \/ r + n <= lo) ->                                                        (* [comment removed for export] *)
    rw_cells rsegs m (fp + -2192) [CB 8 js0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (wz 0x58eb8)] ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [C8 w0] -> rw_cells rsegs m (fp + -2128) [C4 w8] -> rw_cells rsegs m (fp + -2124) [C4 w12] ->
    rw_cells rsegs m (fp + -2120) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2104) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -80) [C8 w2056] -> rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        stk rsegs m' lo fp -> mem_inv rsegs m' -> munch [(r, r + n)] m m' -> wmono rsegs m m' ->
        rw_cells rsegs m' r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0' t1' t2' s0v s1v (wz r) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz calloc_epi_entry) fc None m (seg_rom rsegs)).

#[using="Clg"] Theorem calloc_epiP_ok : calloc_epiP_stmt.
Proof.
  unfold calloc_epiP_stmt. intros until Q.
  intros MI ST LOLE F0 F1 SP A0 RR S0 N0 RN S2 S3 SB0 SB1 PRIM CSB CGOT CRM UB APART C48 P2 O0 O8 O12 O16 S16 O32 O2056 P1 SAV K.
  pose proof alloc_ceiling_val as CV0. unfold calloc_epi_entry in *. subst sp a0 s0 s2 s3.
  pose proof (munch_refl [(r, r + n)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callx (memset_spec_z _ _ _ _ _ _ _ _ _ r 0 n).
  match goal with H : stk _ _ _ _ |- _ => rename H into ST' end.
  amz. amz. (* [comment removed for export] *)
  match goal with H : munch _ _ ?m1, W : wmono rsegs _ ?m1, M : mem_inv rsegs ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    rename H into MUf; rename W into WMf; rename M into MIf end.
  eapply calloc_tail_ok; [ exact MIf | exact ST' | lia | lia | lia | reflexivity | try eassumption .. | ].
  all: try eassumption.
  intros ST''. eapply K; try eassumption.
Qed.

End CEIL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
