(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
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
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition realloc_icpt_entry : Z := 0x58fac.
Definition ia_entry : Z := 0x6467c.
Definition realloc_mid_entry : Z := 0x58ff0.

Section CEIL.
Context {Clg : Ceiling}.

Definition realloc_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
    let fp := bv_unsigned sp in
    mem_inv rsegs m -> stk rsegs m lo fp -> lo <= fp - 2144 - 16 -> alloc_ceiling <= lo ->
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    (forall (a1' : word) (junk pad1 pad2 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2144) [CB 8 pad2] ->
        rw_cells rsegs m' (fp + -2136) [CB 2064 junk] ->
        rw_cells rsegs m' (fp + -72) [CB 8 pad1] ->
        rw_cells rsegs m' (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        munch [(fp - 2144 - 16, fp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (fp - 2144) ->
        evt rsegs Q (MS (mkR (wz 0x58ff0) (wz (fp + -2144)) gp tp t0 t1 t2 sp a1 (wz 1) a1' a2 a3 a4 a5 a6 a7
                            a0 ra s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ia_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_icpt_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition realloc_mid_stmt : Prop :=
  forall (rax gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fp p n tsd ctx thr top bot lo : Z) (ra0 v s6v s5v s4v s3v s2v s1v rc rd : word) (junk pad1 pad2 : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2144) -> lo <= fp - 2144 - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> fp mod 16 = 0 -> fp <= 2^47 ->
    0 < p -> p < alloc_ceiling -> 1 <= n < 2^64 ->
    4096 <= bv_unsigned ra0 -> bv_unsigned ra0 <> 0x590e8 -> bv_unsigned v <= fp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    0x5e8328 <= tsd -> tsd + 8 <= 0x60a000 -> (ctx + 0x10000 <= thr \/ thr + 4096 <= ctx) ->      (* [comment removed for export] *)
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)] -> ro_cells rsegs m 0x144e60 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xb60bc [C4 (wz 30)] ->                                                     (* [comment removed for export] *)
    ro_cells rsegs m 0xa9180 [C8 (wz 0x146ee8)] -> ro_cells rsegs m (0x146ee8 + 34) [C1 (Z_to_bv 8 1)] ->  (* [comment removed for export] *)
    ro_cells rsegs m (0xb65c8 + 8 * Z.shiftr p 32) [C8 (wz 0)] ->                               (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + 2856) [C8 rc; C8 rd] ->                                             (* [comment removed for export] *)
    (thr + 4096 <= lo \/ fp + 2^16 <= thr) ->
    rw_cells rsegs m (fp + -2144) [CB 8 pad2] ->
    rw_cells rsegs m (fp + -2136) [CB 2064 junk] ->                                               (* [comment removed for export] *)
    rw_cells rsegs m (fp + -72) [CB 8 pad1] ->
    rw_cells rsegs m (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->   (* [comment removed for export] *)
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' rc' rd' : word) (jb1 jrest js0 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2136) [C8 (wz (fp + -2136 + 16))] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2136 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2136 + 16) [C8 (wz 0x590e8); C8 ra0]
         else rw_cells rsegs m' (fp + -2136 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2136 + 16) [C8 (wz 0x590e8); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2136 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (fp + -2136 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2136 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (fp + -72) [CB 8 pad1] ->
        rw_cells rsegs m' (fp + -2144) [CB 8 pad2] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (thr + 2856) [C8 rc'; C8 rd'] ->
        rw_cells rsegs m' (fp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->
        rw_cells rsegs m' (fp + -2160) [CB 8 js0; C8 (wz 0x59158)] ->                                   (* [comment removed for export] *)
        rw_cells rsegs m' (fp + -2208) [C8 (wz 1); C8 (wz 0x590e8); C8 (wz p); C8 (wz n); C8 (wz fp); C8 (wz 0x37ca0)] ->  (* [comment removed for export] *)
        munch [(fp - 2144 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1);
               (thr + 2856, thr + 2872)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2208) ->
        evt rsegs Q (MS (mkR (wz 0x37d1c) (wz (fp + -2208)) gp tp t0' t1' t2' (wz (fp + -2136)) (wz p)
                         (wz 0xb1d58) (wz n) (wz 8) (wz (fp + -2136)) (wz 1) (wz 1) a6' a7'
                         (wz 0xb1d58) (wz n) (wz 1) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz alloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR rax (wz (fp + -2144)) gp tp t0 t1 t2 (wz fp) (wz n) (wz 0xb65c0) a1 a2 a3 a4 a5 a6 a7
                     (wz p) ra0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz realloc_mid_entry) fc None m (seg_rom rsegs)).
End CEIL.

Section Pro.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.
  Hypothesis TSS : thread_stats_stmt.

  Theorem realloc_pro_ok : realloc_pro_stmt.
  Proof.
    pose proof alloc_ceiling_val as CE0. unfold realloc_pro_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL CINI K.
    unfold realloc_icpt_entry, ia_entry in *.
    assert (LO0 : 0 <= lo) by lia.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    carve_frame 64%nat ST.      (* [comment removed for export] *)
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    carve_frame 2064%nat ST.    (* [comment removed for export] *)
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    do 15 amz.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 9 amz. if_false. do 4 amz.
    release_frame FR3 ST (bv_unsigned sp + -2144).
    amz. if_false. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply K; try eassumption.
  Qed.

  #[using="TSS UNW"] Theorem realloc_mid_ok : realloc_mid_stmt.
  Proof.
    pose proof alloc_ceiling_val as CE0. unfold realloc_mid_stmt. intros until Q.
    intros MI ST LOLE CEIL TPE FPA FPH P0 PHI NR RA0 RANE VLE TOPR BOTR THC TSDL TSDH SEPTC CINI CGPS CPS CMCS CFL CFU IAM TTB TDT TUNW TST TDJ
           P2 OBJ P1 SAV K.
    pose proof alloc_ceiling_val as CV.
    pose proof THC as THC'.
    (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    aobj_lin1 Bthr. aobj_lin1 Bctx2.
    unfold realloc_mid_entry, alloc_entry, kHighMemBeg, off_th_unwinding, off_th_stats in *. unfold TP in TPE. subst tp.
    rewrite unsigned_lit in Ttsd, Btp by lia. change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
    remember (746952 + 8 * Z.shiftr p 32) as iam eqn:IAME.
    assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
    pose proof (munch_refl [(fp - 2144 - 224, fp); (thr + 3168, thr + 3168 + 1); (thr + 2856, thr + 2872)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (fp - 2144) with (fp + -2144) in ST by lia.
    (* [comment removed for export] *)
    change (CB 2064 junk) with (CB (2056 + 8) junk) in OBJ.
    apply (rwc_CB_split _ _ 2056 8 junk) in OBJ; [| destruct OBJ as [[[WFj _] _] _]; exact WFj].
    pose proof (rwc_tl _ _ _ _ OBJ) as OBT. apply rwc_hd in OBJ.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBT.
    lazymatch type of OBT with rw_cells _ _ ?a _ => replace a with (fp + -80) in OBT by lia end.
    set (jkA := firstn 2056 junk) in OBJ. clearbody jkA. set (jkB := skipn 2056 junk) in OBT. clearbody jkB.
    (* [comment removed for export] *)
    amz. rewrite (Z.shiftr_div_pow2 p 47), (Z.div_small p (2^47)) by lia.
    amz. if_false. (* [comment removed for export] *)
    amz. amz. amz. rewrite (Z.shiftl_mul_pow2 (Z.shiftr p 32) 3) by lia. change (2 ^ 3) with 8.
    replace (746944 + Z.shiftr p 32 * 8) with (iam + -8) by lia.
    amz. (* [comment removed for export] *)
    amz. amz. if_true. (* [comment removed for export] *)
    (* [comment removed for export] *)
    amz. amz. amz. amz. amz. amz. amz.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with H : rw_cells rsegs mc (fp + -2136) [C8 ?w; C8 _; CB 2040 ?j] |- _ =>
        apply (obj_split_80h mc (fp + -2136) w j) in H; [| destruct H as [[WF _] _]; cbn in WF; tauto] end end.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    rewrite (land_ones64_l' fp) by lia.
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
    pose proof SAV as SAV2. do 6 apply rwc_tl in SAV2. apply rwc_ro in SAV2.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.add] in SAV2 || idtac.
    lazymatch type of SAV2 with ro_cells _ _ ?a _ => replace a with (fp - 16) in SAV2 by lia end.
    match goal with T : rw_cells rsegs _ (fp + -80) [C8 _] |- _ =>
      match goal with H : rw_cells rsegs _ (fp + -2136) [C8 _; C4 _; C4 _; CB 2040 _] |- _ => obj_join T H end end.
    match goal with H : rw_cells rsegs _ (fp + -2136) [C8 _; C4 _; C4 _; CB 2040 _; C8 _] |- _ => rename H into OB end.
    replace (fp + -2120) with (fp + -2136 + 16) in OB by lia.
    (* [comment removed for export] *)
    pose proof OB as OBc.
    pose proof (rwc_hd _ _ _ _ OBc) as O0.
    apply rwc_tl in OBc. apply rwc_tl in OBc. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBc.
    pose proof (rwc_hd _ _ _ _ OBc) as O12. apply rwc_tl in OBc. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBc.
    lazymatch type of OBc with rw_cells _ _ _ (CB 2040 ?j :: _) =>
      apply (rwc_CB_split _ _ 16 2024 j) in OBc; [| destruct OBc as [[[WFj _] _] _]; exact WFj] end.
    apply rwc_tl in OBc. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBc.
    pose proof (rwc_hd _ _ _ _ OBc) as O32. clear OBc.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_OB); callx UNW cleaning (unfold off_th_unwinding in *).
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    match goal with H : context [unwind_depth2 _ _ _] |- _ => rename H into DEP end.
    destruct (unwind_depth2 top bot fp) eqn:DD; destruct DEP as [D8 D16].
    (* [comment removed for export] *)
    all: do 5 amz. (* [comment removed for export] *)
    all: carve_frame 16%nat ST.
    all: do 4 amz. (* [comment removed for export] *)
    all: amz; br_not_taken. (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    all: amz; br_taken. (* [comment removed for export] *)
    all: do 5 amz. (* [comment removed for export] *)
    all: carve_frame 48%nat ST.
    all: do 7 amz. (* [comment removed for export] *)
    all: amz; br_not_taken. (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    all: amz; br_not_taken. (* [comment removed for export] *)
    all: amz. all: amz. all: amz. (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    all: callx TSS cleaning (unfold off_th_stats in *).
    all: match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    all: do 6 amz. (* [comment removed for export] *)
    all: do 7 amz. (* [comment removed for export] *)
    all: lazymatch type of O12 with rw_cells _ _ ?a _ => replace a with (fp + -2136 + 12) in O12 by (cbn; lia) end.
    all: lazymatch type of O32 with rw_cells _ _ ?a _ => replace a with (fp + -2136 + 32) in O32 by (cbn; lia) end.
    all: match goal with H : munch _ ?m0 _ |- _ => is_var m0; rename H into MUf; match goal with W : wmono rsegs m0 _ |- _ => rename W into WMf end end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with H : mem_inv rsegs mc |- _ => rename H into MIf end end.
    all: eapply K; try eassumption.
    all: try (split; [assumption| eassumption]).
    Unshelve. all: try exact []; try exact (Z_to_bv 64 0).
  Qed.
End Pro.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
