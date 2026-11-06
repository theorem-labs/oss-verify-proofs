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
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs.

Module ASmStmt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AIcpm9j ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Open Scope bv_scope.
Local Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CEIL.
Context {Clg : Ceiling}.
Definition smallocG_stmt (k : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (tsd ctx thr tlsb tlse dtls dtvbeg fs h sz lo : Z) (oldsh : list byte),
    let pos := h mod fslots k in
    let ff := fframe_addr fs k pos in
    let fl := fflag_addr fs k pos in
    let nsh := (if Z.leb k 6 then fsize k / 8 else sz / 8) in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> a0 = wz sz -> (k = 7 -> sz mod 8 = 0 /\ 8 <= sz <= fsize 7) ->
    tls_consts m -> tls_dyn m dtls dtvbeg -> thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m (thr + 48) [C8 (wz tlsb); C8 (wz tlse)] ->
    poison_consts m ->                                                    (* [comment removed for export] *)
    fs_hdr m fs ->
    0 <= h < 2^64 ->   (* [comment removed for export] *)
    bytes_at rsegs m (fs + 8 * k) (le8 (wz h)) ->                         (* [comment removed for export] *)
    bytes_at rsegs m fl [Z_to_bv 8 0] ->                                  (* [comment removed for export] *)
    mapped m fs kFakeStackBytes ->                                        (* [comment removed for export] *)
    rw_cells rsegs m (sh ff) [CB (Z.to_nat nsh) oldsh] ->                 (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (smalloc_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs h sz lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz (smalloc_entry k)) fc None m (seg_rom rsegs)).
Definition smallocG0_stmt : Prop := smallocG_stmt 0.
Definition smallocG1_stmt : Prop := smallocG_stmt 1.
Definition smallocG7_stmt : Prop := smallocG_stmt 7.
End CEIL.
End ASmStmt.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_fpo ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt2_lib.

Module ARt2_tls.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j AIcp0e6 ARtStmts ARtSscs ARt_fpo AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
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

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem tlsfs_ok : tlsfs_stmt.
Proof.
  unfold tlsfs_stmt. intros until lo. intros MI ST LOLE CEIL TPE A0 TC TD THC TLS RA. pose proof alloc_ceiling_val as CV.
  unfold tlsfs_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (first [ dand10 TC as Cini Creal Cdesc Cdtv Cdtv1 Cflg Cflgb Cverb Cverbv Coff | destruct TC as (Cini & Creal & Cdesc & Cdtv & Cdtv1 & Cflg & Cflgb & Cverb & Cverbv & Coff) ]).
  (first [ dand6 TD as Cdtls Cbeg NZ BR D0 D1 | destruct TD as (Cdtls & Cbeg & NZ & BR & D0 & D1) ]).
  unfold TP in *. subst tp a0.
  pose proof THC as THC'.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
  unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. rewrite unsigned_lit in Ttsd, Btp by lia.
  change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
  zstep. (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 7 zstep. (* [comment removed for export] *)
  callz tryinit_spec.
  1:{ exact Cini. }
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ exact MI. }
  rename POST into ST.
  (* [comment removed for export] *)
  run_to 0x62600.
  callz get_thread_ok.
  1:{ exact MI0. }
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ unfold thread_cells, kHighMemBeg; rewrite unsigned_lit by lia; change (6194136 - 88) with 6194048.
      split; [exact Tini | split; [exact Tkey | split; [exact Ttsd | split; [exact Tctx | split; [exact Tthr | plia]]]]]. }
  1:{ reflexivity. }
  rename POST into ST.
  run_to 0x6fe28. (* [comment removed for export] *)
  carve_frame 144%nat ST.
  run_to 0x70008. (* [comment removed for export] *)
  do 15 zstep. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32).
  do 7 zstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

End CEIL.
End ARt2_tls.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ARt2_tls OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module ARt2ewq.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt2_lib AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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

Theorem sfree7_ok : sfree7_stmt.
Proof.
  unfold sfree7_stmt. intros until oldsh.
  intros MI ST LOLE CEIL A0 A1 SZ8 SZB FF8 FF0 FF1 FL0 FL1 PC SFP CF SHC DJ1 DJ2 RA.
  pose proof alloc_ceiling_val as CV.
  change (fsize 7) with 8192 in *. unfold saved_flag_ptr in SFP. change (fsize 7) with 8192 in SFP.
  replace (ff + 8192 - 8) with (ff + 8184) in SFP by lia.
  set (n8 := sz / 8) in *. assert (N8 : sz = 8 * n8) by (subst n8; rewrite (Z_div_mod_eq_full sz 8) at 1; rewrite SZ8; lia).
  clearbody n8.
  set (q := ff / 8) in *. assert (FQ : ff = 8 * q) by (subst q; rewrite (Z_div_mod_eq_full ff 8) at 1; rewrite FF8; lia).
  clearbody q.
  assert (SHF : sh ff = q + 2147450880).
  { unfold sh, kShadowOffset. rewrite FQ, Z.mul_comm, Z.div_mul by lia. reflexivity. }
  rewrite SHF in *.
  pose proof PC as PC'.
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]).
  unfold sfree7_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kHighMemEnd, kShadowOffset in *. aobj_lin_all. subst a0 a1. lit_addrs.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (fl, fl + 1); (q + 2147450880, q + 2147450880 + n8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 6 amz. (* [comment removed for export] *)
  amz. amz. replace (ff + 8192) with (ff + 8184 + 8) by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  callz m2s_fs_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundle. }
  1:{ reflexivity. }
  1:{ plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  do 7 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  eapply evt_cut; [eapply poison_ok|].
  1:{ exact MI. }
  1:{ exact ST. }
  1:{ lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ exact FF8. }
  1:{ exact SZ8. }
  1:{ lia. }
  1:{ unfold kHighMemBeg; plia. }
  1:{ lia. }
  1:{ lia. }
  1:{ intros X; discriminate X. }
  1:{ rebundle. }
  1:{ rewrite SHF. replace (sz / 8) with n8 by (rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity). exact SHC. }
  1:{ exact RA. }
  clear SHC.
  intros ms' PO. destruct_exs PO. (first [ dand6 PO as E MUc WMc MIc STc SHZ | destruct PO as (E & MUc & WMc & MIc & STc & SHZ) ]). subst ms'.
  replace (sz / 8) with n8 in MUc, SHZ by (rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs mA m' MUc WMc end.
  apply evt_done. unfold sfree7_post.
  replace (sz / 8) with n8 by (rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
  split; [reflexivity|].
  split; [rewrite SHF; exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|].
  split. { eapply (rw_cells_hd _ _ (C1 _)). exact CF. }
  exact SHZ.
Qed.

End CEIL.
End ARt2ewq.

Module ASm_0x1.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ARt2_tls OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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

Theorem smallocG1_ok : smallocG1_stmt.
Proof.
  unfold smallocG1_stmt, smallocG_stmt. intros until oldsh. cbv zeta.
  intros MI ST LOLE CEIL TPE A0 K7 TC TD THC TLS PC FSH HR HINT FLAG MAP SHC RA. clear K7.
  pose proof alloc_ceiling_val as CV.
  change (fslots 1) with 8192 in *. change (fsize 1) with 128 in *.
  replace (if 1 <=? 6 then 128 / 8 else sz / 8) with 16 in * by reflexivity.
  set (pos := h mod 8192) in *.
  assert (POS : 0 <= pos < 8192) by (subst pos; apply Z.mod_pos_bound; lia).
  assert (HP : pos = h mod 8192) by reflexivity.
  set (ff := fframe_addr fs 1 pos) in *. set (fl := fflag_addr fs 1 pos) in *.
  assert (FF : ff = fs + 1085440 + 128 * pos) by (subst ff; unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  assert (FL : fl = fs + 20480 + pos) by (subst fl; unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  clearbody ff fl pos.
  (first [ dand10 TC as Cini Creal Cdesc Cdtv Cdtv1 Cflg Cflgb Cverb Cverbv Coff | destruct TC as (Cini & Creal & Cdesc & Cdtv & Cdtv1 & Cflg & Cflgb & Cverb & Cverbv & Coff) ]). aobj_lin_all.
  (first [ dand6 TD as Cdtls Cbeg NZ BR D0 D1 | destruct TD as (Cdtls & Cbeg & NZ & BR & D0 & D1) ]). aobj_lin_all.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). aobj_lin_all.
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]). aobj_lin_all.
  (first [ dand6 FSH as Hfs Hssl Hgc FSA FS0 FS1 | destruct FSH as (Hfs & Hssl & Hgc & FSA & FS0 & FS1) ]). aobj_lin_all.
  unfold smalloc_entry, kFakeStackBytes, TP, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kHighMemEnd, kShadowOffset, kFakeStackSizeLog in *. aobj_lin_all. subst tp a0. rewrite unsigned_lit in Ttsd, Btp by lia.
  change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
  set (fsq := fs / 4096) in *.
  assert (FSQ : fs = 4096 * fsq) by (subst fsq; rewrite (Z_div_mod_eq_full fs 4096) at 1; rewrite FSA; lia).
  clearbody fsq.
  assert (SHF : sh ff = 512 * fsq + 16 * pos + 2147586560).
  { unfold sh, kShadowOffset. rewrite FF, FSQ. replace (4096 * fsq + 1085440 + 128 * pos) with ((512 * fsq + 135680 + 16 * pos) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite SHF in *.
  (* [comment removed for export] *)
  pose proof (bytes_mapped_C8 m (fs + 8 * 1) (Z_to_bv 64 h) HINT ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CH.
  replace (fs + 8 * 1) with (fs + 8) in CH by lia.
  pose proof (bytes_mapped_C1 m fl (Z_to_bv 8 0) FLAG ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CF.
  destruct (mapped_junk m ff 128 ltac:(eapply mapped_sub; [exact MAP| lia | plia]) ltac:(lia) ltac:(lia) ltac:(lia)) as [jf CFR].
  apply (rw_cells_split_CB rsegs m ff [] 128 _ [] [24; 8; 88; 8]%nat) in CFR; [| reflexivity]. cbn [app mk_CB_cells] in CFR.
  clear HINT FLAG.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (fs + 8, fs + 8 + 8); (fl, fl + 1); (ff, ff + 128); (sh ff, sh ff + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep. (* [comment removed for export] *)
  callz tlsfs_ok.
  all: try exact MI.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ rebundle. }
  1:{ rebundle. }
  1:{ unfold thread_cells; rewrite unsigned_lit by lia; change (6194136 - 88) with 6194048. rebundle. }
  1:{ exact TLS. }
  1:{ reflexivity. }
  rename POST into ST. unfold TP.
  run_to 0x42a14. (* [comment removed for export] *)
  amz. replace (Z.land h 8191) with pos by (rewrite HP; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
  amz. replace (fs + 20480 + pos) with fl by lia.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz.
  amz. rewrite (Z.shiftl_mul_pow2 pos 7) by lia. change (2 ^ 7) with 128.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. replace (fs + 36864 + (1048576 + pos * 128)) with ff by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  callz m2s_fs_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundle. }
  1:{ reflexivity. }
  1:{ plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  amz. amz. amz.
  replace (2147450880 + Z.shiftr ff 3) with (512 * fsq + 16 * pos + 2147586560)
    by (rewrite Z.shiftr_div_pow2, FF, FSQ by lia; replace (4096 * fsq + 1085440 + 128 * pos) with ((512 * fsq + 135680 + 16 * pos) * 8) by lia;
        change (2 ^ 3) with 8; rewrite Z.div_mul by lia; lia).
  change (Z.to_nat 16) with 16%nat in SHC.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  do 6 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  apply evt_done. unfold smalloc_post. cbv zeta.
  change (fslots 1) with 8192. change (fsize 1) with 128.
  replace (if 1 <=? 6 then 128 / 8 else sz / 8) with 16 by reflexivity.
  rewrite <- HP.
  replace (fframe_addr fs 1 pos) with ff by (unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  replace (fflag_addr fs 1 pos) with fl by (unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  rewrite SHF. replace (fs + 8 * 1) with (fs + 8) by lia. unfold saved_flag_ptr. change (fsize 1) with 128.
  replace (ff + 128 - 8) with (ff + 120) by lia.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
  split; [reflexivity|].
  split; [rewrite SHF in MU; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split. { eapply (rw_cells_hd _ _ (C8 _)). exact CH. }
  split. { eapply (rw_cells_hd _ _ (C1 _)). exact CF. }
  split. { apply rw_cells_tl in CFR. lazymatch type of CFR with rw_cells _ _ ?a _ => replace (ff + 24) with a by (cbn; lia) end.
           eapply (rw_cells_hd _ _ (C8 _)). exact CFR. }
  split. { do 3 apply rw_cells_tl in CFR. lazymatch type of CFR with rw_cells _ _ ?a _ => replace (ff + 120) with a by (cbn; lia) end.
           eapply (rw_cells_hd _ _ (C8 _)). exact CFR. }
  change (Z.to_nat 16) with 16%nat.
  lazymatch goal with |- bytes_at _ _ ?a _ =>
    lazymatch goal with SH : rw_cells rsegs _ a ?cs |- _ =>
      change (repeat (Z_to_bv 8 0) 16) with (cells_bytes cs); apply rw_cells_bytes; exact SH end end.
Qed.

End CEIL.
End ASm_0x1.

Module ASm_imo.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASm_mu9.ARt2_tls OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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

Theorem smallocG0_ok : smallocG0_stmt.
Proof.
  unfold smallocG0_stmt, smallocG_stmt. intros until oldsh. cbv zeta.
  intros MI ST LOLE CEIL TPE A0 K7 TC TD THC TLS PC FSH HR HINT FLAG MAP SHC RA. clear K7.
  pose proof alloc_ceiling_val as CV.
  change (fslots 0) with 16384 in *. change (fsize 0) with 64 in *.
  replace (if 0 <=? 6 then 64 / 8 else sz / 8) with 8 in * by reflexivity.
  set (pos := h mod 16384) in *.
  assert (POS : 0 <= pos < 16384) by (subst pos; apply Z.mod_pos_bound; lia).
  assert (HP : pos = h mod 16384) by reflexivity.
  set (ff := fframe_addr fs 0 pos) in *. set (fl := fflag_addr fs 0 pos) in *.
  assert (FF : ff = fs + 36864 + 64 * pos) by (subst ff; unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  assert (FL : fl = fs + 4096 + pos) by (subst fl; unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  clearbody ff fl pos.
  (first [ dand10 TC as Cini Creal Cdesc Cdtv Cdtv1 Cflg Cflgb Cverb Cverbv Coff | destruct TC as (Cini & Creal & Cdesc & Cdtv & Cdtv1 & Cflg & Cflgb & Cverb & Cverbv & Coff) ]). aobj_lin_all.
  (first [ dand6 TD as Cdtls Cbeg NZ BR D0 D1 | destruct TD as (Cdtls & Cbeg & NZ & BR & D0 & D1) ]). aobj_lin_all.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). aobj_lin_all.
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]). aobj_lin_all.
  (first [ dand6 FSH as Hfs Hssl Hgc FSA FS0 FS1 | destruct FSH as (Hfs & Hssl & Hgc & FSA & FS0 & FS1) ]). aobj_lin_all.
  unfold smalloc_entry, kFakeStackBytes, TP, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kHighMemEnd, kShadowOffset, kFakeStackSizeLog in *. aobj_lin_all. subst tp a0. rewrite unsigned_lit in Ttsd, Btp by lia.
  change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
  set (fsq := fs / 4096) in *.
  assert (FSQ : fs = 4096 * fsq) by (subst fsq; rewrite (Z_div_mod_eq_full fs 4096) at 1; rewrite FSA; lia).
  clearbody fsq.
  assert (SHF : sh ff = 512 * fsq + 8 * pos + 2147455488).
  { unfold sh, kShadowOffset. rewrite FF, FSQ. replace (4096 * fsq + 36864 + 64 * pos) with ((512 * fsq + 4608 + 8 * pos) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite SHF in *.
  (* [comment removed for export] *)
  pose proof (bytes_mapped_C8 m (fs + 8 * 0) (Z_to_bv 64 h) HINT ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CH.
  replace (fs + 8 * 0) with fs in CH by lia.
  pose proof (bytes_mapped_C1 m fl (Z_to_bv 8 0) FLAG ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CF.
  destruct (mapped_junk m ff 64 ltac:(eapply mapped_sub; [exact MAP| lia | plia]) ltac:(lia) ltac:(lia) ltac:(lia)) as [jf CFR].
  apply (rw_cells_split_CB rsegs m ff [] 64 _ [] [24; 8; 24; 8]%nat) in CFR; [| reflexivity]. cbn [app mk_CB_cells] in CFR.
  clear HINT FLAG.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (fs, fs + 8); (fl, fl + 1); (ff, ff + 64); (sh ff, sh ff + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep. (* [comment removed for export] *)
  callz tlsfs_ok.
  all: try exact MI.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ rebundle. }
  1:{ rebundle. }
  1:{ unfold thread_cells; rewrite unsigned_lit by lia; change (6194136 - 88) with 6194048. rebundle. }
  1:{ exact TLS. }
  1:{ reflexivity. }
  rename POST into ST. unfold TP.
  run_to 0x42890. (* [comment removed for export] *)
  amz. replace (Z.land h 16383) with pos by (rewrite HP; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; reflexivity).
  amz. replace (fs + 4096 + pos) with fl by lia.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz.
  amz. rewrite (Z.shiftl_mul_pow2 pos 6) by lia. change (2 ^ 6) with 64.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. replace (fs + 36864 + pos * 64) with ff by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  callz m2s_fs_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundle. }
  1:{ reflexivity. }
  1:{ plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  amz. amz. amz.
  replace (2147450880 + Z.shiftr ff 3) with (512 * fsq + 8 * pos + 2147455488)
    by (rewrite Z.shiftr_div_pow2, FF, FSQ by lia; replace (4096 * fsq + 36864 + 64 * pos) with ((512 * fsq + 4608 + 8 * pos) * 8) by lia;
        change (2 ^ 3) with 8; rewrite Z.div_mul by lia; lia).
  change (Z.to_nat 8) with 8%nat in SHC.
  amz. (* [comment removed for export] *)
  do 6 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  apply evt_done. unfold smalloc_post. cbv zeta.
  change (fslots 0) with 16384. change (fsize 0) with 64.
  replace (if 0 <=? 6 then 64 / 8 else sz / 8) with 8 by reflexivity.
  rewrite <- HP.
  replace (fframe_addr fs 0 pos) with ff by (unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  replace (fflag_addr fs 0 pos) with fl by (unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  rewrite SHF. replace (fs + 8 * 0) with fs by lia. unfold saved_flag_ptr. change (fsize 0) with 64.
  replace (ff + 64 - 8) with (ff + 56) by lia.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
  split; [reflexivity|].
  split; [rewrite SHF in MU; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split. { eapply (rw_cells_hd _ _ (C8 _)). exact CH. }
  split. { eapply (rw_cells_hd _ _ (C1 _)). exact CF. }
  split. { apply rw_cells_tl in CFR. lazymatch type of CFR with rw_cells _ _ ?a _ => replace (ff + 24) with a by (cbn; lia) end.
           eapply (rw_cells_hd _ _ (C8 _)). exact CFR. }
  split. { do 3 apply rw_cells_tl in CFR. lazymatch type of CFR with rw_cells _ _ ?a _ => replace (ff + 56) with a by (cbn; lia) end.
           eapply (rw_cells_hd _ _ (C8 _)). exact CFR. }
  change (Z.to_nat 8) with 8%nat. rewrite <- le8_zero_repeat. eapply (rw_cells_hd _ _ (C8 _)). eassumption.
Qed.

End CEIL.
End ASm_imo.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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

Theorem smallocG7_ok : smallocG7_stmt.
Proof.
  unfold smallocG7_stmt, smallocG_stmt. intros until oldsh. cbv zeta.
  intros MI ST LOLE CEIL TPE A0 K7 TC TD THC TLS PC FSH HR HINT FLAG MAP SHC RA.
  destruct (K7 eq_refl) as [SZ8 SZB]. clear K7.
  pose proof alloc_ceiling_val as CV.
  change (fslots 7) with 128 in *. change (fsize 7) with 8192 in *.
  replace (if 7 <=? 6 then 8192 / 8 else sz / 8) with (sz / 8) in * by reflexivity.
  set (pos := h mod 128) in *.
  assert (POS : 0 <= pos < 128) by (subst pos; apply Z.mod_pos_bound; lia).
  assert (HP : pos = h mod 128) by reflexivity.
  set (ff := fframe_addr fs 7 pos) in *. set (fl := fflag_addr fs 7 pos) in *.
  assert (FF : ff = fs + 7376896 + 8192 * pos) by (subst ff; unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  assert (FL : fl = fs + 36608 + pos) by (subst fl; unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  clearbody ff fl pos.
  set (n8 := sz / 8) in *. assert (N8 : sz = 8 * n8) by (subst n8; rewrite (Z_div_mod_eq_full sz 8) at 1; rewrite SZ8; lia).
  clearbody n8.
  (first [ dand10 TC as Cini Creal Cdesc Cdtv Cdtv1 Cflg Cflgb Cverb Cverbv Coff | destruct TC as (Cini & Creal & Cdesc & Cdtv & Cdtv1 & Cflg & Cflgb & Cverb & Cverbv & Coff) ]). aobj_lin_all.
  (first [ dand6 TD as Cdtls Cbeg NZ BR D0 D1 | destruct TD as (Cdtls & Cbeg & NZ & BR & D0 & D1) ]). aobj_lin_all.
  (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). aobj_lin_all.
  pose proof PC as PC'.
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]). aobj_lin_all.
  (first [ dand6 FSH as Hfs Hssl Hgc FSA FS0 FS1 | destruct FSH as (Hfs & Hssl & Hgc & FSA & FS0 & FS1) ]). aobj_lin_all.
  unfold smalloc_entry, kFakeStackBytes, TP, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kHighMemEnd, kShadowOffset, kFakeStackSizeLog in *. aobj_lin_all. subst tp a0. rewrite unsigned_lit in Ttsd, Btp by lia.
  change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
  set (fsq := fs / 4096) in *.
  assert (FSQ : fs = 4096 * fsq) by (subst fsq; rewrite (Z_div_mod_eq_full fs 4096) at 1; rewrite FSA; lia).
  clearbody fsq.
  assert (SHF : sh ff = 512 * fsq + 1024 * pos + 2148372992).
  { unfold sh, kShadowOffset. rewrite FF, FSQ. replace (4096 * fsq + 7376896 + 8192 * pos) with ((512 * fsq + 922112 + 1024 * pos) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite SHF in *.
  (* [comment removed for export] *)
  pose proof (bytes_mapped_C8 m (fs + 8 * 7) (Z_to_bv 64 h) HINT ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CH.
  replace (fs + 8 * 7) with (fs + 56) in CH by lia.
  pose proof (bytes_mapped_C1 m fl (Z_to_bv 8 0) FLAG ltac:(eapply mapped_sub; [exact MAP| lia | plia])) as CF.
  destruct (mapped_junk m (ff + 24) 8 ltac:(eapply mapped_sub; [exact MAP| lia | plia]) ltac:(lia) ltac:(lia) ltac:(lia)) as [jf1 CF1].
  destruct (mapped_junk m (ff + 8184) 8 ltac:(eapply mapped_sub; [exact MAP| lia | plia]) ltac:(lia) ltac:(lia) ltac:(lia)) as [jf2 CF2].
  change (Z.to_nat 8) with 8%nat in CF1, CF2.
  clear HINT FLAG.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (fs + 56, fs + 56 + 8); (fl, fl + 1); (ff, ff + 8192); (sh ff, sh ff + n8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  do 11 zstep. (* [comment removed for export] *)
  callz tlsfs_ok.
  all: try exact MI.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ rebundle. }
  1:{ rebundle. }
  1:{ unfold thread_cells; rewrite unsigned_lit by lia; change (6194136 - 88) with 6194048. rebundle. }
  1:{ exact TLS. }
  1:{ reflexivity. }
  rename POST into ST. unfold TP.
  run_to 0x42bac. (* [comment removed for export] *)
  amz. replace (Z.land h 127) with pos by (rewrite HP; change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
  amz. replace (fs + 36608 + pos) with fl by lia.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz.
  amz. rewrite (Z.shiftl_mul_pow2 pos 13) by lia. change (2 ^ 13) with 8192.
  amz. amz. amz. amz. amz. replace (fs + 36864 + (7340032 + pos * 8192)) with ff by lia.
  amz. (* [comment removed for export] *)
  amz. replace (ff + 8192) with (ff + 8184 + 8) by lia.
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  callz m2s_fs_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundle. }
  1:{ reflexivity. }
  1:{ plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  amz. amz. amz. amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  eapply evt_cut; [eapply poison_ok|].
  all: try exact MI0.
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ rewrite FF, FSQ. replace (4096 * fsq + 7376896 + 8192 * pos) with ((512 * fsq + 922112 + 1024 * pos) * 8) by lia. apply Z_mod_mult. }
  1:{ exact SZ8. }
  1:{ lia. }
  1:{ unfold kHighMemBeg. plia. }
  1:{ lia. }
  1:{ lia. }
  1:{ intros _. rewrite N8. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  1:{ rebundle. }
  1:{ rewrite SHF. replace (sz / 8) with n8 by (rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity). exact SHC. }
  1:{ reflexivity. }
  clear SHC.
  intros ms' PO. destruct_exs PO. (first [ dand6 PO as E MUc WMc MIc STc SHZ | destruct PO as (E & MUc & WMc & MIc & STc & SHZ) ]). aobj_lin_all. subst ms'.
  rewrite ?unsigned_lit in MUc, STc by lia.
  replace (sz / 8) with n8 in MUc, SHZ by (rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs mA m' MUc WMc end.
  clear MUc WMc MI0. rename STc into ST.
  replace (ret_pc (Z_to_bv 64 273488)) with (Z_to_bv 64 273488) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 8 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  apply evt_done. unfold smalloc_post. cbv zeta.
  change (fslots 7) with 128. change (fsize 7) with 8192.
  replace (if 7 <=? 6 then 8192 / 8 else sz / 8) with n8 by (cbn [Z.leb]; rewrite N8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite <- HP.
  replace (fframe_addr fs 7 pos) with ff by (unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog, fsize; lia).
  replace (fflag_addr fs 7 pos) with fl by (unfold fflag_addr, kFakeFlagsOffset, fflags_off; lia).
  replace (fs + 8 * 7) with (fs + 56) by lia. unfold saved_flag_ptr. change (fsize 7) with 8192.
  replace (ff + 8192 - 8) with (ff + 8184) by lia.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split. { eapply (rw_cells_hd _ _ (C8 _)). exact CH. }
  split. { eapply (rw_cells_hd _ _ (C1 _)). exact CF. }
  split. { eapply (rw_cells_hd _ _ (C8 _)). exact CF1. }
  split. { eapply (rw_cells_hd _ _ (C8 _)). exact CF2. }
  exact SHZ.
Qed.

End CEIL.
