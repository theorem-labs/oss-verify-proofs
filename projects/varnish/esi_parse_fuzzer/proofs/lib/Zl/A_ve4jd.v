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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpa09.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VStbd A_VEr47 A_veqih.

Module A_ve2b5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpa09.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VStbd A_VEr47 A_veqih.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, vep_error_post, VEPERR_STACK, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK, h_vsc in H.


Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, vep_error_post, VEPERR_STACK, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK, h_vsc in H.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HMH : vv Fmatch_hit = vi_tbl_attr_include VIA \/ vv Fmatch_hit = vi_tbl_attr_include VIA + 16.
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis ANZ : vv Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : vv Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fattr_vsb /\ vv Finclude_src <> vb_buf ya /\
                   vb_buf yi <> vv Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.   (* [comment removed for export] *)
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vi' : option vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q ->
      frames_same A0 A' -> a_tinycred A' = a_tinycred A0 -> a_seccred A' = a_seccred A0 -> a_primcred A' = a_primcred A0 (* [comment removed for export] *) ->
      (  (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Finclude_src (vv Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                    (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0)
      \/ (* [comment removed for export] *) (vi <> None /\ vv' = fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    (match vi with Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                              a_livebytes A' = a_livebytes A0 - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A0 - 4
                                 | None => False end) /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> r <> vv Finclude_src ->
                               r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) /\ exists ic, bool01 ic /\ vv' = fupd (fupd vv Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))) ->
      match vi' with
      | None => vv' Finclude_src = 0
      | Some yi => vv' Finclude_src <> 0 /\ vsb_obj LPA A' v' (vv' Finclude_src) yi true /\ vb_error yi = 0
      end ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             nowhere (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let SA := vv Fattr_vsb.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Definition FRAME (j : list byte) : list cell :=
    [CB 56 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HMH (conj HIC (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB
      (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO K))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ESA : SA = vv Fattr_vsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 T md0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra lo vi ya q tag vv"] Lemma CFP : client_fp LPA A0 (aview A0 m0) W.
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). pose proof (proj1 HENV) as [ageh HFRh]. cbn.
    split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))) with (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) by lia; exact WMAP00|].
    split; [right; right; left; exists (h_ff H), HCLASS, ageh; split; [exact HFRh|]; change (fsize HCLASS) with 8192; lia|].
    split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra lo vi q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand4 dR_1 as _ _ VEPlo _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & _ & VEPlo & _) ]).
    unfold kHighMemBeg in VEPlo. all_app_facts.
    intros P a Ha NO. cbn [outside W] in NO. unfold h_vsc.
    assert (C3 : (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) <= a < bv_unsigned sp)
                 \/ (h_ff H + 32 + 1304 <= a < h_ff H + 32 + 1320) \/ (VEP <= a < VEP + 312)) by (try (generalize alloc_ceiling_val); clear - NO; try pose proof alloc_ceiling_val as ACV__; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [try (generalize alloc_ceiling_val); clear -VEPlo; try pose proof alloc_ceiling_val as ACV__; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 ya"] Lemma seg_src2 : forall (yi : vsb_rec) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 : word) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME j40) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (VEP + 280)) s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880)) s3 (Z_to_bv 64 VEP) xs5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8eba8) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISA NISB NIBA NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISA & NISB & NIBA & NIBB) ]).
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ)) as dR_5; dand11 dR_5 as SA16 SAlo SAhi _ BA16 BAlo BAhi _ DSBA _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ) as (SA16 & SAlo & SAhi & _ & BA16 & BAlo & BAhi & _ & DSBA & _ & _) ]).
    pose proof AOBJ as (_ & YINV & YLS & YLB & YNE & _).
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_6; dand11 dR_6 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    (first [ pose proof (IOBJ) as dR_7; dand6 dR_7 as _ IINV LSI LBI INE _ | pose proof IOBJ as (_ & IINV & LSI & LBI & INE & _) ]).
    unfold kHighMemBeg in VEPlo, SAlo, BAlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 SA 40 VEP 312 AINV00 YLS VLV NAS) as DJS.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf ya) (vb_size ya) VEP 312 AINV00 YLB VLV NAB) as DJB.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI VLV NIS) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI VLV NIB) as DVBI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI YLS NISA) as DSSA.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI YLS NIBA) as DBSA.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI YLB NISB) as DSBA'.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI YLB NIBB) as DBBA.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfSI, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_boundL (Clg:=Clg) SA 40 ltac:(keeplia SAlo) ltac:(lia) ltac:(exact SAhi)) as SHSA. rewrite SHMAX_val in SHSA.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf ya) (vb_size ya) ltac:(keeplia BAlo) ltac:(try (generalize alloc_ceiling_val); clear - YINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 YINV); lia) ltac:(exact BAhi)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(lia) ltac:(exact SIhi)) as SHSI. rewrite SHMAX_val in SHSI.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(try (generalize alloc_ceiling_val); clear - IINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 IINV); lia) ltac:(exact BIhi)) as SHBI. rewrite SHMAX_val in SHBI.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_8; dand10 dR_8 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_9; dand8 dR_9 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_10; dand4 dR_10 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_11; dand3 dR_11 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    (* [comment removed for export] *)
    assert (AOBJ1 : vsb_obj LPA A0 m1 SA ya true).
    { eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]. }
    assert (IOBJ1 : vsb_obj LPA A0 m1 (vv Finclude_src) yi true).
    { eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]. }
    hide DJS. hide DJB. hide DVSI. hide DVBI. hide DSSA. hide DBSA. hide DSBA'. hide DBBA. hide DJfV. hide DJfS. hide DJfB. hide DJfSI. hide DJfBI.
    hide DSBA. hide DSBI. hide_neqs.
    pose proof VEPC as VEPCF.
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. cbv delta [FRAME] in FR.
    (* [comment removed for export] *)
    fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    clear GOTV SHvs SHc SHw SHG BSSV VC WK.
    henv_here m1 MU WM CNT HENVe DJfV GCE GHI SHF VEPlo.
    (first [ pose proof (HENVe) as dR_14; dand4 dR_14 as _ GLOBe0 HOBJe0 HSHe0 | pose proof HENVe as (_ & GLOBe0 & HOBJe0 & HSHe0) ]).
    assert (SHDq : shadowed LPA m1 VEP 312)
      by (exists VEP, 312; split; [pose proof SHV as T__; rewrite EzsV in T__; exact T__|]; split; [exact V8| keeplia VEPlo VEPhi]).
    unhide DJfS. unhide DJfB. unhide DJfSI. unhide DJfBI.
    try clear CNT. icall (vep_error_ok VEP vv tag q H lo) by
      (rewrite ?unsigned_lit by (keeplia SPR LO CEIL ACV);
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ VEP _ => exact VEPCF
       | |- length _ = _ => exact TAG8
       | |- vep_pads_wf _ => exact PADS
       | |- vv Fvc = _ => exact EVC
       | |- glob_ok _ _ _ _ => exact GLOBe0
       | |- hobj_ok _ _ _ _ => exact HOBJe0
       | |- hshadow _ _ _ => exact HSHe0
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => exact CE1
       | |- shadowed _ _ _ _ => exact SHDq
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => assumption
       | |- _ => unfold kHighMemBeg, HFSIZE, VEPERR_STACK; ufs; keeplia VEPlo VEPhi V8 DJfV LO CEIL ACV SPR
       end).
    try clear VEPCF. clear HENVe GLOBe0 HOBJe0 HSHe0.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => try clear ST; rename X into ST end.
    (* [comment removed for export] *)
    lazymatch goal with X : glob_ok _ _ _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      (first [ pose proof (X) as dR_15; dand4 dR_15 as _ _ _ [cnt' CNT'] | pose proof X as (_ & _ & _ & [cnt' CNT']) ]); fold_cl_segs; cbn [vi_bss_vsc VIA] in CNT'; unfold h_vsc in CNT';
      replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT' by (clear; lia); clear X end.
    hide DJfS. hide DJfB. hide DJfSI. hide DJfBI.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. zstep. hide DJfV. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _, STq : stk _ ?ma lo _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename STq into STw;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      (* [comment removed for export] *)
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl)) as dR_16; dand3 dR_16 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk;
      change (Z.of_nat 224) with 224 in VM; change (Z.of_nat 224) with 224 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 224 + 8) with (VEP + 232) in VBk by lia
    end.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      assert (AOBJa : vsb_obj LPA A0 (aview A0 mq) SA ya true)
        by (unhide DJfS; unhide DJfB; unhide DJS; unhide DJB;
            eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]);
      assert (IOBJa : vsb_obj LPA A0 (aview A0 mq) (vv Finclude_src) yi true)
        by (unhide DJfSI; unhide DJfBI; unhide DVSI; unhide DVBI;
            eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]) end.
    clear AOBJ1 IOBJ1.
    assert (AL16 : (bv_unsigned sp + -160) mod 16 = 0)
      by (apply align16_add; [exact SP16|reflexivity]).
    unhide NAS. unhide NAB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 224) SA ya true lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NAS X)| exact (NAB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact AOBJa | exact TP
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact AL16
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact STw | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; keeplia LO | ].
    hide NAS. hide NAB.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1.
    rewrite unsigned_lit in ST1, CF1 by (keeplia SPR LO CEIL ACV). ufs.
    replace (ret_pc (Z_to_bv 64 0x8ebe0)) with (Z_to_bv 64 0x8ebe0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV).
    assert (LSI1 : a_live A1 (vv Finclude_src) = Some 40) by (rewrite (LIVEq _ NISA NISB); exact LSI).
    assert (LBI1 : a_live A1 (vb_buf yi) = Some (vb_size yi)) by (rewrite (LIVEq _ NIBA NIBB); exact LBI).
    hide_neqs.
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists SA, 40. split; [exact YLS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf ya), (vb_size ya). split; [exact YLB|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    clear HENVa.
    (* [comment removed for export] *)
    unhide DJS. unhide DJB. unhide DSSA. unhide DBSA. unhide DSBA'. unhide DBBA.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 224 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 232)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 232) 80 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ];
      lazymatch goal with FRq : rw_cells _ ma (bv_unsigned sp + -160) ?fcs |- _ =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (bv_unsigned sp + -160) fcs) in FRq;
        [ rename FRq into FR1
        | exact (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -160) 160 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                   (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRq ltac:(off_image_solve LPA)))
        | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SPR|];
          intros i Hi X; unfold newblk, blk in X; keeplia Hi X SAhi BAhi SHSA SHBB VEPhi ACV CEIL LO ] end;
      assert (IOBJc : vsb_obj LPA A1 mb (vv Finclude_src) yi true);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact IOBJa| keeplia CEIL LO| exact LSI1| exact LBI1|];
        intros a Ha X; unfold newblk, blk in X; keeplia Ha X DVSI DVBI DSSA DBSA DSBA' DBBA SHSA SHBB SIlo BIlo VEPlo
      | clear IOBJa ]
    end.
    hide DJS. hide DJB. hide DSSA. hide DBSA. hide DSBA'. hide DBBA.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) tag q)).
    { rewrite <- vep_cells_attr_vsb. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA].
      rewrite EVC. unfold h_vc.
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 224) with 224; change (Z.of_nat 8) with 8; lia]. }
    clear VA VM VBk PSC.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A1 mc)) as MU2. pose proof (wmono_refl rsegs (aview A1 mc)) as WM2.
    ago AINV1. fold_cl_segs.
    zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    astop AINV1 MU2 WM2 I.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINVb end.
    lazymatch goal with FRq : rw_cells _ ?ma (bv_unsigned sp + -160) _, STq : stk _ ?ma lo _ |- _ =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STv end.
    (* [comment removed for export] *)
    lazymatch goal with VEPCq : rw_cells _ ?ma VEP _ |- _ =>
      unfold vep_cells in VEPCq;
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl)) as dR_17; dand3 dR_17 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA] in VA, VM, VBk;
      change (Z.of_nat 280) with 280 in VM; change (Z.of_nat 280) with 280 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia
    end.
    unhide NIS. unhide NIB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A1 (VEP + 280) (vv Finclude_src) yi true lo);
      [ exact AINVb | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact LVEP1| cbn; intros [X|[X|X]]; [exact (NIS X)| exact (NIB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | assumption | exact TP | exact SP16 | exact STv | exact CEIL | ufs; keeplia LO | ].
    hide NIS. hide NIB.
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 mf mdf. cbv zeta.
    intros AINV2 MI2 MDF2 FRS2 LB2 TC2 NL2 SC2 PC2 ST2 PSC2 DEADI DEADBI LIVEq2 CF2. ufs.
    unhide_neqs.
    assert (LVEP2 : a_live A2 VEP = Some 312) by (rewrite (LIVEq2 VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact LVEP1).
    (* [comment removed for export] *)
    assert (HENV2 : henv_ok LPA VIA H A2 (aview A2 mf)).
    { lazymatch goal with HE : henv_ok LPA VIA H A1 (aview A1 ?mx) |- _ =>
        eapply (henv_ok_acall_gen H A1 A2); [exact AINVb| exact CF2| exact HE| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS2 ff); exact HF|] end.
      intros a [X|[X|X]].
      - exists (vv Finclude_src), 40. split; [exact LSI1|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf yi), (vb_size yi). split; [exact LBI1|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact LVEP1|]. left. keeplia X. }
    (* [comment removed for export] *)
    unhide DVSI. unhide DVBI.
    lazymatch type of CF2 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ VEP 312 VEP 280 AINVb LVEP1 ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ];
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (VEP + 288)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ VEP 312 (VEP + 288) 24 AINVb LVEP1 ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ]
    end.
    hide DVSI. hide DVBI.
    assert (VEPC2 : rw_cells rsegs (aview A2 mf) VEP
                      (vep_cells (fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0) tag q)).
    { rewrite <- vep_cells_include_src. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A2 mf) VEP pre); [exact VA| exact PSC2|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC2.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mf mdf (fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0) None);
      [ exact AINV2 | exact MI2
      | eapply amd_frame_sbm_l; [exact SBM| exact MH|]; eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_sbm_l; [exact SBM0| exact MH1| exact MDF2]
      | exact ST2 | exact HENV2
      | split; [exact LVEP2|]; split; [exact VEPC2|]; split; [exact TAG8| exact PADS]
      | intros ff; rewrite (FRS2 ff); apply FRS1 | rewrite TC2; exact TC1 | rewrite SC2; exact SC1 | rewrite PC2; exact PC1 (* [comment removed for export] *)
      | right; left; split; [rewrite EVI; discriminate|]; split; [reflexivity|]; split; [reflexivity|];
        split; [rewrite (LIVEq2 _ (not_eq_sym NISA) (not_eq_sym NIBA)); exact DEADS|];
        split; [rewrite (LIVEq2 _ (not_eq_sym NISB) (not_eq_sym NIBB)); exact DEADB|];
        split; [rewrite EVI; split; [exact DEADI|]; split; [exact DEADBI|]; split; [rewrite LB2, LB1; lia| rewrite NL2, NL1; lia]|];
        rewrite EVI; intros r R1 R2 R3 R4; rewrite (LIVEq2 r R3 R4); exact (LIVEq r R1 R2)
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | ].
    (* [comment removed for export] *)
    assert (MP2 : mapped (aview A2 mf) (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192))))) (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))
      by (eapply (stk_mapped (L:=LPA)); [exact ST2 | exact CEIL | keeplia LO | clear; lia]).
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
    lazymatch type of CF2 with cframe _ _ _ _ _ _ _ ?mb' ?mc2 =>
      assert (CFa : cframe LPA (owned A0) (owned A1) (bv_unsigned sp) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))
                      (fun a => blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a
                                \/ match vi with Some yi0 => vsb_blocks (vv Finclude_src) yi0 a | None => False end
                                \/ h_ff H + 32 + 1304 <= a < h_ff H + 32 + 1320) nowhere (aview A0 m0) mb');
      [ eapply (cframe_extend LPA _ _ (bv_unsigned sp + -160) _ (bv_unsigned sp) _ _ _ _ _ (aview A0 m0) ma mb mb' _ []);
        [ exact MU | ufs; apply W_cover | exact CF1 | ufs; clear; lia | clear; lia
        | intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]]
        | intros a X; left; exact X | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | lazymatch goal with STx : stk _ mb' lo (bv_unsigned sp) |- _ => eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | keeplia LO | clear; lia] end ]
      | eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) mb' mc2 CFa CF2);
        [ clear; lia | ufs; clear; lia | exact MP2 | intros a X; exact X
        | rewrite EVI; intros a [X|[X|X]]; right; [right; right; left; left; exact X | right; right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]]
        | intros a X; destruct X ] ]
    end end.
  Qed.
End S.
End A_ve2b5.


Module A_vebxj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpa09.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VStbd A_VEr47 A_veqih.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, vep_error_post, VEPERR_STACK, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK, h_vsc in H.


Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, vep_error_post, VEPERR_STACK, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK, h_vsc in H.

(* [comment removed for export] *)
Ltac zchk SRC k := zstep; zstep; shadow_addr SRC k; zstep; lit0; chk_branch.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition lws_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' a5' : word) (pc' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' (Z_to_bv 64 VCT_TYPTABA) a4 a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 pc') fc None m (seg_rom rsegs)
    /\ (pc' = 0x8f110 \/ pc' = 0x8f0f0).

Lemma lws_loop : forall (k : nat) (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (B : Z) (bs : list byte) (nb : nat) (i z : Z) (b : byte),
  bv_unsigned a4 = 18446744073709551615 ->
  u8arr rsegs m B bs -> mem_inv rsegs m ->
  bytes_at rsegs m (sh VCT_TYPTABA) (repeat (Z_to_bv 8 0) 64) ->
  bytes_at rsegs m (sh B) (repeat (Z_to_bv 8 0) nb) -> B mod 8 = 0 -> 0 <= B -> Z.of_nat (length bs) <= 8 * Z.of_nat nb ->
  B + Z.of_nat (length bs) <= alloc_ceiling ->
  nth_error bs (Z.to_nat i) = Some b -> 0 <= i -> bv_unsigned b <> 0 ->
  nth_error bs (Z.to_nat z) = Some (Z_to_bv 8 0) -> i < z -> z - i <= Z.of_nat k ->
  evt rsegs (lws_post ra sp gp tp t0 t1 t2 s0 s1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (B + i)) (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 VCT_TYPTABA)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8edbc) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros until b; intros A4 U8 MI VSH BSH B8 B0 LNB BHI Hn Hi Hb Hz IZ ZK; [exfalso; lia|].
  pose proof (u8arr_bound _ _ _ _ U8) as BB. pose proof (nth_error_lt _ _ _ Hz) as LZ.
  pose proof (byte_range b) as RB. pose proof alloc_ceiling_num as ACV.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b) 1) by lia. change (2 ^ 1) with 2.
  (* [comment removed for export] *)
  unfold VCT_TYPTABA in *.
  zchk VSH 2.
  (* [comment removed for export] *)
  pose proof (vct_readA m (bv_unsigned b) (Z_to_bv 64 (148416 + bv_unsigned b * 2)) MI RB ltac:(unfold wa, VCT_TYPTABA; f_equal; lia)) as RD.
  zstep. clear RD.
  pose proof (vct_range (bv_unsigned b)) as VR.
  unfold zx16. rewrite (unsigned_lit (vct (bv_unsigned b))) by lia. rewrite (Z.mod_small (vct (bv_unsigned b)) (2 ^ 16)) by lia.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    apply evt_done. unfold lws_post. do 5 eexists. split; [reflexivity| left; reflexivity].
  - (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { exfalso. rewrite A4 in KU. rewrite ?Z.mod_small in KU by lia. lia. } clear KU.
    (* [comment removed for export] *)
    zchk BSH 1.
    (* [comment removed for export] *)
    destruct (nth_error bs (Z.to_nat (i + 1))) as [b'|] eqn:Hn'; [| apply nth_error_None in Hn'; exfalso; lia].
    pose proof (byte_range b') as RB'.
    pose proof (u8arr_read rsegs m B bs (i + 1) b' (Z_to_bv 64 (B + i + 1)) U8 Hn' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. clear RD. zstep. zstep. if_cases KZ; zify_cond KZ.
    + (* [comment removed for export] *)
      apply evt_done. unfold lws_post. do 5 eexists. split; [reflexivity| right; reflexivity].
    + (* [comment removed for export] *)
      zstep.
      try replace (B + i + 1 + 1) with (B + (i + 1) + 1) by lia. try replace (B + i + 2) with (B + (i + 1) + 1) by lia.
      try replace (B + i + 1) with (B + (i + 1)) by lia.
      assert (NZ : i + 1 <> z) by (intros E; rewrite E in Hn'; rewrite Hz in Hn'; injection Hn' as E'; rewrite <- E' in KZ; apply KZ; reflexivity).
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m B bs nb (i + 1) z b');
        [exact A4 | exact U8 | exact MI | exact VSH | exact BSH | exact B8 | exact B0 | exact LNB | exact BHI | exact Hn' | lia | exact KZ | exact Hz | lia | lia].
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HMH : vv Fmatch_hit = vi_tbl_attr_include VIA \/ vv Fmatch_hit = vi_tbl_attr_include VIA + 16.
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis ANZ : vv Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : vv Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fattr_vsb /\ vv Finclude_src <> vb_buf ya /\
                   vb_buf yi <> vv Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.   (* [comment removed for export] *)
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vi' : option vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q ->
      frames_same A0 A' -> a_tinycred A' = a_tinycred A0 -> a_seccred A' = a_seccred A0 -> a_primcred A' = a_primcred A0 (* [comment removed for export] *) ->
      (  (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Finclude_src (vv Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                    (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0)
      \/ (* [comment removed for export] *) (vi <> None /\ vv' = fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    (match vi with Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                              a_livebytes A' = a_livebytes A0 - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A0 - 4
                                 | None => False end) /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> r <> vv Finclude_src ->
                               r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) /\ exists ic, bool01 ic /\ vv' = fupd (fupd vv Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))) ->
      match vi' with
      | None => vv' Finclude_src = 0
      | Some yi => vv' Finclude_src <> 0 /\ vsb_obj LPA A' v' (vv' Finclude_src) yi true /\ vb_error yi = 0
      end ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             nowhere (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let SA := vv Fattr_vsb.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Definition FRAME (j : list byte) : list cell :=
    [CB 56 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HMH (conj HIC (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB
      (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO K))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ESA : SA = vv Fattr_vsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 T md0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra lo vi ya q tag vv"] Lemma CFP : client_fp LPA A0 (aview A0 m0) W.
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). pose proof (proj1 HENV) as [ageh HFRh]. cbn.
    split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))) with (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) by lia; exact WMAP00|].
    split; [right; right; left; exists (h_ff H), HCLASS, ageh; split; [exact HFRh|]; change (fsize HCLASS) with 8192; lia|].
    split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra lo vi q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand4 dR_1 as _ _ VEPlo _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & _ & VEPlo & _) ]).
    unfold kHighMemBeg in VEPlo. all_app_facts.
    intros P a Ha NO. cbn [outside W] in NO. unfold h_vsc.
    assert (C3 : (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) <= a < bv_unsigned sp)
                 \/ (h_ff H + 32 + 1304 <= a < h_ff H + 32 + 1320) \/ (VEP <= a < VEP + 312)) by (try (generalize alloc_ceiling_val); clear - NO; try pose proof alloc_ceiling_val as ACV__; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [try (generalize alloc_ceiling_val); clear -VEPlo; try pose proof alloc_ceiling_val as ACV__; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 ya"] Lemma seg_accept : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 : word) (m1 : mem) (j40 cnt : list byte),
    vi = None ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME j40) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 224)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880)) (Z_to_bv 64 ((VEP + 224) / 8 + 2147450880)) (Z_to_bv 64 VEP)
                 xs5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8f0f0) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as ISRC0. rewrite EVI in ISRC0.
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ)) as dR_4; dand11 dR_4 as SA16 SAlo SAhi _ BA16 BAlo BAhi _ DSBA _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ) as (SA16 & SAlo & SAhi & _ & BA16 & BAlo & BAhi & _ & DSBA & _ & _) ]).
    pose proof AOBJ as (_ & YINV & YLS & YLB & YNE & _).
    unfold kHighMemBeg in VEPlo, SAlo, BAlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 SA 40 VEP 312 AINV00 YLS VLV NAS) as DJS.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf ya) (vb_size ya) VEP 312 AINV00 YLB VLV NAB) as DJB.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLB) as DJfB.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_boundL (Clg:=Clg) SA 40 ltac:(keeplia SAlo) ltac:(lia) ltac:(exact SAhi)) as SHSA. rewrite SHMAX_val in SHSA.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf ya) (vb_size ya) ltac:(keeplia BAlo) ltac:(try (generalize alloc_ceiling_val); clear - YINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 YINV); lia) ltac:(exact BAhi)) as SHBB. rewrite SHMAX_val in SHBB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (AOBJ1 : vsb_obj LPA A0 m1 SA ya true).
    { eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]. }
    hide DJS. hide DJB. hide DJfV. hide DJfS. hide DJfB. hide DSBA. hide_neqs.
    unfold vep_cells in VEPC. cbv delta [FRAME] in FR.
    (* [comment removed for export] *)
    vrechk SHV EzsV (VEP + 224) 8 0. vrechk SHV EzsV (VEP + 280) 8 0.
    (* [comment removed for export] *)
    zstep. unhide DJfV. zstep. zstep. hide DJfV.
    (* [comment removed for export] *)
    zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    lazymatch goal with FRq : rw_cells _ ?ma (bv_unsigned sp + -160) _, STq : stk _ ?ma lo _ |- _ =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STw end.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename VEPCq into VEPC1;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      assert (AOBJa : vsb_obj LPA A0 ma SA ya true)
        by (unhide DJfS; unhide DJfB; unhide DJS; unhide DJB;
            eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO])
    end.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ (fupd (fupd vv Finclude_src (vv Fattr_vsb)) Fattr_vsb 0) (Some ya));
      [ exact AINVa | assumption
      | apply amd_frame_sbm; [exact SBM| exact MH]
      | exact STw | exact HENVa
      | split; [exact VLV|]; split; [unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC1| split; [exact TAG8| exact PADS]]
      | intros ff; reflexivity | reflexivity | reflexivity | reflexivity (* [comment removed for export] *)
      | left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros r; reflexivity|]; split; reflexivity
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; [exact ANZ|]; split; [exact AOBJa| exact AERR]
      | ].
    (* [comment removed for export] *)
    eapply (cframe_stores LPA); [exact MU| ufs; apply W_cover| eapply (stk_mapped (L:=LPA)); [exact STw | exact CEIL | keeplia LO | clear; lia]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 ya"] Lemma seg_lwserr : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 : word) (m1 : mem) (j40 cnt : list byte),
    vi = None ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME j40) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 224)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880)) (Z_to_bv 64 ((VEP + 224) / 8 + 2147450880)) (Z_to_bv 64 VEP)
                 xs5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8f110) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as ISRC0. rewrite EVI in ISRC0.
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_5; dand7 dR_5 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ)) as dR_6; dand11 dR_6 as SA16 SAlo SAhi _ BA16 BAlo BAhi _ DSBA _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ) as (SA16 & SAlo & SAhi & _ & BA16 & BAlo & BAhi & _ & DSBA & _ & _) ]).
    pose proof AOBJ as (_ & YINV & YLS & YLB & YNE & _).
    unfold kHighMemBeg in VEPlo, SAlo, BAlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 SA 40 VEP 312 AINV00 YLS VLV NAS) as DJS.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf ya) (vb_size ya) VEP 312 AINV00 YLB VLV NAB) as DJB.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLB) as DJfB.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_boundL (Clg:=Clg) SA 40 ltac:(keeplia SAlo) ltac:(lia) ltac:(exact SAhi)) as SHSA. rewrite SHMAX_val in SHSA.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf ya) (vb_size ya) ltac:(keeplia BAlo) ltac:(try (generalize alloc_ceiling_val); clear - YINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 YINV); lia) ltac:(exact BAhi)) as SHBB. rewrite SHMAX_val in SHBB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (AOBJ1 : vsb_obj LPA A0 m1 SA ya true).
    { eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]. }
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_7; dand10 dR_7 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_8; dand8 dR_8 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_9; dand4 dR_9 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_10; dand3 dR_10 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide DJS. hide DJB. hide DJfV. hide DJfS. hide DJfB. hide DSBA. hide_neqs.
    pose proof VEPC as VEPCF.
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. cbv delta [FRAME] in FR.
    (* [comment removed for export] *)
    fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    clear GOTV SHvs SHc SHw SHG BSSV VC WK.
    henv_here m1 MU WM CNT HENVe DJfV GCE GHI SHF VEPlo.
    (first [ pose proof (HENVe) as dR_13; dand4 dR_13 as _ GLOBe0 HOBJe0 HSHe0 | pose proof HENVe as (_ & GLOBe0 & HOBJe0 & HSHe0) ]).
    assert (SHDq : shadowed LPA m1 VEP 312)
      by (exists VEP, 312; split; [pose proof SHV as T__; rewrite EzsV in T__; exact T__|]; split; [exact V8| keeplia VEPlo VEPhi]).
    unhide DJfS. unhide DJfB.
    icall (vep_error_ok VEP vv tag q H lo) by
      (rewrite ?unsigned_lit by (keeplia SPR LO CEIL ACV);
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ VEP _ => exact VEPCF
       | |- length _ = _ => exact TAG8
       | |- vep_pads_wf _ => exact PADS
       | |- vv Fvc = _ => exact EVC
       | |- glob_ok _ _ _ _ => exact GLOBe0
       | |- hobj_ok _ _ _ _ => exact HOBJe0
       | |- hshadow _ _ _ => exact HSHe0
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => exact CE1
       | |- shadowed _ _ _ _ => exact SHDq
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => assumption
       | |- _ => unfold kHighMemBeg, HFSIZE, VEPERR_STACK; ufs; keeplia VEPlo VEPhi V8 DJfV LO CEIL ACV SPR
       end).
    try clear VEPCF. clear HENVe GLOBe0 HOBJe0 HSHe0.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => try clear ST; rename X into ST end.
    (* [comment removed for export] *)
    lazymatch goal with X : glob_ok _ _ _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      (first [ pose proof (X) as dR_14; dand4 dR_14 as _ _ _ [cnt' CNT'] | pose proof X as (_ & _ & _ & [cnt' CNT']) ]); fold_cl_segs; cbn [vi_bss_vsc VIA] in CNT'; unfold h_vsc in CNT';
      replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT' by (clear; lia); clear X end.
    hide DJfS. hide DJfB.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. zstep. hide DJfV. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _, STq : stk _ ?ma lo _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename STq into STw;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      (* [comment removed for export] *)
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl)) as dR_15; dand3 dR_15 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk;
      change (Z.of_nat 224) with 224 in VM; change (Z.of_nat 224) with 224 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 224 + 8) with (VEP + 232) in VBk by lia
    end.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      assert (AOBJa : vsb_obj LPA A0 (aview A0 mq) SA ya true)
        by (unhide DJfS; unhide DJfB; unhide DJS; unhide DJB;
            eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]) end.
    clear AOBJ1.
    assert (AL16 : (bv_unsigned sp + -160) mod 16 = 0)
      by (apply align16_add; [exact SP16|reflexivity]).
    unhide NAS. unhide NAB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 224) SA ya true lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NAS X)| exact (NAB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact AOBJa | exact TP
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact AL16
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact STw | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; keeplia LO | ].
    hide NAS. hide NAB.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1.
    rewrite unsigned_lit in ST1, CF1 by (keeplia SPR LO CEIL ACV). ufs.
    replace (ret_pc (Z_to_bv 64 0x8f148)) with (Z_to_bv 64 0x8f148) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV).
    hide_neqs.
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists SA, 40. split; [exact YLS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf ya), (vb_size ya). split; [exact YLB|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    clear HENVa.
    (* [comment removed for export] *)
    unhide DJS. unhide DJB.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 224 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 232)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 232) 80 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ];
      lazymatch goal with FRq : rw_cells _ ma (bv_unsigned sp + -160) ?fcs |- _ =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (bv_unsigned sp + -160) fcs) in FRq;
        [ rename FRq into FR1
        | exact (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -160) 160 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                   (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRq ltac:(off_image_solve LPA)))
        | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SPR|];
          intros i Hi X; unfold newblk, blk in X; keeplia Hi X SAhi BAhi SHSA SHBB VEPhi ACV CEIL LO ] end
    end.
    hide DJS. hide DJB.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) tag q)).
    { rewrite <- vep_cells_attr_vsb. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA].
      rewrite EVC. unfold h_vc.
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 224) with 224; change (Z.of_nat 8) with 8; lia]. }
    clear VA VM VBk PSC.
    pose proof VEPC1 as VEPCx. unfold vep_cells in VEPCx. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA] in VEPCx. rewrite ISRC0 in VEPCx.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV1 LVEP1) as SHV1. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A1 mc)) as MU2. pose proof (wmono_refl rsegs (aview A1 mc)) as WM2.
    hide VEPC1.
    ago AINV1. fold_cl_segs.
    vrechk SHV1 EzsV (VEP + 280) 8 0.
    zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; apply KZ; reflexivity|]. clear KZ.
    zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    astop AINV1 MU2 WM2 I.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINVb end.
    lazymatch goal with FRq : rw_cells _ ?ma (bv_unsigned sp + -160) _, STq : stk _ ?ma lo _ |- _ =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STv end.
    unhide VEPC1. unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 _ _ (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) None);
      [ exact AINVb | assumption
      | eapply amd_frame_sbm_l; [exact SBM| exact MH|]; eapply amd_frame_trans; [exact MDF1|]; apply amd_frame_sbm; [exact SBM0| exact MH1]
      | exact STv | assumption
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | exact FRS1 | exact TC1 | exact SC1 | exact PC1 (* [comment removed for export] *)
      | right; right; left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|];
        split; [exact DEADS|]; split; [exact DEADB|]; split; [exact LB1|]; split; [exact NL1|]; exact LIVEq
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact ISRC0
      | ].
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      eapply (cframe_extend LPA _ _ (bv_unsigned sp + -160) _ (bv_unsigned sp) _ _ _ _ _ (aview A0 m0) ma mb mb _ []);
        [ exact MU | ufs; apply W_cover | exact CF1 | ufs; clear; lia | clear; lia
        | intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]]
        | intros a X; left; exact X | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | eapply (stk_mapped (L:=LPA)); [exact STv | exact CEIL | keeplia LO | clear; lia] ]
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 ya"] Lemma seg_src0 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 xs3 xs5 : word) (m1 : mem) (j40 cnt : list byte),
    vi = None ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -160) ->
    rw_cells rsegs m1 (bv_unsigned sp + -160) (FRAME j40) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (VEP + 280)) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880)) xs3 (Z_to_bv 64 VEP) xs5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8ed74) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as ISRC0. rewrite EVI in ISRC0.
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_16; dand7 dR_16 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ)) as dR_17; dand11 dR_17 as SA16 SAlo SAhi _ BA16 BAlo BAhi _ DSBA _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 SA ya true AINV00 AOBJ) as (SA16 & SAlo & SAhi & _ & BA16 & BAlo & BAhi & _ & DSBA & _ & _) ]).
    pose proof AOBJ as (_ & YINV & YLS & YLB & YNE & _).
    unfold kHighMemBeg in VEPlo, SAlo, BAlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 SA 40 VEP 312 AINV00 YLS VLV NAS) as DJS.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf ya) (vb_size ya) VEP 312 AINV00 YLB VLV NAB) as DJB.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh YLB) as DJfB.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_boundL (Clg:=Clg) SA 40 ltac:(keeplia SAlo) ltac:(lia) ltac:(exact SAhi)) as SHSA. rewrite SHMAX_val in SHSA.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf ya) (vb_size ya) ltac:(keeplia BAlo) ltac:(try (generalize alloc_ceiling_val); clear - YINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 YINV); lia) ltac:(exact BAhi)) as SHBB. rewrite SHMAX_val in SHBB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (as_live_shadow LPA _ _ _ SA 40 AINV00 YLS) as SHS0. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) SA 40 ltac:(lia) ltac:(lia) ltac:(exact SAhi)) as SHSB. rewrite SHMAX_val in SHSB.
    assert (SHS : bytes_at rsegs m1 (sh SA) (shpat 40)).
    { eapply (bytes_at_munch LPA); [exact SHS0| exact MU|]. intros a Ha. cbn. keeplia Ha SHSB GCE VEPlo LO CEIL ACV. }
    clear SHS0.
    pose proof (as_live_shadow LPA _ _ _ (vb_buf ya) (vb_size ya) AINV00 YLB) as BSH0. fold_cl_segs. fold_aview.
    assert (EBP : shpat (vb_size ya) = repeat (Z_to_bv 8 0) (Z.to_nat (vb_size ya / 8))).
    { unfold shpat. (first [ pose proof (YINV) as dR_18; dand9 dR_18 as Ysz _ _ _ _ _ _ _ Ysm | pose proof YINV as (Ysz & _ & _ & _ & _ & _ & _ & _ & Ysm) ]).
      replace (vb_size ya mod 8 =? 0) with true; [rewrite app_nil_r; reflexivity|].
      symmetry. apply Z.eqb_eq. clear - Ysm Ysz; try pose proof alloc_ceiling_val as ACV__. Z.div_mod_to_equations. lia. }
    rewrite EBP in BSH0. clear EBP.
    remember (repeat (Z_to_bv 8 0) (Z.to_nat (vb_size ya / 8))) as zsB eqn:EzsB in BSH0.
    assert (LZB : 8 * Z.of_nat (length zsB) = vb_size ya).
    { rewrite EzsB, repeat_length. (first [ pose proof (YINV) as dR_19; dand9 dR_19 as Ysz _ _ _ _ _ _ _ Ysm | pose proof YINV as (Ysz & _ & _ & _ & _ & _ & _ & _ & Ysm) ]). clear - Ysz Ysm; try pose proof alloc_ceiling_val as ACV__. Z.div_mod_to_equations. nia. }
    assert (SHBz : sh (vb_buf ya) + Z.of_nat (length zsB) <= SHMAX) by (rewrite SHMAX_val; clear - LZB SHBB; try pose proof alloc_ceiling_val as ACV__; mlia).
    rewrite SHMAX_val in SHBz.
    assert (BSH : bytes_at rsegs m1 (sh (vb_buf ya)) zsB).
    { eapply (bytes_at_munch LPA); [exact BSH0| exact MU|]. intros a Ha. cbn. keeplia Ha SHBz GCE VEPlo LO CEIL ACV. }
    clear BSH0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (AOBJ1 : vsb_obj LPA A0 m1 SA ya true).
    { eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]. }
    hide DJS. hide DJB. hide DJfV. hide DJfS. hide DJfB. hide DSBA. hide_neqs.
    unfold vep_cells in VEPC. cbv delta [FRAME] in FR.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep.
    pose proof AOBJ1 as AO. vsb_open AO. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS NUL | dand4 VBUF as bs U8 LBS NUL | destruct VBUF as (bs & U8 & LBS & NUL) ]). unfold vsb_cells in VSBC. fold_cl_segs.
    pose proof (mod8_of_mod16 SA SA16) as SA8.
    icall (VSB_data_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 SA ya lo)
      by (try rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; unfold kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV
                | (eexists _, _; split; [exact SHS| try (generalize alloc_ceiling_val); clear - SA8 SAhi SAlo ACV; try pose proof alloc_ceiling_val as ACV__; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | exact CE1
                | exact SA8
                | exact ST
                | assumption
                | keeplia SAlo | keeplia SAhi | keeplia LO | exact CEIL ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => try clear ST; rename X into ST end.
    (* [comment removed for export] *)
    (first [ pose proof ((cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl))) as dR_21; dex1 dR_21 as z; dand4 dR_21 as ZLE Ebs NZS LZ | pose proof ((cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl))) as dR_21; dand5 dR_21 as z ZLE Ebs NZS LZ | destruct (cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl)) as (z & ZLE & Ebs & NZS & LZ) ]).
    unfold vsb_inv in VINV.
    pose proof (mod8_of_mod16 (vb_buf ya) BA16) as BA8.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?Z.mod_small in KU by (keeplia BAlo BAhi ACV). keeplia KU BAlo. } clear KU.
    (* [comment removed for export] *)
    lazymatch goal with BSHq : bytes_at _ ?mx (sh (vb_buf ya)) zsB |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof BSHq as BSHr; rewrite EzsB in BSHr end.
    zchk BSHr 1. clear BSHr.
    (* [comment removed for export] *)
    destruct (nth_error bs 0) as [b0|] eqn:Hn0; [| apply nth_error_None in Hn0; exfalso; try (generalize alloc_ceiling_val); clear - Hn0 LBS VINV; try pose proof alloc_ceiling_val as ACV__; cbn in Hn0; lia].
    pose proof (byte_range b0) as RB0.
    lazymatch goal with U8q : u8arr _ ?mx (vb_buf ya) bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_read rsegs mx (vb_buf ya) bs 0 b0 (Z_to_bv 64 (vb_buf ya)) U8q Hn0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    zstep. clear RD.
    (* [comment removed for export] *)
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, VEPCq : rw_cells _ ?mx VEP _, CNTq : rw_cells _ ?mx (h_ff H + 1336) _,
                        STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx |- evt _ ?P (MS _ _ _ _ _ ?mx _) =>
      assert (TAILS : forall (pc' : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                (pc' = 0x8f110 \/ pc' = 0x8f0f0) ->
                evt rsegs P (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 224))
                                 a0' a1' a2' a3' a4' a5' a6' a7'
                                 (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880)) (Z_to_bv 64 ((VEP + 224) / 8 + 2147450880)) (Z_to_bv 64 VEP)
                                 xs5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 pc') fc None mx (seg_rom rsegs)));
      [ intros pc' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' [-> | ->];
        [ eapply (seg_lwserr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx j40 cnt); [exact EVI| exact MIq| exact STq| exact FRq| exact VEPCq| exact CNTq| exact MU| exact WM]
        | eapply (seg_accept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx j40 cnt); [exact EVI| exact MIq| exact STq| exact FRq| exact VEPCq| exact CNTq| exact MU| exact WM] ]
      | ]
    end.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *) apply TAILS. right. reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CEq : cenv mx) by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]);
      pose proof (got_vct_cell mx (proj1 CEq)) as GOTT; unfold GOTA_vct in GOTT;
      pose proof (vct_shadowA mx (proj1 CEq)) as VSH end.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (Z0 : z <> 0%nat).
    { intros E. rewrite E in Ebs. cbn in Ebs. rewrite Ebs in Hn0. cbn in Hn0. injection Hn0 as E0. apply KZ. rewrite <- E0. reflexivity. }
    assert (HzN : nth_error bs z = Some (Z_to_bv 8 0)).
    { rewrite Ebs at 1. rewrite nth_error_app2 by lia. rewrite LZ, Nat.sub_diag. reflexivity. }
    replace (vb_buf ya + 1) with (vb_buf ya + 0 + 1) by lia.
    replace (Z_to_bv 64 (vb_buf ya)) with (Z_to_bv 64 (vb_buf ya + 0)) by (f_equal; lia).
    lazymatch goal with U8q : u8arr _ ?mx (vb_buf ya) bs, BSHq : bytes_at _ ?mx (sh (vb_buf ya)) zsB, MIq : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof BSHq as BSHr; rewrite EzsB in BSHr;
      eapply evt_cut;
      [ eapply (lws_loop (Z.to_nat (vb_size ya)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (vb_buf ya) bs (Z.to_nat (vb_size ya / 8)) 0 (Z.of_nat z) b0);
        [ vm_compute; reflexivity | exact U8q | exact MIq | exact VSH | exact BSHr | exact BA8 | keeplia BAlo
        | clear - LBS VINV; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by mlia; mlia | rewrite LBS; exact BAhi
        | exact Hn0 | clear; lia | exact KZ | rewrite Nat2Z.id; exact HzN | try (generalize alloc_ceiling_val); clear - Z0; try pose proof alloc_ceiling_val as ACV__; lia
        | rewrite Z2Nat.id by (try (generalize alloc_ceiling_val); clear - VINV; try pose proof alloc_ceiling_val as ACV__; lia); pose proof (nth_error_lt _ _ _ HzN) as LZ'; try (generalize alloc_ceiling_val); clear - LZ' LBS; try pose proof alloc_ceiling_val as ACV__; lia ]
      | clear BSHr ]
    end.
    cbv beta. intros ms' POST. (first [ dex5 POST as a0' a1' a2' a5' pc'; destruct POST as [-> PC'] | dand7 POST as a0' a1' a2' a5' pc' -> PC' | destruct POST as (a0' & a1' & a2' & a5' & pc' & -> & PC') ]).
    apply TAILS. exact PC'.
  Qed.
End S.
End A_vebxj.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve4jd.A_ve2b5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve4jd.A_vebxj.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK in H.


Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK in H.

(* [comment removed for export] *)
Definition A_src : Z := 0x23b60.
Definition STR_src : list byte := [Z_to_bv 8 115; Z_to_bv 8 114; Z_to_bv 8 99; Z_to_bv 8 61].
Definition A_onerror : Z := 0x23b80.
Definition STR_onerror : list byte :=
  [Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 101; Z_to_bv 8 114; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 61].
Lemma str_src_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_src (STR_src ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_src; lia| cbn; unfold A_src; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma str_onerror_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_onerror (STR_onerror ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_onerror; lia| cbn; unfold A_onerror; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma str_src_nonul : ~ In (Z_to_bv 8 0) STR_src.
Proof. cbv. intuition discriminate. Qed.
Lemma str_onerror_nonul : ~ In (Z_to_bv 8 0) STR_onerror.
Proof. cbv. intuition discriminate. Qed.
Lemma sign_src_src : strcmp_sign STR_src STR_src = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma sign_src_onerror : strcmp_sign STR_src STR_onerror = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma sign_onerror_onerror : strcmp_sign STR_onerror STR_onerror = 0.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HMH : vv Fmatch_hit = vi_tbl_attr_include VIA \/ vv Fmatch_hit = vi_tbl_attr_include VIA + 16.
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis ANZ : vv Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : vv Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fattr_vsb /\ vv Finclude_src <> vb_buf ya /\
                   vb_buf yi <> vv Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.   (* [comment removed for export] *)
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vi' : option vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q ->
      frames_same A0 A' -> a_tinycred A' = a_tinycred A0 -> a_seccred A' = a_seccred A0 -> a_primcred A' = a_primcred A0 (* [comment removed for export] *) ->
      (  (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Finclude_src (vv Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                    (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0)
      \/ (* [comment removed for export] *) (vi <> None /\ vv' = fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    (match vi with Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                              a_livebytes A' = a_livebytes A0 - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A0 - 4
                                 | None => False end) /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> r <> vv Finclude_src ->
                               r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))
      \/ (* [comment removed for export] *) (vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) /\ exists ic, bool01 ic /\ vv' = fupd (fupd vv Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                    a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                    a_livebytes A' = a_livebytes A0 - 40 - vb_size ya /\ a_nlive A' = a_nlive A0 - 2 /\
                    (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A0 r))) ->
      match vi' with
      | None => vv' Finclude_src = 0
      | Some yi => vv' Finclude_src <> 0 /\ vsb_obj LPA A' v' (vv' Finclude_src) yi true /\ vb_error yi = 0
      end ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             nowhere (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let SA := vv Fattr_vsb.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Definition FRAME (j : list byte) : list cell :=
    [CB 56 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HMH (conj HIC (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB
      (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO K))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ESA : SA = vv Fattr_vsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Local Ltac strcmp_globals Aa Sa ka STRa NNa Ab Sb kb STRb NNb :=
    lazymatch goal with CE0 : cenv (aview A0 m0), MU : munch _ (aview A0 m0) ?mq, ST : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      let CEq := fresh "CEq" in let R1 := fresh "R1" in let R2 := fresh "R2" in
      let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
      lazymatch goal with VEPlo : 17594333495296 <= VEP, GCE : context [ (8 * (sh (h_ff H) - 2147450880))%Z ], SPR : 0 <= bv_unsigned sp < _ |- _ =>   (* [comment removed for export] *)
      assert (CEq : cenv mq) by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]);
      assert (R1 : range_ok mq Aa (Z.of_nat (length Sa) + 1))
        by (eapply (global_range_ok _ Aa ka 32); [exact CEq| gdesc_in| lia| cbn; lia| lia| unfold pa_static; cbv delta [A_src A_onerror]; cbn; lia| unfold pa_static; cbv delta [A_src A_onerror]; cbn; lia]);
      assert (R2 : range_ok mq Ab (Z.of_nat (length Sb) + 1))
        by (eapply (global_range_ok _ Ab kb 32); [exact CEq| gdesc_in| lia| cbn; lia| lia| unfold pa_static; cbv delta [A_src A_onerror]; cbn; lia| unfold pa_static; cbv delta [A_src A_onerror]; cbn; lia]);
      icall (strcmp_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq Sa Sb [] [] lo)
        by (try rewrite !unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; unfold STRCMP_ICPT_STACK;
            first [ apply STRa; assumption
                  | apply STRb; assumption
                  | exact NNa | exact NNb
                  | exact (strcmp_icpt_cells_of_consts _ (proj1 CEq))
                  | exact ST
                  | exact CEIL
                  | exact R1 | exact R2
                  | assumption
                  | (left; cbv delta [A_src A_onerror]; cbn; keeplia LO CEIL ACV)
                  | (cbn; lia)
                  | keeplia LO ]);
      clear R1 R2 CEq ACV;
      repeat match goal with Hb : bytes_at _ _ Aa _ |- _ => clear Hb | Hb : bytes_at _ _ Ab _ |- _ => clear Hb end
      end end.

  (* [comment removed for export] *)
  Local Ltac lit_chk SRC X :=
    zstep; zstep; shadow_addr_at SRC X 8;
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end;
    zstep;
    let K0 := fresh "K0" in
    zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 W SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 H vi ya q tag vv"] Lemma main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) -> a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 0 ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 vep_do_include_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI -> -> ST. unfold vep_do_include_entry.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & VEPC & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand7 dR_1 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    pose proof HENV as (_ & GLOB & _ & _). (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as _ _ _ [cnt CNT] | pose proof GLOB as (_ & _ & _ & [cnt CNT]) ]). fold_cl_segs. unfold h_vsc in CNT.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    pose proof (map_cells_of_consts _ (proj1 CE0)) as MC. fold_aview. open_map_cells MC.
    hide_neqs.
    pose proof (munch_refl W (aview A0 m0)) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    unfold vep_cells in VEPC.
    ago AINV00. fold_cl_segs.
    carve_frame 160%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT; [exfalso; try (generalize alloc_ceiling_val); clear - KT; try pose proof alloc_ceiling_val as ACV__; lia|]. clear KT.
    zstep. if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT.
    (* [comment removed for export] *)
    lazymatch goal with X : bytes_at _ ?mq (sh VEP) zsV |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into SHV end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (CE1 : cenv mq) by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]);
      (first [ pose proof ((img_tabs_of_consts mq (proj1 CE1))) as dR_3; dand3 dR_3 as _ TBL _ | pose proof (img_tabs_of_consts mq (proj1 CE1)) as (_ & TBL & _) ]);
      cbn [mtab_cells tbl_attr_include me_ptr me_svar] in TBL; unfold TBL_attr_include in TBL;
      pose proof (global_shadow_pat mq 0xad280 48 96 (proj1 CE1) ltac:(gdesc_in)) as SHT
    end.
    cbn [vi_tbl_attr_include VIA] in HMH. unfold TBL_attr_include in HMH.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?Z.mod_small in KU by (keeplia VEPlo VEPhi ACV). keeplia KU VEPlo. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [keeplia VEPlo| exact V8]. } clear KU.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep.
    pose proof HMH as [EMH|EMH]; rewrite EMH.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. vm_compute. congruence. } clear KU.
      zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. vm_compute. congruence. } clear KU.
      (* [comment removed for export] *)
      lit_chk SHT 0xad280. zstep. zstep. zstep. zstep. zstep.
      try clear SHT. strcmp_globals A_src STR_src 5 str_src_at str_src_nonul A_src STR_src 5 str_src_at str_src_nonul.
      rewrite sign_src_src.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT.
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep.
      assert (EV : (exists yi, vi = Some yi) \/ vi = None) by (clear; destruct vi; [left; eexists; reflexivity | right; reflexivity]).
      destruct EV as [[yi EVI]|EVI].
      + (* [comment removed for export] *)
        pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand3 HVI' as INZ IOBJ _ | destruct HVI' as (INZ & IOBJ & _) ]).
        (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_5; dand4 dR_5 as _ SIlo SIhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (_ & SIlo & SIhi & _) ]). unfold kHighMemBeg in SIlo. all_app_facts.
        zstep. if_cases KT; zify_cond KT; [exfalso; apply INZ; clear - KT SIlo SIhi ACV; try pose proof alloc_ceiling_val as ACV__; mlia|]. clear KT.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        lazymatch goal with FRq : rw_cells _ mq (bv_unsigned sp + -160) _, STq : stk _ mq lo _, MIq : mem_inv _ mq, VEPCq : rw_cells _ mq VEP _, CNTq : rw_cells _ mq (h_ff H + 1336) [CB 16 ?c] |- _ =>
          eapply (seg_src2 VEP vv tag q ya vi H lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T AINV00 VOBJ VBASE HENV HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 WMAP00 CEIL LO K yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ c);
          [exact EVI| exact MIq| exact STq| exact FRq| exact VEPCq| exact CNTq| exact MU| exact WM]
        end end.
      + (* [comment removed for export] *)
        pose proof HVI as ISRC0. rewrite EVI in ISRC0. rewrite ISRC0.
        zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        lazymatch goal with FRq : rw_cells _ mq (bv_unsigned sp + -160) _, STq : stk _ mq lo _, MIq : mem_inv _ mq, VEPCq : rw_cells _ mq VEP _, CNTq : rw_cells _ mq (h_ff H + 1336) [CB 16 ?c] |- _ =>
          eapply (seg_src0 VEP vv tag q ya vi H lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T AINV00 VOBJ VBASE HENV HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 WMAP00 CEIL LO K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ c);
          [exact EVI| exact MIq| exact STq| exact FRq| exact VEPCq| exact CNTq| exact MU| exact WM]
        end end.
    - (* [comment removed for export] *)
      replace (709248 + 16) with 709264 by reflexivity.
      (* [comment removed for export] *)
      zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. vm_compute. congruence. } clear KU.
      zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. vm_compute. congruence. } clear KU.
      (* [comment removed for export] *)
      lit_chk SHT 0xad290. zstep. zstep. zstep. zstep. zstep.
      try clear SHT. strcmp_globals A_src STR_src 5 str_src_at str_src_nonul A_onerror STR_onerror 9 str_onerror_at str_onerror_nonul.
      rewrite sign_src_onerror.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT; [exfalso; try (generalize alloc_ceiling_val); clear - KT; try pose proof alloc_ceiling_val as ACV__; lia|]. clear KT.
      zstep. zstep. zstep. zstep.
      strcmp_globals A_onerror STR_onerror 9 str_onerror_at str_onerror_nonul A_onerror STR_onerror 9 str_onerror_at str_onerror_nonul.
      rewrite sign_onerror_onerror.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with FRq : rw_cells _ mq (bv_unsigned sp + -160) _, STq : stk _ mq lo _, MIq : mem_inv _ mq, VEPCq : rw_cells _ mq VEP _, CNTq : rw_cells _ mq (h_ff H + 1336) [CB 16 ?c] |- _ =>
        eapply (seg_onerr VEP vv tag q ya vi H lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T AINV00 VOBJ VBASE HENV HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 WMAP00 CEIL LO K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ c);
          [exact EMH| exact MIq| exact STq| exact FRq| exact VEPCq| exact CNTq| exact MU| exact WM]
      end end.
  Qed.
End S.

(* [comment removed for export] *)
Section T.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  #[using="AI16"] Theorem vep_do_include_attr_ok : vep_do_include_attr_stmt.
  Proof.
    unfold vep_do_include_attr_stmt. intros until T. cbv zeta.
    intros AINV MI A0e A1e VOBJ VBASE HENV HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 ST CEIL LO K.
    eapply (main VEP vv tag q ya vi H lo); try eassumption.
    eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL| pose proof (zr_word sp) as SPR; unfold inr64 in SPR; lia| unfold_stacks; lia].
  Qed.
End T.
