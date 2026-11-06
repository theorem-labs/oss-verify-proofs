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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpa09.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VStbd A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.

Module A_VE1nh.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma frames_aged_le {AI : AsanAlloc LPA} : forall A A' a0 a1 b0 b1,
  frames_aged A A' a0 a1 -> (a0 <= b0)%nat -> (a1 <= b1)%nat -> frames_aged A A' b0 b1.
Proof.
  intros A A' a0 a1 b0 b1 [AG NN] H0 H1. split; [|exact NN].
  intros ff k age HF. (first [ pose proof ((AG ff k age HF)) as dR_1; dex1 dR_1 as d; destruct dR_1 as [E D] | pose proof ((AG ff k age HF)) as dR_1; dand3 dR_1 as d E D | destruct (AG ff k age HF) as (d & E & D) ]). exists d. split; [exact E|].
  unfold fbound in *. destruct (Z.eqb k 0); [lia|]. destruct (Z.eqb k 1); lia.
Qed.

End CEIL.

Lemma vsb_extendsize_le : forall sz, 16 <= sz <= 2^40 -> vsb_extendsize sz <= sz + 4096.
Proof.
  intros sz Hsz. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge].
  - pose proof (vsb_dbl_le 9 16 sz ltac:(lia)) as C. lia.
  - pose proof (Z.mul_div_le (sz + 4095) 4096 ltac:(lia)) as X. lia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let jst := jst H VEP wa N DATA v0 tag q vv0 va vi lo ra sp s0 s1 s2 s3 s4 s5 s6 m0 md0 A0.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  (* [comment removed for export] *)
  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Local Definition T5' := T5 (* [comment removed for export] *) HMC HEC HCB HDS HFI HLN H VEP wa n N DATA v0 tag q vv0 va vi lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                     AINV00 PW HENV0 TP SP16 CEIL LO LD0 N0 DRANGE NEDV NEDS NPB LBM0 NLV0 SCC0 PCC0 FY0 K.

  (* [comment removed for export] *)
  #[using="K NPB PW S T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp sp ra lo q tag v0 DATA N n wa VEP H AI Clg"] Lemma world_bytes_ge : 56 <= world_bytes vv0 va vi.
  Proof.
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & _ & _ & VA & VI).
    pose proof (proj1 (proj2 VO)) as (SZ & _). unfold world_bytes.
    destruct va as [x|]; [destruct VA as (VX & _); pose proof (proj1 (proj2 VX)) as (SX & _)|];
    (destruct vi as [[y fy]|]; [destruct VI as (VY & _); pose proof (proj1 (proj2 VY)) as (SY & _)|]); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma jst_rebase : forall A m md m1 md1 v vv fin lenb fa cr,
    jst A m md v vv fin lenb fa cr -> ainv A m1 md1 -> aview A m1 = aview A m -> same_but_materialized md md1 ->
    jst A m1 md1 v vv fin lenb fa cr.
  Proof.
    intros A m md m1 md1 v vv fin lenb fa cr J AI1 EV SB. pose proof (as_minv LPA A _ _ (proj1 J)) as [_ MH].
    (first [ dand4 J as AIm MIm MDF REST | destruct J as (AIm & MIm & MDF & REST) ]). split; [exact AI1|]. split; [rewrite EV; exact MIm|].
    split; [eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SB| exact MH]]|].
    unfold jst, A_VEr47.jst in *. rewrite EV. exact REST.
  Qed.

  #[using="S"] Lemma jst_weaken : forall A m md v vv fin lenb fa cr lenb' fa' cr',
    jst A m md v vv fin lenb fa cr -> lenb <= lenb' -> (fa <= fa')%nat -> cr <= cr' -> jst A m md v vv fin lenb' fa' cr'.
  Proof.
    intros A m md v vv fin lenb fa cr lenb' fa' cr' J HL HF HC.
    (first [ dand29 J as AIm MIm MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AIm & MIm & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold jst, A_VEr47.jst. repeat (split; [assumption|]).
    split; [lia|]. repeat (split; [assumption|]). split; [eapply frames_aged_le; [exact FA| exact HF| lia]|].
    split; [exact LB|]. split; [lia| exact CF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 S HLN HFI HDS HCB HEC HMC"] Lemma T4 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs4 xs5 : word) A m md v vv lenb cr,
    jst A m md v vv false lenb 2%nat cr -> lenb <= 10 * N -> cr <= FIN_CRED N - 2 -> vep_cnt v n ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 24))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (VEP + 144)) (Z_to_bv 64 (VEP + 304)) xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x908b0) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until cr. intros J LB10 CR CNT0. prelims.
    pose proof J as J0.
    (first [ dand29 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold NMAX in CBX.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & NN0 & NNM & VP0 & _ & _ & APART0 & _). unfold NMAX in NNM.
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (first [ pose proof (CNT0) as dR_5; dand7 dR_5 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    pose proof world_bytes_ge as WB0.
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_6; dand4 dR_6 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vv false AINV VOBJ)) as dR_9; dand11 dR_9 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_10; dand6 dR_10 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_13; dand7 dR_13 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint LPA A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint (Clg:=Clg) LPA A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (first [ pose proof ((live_geomP LPA A m md DATA _ AINV LD)) as dR_14; dand7 dR_14 as _ _ Dlo Dhi _ _ _ | pose proof (live_geomP LPA A m md DATA _ AINV LD) as (_ & _ & Dlo & Dhi & _ & _ & _) ]).
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh S 40 AINV HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh wa 40 AINV HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfS, DJfB, DJfV, DJfW.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vv) (vb_size vv) ltac:(lia) ltac:(lia) ltac:(lia)) as SHB. rewrite SHMAX_val in SHB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHS. rewrite SHMAX_val in SHS.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (cenv_intro A m md AINV) as CEx.
    (first [ pose proof (VB) as dR_15; dand5 dR_15 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]). cbn [vi_cb vi_url VIA] in EVCB, EVURL.
    pose proof VEPC as VEPCF. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    hide DSB. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB. hide DJfS. hide DJfB. hide DJfV. hide DJfW. hide BUF0. hide Verr. hide BEF0. hide_neqs.
    pose proof ST as STw. clear ST.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW.
    { (* [comment removed for export] *)
      apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP). intros m1 md1 AINV1 EV SBM HID.
      eapply (T5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v vv lenb cr); [| lia].
      eapply jst_weaken; [eapply jst_rebase; [exact J0| exact AINV1| exact EV| exact SBM]| lia| lia| lia]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0.
    zstep. zstep. zstep. zstep. zstep. zstep.
    unhide VEPCF. unhide DJS. unhide DJB. (first [ pose proof (HENV) as dR_16; dand4 dR_16 as _ GLOB HOBJ HSH | pose proof HENV as (_ & GLOB & HOBJ & HSH) ]).
    icall (HCB VEP v tag q H 0 lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact VEPCF
       | |- length _ = _ => exact TAG8
       | |- vep_pads_wf _ => exact PADS
       | |- hobj_ok _ _ _ _ => exact HOBJ
       | |- hshadow _ _ _ => exact HSH
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => exact CEx
       | |- shadowed _ _ _ _ => exists VEP, 312; split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|]; lia
       | |- stk _ _ _ _ => exact STw
       | |- mem_inv _ _ => assumption
       | |- _ => try unhide DJfV; unfold kHighMemBeg, HFSIZE, CB_STACK; lia
       end).
    clear GLOB HOBJ HSH. try clear STw. try clear VEPCF. try clear VEPC. hide DJS. hide DJB.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    lazymatch goal with X : rw_cells _ ?mq VEP (vep_cells _ tag q) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into VEPC1 end.
    rewrite (vep_cells_ext v (fupd v Fcb_x (v Fcb_x + 0)) tag q (fupd_cbx0 v)) in VEPC1.
    pose proof VEPC1 as VEPC. pose proof VEPC1 as VEPCF. clear VEPC1. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP in VEPC.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 4 1.
    zstep. unhide BLM. rewrite (sx32_small (v Flast_mark)) by (clear - BLM; try pose proof alloc_ceiling_val as ACV__; destruct BLM as [E|E]; rewrite E; lia).
    zstep. zstep. zstep.
    astop AINV MU WM CFP.
    unhide VEPCF. unhide DJS. unhide DJB. unhide NESV. unhide NEbV.
    pose proof (vsb_extendsize_le (vb_size vv + 9) ltac:(unfold EXT_MAX in *; lia)) as EXL.
    eapply (HEC VEP v tag q vv (v Fcb_x - v Fo_last) (v Flast_mark) lo);
      [ exact AINV0 | assumption | reflexivity | first [reflexivity | f_equal; lia] | reflexivity
      | lia | lia | lia | exact BLM
      | split; [exact VLV|]; split; [exact VEPCF|]; split; [exact TAG8| exact PADS]
      | exact EVDZ
      | rewrite EVSB; eapply vsb_obj_munch; [exact VOBJ| exact MU| exact WM| intros a__ Ha__; cbn; lia]
      | rewrite EVSB; exact (not_eq_sym NESV) | exact (not_eq_sym NEbV)
      | unfold EXT_MAX; lia
      | unfold FIN_LIVE in LBM0; lia
      | pose proof (proj1 (proj2 BC)) as BCn; keeplia BCn NLV0 WNL
      | pose proof (proj2 (proj2 BC)) as BCs; keeplia BCs SCC0 CR
      | pose proof (proj2 (proj2 (proj2 BC))) as BCp; pose proof (vsb_ppot_range vv) as PPR; unfold PPOT_CAP in *; keeplia BCp PCC0 PPR (* [comment removed for export] *)
      | eapply (frames_young_aged A0 A 2%nat 0%nat 2%nat 0%nat); [exact FY0| exact FA| exact (frames_aged_back _ _ _ _ FA)]
      | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact STq | exact CEIL
      | rewrite unsigned_lit by lia; ufs; lia | ].
    clear VEPC. hide NESV. hide NEbV.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc vv1 vr1. cbv zeta.
    intros AINV1 MI1 MDF1 ST1 VOBJ1 CASES SOBJ1 LEN1 SZ1 REL1 LIVEq FA1 LB1 TC1 NL1 SC1 PC1 CF1.   (* [comment removed for export] *)
    cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VOBJ1, CASES, SOBJ1, CF1.
    rewrite unsigned_lit in ST1, CF1 by lia. ufs. rewrite EVSB in SOBJ1, CF1.
    replace (ret_pc (Z_to_bv 64 0x90950)) with (Z_to_bv 64 0x90950) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (VK : forall f, f <> Fcrc -> f <> Fo_crc -> f <> Fo_total -> vv1 f = v f).
    { destruct CASES as [(_ & -> & _) | (_ & c & ->)]; intros f F1 F2 F3.
      - unfold fupd. destruct (vf_beq f Fcb_x) eqn:E; [apply vf_beq_eq in E; subst f; lia| reflexivity].
      - rewrite !fupd_other by assumption. unfold fupd. destruct (vf_beq f Fcb_x) eqn:E; [apply vf_beq_eq in E; subst f; lia| reflexivity]. }
    (* [comment removed for export] *)
    assert (NEbV1 : vb_buf vr1 <> VEP).
    { destruct REL1 as [E|[E _]]; [rewrite E; unhide NEbV; exact NEbV|]. intros X. rewrite X, VLV in E. discriminate E. }
    assert (NEbw1 : vb_buf vr1 <> wa).
    { destruct REL1 as [E|[E _]]; [rewrite E; unhide NEbw; exact NEbw|]. intros X. rewrite X, LWA in E. discriminate E. }
    unhide NEbV. unhide NEbw. unhide NEwB.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NEbV) (not_eq_sym NEbV1)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwB (not_eq_sym NEbw1)); exact LWA).
    assert (NEbD : vb_buf vv <> DATA).
    { unhide BUF0. destruct BUF0 as [E|E]; intros X; rewrite X in E; [exact (NPB E)| rewrite LD0 in E; discriminate E]. }
    assert (NEbD1 : vb_buf vr1 <> DATA).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbD|]. intros X. rewrite X, LD in E. discriminate E. }
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NEbD) (not_eq_sym NEbD1)); exact LD).
    assert (LS1 : a_live A1 S = Some 40) by exact (proj1 (proj2 (proj2 SOBJ1))).
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A A1); [exact AINV0| exact CF1| | keeplia CEIL LO| |].
      - eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|].
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; keeplia Ha__ DJfV GHI ACV CEIL LO VEPlo SHF.
      - intros ff k age HF. (first [ pose proof ((proj1 FA1 ff k age HF)) as dR_17; dex1 dR_17 as d; destruct dR_17 as [E _] | pose proof ((proj1 FA1 ff k age HF)) as dR_17; dand3 dR_17 as d E _ | destruct (proj1 FA1 ff k age HF) as (d & E & _) ]). exists (age + d)%nat. exact E.
      - intros a [X|[X|X]].
        + exists VEP, 312. split; [exact VLV|]. left. unfold blk in X. keeplia X.
        + exists (vb_buf vv), (vb_size vv). split; [exact VLB|]. unfold newblk, blk in X. keeplia X.
        + exists S, 40. split; [exact VLS|]. left. keeplia X. }
    assert (WS1_1 : ws1_obj LPA H A1 (aview A1 mc) wa VEP).
    { eapply ws1_obj_ccall; [exact AINV0| exact (proj1 HENV)| exact CF1| | keeplia CEIL LO| exact LWA1| exact LVEP1|].
      - eapply ws1_obj_munch; [exact WS1| exact MU| exact WM|]. intros a__ Ha__. unfold h_ws, h_wsbuf in *. cbn.
        keeplia Ha__ DJfV DJ3 GHI ACV CEIL LO WAhi.
      - intros a Ha X. unfold h_ws, h_wsbuf, newblk, blk in *. keeplia Ha X DJ1 DJ2 DJ3 DJfV DJfS DJfB SHB WAlo GCE. }
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ ma (bv_unsigned sp - 64) 64 AINV0 ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF;
      lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
        apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 fa fcs) in FR;
        [ | exact CRF
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; try (generalize alloc_ceiling_val); clear - ACV CEIL LO VEPhi Bhi Shi SHB SPR VEPlo Blo Slo; try pose proof alloc_ceiling_val as ACV__;
            split; [lia|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ] end;
      clear CRF
    end.
    (* [comment removed for export] *)
    eapply (T5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mc mdc vv1 vr1 (10 * N + 9) (cr + 2)); [| keeplia CR].
    split; [exact AINV1|]. split; [exact MI1|].
    split; [eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]|].
    split; [exact ST1|]. split; [exact FR|]. split; [exact HENV1|]. split; [exact VOBJ1|].
    split. { unfold vep_base. rewrite !VK by discriminate. exact VB. }
    split; [rewrite VK by discriminate; exact EVSB|]. split; [rewrite VK by discriminate; exact EIS|]. split; [rewrite VK by discriminate; exact EAV|].
    split; [rewrite VK by discriminate; exact EST|]. split; [rewrite VK by discriminate; exact EEF|].
    split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; exact EVP|].
    split; [rewrite VK by discriminate; unfold NMAX; keeplia CBX|].
    split; [exact SOBJ1|]. split; [keeplia SZ1 SZB LEN1|]. split; [keeplia LEN1 LENB LB10|].
    split; [exact NEbV1|]. split; [exact NEbw1|]. split; [exact WS1_1|]. split; [exact LD1|].
    split. { intros p k L0 NS NP. rewrite (LIVEq p).
             - exact (LIVE0 p k L0 NS NP).
             - intros ->. unhide BUF0. destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0].
             - intros ->. destruct REL1 as [E|[E _]].
               + rewrite E in *. unhide BUF0. destruct BUF0 as [E2|E2]; [exact (NP E2)| rewrite E2 in L0; discriminate L0].
               + rewrite (LIVE0 _ _ L0 NS NP) in E. discriminate E. }
    split. { destruct REL1 as [E|[E _]]; [rewrite E; unhide BUF0; exact BUF0|].
             destruct (a_live A0 (vb_buf vr1)) as [k|] eqn:L0; [|right; reflexivity]. left.
             destruct (Classical_Prop.classic (parse_blocks v0 vv0 va vi (vb_buf vr1))) as [Y|NP]; [exact Y|]. exfalso.
             assert (NS1 : vb_buf vr1 <> S) by (intros X; clear - X E VLS ES; try pose proof alloc_ceiling_val as ACV__; congruence).
             rewrite (LIVE0 _ k L0 NS1 NP) in E. discriminate E. }
    split; [exact (frames_aged_trans A0 A A1 2%nat 0%nat 2%nat 0%nat FA FA1)|].
    split; [keeplia LB1 LB|].
    split. { split; [rewrite TC1; exact (proj1 BC)|]. split; [pose proof (proj1 (proj2 BC)) as BCn; keeplia NL1 BCn|].
             pose proof (proj2 (proj2 BC)) as BCs. pose proof (vsb_pot_diff vv vr1 ltac:(keeplia SZ1)) as PD.
             pose proof (proj1 (proj2 VOBJ)) as VINVv. unfold vsb_inv in VINVv.
             assert (PD2 : vsb_pot vr1 - vsb_pot vv <= 2) by (try (generalize alloc_ceiling_val); clear - PD SZ1 LEN1 VINVv; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia).
             split; [keeplia BCs SC1 PD2| keeplia BCs PC1]. }   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (MP1 : mapped (aview A1 mc) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST1 | exact FR | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      assert (CF2 : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8864
                      (fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ S <= a < S + 40) (newblk (vb_buf vr1) (vb_size vr1)) (aview A m) mb)
        by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) ma mb mb _ []);
            [ exact MU | | exact CF1 | keeplia ACV CEIL LO SPR | keeplia ACV CEIL LO SPR
            | intros a X; exact X | intros a X; left; exact X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
            | exact MP1 ];
            intros a Ha NO; cbn [outside] in NO;
            assert (CS : bv_unsigned sp - 8864 <= a < bv_unsigned sp \/ VEP <= a < VEP + 312) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia); clear NO;
            destruct CS as [X|X]; [left; exact X| right; left; unfold blk; split; [keeplia VEPlo| exact X]]);
      eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A m) mb CF CF2);
        [ ufs; keeplia SPR | ufs; keeplia SPR | exact MP1 | intros a X; exact X | | ]
    end.
    - (* [comment removed for export] *)
      intros a [X|[X|X]].
      + right. left. exact X.
      + left. right. exact X.
      + right. right. left. left. unfold newblk, blk. left. split; [keeplia Slo| exact X].
    - (* [comment removed for export] *)
      intros a [X|X].
      + left. left. exact X.
      + right. left. exact X.
  Qed.
End S.
End A_VE1nh.

Module A_VEt76.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VE1nh.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let jst := jst H VEP wa N DATA v0 tag q vv0 va vi lo ra sp s0 s1 s2 s3 s4 s5 s6 m0 md0 A0.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  (* [comment removed for export] *)
  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Local Definition T4' := T4 (* [comment removed for export] *) HMC HEC HCB HDS HFI HLN H VEP wa n N DATA v0 tag q vv0 va vi lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                     AINV00 PW HENV0 TP SP16 CEIL LO LD0 N0 DRANGE NEDV NEDS NPB LBM0 NLV0 SCC0 PCC0 FY0 K.

  (* [comment removed for export] *)
  #[using="K NPB PW S T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp sp ra lo q tag v0 DATA N n wa VEP H AI Clg"] Lemma world_bytes_ge : 56 <= world_bytes vv0 va vi.
  Proof.
    pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & _ & _ & VA & VI).
    pose proof (proj1 (proj2 VO)) as (SZ & _). unfold world_bytes.
    destruct va as [x|]; [destruct VA as (VX & _); pose proof (proj1 (proj2 VX)) as (SX & _)|];
    (destruct vi as [[y fy]|]; [destruct VI as (VY & _); pose proof (proj1 (proj2 VY)) as (SY & _)|]); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma jst_rebase : forall A m md m1 md1 v vv fin lenb fa cr,
    jst A m md v vv fin lenb fa cr -> ainv A m1 md1 -> aview A m1 = aview A m -> same_but_materialized md md1 ->
    jst A m1 md1 v vv fin lenb fa cr.
  Proof.
    intros A m md m1 md1 v vv fin lenb fa cr J AI1 EV SB. pose proof (as_minv LPA A _ _ (proj1 J)) as [_ MH].
    (first [ dand4 J as AIm MIm MDF REST | destruct J as (AIm & MIm & MDF & REST) ]). split; [exact AI1|]. split; [rewrite EV; exact MIm|].
    split; [eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SB| exact MH]]|].
    unfold jst, A_VEr47.jst in *. rewrite EV. exact REST.
  Qed.

  #[using="S"] Lemma jst_weaken : forall A m md v vv fin lenb fa cr lenb' fa' cr',
    jst A m md v vv fin lenb fa cr -> lenb <= lenb' -> (fa <= fa')%nat -> cr <= cr' -> jst A m md v vv fin lenb' fa' cr'.
  Proof.
    intros A m md v vv fin lenb fa cr lenb' fa' cr' J HL HF HC.
    (first [ dand29 J as AIm MIm MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AIm & MIm & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold jst, A_VEr47.jst. repeat (split; [assumption|]).
    split; [lia|]. repeat (split; [assumption|]). split; [eapply frames_aged_le; [exact FA| exact HF| lia]|].
    split; [exact LB|]. split; [lia| exact CF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 S HLN HFI HDS HCB HEC HMC"] Lemma T3 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs3 xs4 xs5 : word) A m md v vv,
    jst A m md v vv false (7 * N) 0%nat 0 -> vep_cnt v n ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 24))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (VEP + 144)) xs3 xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x9085c) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until vv. intros J CNT0. prelims.
    pose proof J as J0.
    (first [ dand29 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold NMAX in CBX.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & _ & _ & BEF0 & _ & NN0 & NNM & VP0 & _ & _ & APART0 & _). unfold NMAX in NNM.
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (first [ pose proof (CNT0) as dR_4; dand7 dR_4 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    pose proof world_bytes_ge as WB0.
    (first [ pose proof (VEPO) as dR_5; dand4 dR_5 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_6; dand7 dR_6 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_7; dand7 dR_7 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vv false AINV VOBJ)) as dR_8; dand11 dR_8 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_9; dand6 dR_9 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_12; dand7 dR_12 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint LPA A m md S 40 wa 40 AINV VLS LWA (not_eq_sym NEwS)) as DJ1.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) wa 40 AINV VLB LWA (not_eq_sym NEwB)) as DJ2.
    pose proof (as_live_disjoint (Clg:=Clg) LPA A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DJ3.
    (first [ pose proof ((live_geomP LPA A m md DATA _ AINV LD)) as dR_13; dand7 dR_13 as _ _ Dlo Dhi _ _ _ | pose proof (live_geomP LPA A m md DATA _ AINV LD) as (_ & _ & Dlo & Dhi & _ & _ & _) ]).
    assert (NEbD : vb_buf vv <> DATA).
    { destruct BUF0 as [E|E]; intros X; rewrite X in E; [exact (NPB E)| rewrite LD0 in E; discriminate E]. }
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh S 40 AINV HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh wa 40 AINV HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfS, DJfB, DJfV, DJfW.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vv) (vb_size vv) ltac:(lia) ltac:(lia) ltac:(lia)) as SHB. rewrite SHMAX_val in SHB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHS. rewrite SHMAX_val in SHS.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (first [ pose proof (VB) as dR_14; dand5 dR_14 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]). cbn [vi_cb vi_url VIA] in EVCB, EVURL.
    pose proof VEPC as VEPCF. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP, EVP in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    hide DSB. hide DJ1. hide DJ2. hide DJ3. hide DJS. hide DJB. hide DJfS. hide DJfB. hide DJfV. hide DJfW. hide BUF0. hide Verr. hide BEF0. hide_neqs.
    pose proof ST as STw. clear ST.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP). intros m1 md1 AINV1 EV SBM HID.
      eapply (T4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v vv (7 * N) 0); [| lia| unfold FIN_CRED; try (generalize alloc_ceiling_val); clear - NN0; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia| exact CNT0].
      eapply jst_weaken; [eapply jst_rebase; [exact J0| exact AINV1| exact EV| exact SBM]| lia| lia| lia]. }
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 4 1.
    zstep. unhide BLM. rewrite (sx32_small (v Flast_mark)) by (clear - BLM; try pose proof alloc_ceiling_val as ACV__; destruct BLM as [E|E]; rewrite E; lia).
    zstep. zstep.
    astop AINV MU WM CFP.
    unhide VEPCF. unhide DJS. unhide DJB. unhide NESV. unhide NEbV.
    pose proof (vsb_extendsize_le (vb_size vv + 9) ltac:(unfold EXT_MAX in *; lia)) as EXL.
    eapply (HMC VEP v tag q vv H (v0 Fver_p) (v Flast_mark) n [] lo);
      [ exact AINV0 | assumption | reflexivity | reflexivity | reflexivity | exact BLM
      | split; [exact VLV|]; split; [exact VEPCF|]; split; [exact TAG8| exact PADS]
      | exact VB
      | eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; keeplia Ha__ DJfV GHI ACV CEIL LO VEPlo SHF
      | exact BLM | exact CNT0 | keeplia NN0 | rewrite EVP; unfold NMAX; keeplia NN0 NNM
      | rewrite EVSB; eapply vsb_obj_munch; [exact VOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJS DJB Shi Bhi ACV CEIL LO]
      | rewrite EVSB; exact (not_eq_sym NESV) | exact (not_eq_sym NEbV)
      | unfold EXT_MAX; keeplia SZB LENB NN0 NNM
      | unfold FIN_LIVE in LBM0; keeplia LBM0 LB EXL WB0 SZB LENB NN0
      | pose proof (proj1 (proj2 BC)) as BCn; keeplia BCn NLV0 WNL
      | pose proof (proj2 (proj2 BC)) as BCs; unfold FIN_CRED in *; try (generalize alloc_ceiling_val); clear - BCs SCC0 NN0; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia
      | pose proof (proj2 (proj2 (proj2 BC))) as BCp; pose proof (vsb_ppot_range vv) as PPR; unfold PPOT_CAP in *; keeplia BCp PCC0 PPR (* [comment removed for export] *)
      | eapply (frames_young_aged A0 A 0%nat 0%nat 2%nat 0%nat); [eapply frames_young_le; [exact FY0| lia| lia]| exact FA| exact (frames_aged_back _ _ _ _ FA)]
      | rewrite EVP; split; [keeplia VP0|]; split; [cbn; keeplia VP0 ACV|]; intros i Hi; cbn in Hi; keeplia Hi
      | rewrite EVP; cbn; keeplia VP0
      | rewrite EVP; keeplia VP0 | keeplia VP0
      | rewrite EVP; exists DATA, N; split; [exact (as_live_shadow LPA _ _ _ DATA N AINV0 LD)|];
        (first [ pose proof ((live_geomP LPA A _ _ DATA _ AINV0 LD)) as dR_15; dand3 dR_15 as _ D16 _ | pose proof (live_geomP LPA A _ _ DATA _ AINV0 LD) as (_ & D16 & _) ]); split; [exact (mod8_of_mod16 DATA D16)|]; keeplia DRANGE Dlo Dhi
      | right; exists DATA, N; split; [exact LD|]; split; [exact N0|]; rewrite EVP; split; [keeplia DRANGE|]; split; [keeplia DRANGE|];
        split; [exact NEDV|]; split; [rewrite EVSB; exact NEDS| exact (not_eq_sym NEbD)]
      | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact STw | exact CEIL
      | rewrite unsigned_lit by lia; ufs; lia | ].
    clear VEPC. hide NESV. hide NEbV.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc vv1 vr1. cbv zeta.
    intros AINV1 MI1 MDF1 ST1 VOBJ1 VK1 EVP1 ELM1 EPD1 CNT1 CRC1 CRCP1 SOBJ1 LEN1 SZ1 REL1 LIVEq FA1 LB1 TC1 NL1 SC1 PC1 HENV1 BSEG1 CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by lia. ufs. rewrite EVSB in SOBJ1, CF1.
    replace (ret_pc (Z_to_bv 64 0x908b0)) with (Z_to_bv 64 0x908b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (n + (v0 Fver_p - v Fver_p)) with n in CNT1 by (rewrite EVP; lia).
    (* [comment removed for export] *)
    assert (NEbV1 : vb_buf vr1 <> VEP).
    { destruct REL1 as [E|[E _]]; [rewrite E; unhide NEbV; exact NEbV|]. intros X. rewrite X, VLV in E. discriminate E. }
    assert (NEbw1 : vb_buf vr1 <> wa).
    { destruct REL1 as [E|[E _]]; [rewrite E; unhide NEbw; exact NEbw|]. intros X. rewrite X, LWA in E. discriminate E. }
    unhide NEbV. unhide NEbw. unhide NEwB.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NEbV) (not_eq_sym NEbV1)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwB (not_eq_sym NEbw1)); exact LWA).
    assert (NEbD1 : vb_buf vr1 <> DATA).
    { destruct REL1 as [E|[E _]]; [rewrite E; exact NEbD|]. intros X. rewrite X, LD in E. discriminate E. }
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NEbD) (not_eq_sym NEbD1)); exact LD).
    assert (LS1 : a_live A1 S = Some 40) by exact (proj1 (proj2 (proj2 SOBJ1))).
    (* [comment removed for export] *)
    assert (WS1_1 : ws1_obj LPA H A1 (aview A1 mc) wa VEP).
    { eapply ws1_obj_ccall; [exact AINV0| exact (proj1 HENV)| exact CF1| | keeplia CEIL LO| exact LWA1| exact LVEP1|].
      - eapply ws1_obj_munch; [exact WS1| exact MU| exact WM|]. intros a__ Ha__. unfold h_ws, h_wsbuf in *. cbn.
        keeplia Ha__ DJfV DJ3 GHI ACV CEIL LO WAhi.
      - intros a Ha X. unfold h_ws, h_wsbuf, newblk, blk in *. keeplia Ha X DJ1 DJ2 DJ3 DJfV DJfS DJfB SHB WAlo GCE. }
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ ma (bv_unsigned sp - 64) 64 AINV0 ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF;
      lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
        apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 fa fcs) in FR;
        [ | exact CRF
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; try (generalize alloc_ceiling_val); clear - ACV CEIL LO VEPhi Bhi Shi SHB SPR VEPlo Blo Slo; try pose proof alloc_ceiling_val as ACV__;
            split; [lia|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ] end;
      clear CRF
    end.
    (* [comment removed for export] *)
    eapply (T4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mc mdc vv1 vr1 (10 * N) 2); [| keeplia NN0| unfold FIN_CRED; try (generalize alloc_ceiling_val); clear - NN0; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia| exact CNT1].
    split; [exact AINV1|]. split; [exact MI1|].
    split; [eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]|].
    split; [exact ST1|]. split; [exact FR|]. split; [exact HENV1|]. split; [exact VOBJ1|].
    split. { unfold vep_base. rewrite !VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]). exact VB. }
    split; [rewrite VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]); exact EVSB|]. split; [rewrite VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]); exact EIS|].
    split; [rewrite VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]); exact EAV|]. split; [rewrite VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]); exact EST|].
    split; [rewrite VK1 by (cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [exact X | discriminate X]); exact EEF|].
    split; [rewrite ELM1; exact BLM|]. split; [rewrite EVP1; reflexivity|].
    split; [unfold NMAX, vep_cnt in *; keeplia CNT1 NN0 NNM|].
    split; [exact SOBJ1|]. split; [keeplia SZ1 SZB LEN1|]. split; [unfold vep_cnt in *; keeplia LEN1 LENB CNT0 CNT1 NN0|].
    split; [exact NEbV1|]. split; [exact NEbw1|]. split; [exact WS1_1|]. split; [exact LD1|].
    split. { intros p k L0 NS NP. rewrite (LIVEq p).
             - exact (LIVE0 p k L0 NS NP).
             - intros ->. unhide BUF0. destruct BUF0 as [E|E]; [exact (NP E)| rewrite E in L0; discriminate L0].
             - intros ->. destruct REL1 as [E|[E _]].
               + rewrite E in *. unhide BUF0. destruct BUF0 as [E2|E2]; [exact (NP E2)| rewrite E2 in L0; discriminate L0].
               + rewrite (LIVE0 _ _ L0 NS NP) in E. discriminate E. }
    split. { destruct REL1 as [E|[E _]]; [rewrite E; unhide BUF0; exact BUF0|].
             destruct (a_live A0 (vb_buf vr1)) as [k|] eqn:L0; [|right; reflexivity]. left.
             destruct (Classical_Prop.classic (parse_blocks v0 vv0 va vi (vb_buf vr1))) as [Y|NP]; [exact Y|]. exfalso.
             assert (NS1 : vb_buf vr1 <> S) by (intros X; clear - X E VLS ES; try pose proof alloc_ceiling_val as ACV__; congruence).
             rewrite (LIVE0 _ k L0 NS1 NP) in E. discriminate E. }
    split; [exact (frames_aged_trans A0 A A1 0%nat 0%nat 2%nat 0%nat FA FA1)|].
    split; [keeplia LB1 LB|].
    split. { split; [rewrite TC1; exact (proj1 BC)|]. split; [pose proof (proj1 (proj2 BC)) as BCn; keeplia NL1 BCn|].
             pose proof (proj2 (proj2 BC)) as BCs. pose proof (vsb_pot_diff vv vr1 ltac:(keeplia SZ1)) as PD.
             pose proof (proj1 (proj2 VOBJ)) as VINVv. unfold vsb_inv in VINVv.
             assert (PD2 : vsb_pot vr1 - vsb_pot vv <= 2)
               by (unfold vep_cnt in *; try (generalize alloc_ceiling_val); clear - PD SZ1 LEN1 VINVv CNT0 CNT1 NN0 LENB; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia).
             split; [keeplia BCs SC1 PD2| keeplia BCs PC1]. }   (* [comment removed for export] *)
    assert (MP1 : mapped (aview A1 mc) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST1 | exact FR | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      assert (CF2 : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8864
                      (fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ S <= a < S + 40) (newblk (vb_buf vr1) (vb_size vr1)) ma mb)
        by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ ma ma mb mb [] []);
            [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF1 | keeplia ACV CEIL LO SPR | keeplia ACV CEIL LO SPR
            | intros a X; exact X | intros a X; left; exact X | apply munch_refl | intros a _ X; exfalso; apply X; exact I
            | exact MP1 ]);
      eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) ma mb CF CF2);
        [ ufs; keeplia SPR | ufs; keeplia SPR | exact MP1 | intros a X; exact X | | ]
    end.
    - intros a [X|[X|X]].
      + right. left. exact X.
      + left. right. exact X.
      + right. right. left. left. unfold newblk, blk. left. split; [keeplia Slo| exact X].
    - intros a [X|X].
      + left. left. exact X.
      + right. left. exact X.
  Qed.
End S.
End A_VEt76.

Module A_VEdm4.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VE1nh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEt76.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let jst := jst H VEP wa N DATA v0 tag q vv0 va vi lo ra sp s0 s1 s2 s3 s4 s5 s6 m0 md0 A0.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  (* [comment removed for export] *)
  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Local Definition T3' := T3 (* [comment removed for export] *) HMC HEC HCB HDS HFI HLN H VEP wa n N DATA v0 tag q vv0 va vi lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                     AINV00 PW HENV0 TP SP16 CEIL LO LD0 N0 DRANGE NEDV NEDS NPB LBM0 NLV0 SCC0 PCC0 FY0 K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma jst_rebase : forall A m md m1 md1 v vv fin lenb fa cr,
    jst A m md v vv fin lenb fa cr -> ainv A m1 md1 -> aview A m1 = aview A m -> same_but_materialized md md1 ->
    jst A m1 md1 v vv fin lenb fa cr.
  Proof.
    intros A m md m1 md1 v vv fin lenb fa cr J AI1 EV SB. pose proof (as_minv LPA A _ _ (proj1 J)) as [_ MH].
    (first [ dand4 J as AIm MIm MDF REST | destruct J as (AIm & MIm & MDF & REST) ]). split; [exact AI1|]. split; [rewrite EV; exact MIm|].
    split; [eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SB| exact MH]]|].
    unfold jst, A_VEr47.jst in *. rewrite EV. exact REST.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 S HLN HFI HDS HCB HEC HMC"] Lemma T2 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 xs2 xs3 xs4 xs5 : word) A m md v vv,
    jst A m md v vv false (7 * N) 0%nat 0 -> vep_cnt v n ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) xs1
                                    a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90754) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until vv. intros J CNT0. prelims.
    pose proof J as J0.
    (first [ dand29 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ SZB LENB NEbV NEbw WS1 LD LIVE0 BUF0 FA LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & SZB & LENB & NEbV & NEbw & WS1 & LD & LIVE0 & BUF0 & FA & LB & BC & CF) ]).
    unfold NMAX in CBX.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & [st EST0] & _ & _ & _ & _ & _ & _ & _ & _ & APART0 & _).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV _]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw _].
    (first [ pose proof (VEPO) as dR_4; dand4 dR_4 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_6; dand7 dR_6 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vv false AINV VOBJ)) as dR_7; dand11 dR_7 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vv false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_8; dand6 dR_8 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv) (vb_size vv) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_10; dand7 dR_10 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh S 40 AINV HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh wa 40 AINV HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfS, DJfB, DJfV, DJfW.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (cenv_intro A m md AINV) as CEx.
    pose proof (got_vsc_cell (aview A m) (proj1 CEx)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV. fold_cl_segs.
    (* [comment removed for export] *)
    (first [ pose proof (HENV) as dR_11; dand4 dR_11 as _ GLOB HOBJ HSH | pose proof HENV as (_ & GLOB & HOBJ & HSH) ]).
    (first [ pose proof (HSH) as dR_12; dand10 dR_12 as SHV _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHV & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHV, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CEx))) as dR_13; dand8 dR_13 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CEx)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_14; dand4 dR_14 as BSSV BSS CP [cnt CNT] | pose proof GLOB as (BSSV & BSS & CP & [cnt CNT]) ]). fold_cl_segs. cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS. unfold h_vsc, h_cp in BSSV, BSS, CP, CNT.
    (first [ pose proof (HOBJ) as dR_15; dand3 dR_15 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    (first [ pose proof (VB) as dR_18; dand5 dR_18 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]). cbn [vi_cb vi_url VIA] in EVCB, EVURL.
    unfold vep_cells in VEPC. rewrite EVSB, EVC, EVCB, EVCBP, EST, EST0 in VEPC. unfold h_vc in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (h_ff H + 32 + 1304, h_ff H + 32 + 1320)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (h_ff H + 32 + 1304, h_ff H + 32 + 1320)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [| exact I]. right; right; left. exists (h_ff H), HCLASS, ageh. split; [exact HFRh|]. change (fsize HCLASS) with 8192. lia. }
    hide DSB. hide DJS. hide DJB. hide DJfS. hide DJfB. hide DJfV. hide DJfW. hide BUF0. hide_neqs.
    pose proof ST as STw. clear ST.
    (* [comment removed for export] *)
    assert (GO3 : forall md1 m1, ainv A m1 md1 -> aview A m1 = aview A m -> same_but_materialized md md1 ->
              forall (ya0 ya1 : word),
              srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 24))
                                    ya0 ya1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (VEP + 144)) xs3 xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x9085c) fc None m1 (seg_rom rsegs)) md1) T).
    { intros md1 m1 AI1 EV SB ya0 ya1. eapply (T3' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v vv); [| exact CNT0].
      eapply jst_rebase; [exact J0| exact AI1| exact EV| exact SB]. }
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K1; [apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP); intros m1 md1 AINV1 EV SBM HID; apply (GO3 md1 m1 AINV1 EV SBM) |]. clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; [apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP); intros m1 md1 AINV1 EV SBM HID; apply (GO3 md1 m1 AINV1 EV SBM) |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP); intros m1 md1 AINV1 EV SBM HID; apply (GO3 md1 m1 AINV1 EV SBM) |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP); intros m1 md1 AINV1 EV SBM HID; apply (GO3 md1 m1 AINV1 EV SBM) |]. clear K1.
    zstep. zstep. zstep. if_cases K1; [apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP); intros m1 md1 AINV1 EV SBM HID; apply (GO3 md1 m1 AINV1 EV SBM) |]. clear K1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    unhide DJfS. unhide DJfB. unhide DJfV. unhide DJfW.
    zstep. zstep. shadow_chk0 SHV 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep. zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. carve_frame 48%nat STw.
    try replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in * by lia.
    try replace (bv_unsigned sp - 64 + -48) with (bv_unsigned sp + -112) in * by lia.
    do 8 zstep.
    try replace (bv_unsigned sp + -112 + 48) with (bv_unsigned sp + -64) by lia.
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -112) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv STw (bv_unsigned sp + -64) end.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    unhide DJS. unhide DJB. unhide BUF0.
    lazymatch goal with VEPCx : rw_cells _ (aview ?Ax ?m1) VEP _ |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
      eapply (T3' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v vv); [| exact CNT0];
      split; [exact AINV0|]; split; [assumption|];
      split; [eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]|];
      split; [exact STw|]; split; [exact FR|];
      split; [ split; [exact (proj1 HENV)|]; split;
               [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
                 [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact CNT']
               | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                          intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd in *; cbn [outside]; keeplia Ha__ GHI ACV CEIL LO
                        | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HG|];
                          intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE ACV CEIL LO ] ] |];
      split; [ split; [exact VLV|]; split; [unfold vep_cells; rewrite EVSB, EVC, EVCB, EVCBP, EST, EST0; unfold h_vc; exact VEPCx| split; [exact TAG8| exact PADS]] |]
    end.
    split; [exact VB|]. split; [exact EVSB|]. split; [exact EIS|]. split; [exact EAV|]. split; [exact EST|]. split; [exact EEF|].
    split; [exact BLM|]. split; [exact EVP|]. split; [unfold NMAX; exact CBX|].
    split. { eapply vsb_obj_munch; [exact VOBJ| exact MU| exact WM|]. intros a__ Ha__. cbn. keeplia Ha__ DJfS DJfB Shi Bhi ACV CEIL LO. }
    split; [exact SZB|]. split; [exact LENB|]. split; [unhide NEbV; exact NEbV|]. split; [unhide NEbw; exact NEbw|].
    split. { eapply ws1_obj_munch; [exact WS1| exact MU| exact WM|]. intros a__ Ha__. unfold h_ws, h_wsbuf in Ha__. cbn.
             keeplia Ha__ DJfW GHI WAhi ACV CEIL LO. }
    split; [exact LD|]. split; [exact LIVE0|]. split; [exact BUF0|]. split; [exact FA|]. split; [exact LB|]. split; [exact BC|].
    ufs.
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ (aview ?Ax ?m1) =>
      eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A m) (aview A m1)); [exact CF| exact MU| |] end.
    - intros a Ha NO. cbn [outside] in NO.
      assert (CS : bv_unsigned sp - 8864 <= a < bv_unsigned sp \/ h_ff H + 32 + 1304 <= a < h_ff H + 32 + 1320) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia).
      clear NO. destruct CS as [X|X]; [left; exact X|]. right; left. unfold finish_changed. right; right; right; right. unfold h_vsc. exact X.
    - eapply (window_mapped LPA _ lo); [exact STw | exact FR | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO].
  Qed.
End S.
End A_VEdm4.

Module A_VE7pv.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VE1nh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEt76 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEdm4.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let jst := jst H VEP wa N DATA v0 tag q vv0 va vi lo ra sp s0 s1 s2 s3 s4 s5 s6 m0 md0 A0.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  (* [comment removed for export] *)
  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Local Definition T2' := T2 (* [comment removed for export] *) HMC HEC HCB HDS HFI HLN H VEP wa n N DATA v0 tag q vv0 va vi lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                     AINV00 PW HENV0 TP SP16 CEIL LO LD0 N0 DRANGE NEDV NEDS NPB LBM0 NLV0 SCC0 PCC0 FY0 K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition jst1 (A : AS) (m : mem) (md : Model) (v : vep) : Prop :=
       ainv A m md /\ mem_inv rsegs (aview A m) /\ amd_frame md0 md
    /\ stk rsegs (aview A m) lo (bv_unsigned sp - 64)
    /\ rw_cells rsegs (aview A m) (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ henv_ok LPA VIA H A (aview A m)
    /\ vep_obj LPA A (aview A m) VEP v tag q /\ vep_base H VEP v
    /\ v Fvsb = S /\ v Finclude_src = 0 /\ v Fattr_vsb = v0 Fattr_vsb
    /\ v Fstate = v0 Fstate /\ v Fesi_found = v0 Fesi_found /\ bool01 (v Flast_mark) /\ v Fver_p = v0 Fver_p
    /\ 0 <= v Fcb_x < NMAX
    /\ vsb_obj LPA A (aview A m) S vv0 false
    /\ match va with
       | None => v0 Fattr_vsb = 0
       | Some x => vsb_obj LPA A (aview A m) (v0 Fattr_vsb) x false /\ vsb_apart (v0 Fattr_vsb) x [VEP; wa; S; vb_buf vv0]
       end
    /\ ws1_obj LPA H A (aview A m) wa VEP
    /\ a_live A DATA = Some N
    /\ (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A p = Some k)
    /\ frames_same A0 A
    /\ a_livebytes A = a_livebytes A0 - match vi with None => 0 | Some (x, _) => 40 + vb_size x end
    /\ (a_tinycred A = a_tinycred A0 /\ a_nlive A + match vi with None => 0 | Some _ => 2 end = a_nlive A0 /\ a_seccred A = a_seccred A0 /\ a_primcred A = a_primcred A0 (* [comment removed for export] *))
    /\ cframe LPA (owned A0) (owned A) (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
              (vsb_blocks S vv0) (aview A0 m0) (aview A m).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="jst K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 HLN HFI HDS HCB HEC HMC"] Lemma T1 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 xs2 xs3 xs4 xs5 : word) A m md v,
    jst1 A m md v -> vep_cnt v n ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) xs1
                                    a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5
                                    (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90734) fc None m (seg_rom rsegs)) md) T.
  Proof.
    touch_all. intros until v. intros J CNT0. prelims.
    (first [ dand25 J as AINV MI MDF ST FR HENV VEPO VB EVSB EIS EAV EST EEF BLM EVP CBX VOBJ VAM WS1 LD LIVE0 FS LB BC CF | destruct J as (AINV & MI & MDF & ST & FR & HENV & VEPO & VB & EVSB & EIS & EAV & EST & EEF & BLM & EVP & CBX
                   & VOBJ & VAM & WS1 & LD & LIVE0 & FS & LB & BC & CF) ]).
    unfold NMAX in CBX.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof PW as (_ & _ & _ & _ & _ & _ & NN0 & NNM & _ & _ & ROOM0 & APART0 & _ & VIW). unfold NMAX in NNM. destruct ROOM0 as [RM1 RM2].
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV NEbV]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw NEbw].
    (first [ pose proof (VEPO) as dR_4; dand4 dR_4 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_6; dand7 dR_6 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vv0 false AINV VOBJ)) as dR_7; dand11 dR_7 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vv0 false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_8; dand6 dR_8 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (as_live_disjoint LPA A m md S 40 VEP 312 AINV VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A m md (vb_buf vv0) (vb_size vv0) VEP 312 AINV VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv0) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((live_geomP LPA A m md wa _ AINV LWA)) as dR_11; dand7 dR_11 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh VEP 312 AINV HFRh VLV) as DJfV.
    change (fsize HCLASS) with 8192 in DJfV.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    assert (VIS : 0 <= match vi with None => 0 | Some (x, _) => 40 + vb_size x end).
    { destruct vi as [[y fy]|]; [|lia]. destruct VIW as (VY & _). pose proof (proj1 (proj2 VY)) as (SY & _). lia. }
    (* [comment removed for export] *)
    assert (JST : forall A' m' md' v', ainv A' m' md' -> mem_inv rsegs (aview A' m') -> amd_frame md0 md' ->
              stk rsegs (aview A' m') lo (bv_unsigned sp - 64) ->
              rw_cells rsegs (aview A' m') (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              henv_ok LPA VIA H A' (aview A' m') -> vep_obj LPA A' (aview A' m') VEP v' tag q ->
              (forall f, f <> Fattr_vsb -> v' f = v f) -> v' Fattr_vsb = 0 ->
              vsb_obj LPA A' (aview A' m') S vv0 false -> ws1_obj LPA H A' (aview A' m') wa VEP -> a_live A' DATA = Some N ->
              (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
              frames_same A0 A' -> a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + 40 + vb_size vv0 ->
              a_tinycred A' = a_tinycred A0 -> a_nlive A' + world_nlive va vi = a_nlive A0 -> a_seccred A' = a_seccred A0 -> a_primcred A' = a_primcred A0 (* [comment removed for export] *) ->
              cframe LPA (owned A0) (owned A') (bv_unsigned sp) 8864 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) (aview A0 m0) (aview A' m') ->
              jst A' m' md' v' vv0 false (7 * N) 0%nat 0).
    { intros A' m' md' v' X1 X2 X3 X4 X5 X6 X8 VK X10 X11 X12 X13 X14 X15 X16 X17 X17n X17s X17p X18.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
      split; [exact X6|]. split; [exact X8|].
      split; [unfold vep_base; rewrite !VK by discriminate; exact VB|].
      split; [rewrite VK by discriminate; exact EVSB|]. split; [rewrite VK by discriminate; exact EIS|]. split; [exact X10|].
      split; [rewrite VK by discriminate; exact EST|]. split; [rewrite VK by discriminate; exact EEF|].
      split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; exact EVP|].
      split; [rewrite VK by discriminate; unfold NMAX; exact CBX|].
      split; [exact X11|]. split; [exact RM1|]. split; [lia|]. split; [exact NEbV|]. split; [exact NEbw|].
      split; [exact X12|]. split; [exact X13|]. split; [exact X14|]. split; [left; left; reflexivity|].
      split; [apply frames_same_aged; exact X15|]. split; [exact X16|]. split; [split; [exact X17| split; [exact X17n| split; [rewrite X17s; lia| rewrite X17p; lia]]]|]. ufs. exact X18. }   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (first [ pose proof (VB) as dR_12; dand5 dR_12 as EVC EVCB EVCBP EVDZ EVURL | pose proof VB as (EVC & EVCB & EVCBP & EVDZ & EVURL) ]).
    pose proof VEPC as VEPCF. hide VEPCF.
    unfold vep_cells in VEPC. rewrite EVSB, EAV in VEPC.
    pose proof VOBJ as VOBJx. vsb_open VOBJx. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]). fold_cl_segs.
    hide DSB. hide Verr. hide DJS. hide DJB. hide DJfV. hide_neqs.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8864) 8864).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8864, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    pose proof ST as STw. clear ST.
    ago AINV. fold_cl_segs.
    remember va as vax eqn:EVA in VAM. destruct vax as [x|].
    2:{ (* [comment removed for export] *)
        rewrite VAM in VEPC.
        zstep. vchk SHV0 EzsV 8 0. zstep. zstep. kdead2.
        apply (astop_lemma A m md _ _ _ _ _ _ _ _ AINV MU WM CFP). intros m1 md1 AINV1 EV SBM HID.
        eapply (T2' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m1 md1 v vv0); [| exact CNT0].
        unhide VEPCF. rewrite <- EV in *.
        eapply (JST A m1 md1 v); [exact AINV1| exact MI| eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]| exact STw| exact FR| exact HENV
          | exact VEPO | intros f _; reflexivity | rewrite EAV; exact VAM | exact VOBJ| exact WS1| exact LD| exact LIVE0| exact FS
          | rewrite LB; unfold world_bytes; rewrite <- EVA; lia | exact (proj1 BC)
          | pose proof (proj1 (proj2 BC)) as BCn; unfold world_nlive; rewrite <- EVA; keeplia BCn | exact (proj1 (proj2 (proj2 BC))) | exact (proj2 (proj2 (proj2 BC))) (* [comment removed for export] *) | ufs; exact CF]. }
    (* [comment removed for export] *)
    destruct VAM as [XOBJ XAP].
    destruct (XAP VEP ltac:(left; reflexivity)) as [NXV NXbV]. destruct (XAP wa ltac:(right; left; reflexivity)) as [NXw NXbw].
    destruct (XAP S ltac:(right; right; left; reflexivity)) as [NXS NXbS]. destruct (XAP (vb_buf vv0) ltac:(right; right; right; left; reflexivity)) as [NXB NXbB].
    (first [ pose proof ((vsb_obj_geom LPA A m md (v0 Fattr_vsb) x false AINV XOBJ)) as dR_14; dand11 dR_14 as X16 Xlo Xhi Ximg XB16 XBlo XBhi XBimg XDSB Xmap XBmap | pose proof (vsb_obj_geom LPA A m md (v0 Fattr_vsb) x false AINV XOBJ) as (X16 & Xlo & Xhi & Ximg & XB16 & XBlo & XBhi & XBimg & XDSB & Xmap & XBmap) ]).
    (first [ pose proof (XOBJ) as dR_15; dand6 dR_15 as _ XINV XLS XLB XNE _ | pose proof XOBJ as (_ & XINV & XLS & XLB & XNE & _) ]). pose proof (proj1 XINV) as XSZ.
    pose proof (as_live_disjoint LPA A m md (v0 Fattr_vsb) 40 VEP 312 AINV XLS VLV NXV) as DX1.
    pose proof (as_live_disjoint LPA A m md (vb_buf x) (vb_size x) VEP 312 AINV XLB VLV NXbV) as DX2.
    pose proof (as_live_disjoint LPA A m md (v0 Fattr_vsb) 40 S 40 AINV XLS VLS NXS) as DX3.
    pose proof (as_live_disjoint LPA A m md (vb_buf x) (vb_size x) S 40 AINV XLB VLS NXbS) as DX4.
    pose proof (as_live_disjoint LPA A m md (v0 Fattr_vsb) 40 (vb_buf vv0) (vb_size vv0) AINV XLS VLB NXB) as DX5.
    pose proof (as_live_disjoint LPA A m md (vb_buf x) (vb_size x) (vb_buf vv0) (vb_size vv0) AINV XLB VLB NXbB) as DX6.
    pose proof (as_live_disjoint LPA A m md (v0 Fattr_vsb) 40 wa 40 AINV XLS LWA NXw) as DX7.
    pose proof (as_live_disjoint LPA A m md (vb_buf x) (vb_size x) wa 40 AINV XLB LWA NXbw) as DX8.
    pose proof (as_live_disjoint (Clg:=Clg) LPA A m md wa 40 VEP 312 AINV LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DX9.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh XLS) as DJfX.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh XLB) as DJfXB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS ageh _ _ AINV HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfX, DJfXB, DJfS, DJfB, DJfW.
    unfold kHighMemBeg in Xlo, XBlo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (v0 Fattr_vsb) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHX. rewrite SHMAX_val in SHX.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf x) (vb_size x) ltac:(lia) ltac:(lia) ltac:(lia)) as SHXB. rewrite SHMAX_val in SHXB.
    hide DX1. hide DX2. hide DX3. hide DX4. hide DX5. hide DX6. hide DX7. hide DX8. hide DX9. hide XDSB. hide DJfX. hide DJfXB. hide DJfS. hide DJfB. hide DJfW. hide_neqs.
    (* [comment removed for export] *)
    (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 (v0 Fattr_vsb))) VEPC eq_refl)) as dR_16; dand3 dR_16 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 (v0 Fattr_vsb))) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 224) with 224 in VM. change (Z.of_nat 224) with 224 in VBk. change (Z.of_nat 8) with 8 in VBk.
    replace (VEP + 224 + 8) with (VEP + 232) in VBk by lia.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. if_cases KZ; zify_cond KZ; [unhide_neqs; exfalso; lia|]. clear KZ.
    zstep.
    astop AINV MU WM CFP.
    unhide NXV. unhide NXbV.
    eapply (HDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A (VEP + 224) (v0 Fattr_vsb) x false lo);
      [ exact AINV0 | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NXV X)| exact (NXbV X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | lia
      | exact XOBJ | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact STw | exact CEIL
      | rewrite unsigned_lit by lia; ufs; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by lia. ufs.
    replace (ret_pc (Z_to_bv 64 0x90754)) with (Z_to_bv 64 0x90754) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NXV) (not_eq_sym NXbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa (not_eq_sym NXw) (not_eq_sym NXbw)); exact LWA).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NXS) (not_eq_sym NXbS)); exact VLS).
    assert (LBf1 : a_live A1 (vb_buf vv0) = Some (vb_size vv0)) by (rewrite (LIVEq (vb_buf vv0) (not_eq_sym NXB) (not_eq_sym NXbB)); exact VLB).
    assert (NXD : v0 Fattr_vsb <> DATA) by (intros X; apply NPB; rewrite <- EVA; right; left; left; symmetry; exact X).
    assert (NXbD : vb_buf x <> DATA) by (intros X; apply NPB; rewrite <- EVA; right; left; right; symmetry; exact X).
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NXD) (not_eq_sym NXbD)); exact LD).
    hide_neqs.
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A A1); [exact AINV0| exact CF1| exact HENV| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists (v0 Fattr_vsb), 40. split; [exact XLS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf x), (vb_size x). split; [exact XLB|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    assert (WS1_1 : ws1_obj LPA H A1 (aview A1 mc) wa VEP).
    { eapply ws1_obj_ccall; [exact AINV0| exact (proj1 HENV)| exact CF1| exact WS1| keeplia CEIL LO| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, newblk, blk in *. keeplia Ha X DX7 DX8 DX9 DJfX DJfXB DJfV SHX SHXB WAlo GCE VEPlo. }
    (* [comment removed for export] *)
    clear XOBJ.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 S) in VSBC;
        [| rewrite vsb_cells_size; exact (crange_block (Clg:=Clg) (L:=LPA) A _ _ S 40 S 40 AINV0 VLS ltac:(keeplia Slo) ltac:(keeplia Slo) ltac:(keeplia Slo))
         | rewrite vsb_cells_size; change (Z.of_nat 40) with 40; split; [keeplia Shi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX3 DX4 DJS SHX SHXB Slo] ];
      apply (u8arr_ccall LPA A A1 xsp win V Nn ma mb CF1 (vb_buf vv0) bs) in U8;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A _ _ (vb_buf vv0) (vb_size vv0) (vb_buf vv0) (Z.of_nat (length bs)) AINV0 VLB ltac:(keeplia Blo) ltac:(keeplia LBS) ltac:(keeplia LBS))
         | split; [keeplia Bhi LBS ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX5 DX6 DJB LBS SHX SHXB Blo] ];
      apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A _ _ VEP 312 VEP 224 AINV0 VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX1 DX2 SHX SHXB VEPlo] ];
      apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 (VEP + 232)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A _ _ VEP 312 (VEP + 232) 80 AINV0 VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8, ?P236, ?P268, ?P308; cbn [Nat.add];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX1 DX2 SHX SHXB VEPlo] ];
      lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
        apply (rw_cells_ccall LPA A A1 xsp win V Nn ma mb CF1 fa fcs) in FR;
        [ | exact (crange_stack (Clg:=Clg) (L:=LPA) A _ _ ma (bv_unsigned sp - 64) 64 AINV0 ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR) (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA)))
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SPR|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X;
            try (generalize alloc_ceiling_val); clear - Hi X ACV CEIL LO VEPhi Xhi XBhi SHX SHXB SPR; try pose proof alloc_ceiling_val as ACV__; lia ] end;
      apply (stk_ccall LPA A A1 _ _ ma mb xsp win V Nn lo _ AINV0 CF1) in STw;
        [ | exact CEIL | keeplia ACV CEIL LO | keeplia SPR | clear - ACV CEIL LO VEPhi Xhi XBhi SHX SHXB; try pose proof alloc_ceiling_val as ACV__; intros a Ha X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ]
    end.
    assert (VOBJ1 : vsb_obj LPA A1 (aview A1 mc) S vv0 false).
    { split; [exact VSBC|]. split; [exact VINV|]. split; [exact LS1|]. split; [exact LBf1|]. split; [exact VNE0|].
      exists bs. split; [exact U8|]. split; [exact LBS| intros X; discriminate X]. }
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd v Fattr_vsb 0) tag q)).
    { rewrite <- vep_cells_attr_vsb. unfold vep_cells. rewrite ?EVSB, ?EAV. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 224) with 224; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (T2' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mc mdc (fupd v Fattr_vsb 0) vv0);
      [| unfold vep_cnt; rewrite !fupd_other by discriminate; exact CNT0].
    eapply (JST A1 mc mdc (fupd v Fattr_vsb 0)); [exact AINV1| exact MI1
      | eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]
      | exact STw| exact FR | exact HENV1
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | intros f Hf; apply fupd_other; exact Hf | apply fupd_same | exact VOBJ1| exact WS1_1| exact LD1|
      | intros ff; rewrite (FRS1 ff); apply FS
      | rewrite LB1, LB; unfold world_bytes; rewrite <- EVA; lia
      | rewrite TC1; exact (proj1 BC)
      | pose proof (proj1 (proj2 BC)) as BCn; unfold world_nlive; rewrite <- EVA; keeplia NL1 BCn
      | rewrite SC1; exact (proj1 (proj2 (proj2 BC))) | rewrite PC1; exact (proj2 (proj2 (proj2 BC))) (* [comment removed for export] *) | ].
    - intros p k L0 NS NP. rewrite (LIVEq p); [exact (LIVE0 p k L0 NS NP)| |];
        intros ->; apply NP; rewrite <- EVA; right; left; [left|right]; reflexivity.
    - assert (MP1 : mapped (aview A1 mc) (bv_unsigned sp - 8864) 8864) by (eapply (window_mapped LPA _ lo); [exact STw | exact FR | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]).
      lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
        assert (CF2 : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8864
                        (fun a => newblk (v0 Fattr_vsb) 40 a \/ newblk (vb_buf x) (vb_size x) a \/ VEP + 224 <= a < VEP + 224 + 8) nowhere ma mb)
          by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ ma ma mb mb [] []);
              [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF1 | lia | lia
              | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact MP1 ]);
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) ma mb CF CF2);
          [ lia | lia | exact MP1 | intros a X; exact X | | intros a X; left; exact X ]
      end.
      intros a [X|[X|X]].
      + right. right. right. left. rewrite <- EVA. left. exact X.
      + right. right. right. left. rewrite <- EVA. right. exact X.
      + right. left. unfold blk. split; [keeplia VEPlo| keeplia X].
  Qed.
End S.
End A_VE7pv.

Module A_VEliw.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VE1nh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEt76 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VEdm4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih.A_VE7pv.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vsb_leaf_post, vep_default_cb_post, VSB_finish_post, CB_STACK, FINISH_STACK, LEN_STACK, ASSERT_STACK, ERRNOA in H.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HLN : VSB_len_stmt.

  (* [comment removed for export] *)
  Variables (H : henv) (VEP wa n N DATA : Z) (v0 : vep) (tag : list byte) (q : vep_pads) (vv0 : vsb_rec)
            (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Let S := v0 Fvsb.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis PW : parsed_world H A0 (aview A0 m0) VEP v0 tag q vv0 va vi wa n N.
  Hypothesis HENV0 : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VEPFIN_STACK <= bv_unsigned sp.
  Hypothesis LD0 : a_live A0 DATA = Some N.
  Hypothesis N0 : 0 < N.
  Hypothesis DRANGE : DATA <= v0 Fver_p <= DATA + N.
  Hypothesis NEDV : DATA <> VEP.
  Hypothesis NEDS : DATA <> v0 Fvsb.
  Hypothesis NPB : ~ parse_blocks v0 vv0 va vi DATA.
  Hypothesis LBM0 : a_livebytes A0 + FIN_LIVE N <= LIVE_MAX.
  Hypothesis NLV0 : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCC0 : FIN_CRED N <= a_seccred A0.
  Hypothesis PCC0 : PRIM_ROOM + (PPOT_CAP - vsb_ppot vv0) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY0 : frames_young A0 4 0.
  Hypothesis K :
    forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
           (v' : vep) (vr : vsb_rec),
      let w' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md0 md' ->
      stk rsegs w' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' w' ->
      vep_obj LPA A' w' VEP v' tag q -> ws1_obj LPA H A' w' wa VEP ->
      (r = 0 \/ (r <> 0 /\ r = v0 Fvsb /\ vsb_obj LPA A' w' r vr true /\ vsb_apart r vr [VEP; wa] /\
                 (parse_blocks v0 vv0 va vi (vb_buf vr) \/ a_live A0 (vb_buf vr) = None))) ->
      (forall p k, a_live A0 p = Some k -> p <> v0 Fvsb -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
      frames_aged A0 A' 4 0 ->
      a_livebytes A' = a_livebytes A0 - world_bytes vv0 va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
      a_seccred A0 - FIN_CRED N <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (PPOT_CAP - vsb_ppot vv0) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v0 vv0 va vi)
             (fun a => r <> 0 /\ vsb_blocks r vr a) (aview A0 m0) w' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let jst1 := jst1 H VEP wa N DATA v0 tag q vv0 va vi lo ra sp s0 s1 s2 s3 s4 s5 s6 m0 md0 A0.

  Local Ltac touch_all :=
    pose proof (conj HMC (conj HEC (conj HCB (conj HDS (conj HFI (conj HLN (conj AINV00 (conj PW (conj HENV0 (conj TP (conj SP16
      (conj CEIL (conj LO (conj LD0 (conj N0 (conj DRANGE (conj NEDV (conj NEDS (conj NPB (conj LBM0 (conj NLV0 (conj SCC0 (conj PCC0 (conj FY0 K)))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV0)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = v0 Fvsb) by reflexivity;
    pose proof (world_nlive_nonneg va vi) as WNL;
    unfold_stacks; unfold NMAX, kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition T1' := T1 (* [comment removed for export] *) HMC HEC HCB HDS HFI HLN H VEP wa n N DATA v0 tag q vv0 va vi lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                     AINV00 PW HENV0 TP SP16 CEIL LO LD0 N0 DRANGE NEDV NEDS NPB LBM0 NLV0 SCC0 PCC0 FY0 K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="jst1 K FY0 SCC0 PCC0 NLV0 LBM0 NPB NEDS NEDV DRANGE N0 LD0 LO CEIL SP16 TP HENV0 PW AINV00 S vi va vv0 q tag v0 DATA N n HLN HFI HDS HCB HEC HMC"] Lemma T0 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) -> a0 = Z_to_bv 64 VEP ->
    ws1_obj LPA H A0 (aview A0 m0) wa VEP -> stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 VEP_Finish_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI Ha0 WS1 ST. prelims. rewrite Ha0. unfold VEP_Finish_entry.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof PW as (VEPO & VB & [st EST0] & BLM & BEF & CNT0 & NN0 & NNM & VP0 & VOBJ & ROOM0 & APART0 & VAM & VIM).
    unfold NMAX in NNM. (first [ pose proof (CNT0) as dR_1; dand7 dR_1 as C1 C2 C3 C4 C5 C6 C7 | pose proof CNT0 as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
    destruct (APART0 VEP ltac:(left; reflexivity)) as [NESV NEbV]. destruct (APART0 wa ltac:(right; left; reflexivity)) as [NESw NEbw].
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof (PADS) as dR_3; dand7 dR_3 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vv0 false AINV00 VOBJ)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A0 m0 md0 S vv0 false AINV00 VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (VOBJ) as dR_6; dand6 dR_6 as _ VINV VLS VLB VNE _ | pose proof VOBJ as (_ & VINV & VLS & VLB & VNE & _) ]).
    pose proof (as_live_disjoint LPA A0 m0 md0 S 40 VEP 312 AINV00 VLS VLV NESV) as DJS.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf vv0) (vb_size vv0) VEP 312 AINV00 VLB VLV NEbV) as DJB.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL _ _ LWA _ _ | dand9 WS1x as id pad IDOK PADL _ _ LWA _ _ | destruct WS1x as (id & pad & IDOK & PADL & _ & _ & LWA & _ & _) ]).
    assert (NEwS : wa <> S) by (intros X; apply NESw; symmetry; exact X).
    assert (NEwB : wa <> vb_buf vv0) by (intros X; apply NEbw; symmetry; exact X).
    (first [ pose proof ((live_geomP LPA A0 m0 md0 wa _ AINV00 LWA)) as dR_8; dand7 dR_8 as _ _ WAlo WAhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 wa _ AINV00 LWA) as (_ & _ & WAlo & WAhi & _ & _ & _) ]).
    pose proof (as_live_disjoint (Clg:=Clg) LPA A0 m0 md0 wa 40 VEP 312 AINV00 LWA VLV ltac:(intros X; rewrite X in LWA; rewrite VLV in LWA; discriminate LWA)) as DX9.
    pose proof (proj1 HENV0) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh VLB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfW.
    unfold kHighMemBeg in *. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in GHI; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    (* [comment removed for export] *)
    assert (VIS : 0 <= match vi with None => 0 | Some (x, _) => 40 + vb_size x end).
    { destruct vi as [[y fy]|]; [|lia]. destruct VIM as (VY & _). pose proof (proj1 (proj2 VY)) as (SY & _). lia. }
    (* [comment removed for export] *)
    assert (JST : forall A' m' md' v', ainv A' m' md' -> mem_inv rsegs (aview A' m') -> amd_frame md0 md' ->
              stk rsegs (aview A' m') lo (bv_unsigned sp - 64) ->
              rw_cells rsegs (aview A' m') (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              henv_ok LPA VIA H A' (aview A' m') -> vep_obj LPA A' (aview A' m') VEP v' tag q ->
              (forall f, f <> Finclude_src -> v' f = v0 f) -> v' Finclude_src = 0 ->
              vsb_obj LPA A' (aview A' m') S vv0 false ->
              match va with None => v0 Fattr_vsb = 0
                          | Some x => vsb_obj LPA A' (aview A' m') (v0 Fattr_vsb) x false /\ vsb_apart (v0 Fattr_vsb) x [VEP; wa; S; vb_buf vv0] end ->
              ws1_obj LPA H A' (aview A' m') wa VEP -> a_live A' DATA = Some N ->
              (forall p k, a_live A0 p = Some k -> p <> S -> ~ parse_blocks v0 vv0 va vi p -> a_live A' p = Some k) ->
              frames_same A0 A' ->
              a_livebytes A' = a_livebytes A0 - match vi with None => 0 | Some (x, _) => 40 + vb_size x end ->
              a_tinycred A' = a_tinycred A0 -> a_nlive A' + match vi with None => 0 | Some _ => 2 end = a_nlive A0 -> a_seccred A' = a_seccred A0 -> a_primcred A' = a_primcred A0 (* [comment removed for export] *) ->
              cframe LPA (owned A0) (owned A') (bv_unsigned sp) 8864 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) (aview A0 m0) (aview A' m') ->
              jst1 A' m' md' v').
    { intros A' m' md' v' X1 X2 X3 X4 X5 X6 X8 VK X10 X11 X12 X13 X14 X15 X16 X17 X18 X18n X18s X18p X19.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
      split; [exact X6|]. split; [exact X8|].
      split; [unfold vep_base; rewrite !VK by discriminate; exact VB|].
      split; [rewrite VK by discriminate; reflexivity|]. split; [exact X10|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; reflexivity|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; exact BLM|]. split; [rewrite VK by discriminate; reflexivity|].
      split; [rewrite VK by discriminate; unfold NMAX; keeplia C1 C2 C3 NN0 NNM|].
      split; [exact X11|]. split; [exact X12|]. split; [exact X13|]. split; [exact X14|]. split; [exact X15|].
      split; [exact X16|]. split; [exact X17|]. split; [split; [exact X18| split; [exact X18n| split; [exact X18s| exact X18p]]]|]. ufs. exact X19. }   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof VEPC as VEPCF. hide VEPCF.
    unfold vep_cells in VEPC.
    hide DSB. hide DJS. hide DJB. hide DX9. hide DJfV. hide DJfS. hide DJfB. hide DJfW. hide_neqs.
    pose proof (munch_refl [(bv_unsigned sp - 8864, bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAPx : mapped (aview A0 m0) (bv_unsigned sp - 8864) 8864).
    { eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | keeplia LO | keeplia LO SPR]. }
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - 8864, bv_unsigned sp)]).
    { cbn. split; [left; split; [keeplia LO CEIL ACV|]; split; [keeplia SPR|]; replace (bv_unsigned sp - (bv_unsigned sp - 8864)) with 8864 by lia; exact WMAPx | exact I]. }
    (* [comment removed for export] *)
    assert (NOCALL : forall mx mdx, ainv A0 mx mdx -> same_but_materialized md0 mdx ->
              munch [(bv_unsigned sp - 8864, bv_unsigned sp)] (aview A0 m0) (aview A0 mx) -> wmono rsegs (aview A0 m0) (aview A0 mx) ->
              mem_inv rsegs (aview A0 mx) -> stk rsegs (aview A0 mx) lo (bv_unsigned sp - 64) ->
              rw_cells rsegs (aview A0 mx) (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              henv_ok LPA VIA H A0 (aview A0 mx) /\ vsb_obj LPA A0 (aview A0 mx) S vv0 false /\
              match va with None => v0 Fattr_vsb = 0
                          | Some x => vsb_obj LPA A0 (aview A0 mx) (v0 Fattr_vsb) x false /\ vsb_apart (v0 Fattr_vsb) x [VEP; wa; S; vb_buf vv0] end /\
              ws1_obj LPA H A0 (aview A0 mx) wa VEP /\
              cframe LPA (owned A0) (owned A0) (bv_unsigned sp) 8864 (finish_changed H VEP v0 vv0 va vi) (vsb_blocks S vv0) (aview A0 m0) (aview A0 mx)).
    { intros mx mdx AIx SBx MUx WMx MIx STx FRx.
      split; [|split; [|split; [|split]]].
      - eapply henv_ok_munch; [exact HENV0| exact MUx| exact WMx| exact HG|].
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; keeplia Ha__ GHI ACV CEIL LO SHF.
      - eapply vsb_obj_munch; [exact VOBJ| exact MUx| exact WMx|]. intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO.
      - destruct va as [y|]; [|exact VAM]. (first [ dand4 VAM as YO _ _ YA | destruct VAM as (YO & _ & _ & YA) ]). split; [|exact YA].
        (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (v0 Fattr_vsb) y false AINV00 YO)) as dR_10; dand8 dR_10 as _ _ Yhi _ _ _ YBhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (v0 Fattr_vsb) y false AINV00 YO) as (_ & _ & Yhi & _ & _ & _ & YBhi & _) ]).
        eapply vsb_obj_munch; [exact YO| exact MUx| exact WMx|]. intros a__ Ha__; cbn; keeplia Ha__ Yhi YBhi ACV CEIL LO.
      - eapply ws1_obj_munch; [exact WS1| exact MUx| exact WMx|]. intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; keeplia Ha__ GHI WAhi ACV CEIL LO.
      - assert (MPx : mapped (aview A0 mx) (bv_unsigned sp - 8864) 8864)
          by (eapply (window_mapped LPA _ lo); [exact STx | exact FRx | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]).
        eapply (cframe_noalloc LPA); [exact MUx| | exact MPx| intros a X; right; left; exact X].
        intros a Ha NO; cbn [outside] in NO; left; keeplia Ha NO. }
    pose proof ST as STw. clear ST.
    ago AINV00. fold_cl_segs.
    carve_frame 64%nat STw.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0.
    remember vi as vix eqn:EVI in VIM. destruct vix as [[x fi]|].
    2:{ (* [comment removed for export] *)
        rewrite VIM in VEPC. zstep. zstep. kdead2.
        try replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
        astop AINV00 MU WM CFP.
        lazymatch goal with AIq : ainv A0 ?m1 ?md1, SBq : same_but_materialized md0 ?md1,
                            STq : stk _ (aview A0 ?m1) lo _, FRq : rw_cells _ (aview A0 ?m1) (bv_unsigned sp - 64) _,
                            VEPCq : rw_cells _ (aview A0 ?m1) VEP _
          |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
          (first [ pose proof ((NOCALL m1 md1 AIq SBq MU WM ltac:(eassumption) STq FRq)) as dR_11; dand5 dR_11 as HENVx VOBJx VAMx WS1x' CFx | destruct (NOCALL m1 md1 AIq SBq MU WM ltac:(eassumption) STq FRq) as (HENVx & VOBJx & VAMx & WS1x' & CFx) ]);
          eapply (T1' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 m1 md1 v0); [| exact CNT0];
          eapply (JST A0 m1 md1 v0);
          [ exact AIq | assumption | apply amd_frame_sbm; [exact SBq| exact MH] | exact STq | exact FRq | exact HENVx
          | split; [exact VLV|]; split; [unfold vep_cells; rewrite VIM; exact VEPCq| split; [exact TAG8| exact PADS]]
          | intros f _; reflexivity | exact VIM | exact VOBJx | exact VAMx | exact WS1x' | exact LD0
          | intros p k L0 _ _; exact L0 | intros ff; reflexivity | rewrite <- EVI; keeplia VIS | reflexivity
          | rewrite <- EVI; keeplia VIS | reflexivity | reflexivity (* [comment removed for export] *) | exact CFx ]
        end. }
    (* [comment removed for export] *)
    (first [ dand4 VIM as XOBJ XSM XAP XVA | destruct VIM as (XOBJ & XSM & XAP & XVA) ]).
    destruct (XAP VEP ltac:(left; reflexivity)) as [NXV NXbV]. destruct (XAP wa ltac:(right; left; reflexivity)) as [NXw NXbw].
    destruct (XAP S ltac:(right; right; left; reflexivity)) as [NXS NXbS]. destruct (XAP (vb_buf vv0) ltac:(right; right; right; left; reflexivity)) as [NXB NXbB].
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (v0 Finclude_src) x fi AINV00 XOBJ)) as dR_13; dand11 dR_13 as X16 Xlo Xhi Ximg XB16 XBlo XBhi XBimg XDSB Xmap XBmap | pose proof (vsb_obj_geom LPA A0 m0 md0 (v0 Finclude_src) x fi AINV00 XOBJ) as (X16 & Xlo & Xhi & Ximg & XB16 & XBlo & XBhi & XBimg & XDSB & Xmap & XBmap) ]).
    (first [ pose proof (XOBJ) as dR_14; dand6 dR_14 as _ XINV XLS XLB XNE _ | pose proof XOBJ as (_ & XINV & XLS & XLB & XNE & _) ]). pose proof (proj1 XINV) as XSZ.
    pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 VEP 312 AINV00 XLS VLV NXV) as DX1.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) VEP 312 AINV00 XLB VLV NXbV) as DX2.
    pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 S 40 AINV00 XLS VLS NXS) as DX3.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) S 40 AINV00 XLB VLS NXbS) as DX4.
    pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 (vb_buf vv0) (vb_size vv0) AINV00 XLS VLB NXB) as DX5.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) (vb_buf vv0) (vb_size vv0) AINV00 XLB VLB NXbB) as DX6.
    pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 wa 40 AINV00 XLS LWA NXw) as DX7.
    pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) wa 40 AINV00 XLB LWA NXbw) as DX8.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh XLS) as DJfX.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh XLB) as DJfXB.
    change (fsize HCLASS) with 8192 in DJfX, DJfXB.
    unfold kHighMemBeg in Xlo, XBlo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (v0 Finclude_src) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHX. rewrite SHMAX_val in SHX.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf x) (vb_size x) ltac:(lia) ltac:(lia) ltac:(lia)) as SHXB. rewrite SHMAX_val in SHXB.
    hide DX1. hide DX2. hide DX3. hide DX4. hide DX5. hide DX6. hide DX7. hide DX8. hide XDSB. hide DJfX. hide DJfXB. hide_neqs.
    (* [comment removed for export] *)
    assert (VAG : match va with None => True | Some y =>
              v0 Fattr_vsb + 40 <= alloc_ceiling /\ vb_buf y + vb_size y <= alloc_ceiling /\
              17594333495296 <= v0 Fattr_vsb /\ app_range LPA (vb_buf y) (vb_size y) (* [comment removed for export] *) /\
              a_live A0 (v0 Fattr_vsb) = Some 40 /\ a_live A0 (vb_buf y) = Some (vb_size y) /\
              v0 Finclude_src <> v0 Fattr_vsb /\ vb_buf x <> v0 Fattr_vsb /\ v0 Finclude_src <> vb_buf y /\ vb_buf x <> vb_buf y /\
              (v0 Finclude_src + 40 <= v0 Fattr_vsb \/ v0 Fattr_vsb + 40 <= v0 Finclude_src) /\
              (vb_buf x + vb_size x <= v0 Fattr_vsb \/ v0 Fattr_vsb + 40 <= vb_buf x) /\
              (v0 Finclude_src + 40 <= vb_buf y \/ vb_buf y + vb_size y <= v0 Finclude_src) /\
              (vb_buf x + vb_size x <= vb_buf y \/ vb_buf y + vb_size y <= vb_buf x) /\
              (v0 Fattr_vsb + 40 <= VEP \/ VEP + 312 <= v0 Fattr_vsb) /\
              (vb_buf y + vb_size y <= VEP \/ VEP + 312 <= vb_buf y) end).
    { destruct va as [y|]; [|exact I]. (first [ dand4 VAM as YO _ _ YA | destruct VAM as (YO & _ & _ & YA) ]).
      (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (v0 Fattr_vsb) y false AINV00 YO)) as dR_16; dand8 dR_16 as _ Ylo Yhi _ _ YBlo YBhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (v0 Fattr_vsb) y false AINV00 YO) as (_ & Ylo & Yhi & _ & _ & YBlo & YBhi & _) ]).
      unfold kHighMemBeg in Ylo, YBlo. all_app_facts.
      (first [ pose proof (YO) as dR_17; dand6 dR_17 as _ _ YLS YLB _ _ | pose proof YO as (_ & _ & YLS & YLB & _ & _) ]).
      destruct (XVA (v0 Fattr_vsb) ltac:(left; reflexivity)) as [NY1 NY2].
      destruct (XVA (vb_buf y) ltac:(right; left; reflexivity)) as [NY3 NY4].
      destruct (YA VEP ltac:(left; reflexivity)) as [NY5 NY6].
      pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 (v0 Fattr_vsb) 40 AINV00 XLS YLS NY1) as DY1.
      pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) (v0 Fattr_vsb) 40 AINV00 XLB YLS NY2) as DY2.
      pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Finclude_src) 40 (vb_buf y) (vb_size y) AINV00 XLS YLB NY3) as DY3.
      pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf x) (vb_size x) (vb_buf y) (vb_size y) AINV00 XLB YLB NY4) as DY4.
      pose proof (as_live_disjoint LPA A0 m0 md0 (v0 Fattr_vsb) 40 VEP 312 AINV00 YLS VLV NY5) as DY5.
      pose proof (as_live_disjoint LPA A0 m0 md0 (vb_buf y) (vb_size y) VEP 312 AINV00 YLB VLV NY6) as DY6.
      repeat (split; [first [assumption | exact YBlo_a]|]). exact DY6. }
    hide VAG.
    (* [comment removed for export] *)
    (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (v0 Finclude_src))) VEPC eq_refl)) as dR_18; dand3 dR_18 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (v0 Finclude_src))) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk.
    change (Z.of_nat 280) with 280 in VM. change (Z.of_nat 280) with 280 in VBk. change (Z.of_nat 8) with 8 in VBk.
    replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KZ; zify_cond KZ; [unhide_neqs; exfalso; keeplia KZ Xlo Xhi ACV|]. clear KZ.
    zstep.
    try replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
    astop AINV00 MU WM CFP.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq,
                        STq : stk _ (aview A0 ?mq) lo _, FRq : rw_cells _ (aview A0 ?mq) (bv_unsigned sp - 64) _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      (first [ pose proof ((NOCALL _ _ AIq SBq MU WM ltac:(eassumption) STq FRq)) as dR_19; dand5 dR_19 as HENVa VOBJa VAMa WS1a CFa | destruct (NOCALL _ _ AIq SBq MU WM ltac:(eassumption) STq FRq) as (HENVa & VOBJa & VAMa & WS1a & CFa) ]);
      rename STq into STa; rename FRq into FRa; rename AIq into AINVa; rename SBq into SBMa end.
    unhide NXV. unhide NXbV.
    eapply (HDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 280) (v0 Finclude_src) x fi lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NXV X)| exact (NXbV X)| exact X] | keeplia VEPlo | keeplia VEPlo]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | eapply vsb_obj_munch; [exact XOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Xhi XBhi ACV CEIL LO]
      | exact TP
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact STa | exact CEIL
      | rewrite unsigned_lit by lia; ufs; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by lia. ufs.
    replace (ret_pc (Z_to_bv 64 0x90734)) with (Z_to_bv 64 0x90734) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NXV) (not_eq_sym NXbV)); exact VLV).
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa (not_eq_sym NXw) (not_eq_sym NXbw)); exact LWA).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NXS) (not_eq_sym NXbS)); exact VLS).
    assert (LBf1 : a_live A1 (vb_buf vv0) = Some (vb_size vv0)) by (rewrite (LIVEq (vb_buf vv0) (not_eq_sym NXB) (not_eq_sym NXbB)); exact VLB).
    assert (NXD : v0 Finclude_src <> DATA) by (intros X; apply NPB; rewrite <- EVI; right; right; left; symmetry; exact X).
    assert (NXbD : vb_buf x <> DATA) by (intros X; apply NPB; rewrite <- EVI; right; right; right; symmetry; exact X).
    assert (LD1 : a_live A1 DATA = Some N) by (rewrite (LIVEq DATA (not_eq_sym NXD) (not_eq_sym NXbD)); exact LD0).
    hide_neqs.
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists (v0 Finclude_src), 40. split; [exact XLS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf x), (vb_size x). split; [exact XLB|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    assert (WS1_1 : ws1_obj LPA H A1 (aview A1 mc) wa VEP).
    { eapply ws1_obj_ccall; [exact AINVa| exact (proj1 HENVa)| exact CF1| exact WS1a| keeplia CEIL LO| exact LWA1| exact LVEP1|].
      intros a Ha X. unfold h_ws, h_wsbuf, newblk, blk in *. keeplia Ha X DX7 DX8 DX9 DJfX DJfXB DJfV SHX SHXB WAlo GCE VEPlo. }
    assert (VOBJ1 : vsb_obj LPA A1 (aview A1 mc) S vv0 false).
    { eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact VOBJa| keeplia CEIL LO| exact LS1| exact LBf1|].
      intros a Ha X. unfold newblk, blk in X. keeplia Ha X DX3 DX4 DX5 DX6 DJS DJB SHX SHXB Slo Blo. }
    assert (VAM1 : match va with None => v0 Fattr_vsb = 0
            | Some y => vsb_obj LPA A1 (aview A1 mc) (v0 Fattr_vsb) y false /\ vsb_apart (v0 Fattr_vsb) y [VEP; wa; S; vb_buf vv0] end).
    { unhide VAG. destruct va as [y|]; [|exact VAMa]. destruct VAMa as [YO YA]. split; [|exact YA].
      (first [ dand16 VAG as Yhi YBhi Ylo YBlo YLS YLB NY1 NY2 NY3 NY4 DY1 DY2 DY3 DY4 DY5 DY6 | destruct VAG as (Yhi & YBhi & Ylo & YBlo & YLS & YLB & NY1 & NY2 & NY3 & NY4 & DY1 & DY2 & DY3 & DY4 & DY5 & DY6) ]).
      all_app_facts.   (* [comment removed for export] *)
      eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact YO| keeplia CEIL LO
        | rewrite (LIVEq _ (not_eq_sym NY1) (not_eq_sym NY2)); exact YLS
        | rewrite (LIVEq _ (not_eq_sym NY3) (not_eq_sym NY4)); exact YLB |].
      intros a Ha X. unfold newblk, blk in X. keeplia Ha X DY1 DY2 DY3 DY4 DY5 DY6 SHX SHXB Ylo YBlo. }
    (* [comment removed for export] *)
    clear XOBJ.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 280 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; split; [keeplia VEPhi ACV CEIL LO|]; intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX1 DX2 SHX SHXB VEPlo ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 288)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 288) 24 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?P308; cbn [Nat.add];
           split; [keeplia VEPhi ACV CEIL LO|]; intros i Hi X; unfold newblk, blk in X; keeplia Hi X DX1 DX2 SHX SHXB VEPlo ];
      lazymatch type of FRa with rw_cells _ _ ?fa ?fcs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 fa fcs) in FRa;
        [ | exact (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp - 64) 64 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR) (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRa ltac:(off_image_solve LPA)))
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SPR|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X;
            keeplia Hi X ACV CEIL LO VEPhi Xhi XBhi SHX SHXB SPR ] end
    end.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd v0 Finclude_src 0) tag q)).
    { rewrite <- vep_cells_include_src. unfold vep_cells. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (T1' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mc mdc (fupd v0 Finclude_src 0));
      [| unfold vep_cnt; rewrite !fupd_other by discriminate; exact CNT0].
    eapply (JST A1 mc mdc (fupd v0 Finclude_src 0)); [exact AINV1| exact MI1
      | eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMa| exact MH]| exact MDF1]
      | exact ST1| exact FRa | exact HENV1
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | intros f Hf; apply fupd_other; exact Hf | apply fupd_same | exact VOBJ1| exact VAM1| exact WS1_1| exact LD1|
      | exact FRS1
      | rewrite LB1, <- EVI; keeplia VIS
      | exact TC1 | rewrite NL1, <- EVI; keeplia VIS | exact SC1 | exact PC1 (* [comment removed for export] *) | ].
    - intros p k L0 NS NP. rewrite (LIVEq p); [exact L0| |];
        intros ->; apply NP; rewrite <- EVI; right; right; [left|right]; reflexivity.
    - assert (MP1 : mapped (aview A1 mc) (bv_unsigned sp - 8864) 8864)
        by (eapply (window_mapped LPA _ lo); [exact ST1 | exact FRa | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]).
      lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
        assert (CF2 : cframe LPA (owned A0) (owned A1) (bv_unsigned sp) 8864
                        (fun a => newblk (v0 Finclude_src) 40 a \/ newblk (vb_buf x) (vb_size x) a \/ VEP + 280 <= a < VEP + 280 + 8) nowhere ma mb)
          by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ ma ma mb mb [] []);
              [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF1 | keeplia SPR | keeplia SPR
              | intros a X; exact X | intros a X; destruct X | apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact MP1 ]);
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) ma mb CFa CF2);
          [ keeplia SPR | keeplia SPR | exact MP1 | intros a X; exact X | | intros a X; left; exact X ]
      end.
      intros a [X|[X|X]].
      + right. right. right. right. left. rewrite <- EVI. left. exact X.
      + right. right. right. right. left. rewrite <- EVI. right. exact X.
      + right. left. unfold blk. split; [keeplia VEPlo| keeplia X].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Theorem VEP_Finish_ok :
    vep_mark_common_stmt -> vep_emit_common_stmt -> vep_default_cb_stmt ->
    VSB_destroy_stmt -> VSB_finish_stmt -> VSB_len_stmt -> VEP_Finish_stmt.
  Proof.
    intros HMC HEC HCB HDS HFI HLN. unfold VEP_Finish_stmt. intros H VEP wa n N DATA vv tag q vr va vi lo. intros until T.
    cbv zeta. intros AINV MI Ha0 PW WS1 HENV LD N0 DR NEDV NEDS NPB LBM BIG SCC PCC FY TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    eapply (T0 HMC HEC HCB HDS HFI HLN H VEP wa n N DATA vv tag q vr va vi lo); eassumption.
  Qed.
End Main.
End A_VEliw.

   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strcmp_icpt_post, DATA_STACK, ASSERT_STACK, STRCMP_ICPT_STACK in H.

(* [comment removed for export] *)
Definition A_continue : Z := 0x241e0.
Definition STR_continue : list byte :=
  [Z_to_bv 8 99; Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 116; Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 101].
Lemma str_continue_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_continue (STR_continue ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_continue; lia| cbn; unfold A_continue; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma str_continue_nonul : ~ In (Z_to_bv 8 0) STR_continue.
Proof. cbv. intuition discriminate. Qed.

(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma strcmp_icpt_cells_of_consts : forall v, consts_hold LPA v -> strcmp_icpt_cells v.
  Proof.
    intros v CH. eapply (strcmp_icpt_cells_of_bytes v pa_common_flags_bytes);
      [ .. | reflexivity | reflexivity | exact (map_cells_of_consts v CH)];
      (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.
End Cells.

(* [comment removed for export] *)
Lemma cstr_split : forall (l : list byte) (n : nat), nth_error l n = Some (Z_to_bv 8 0) ->
  exists z, (z <= n)%nat /\ l = firstn z l ++ Z_to_bv 8 0 :: skipn (S z) l /\ ~ In (Z_to_bv 8 0) (firstn z l) /\ length (firstn z l) = z.
Proof.
  intros l n Hn.
  destruct (find_byte 0 l) as [z|] eqn:FB.
  - (first [ pose proof ((find_byte_Some _ _ _ FB)) as dR_1; dand3 dR_1 as LZ (b & Hb & Hb0) MIN | destruct (find_byte_Some _ _ _ FB) as (LZ & (b & Hb & Hb0) & MIN) ]).
    assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Hb0; reflexivity). subst b.
    exists z. assert (ZN : (z <= n)%nat).
    { destruct (Nat.le_gt_cases z n) as [X|X]; [exact X|]. exfalso. exact (MIN n _ X Hn eq_refl). }
    split; [exact ZN|]. split; [| split; [| apply firstn_length_le; lia]].
    + (first [ pose proof ((nth_error_split l z _ Hb)) as dR_2; dex2 dR_2 as pre post; destruct dR_2 as [E L] | pose proof ((nth_error_split l z _ Hb)) as dR_2; dand4 dR_2 as pre post E L | destruct (nth_error_split l z _ Hb) as (pre & post & E & L) ]). rewrite E at 1.
      rewrite E. rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
      f_equal. f_equal. replace (S z) with (length (pre ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
      replace (pre ++ Z_to_bv 8 0 :: post) with ((pre ++ [Z_to_bv 8 0]) ++ post) by (rewrite <- app_assoc; reflexivity).
      rewrite skipn_app, skipn_all, Nat.sub_diag; reflexivity.
    + intros IN. apply In_nth_error in IN. destruct IN as [j Hj].
      assert (J : (j < z)%nat). { pose proof (nth_error_lt _ _ _ Hj) as J. rewrite firstn_length_le in J by lia. exact J. }
      rewrite nth_error_firstn in Hj. replace (j <? z)%nat with true in Hj by (symmetry; apply Nat.ltb_lt; exact J). exact (MIN j _ J Hj eq_refl).
  - exfalso. exact (find_byte_None _ _ FB _ _ Hn eq_refl).
Qed.

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
    [CB 40 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

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
    split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - (144 + (128 + 16 + (192 + 16 + (80 + 8192)))))) with (144 + (128 + 16 + (192 + 16 + (80 + 8192)))) by lia; exact WMAP00|].
    split; [right; right; left; exists (h_ff H), HCLASS, ageh; split; [exact HFRh|]; change (fsize HCLASS) with 8192; lia|].
    split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra lo vi q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_3; dand4 dR_3 as _ _ VEPlo _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & _ & VEPlo & _) ]).
    unfold kHighMemBeg in VEPlo. all_app_facts.
    intros P a Ha NO. cbn [outside W] in NO. unfold h_vsc.
    assert (C3 : (bv_unsigned sp - (144 + (128 + 16 + (192 + 16 + (80 + 8192)))) <= a < bv_unsigned sp)
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
    (first [ pose proof (GLOB) as dR_4; dand4 dR_4 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
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
  #[using="SA K LO CEIL WMAP00 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH HENV VBASE VOBJ AINV00 vi ya"] Lemma seg_onerr : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 : word) (m1 : mem) (j40 cnt : list byte),
    vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME j40) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 VEP) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8eaf8) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros HIT MI ST FR VEPC CNT MU WM.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
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
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    assert (AOBJ1 : vsb_obj LPA A0 m1 SA ya true).
    { eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]. }
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    pose proof (as_live_shadow LPA _ _ _ SA 40 AINV00 YLS) as SHS0. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) SA 40 ltac:(lia) ltac:(lia) ltac:(exact SAhi)) as SHSB. rewrite SHMAX_val in SHSB.
    assert (SHS : bytes_at rsegs m1 (sh SA) (shpat 40)).
    { eapply (bytes_at_munch LPA); [exact SHS0| exact MU|]. intros a Ha. cbn. keeplia Ha SHSB GCE VEPlo LO CEIL ACV. }
    clear SHS0.
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
    (first [ pose proof ((cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl))) as dR_8; dex1 dR_8 as z; dand4 dR_8 as ZLE Ebs NZS LZ | pose proof ((cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl))) as dR_8; dand5 dR_8 as z ZLE Ebs NZS LZ | destruct (cstr_split bs (Z.to_nat (vb_len ya)) (NUL eq_refl)) as (z & ZLE & Ebs & NZS & LZ) ]).
    pose proof (proj1 U8) as BY. rewrite Ebs in BY.
    unfold vsb_inv in VINV.
    assert (RA : range_ok (aview A0 m0) (vb_buf ya) (Z.of_nat (length (firstn z bs)) + 1))
      by (eapply (live_range_ok A0 m0 md0); [exact AINV00| exact YLB| lia| rewrite LZ; try (generalize alloc_ceiling_val); clear - ZLE VINV LBS; try pose proof alloc_ceiling_val as ACV__; lia| lia]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (CEq : cenv mq) by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]);
      assert (R1 : range_ok mq A_continue (Z.of_nat (length STR_continue) + 1))
        by (eapply (global_range_ok _ 0x241e0 9 32); [exact CEq| gdesc_in| unfold A_continue; lia| unfold A_continue; cbn; lia| lia
                                                    | unfold pa_static, A_continue; cbn; lia| unfold pa_static, A_continue; cbn; lia]);
      assert (R2 : range_ok mq (vb_buf ya) (Z.of_nat (length (firstn z bs)) + 1))
        by (eapply range_ok_high_munch; [exact RA| exact MU| keeplia BAlo| lia| rewrite LZ; try (generalize alloc_ceiling_val); clear - ZLE VINV LBS BAhi; try pose proof alloc_ceiling_val as ACV__; lia
                                        | repeat (apply Forall_cons); try apply Forall_nil; cbn; rewrite ?SHMAX_val; keeplia LO CEIL ACV GCE VEPlo]);
      icall (strcmp_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq STR_continue (firstn z bs) [] (skipn (S z) bs) lo)
        by (try rewrite !unsigned_lit by (keeplia SPR LO CEIL ACV BAlo BAhi VINV); ufs; unfold STRCMP_ICPT_STACK;
            first [ apply str_continue_at; assumption
                  | exact BY
                  | exact str_continue_nonul
                  | exact NZS
                  | exact (strcmp_icpt_cells_of_consts _ (proj1 CEq))
                  | exact ST
                  | exact CEIL
                  | exact R1 | exact R2
                  | assumption
                  | (left; unfold A_continue; cbn; keeplia LO CEIL ACV)
                  | (left; rewrite <- Ebs, LBS; keeplia BAhi LO CEIL ACV)
                  | (cbn; lia)
                  | keeplia LO ])
    end.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => try clear ST; rename X into ST end.
    repeat match goal with Hb : bytes_at _ _ 147936 _ |- _ => clear Hb | Hb : bytes_at _ _ (vb_buf ya) _ |- _ => clear Hb end.
    clear R1 R2 RA CEq. try clear BY.
    set (rc := strcmp_sign STR_continue (firstn z bs)) in *.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. unhide DJfV. try clear VSBC. try clear U8. zstep. hide DJfV.
    set (ic := Z.b2z (rc mod 18446744073709551616 <? 1)) in *.
    assert (HIC' : bool01 ic) by (subst ic; destruct (rc mod 18446744073709551616 <? 1); cbv; [right|left]; reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    lazymatch goal with FRq : rw_cells _ ?ma (bv_unsigned sp + -144) _, STq : stk _ ?ma lo _ |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STw end.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa;
      (* [comment removed for export] *)
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      (* [comment removed for export] *)
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl)) as dR_9; dand3 dR_9 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 36 (C8 (Z_to_bv 64 SA)) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk;
      change (Z.of_nat 224) with 224 in VM; change (Z.of_nat 224) with 224 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 224 + 8) with (VEP + 232) in VBk by lia
    end.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      assert (AOBJa : vsb_obj LPA A0 (aview A0 mq) SA ya true)
        by (unhide DJfS; unhide DJfB; unhide DJS; unhide DJB;
            eapply vsb_obj_munch; [exact AOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SAhi BAhi DJfS DJfB DJS DJB ACV CEIL LO]) end.
    unhide NAS. unhide NAB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 224) SA ya true lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NAS X)| exact (NAB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact AOBJa | exact TP | exact SP16 | exact STw | exact CEIL | ufs; keeplia LO | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mc mdc. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADS DEADB LIVEq CF1. ufs.
    hide NAS. hide NAB.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (unhide NAS; unhide NAB; rewrite (LIVEq VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV).
    pose proof (sh_boundL (Clg:=Clg) (vb_buf ya) (vb_size ya) ltac:(keeplia BAlo) ltac:(try (generalize alloc_ceiling_val); clear - YINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 YINV); lia) ltac:(exact BAhi)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (sh_boundL (Clg:=Clg) SA 40 ltac:(keeplia SAlo) ltac:(lia) ltac:(exact SAhi)) as SHSA. rewrite SHMAX_val in SHSA.
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mc)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HF; exists age; rewrite (FRS1 ff); exact HF|].
      intros a [X|[X|X]].
      - exists SA, 40. split; [exact YLS|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf ya), (vb_size ya). split; [exact YLB|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    (* [comment removed for export] *)
    unhide DJS. unhide DJB.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 224 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 232)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 232) 80 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJS DJB SHSA SHBB VEPlo] ]
    end.
    hide DJS. hide DJB.
    (* [comment removed for export] *)
    assert (VEPC1 : rw_cells rsegs (aview A1 mc) VEP (vep_cells (fupd (fupd vv Finclude_continue ic) Fattr_vsb 0) tag q)).
    { rewrite <- vep_cells_attr_vsb. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mc) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; change (Z.of_nat 224) with 224; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mc mdc (fupd (fupd vv Finclude_continue ic) Fattr_vsb 0) vi);
      [ exact AINV1 | exact MI1
      | eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]
      | exact ST1 | exact HENV1
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | exact FRS1 | exact TC1 | exact SC1 | exact PC1 (* [comment removed for export] *)
      | right; right; right; split; [exact HIT|]; exists ic; split; [exact HIC'|]; split; [reflexivity|]; split; [reflexivity|];
        split; [exact DEADS|]; split; [exact DEADB|]; split; [exact LB1|]; split; [exact NL1|]; exact LIVEq
      | | ].
    - (* [comment removed for export] *)
      destruct vi as [yi|]; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; [| exact HVI].
      pose proof HVI as (INZ & IOBJ & IERR & NIS & NIB & NISA & NISB & NIBA & NIBB).
      (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_10; dand8 dR_10 as _ SIlo SIhi _ _ BIlo BIhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (_ & SIlo & SIhi & _ & _ & BIlo & BIhi & _) ]).
      (first [ pose proof (IOBJ) as dR_11; dand5 dR_11 as _ IINV LSI LBI _ | pose proof IOBJ as (_ & IINV & LSI & LBI & _) ]).
      unfold kHighMemBeg in SIlo, BIlo. all_app_facts.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI VLV NIS) as DVSI.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI VLV NIB) as DVBI.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI YLS NISA) as DSSA.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI YLS NIBA) as DBSA.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI YLB NISB) as DSBA'.
      pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI YLB NIBB) as DBBA.
      pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
      pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
      change (fsize HCLASS) with 8192 in DJfSI, DJfBI.
      split; [exact INZ|]. split; [| exact IERR].
      lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
        assert (IOBJa : vsb_obj LPA A0 ma (vv Finclude_src) yi true)
          by (eapply vsb_obj_munch; [exact IOBJ | exact MU | exact WM | intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]);
        eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact IOBJa| keeplia CEIL LO
          | rewrite (LIVEq _ NISA NISB); exact LSI | rewrite (LIVEq _ NIBA NIBB); exact LBI |]
      end.
      intros a Ha X. unfold newblk, blk in X.
      pose proof (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(lia) ltac:(exact SIhi)) as SHSI. rewrite SHMAX_val in SHSI.
      pose proof (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(try (generalize alloc_ceiling_val); clear - IINV; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 IINV); lia) ltac:(exact BIhi)) as SHBI. rewrite SHMAX_val in SHBI.
      keeplia Ha X DVSI DVBI DSSA DBSA DSBA' DBBA SHSA SHBB SIlo BIlo VEPlo.
    - (* [comment removed for export] *)
      eapply (cframe_extend LPA _ _ (bv_unsigned sp) _ (bv_unsigned sp) _ _ _ _ _ (aview A0 m0) _ (aview A1 mc) (aview A1 mc) _ []);
        [ exact MU | | exact CF1 | clear; lia | clear; lia | | intros a X; left; exact X | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | keeplia LO | clear; lia] ].
      + ufs. apply W_cover.
      + intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]].
  Qed.
End S.
