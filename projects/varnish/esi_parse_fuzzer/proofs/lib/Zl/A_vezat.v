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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.

Module A_vekxy.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.
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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l c8 c16 c64 lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL : 1 <= l < 2^62.
  Hypothesis HC8 : 0 <= c8 < 256.
  Hypothesis HC16 : 0 <= c16 < 256.
  Hypothesis HC64 : 0 <= c64 < 256.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITLEN_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv tag q ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 1 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITLEN_STACK
             (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj HL (conj HC8 (conj HC16 (conj HC64 (conj VOBJ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Definition fr_alloc (A A1 : AS) (ff : Z) : Prop :=
       a_frame A ff = None /\ a_frame A1 ff = Some (0, 0%nat)
    /\ (forall g k' age', g <> ff -> a_frame A g = Some (k', age') -> a_frame A1 g = Some (k', if Z.eqb k' 0 then Datatypes.S age' else age'))
    /\ (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None)
    /\ (forall q0, a_live A1 q0 = a_live A q0) /\ a_livebytes A1 = a_livebytes A /\ a_tinycred A1 = a_tinycred A /\ a_nlive A1 = a_nlive A
    /\ a_seccred A1 = a_seccred A
    /\ a_primcred A1 = a_primcred A   (* [comment removed for export] *)
    /\ ff mod 32 = 0 /\ app_range LPA ff 64 (* [comment removed for export] *) /\ ff + 64 <= alloc_ceiling /\ 0 <= sh ff /\ sh ff + 8 <= SHMAX.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ VOBJ HC64 HC16 HC8 HL AINV00"] Lemma EL_C : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (d ff : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                      (vr2 : vsb_rec) (j32 fj shj : list byte),
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp - 128 - d) -> stk rsegs (aview A2 m2) (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp - 128)
             [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc A0 A1 ff -> frames_same A1 A2 ->
    length fj = 56%nat -> rw_cells rsegs (aview A2 m2) ff [CB 56 fj] ->
    length shj = 8%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 8 shj] ->
    vep_obj LPA A2 (aview A2 m2) VEP vv tag q -> vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.min 9 (2 + l) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) EMITLEN_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 0 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 128 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp - 128 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 VEP) (Z_to_bv 64 l) (Z_to_bv 64 c64) (Z_to_bv 64 c16) (Z_to_bv 64 c8)
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x909e0) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 AINV MI MDF STlo STpad FR FA FS12 LFJ FFC LSH SHC VEPO SOBJ2 LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PC2 CF02.
    prelims.
    (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PC1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PC1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts. try (unhide_app_of ff).
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : a_frame A2 ff = Some (0, 0%nat)) by (rewrite (FS12 ff); exact FF1).
    (* [comment removed for export] *)
    (first [ pose proof ((fframe_flag A2 m2 md2 ff 0 0%nat AINV FF2)) as dR_2; dex2 dR_2 as fa fb; dand6 dR_2 as FAW FB FRO FRW FOW FNI | pose proof ((fframe_flag A2 m2 md2 ff 0 0%nat AINV FF2)) as dR_2; dand8 dR_2 as fa fb FAW FB FRO FRW FOW FNI | destruct (fframe_flag A2 m2 md2 ff 0 0%nat AINV FF2) as (fa & fb & FAW & FB & FRO & FRW & FOW & FNI) ]).
    change (fsize 0) with 64 in FRO. replace (ff + 64 - 8) with (ff + 56) in FRO by lia.
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_3; dand4 dR_3 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A2 m2 md2 VEP _ AINV VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A2 m2 md2 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ2) as dR_6; dand6 dR_6 as _ VINV2 VLS VLB VNE _ | pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat VEP 312 AINV FF2 VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat _ _ AINV FF2 VLB) as DJfB.
    change (fsize 0) with 64 in DJfV, DJfS, DJfB.
    pose proof (owned_outside_live A2 m2 md2 VEP 312 _ AINV VLV FOW) as OWV.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLS FOW) as OWS.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLB FOW) as OWB.
    pose proof (owned_outside_fframe A2 m2 md2 ff 0 0%nat _ AINV FF2 FOW) as [OWF OWSH].
    change (fsize 0) with 64 in OWF, OWSH. change (64 / 8) with 8 in OWSH.
    hide DJfV. hide DJfS. hide DJfB. hide OWV. hide OWS. hide OWB. hide VEPC. hide DSB. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFR : client_fp_rel LPA A2 [ff] (aview A2 m2) [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)]).
    { unfold client_fp_rel. split; [| split; [| split; [| exact I]]].
      - right; right; right; left. exists ff, 0, 0%nat. split; [exact FF2|]. change (fsize 0 / 8) with 8. lia.
      - right; right; left. exists ff, 0, 0%nat. split; [exact FF2|]. change (fsize 0) with 64. lia.
      - right; right; right; right. exists ff, 0, 0%nat, (Z_to_bv 64 fa). split; [left; reflexivity|]. split; [exact FF2|].
        split; [exact FB|]. rewrite unsigned_lit by (keeplia FAW ACV); split; reflexivity. }
    hide FB.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1. sb1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. fix_neg. do 8 sb1.
    (* [comment removed for export] *)
    zstep. unhide OWV. unhide OWS. unhide OWB. try clear FRO. sb1. hide OWV. hide OWS. hide OWB. zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by lia.
    do 12 zstep. zstep.
    try replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with ST1 : stk _ ?mq lo _, ST2 : stk _ ?mq (bv_unsigned sp - 128 - d) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (stk_merge rsegs mq _ _ _ ST1 ST2 ltac:(keeplia D0 LO CEIL ACV)) as STm; clear ST1 ST2 end.
    lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp - 128) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FRq STm (bv_unsigned sp) end.
    (* [comment removed for export] *)
    lazymatch goal with FLq : rw_cells _ ?mq fa [C1 ?b] |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (flag_cleared (Clg:=Clg) mq fa FLq FNI ltac:(keeplia FAW ACV)) as FL end.
    unhide FB. astop_rel1 AINV FF2 FB MU WM CFR FL.
    (first [ pose proof ((as_release_spec LPA A2 m2 md2 ff 0 0%nat AINV FF2)) as dR_7; dand11 dR_7 as RN RO RL RLB RTC RSC RPC RNL RH RE ROW | destruct (as_release_spec LPA A2 m2 md2 ff 0 0%nat AINV FF2) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW) ]).
    unhide VEPC.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a_release A2 ff) m1 md1 vr2);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | assumption
      | (* [comment removed for export] *) split; [rewrite RL; exact VLV|]; split; [| split; [exact TAG8| exact PADS]];
        eapply (rw_cells_munch LPA); [exact VEPC| exact MU| exact WM|];
        rewrite (vep_cells_size vv tag q TAG8 PADS); change (Z.of_nat 312) with 312;
        intros a Ha; cbn; keeplia Ha DJfV OWV SH1 VEPlo
      | (* [comment removed for export] *)
        (first [ pose proof (SOBJ2) as dR_8; dand6 dR_8 as XC XI XLS XLB XNE XB | pose proof SOBJ2 as (XC & XI & XLS & XLB & XNE & XB) ]); split; [| split; [exact XI| split; [rewrite RL; exact XLS| split; [rewrite RL; exact XLB| split; [exact XNE|]]]]];
        [ eapply (rw_cells_munch LPA); [exact XC| exact MU| exact WM|]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40;
          intros a Ha; cbn; keeplia Ha DJfS OWS SH1 Slo
        | (first [ dex1 XB as bs; dand3 XB as [UB UW] LENx NULx | dand4 XB as bs [UB UW] LENx NULx | destruct XB as (bs & [UB UW] & LENx & NULx) ]); exists bs; split; [| split; [exact LENx| exact NULx]]; split;
          [ eapply (bytes_at_munch LPA); [exact UB| exact MU| rewrite LENx; intros a Ha; cbn; keeplia Ha DJfB OWB SH1 Blo]
          | eapply wr_at_transport; [exact UW| exact WM] ] ]
      | exact LEN2 | exact SZ2
      | destruct REL2 as [E|[E1 E2]]; [left; exact E| right; split; [rewrite <- (LV1 (vb_buf vr2)); exact E1| rewrite RL; exact E2]]
      | intros p Hp1 Hp2; rewrite RL, (LIVEq2 p Hp1 Hp2); apply LV1
      | eapply (frames_aged_alloc_release A0 A1 A2 m2 md2 ff 0); [left; reflexivity| exact FN| exact FF1| exact AGE| exact NONE| exact FS12| exact AINV| exists 0%nat; exact FF2]
      | rewrite RLB, LB2, LB1; reflexivity
      | rewrite RTC, TC2, TC1; reflexivity
      | rewrite RNL, NL2, NL1; reflexivity
      | rewrite RSC; try (generalize alloc_ceiling_val); clear - SC2 SC1; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite RPC; clear - PC2 PC1; lia (* [comment removed for export] *)
      | ]
    end.
    (* [comment removed for export] *)
    ufs. eapply (cframe_release (owned A0) (owned A2) (owned (a_release A2 ff))); [exact CF02| exact MU| | keeplia LO CEIL ACV| keeplia SPR| | | intros a X; right; exact X].
    - intros a Ha NO. cbn [outside] in NO.
      assert (CS : sh ff <= a < sh ff + 8 \/ ff <= a < ff + 8 \/ a = fa) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
      destruct CS as [X|[X|X]]; [left; left; right; change (fsize 0 / 8) with 8; exact X| left; left; left; change (fsize 0) with 64; keeplia X| right; rewrite X; exact FOW].
    - intros i Hi. cbn. keeplia Hi SH1 FHI FAW LO CEIL ACV.
    - intros a Oa. apply ROW in Oa. destruct Oa as [X|[X|X]]; [left; exact X| right; left; left; change (fsize 0) with 64 in *; keeplia X| right; left; right; exact X].
  Qed.
End S.
End A_vekxy.


Module A_vemp4.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.A_Bits.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSbb4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Import ListNotations.
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


(* [comment removed for export] *)
Lemma be64_redecode_pub : forall l, 0 <= l < 2^62 ->
  Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftr (Z.shiftl (l / 281474976710656) 56 mod 18446744073709551616) 40)
                                (Z.shiftl (l / 72057594037927936) 24 mod 18446744073709551616))
                         (Z.lor (Z.shiftr (Z.shiftl (l / 1099511627776) 56 mod 18446744073709551616) 48)
                                (Z.land (l / 4294967296) 255))) 32 mod 18446744073709551616)
        (l mod 4294967296) = l.
Proof.
  intros l Hl.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  set (A := l / 281474976710656 * 2 ^ 56 mod 18446744073709551616 / 2 ^ 40).
  set (B := l / 72057594037927936 * 2 ^ 24 mod 18446744073709551616).
  set (C := l / 1099511627776 * 2 ^ 56 mod 18446744073709551616 / 2 ^ 48).
  set (D := (l / 4294967296) mod 2 ^ 8).
  assert (EA : A = ((l / 281474976710656) mod 2^8) * 2^16) by (subst A; mlia).
  assert (EB : B = (l / 72057594037927936) * 2^24 /\ 0 <= l / 72057594037927936 < 2^6) by (subst B; mlia).
  assert (EC : C = ((l / 1099511627776) mod 2^8) * 2^8) by (subst C; mlia).
  assert (ED : 0 <= D < 2^8) by (subst D; mlia).
  rewrite (lor_add' A B 24) by mlia.
  rewrite (lor_add C D 8) by mlia.
  rewrite (lor_add (A + B) (C + D) 16) by mlia.
  rewrite (Z.mod_small ((A + B + (C + D)) * 2^32)) by mlia.
  rewrite (lor_add ((A + B + (C + D)) * 2^32) (l mod 4294967296) 32) by mlia.
  subst D. mlia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l c8 c16 c64 lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL : 1 <= l < 2^62.
  Hypothesis HC8 : 0 <= c8 < 256.
  Hypothesis HC16 : 0 <= c16 < 256.
  Hypothesis HC64 : 0 <= c64 < 256.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITLEN_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv tag q ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 1 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITLEN_STACK
             (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj HL (conj HC8 (conj HC16 (conj HC64 (conj VOBJ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EL_C' := EL_C (* [comment removed for export] *) VEP vv tag q vr l c8 c16 c64 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                       AINV00 HL HC8 HC16 HC64 VOBJ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition code_post (xra xsp : word) (t2 : word) (xs0 xs1 : word) (ff : Z) (t3 t4 t5 t6 : word)
      (mg dsc pcw : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 a0 a3 a4 a5 a6 a7 : word) (m' : mem) (j8 w9 j15 code : list byte),
      ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0 (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (Z.of_nat (length code))) a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 VEP) (Z_to_bv 64 l) (Z_to_bv 64 c64) (Z_to_bv 64 c16) (Z_to_bv 64 c8)
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x909c4) fc None m' (seg_rom rsegs)
      /\ munch [(ff + 32, ff + 41)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' ff [C8 mg; C8 dsc; C8 pcw; CB 8 j8; CB 9 w9; CB 15 j15]%list
      /\ bytes_at rsegs m' (ff + 32) code /\ 1 <= Z.of_nat (length code) <= 9 /\ Z.of_nat (length code) <= 2 + l.

  (* [comment removed for export] *)
  Local Ltac seg_finish ff FR MU WM w9 code :=
    let WF := fresh "WF" in
    pose proof FR as [[WF _] _]; cbn [cells_wf cell_wf] in WF;
    lazymatch type of FR with rw_cells _ ?mx ?A (C8 ?mg :: C8 ?dsc :: C8 ?pcw :: CB 8 ?j8 :: ?rest) =>
      lazymatch rest with context [CB 15 ?j15] =>
      apply (rw_cells_recast rsegs mx A _ [C8 mg; C8 dsc; C8 pcw; CB 8 j8; CB 9 w9; CB 15 j15]) in FR;
        [ | cbn [cells_wf cell_wf length]; cbn [length] in WF; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia
          | cbn [cells_bytes cbytes app]; reflexivity ];
      let B := fresh "B" in
      pose proof (rw_cells_bytes_at_cell rsegs mx A _ 32 (CB 9 w9) FR eq_refl) as B;
      cbn [cbytes cells_size csize Nat.add firstn] in B;
      replace (A + Z.of_nat 32) with (ff + 32) in B by lia;
      apply (bytes_at_prefix rsegs mx _ code) in B;
      apply evt_done; unfold code_post;
      hot_eexists_k8; eexists mx, j8, w9, j15, code;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
      split; [exact FR|]; split; [exact B| cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    end end.

  (* [comment removed for export] *)
  Local Ltac ubguard K FHI F0 ACV :=
    exfalso; revert K FHI F0 ACV; clear; intros K FHI F0 ACV; first [rewrite Z.mod_small in K by lia | idtac]; lia.
  Local Ltac gstep tac := let G := fresh "G" in zstep; if_cases G; zify_cond G; [ tac G |]; try clear G.

  #[using="S HC64 HC16 HC8 HL sp vv AI"] Lemma emit_code_seg :
    forall (xra xsp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (ff : Z) (mg dsc pcw : word) (j8 w0 j15 : list byte),
      app_range LPA ff 64 (* [comment removed for export] *) -> ff + 64 <= alloc_ceiling -> ff mod 32 = 0 -> 0 <= sh ff -> sh ff + 8 <= 17594333495296 ->
      rw_cells rsegs m ff [C8 mg; C8 dsc; C8 pcw; CB 8 j8; CB 9 w0; CB 15 j15] -> mem_inv rsegs m ->
      0 <= VEP < 2^64 -> VEP mod 8 = 0 ->   (* [comment removed for export] *)
      evt rsegs (code_post xra xsp t2 xs0 xs1 ff t3 t4 t5 t6 mg dsc pcw m)
        (MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ff) (Z_to_bv 64 VEP) (Z_to_bv 64 l) (Z_to_bv 64 c64) (Z_to_bv 64 c16) (Z_to_bv 64 c8)
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9089c) fc None m (seg_rom rsegs)).
  Proof.
    intros until j15. intros FLO FHI FAL SH0 SH1 FR MI VR V8. all_app_facts. try (unhide_app_of ff).
    pose proof HL as HL'. pose proof HC8 as HC8'. pose proof HC16 as HC16'. pose proof HC64 as HC64'. pose proof alloc_ceiling_num as ACV.
    pose proof (munch_refl [(ff + 32, ff + 41)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (F0 : 0 <= ff) by (keeplia SH0).
    assert (L7 : Z.land VEP 7 = 0) by (apply land7_of_mod8; [clear - VR; lia | exact V8]).
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA; [exfalso; try (generalize alloc_ceiling_val); clear - KA HL'; try pose proof alloc_ceiling_val as ACV__; lia| ]. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        (* [comment removed for export] *)
        zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        (* [comment removed for export] *)
        do 13 zstep. sb1.
        zstep. if_cases KT; zify_cond KT.
        { exfalso. apply KT. apply be64_redecode_pub. clear - HL'; lia. }
        clear KT.
        (* [comment removed for export] *)
        zstep. rewrite L7. gstep ltac:(fun G => exfalso; apply G; reflexivity). zstep.
        lazymatch type of FR with rw_cells _ _ _ [_; _; _; _; C1 ?b0; C1 ?b1; C1 ?b2; C1 ?b3; C1 ?b4; C1 ?b5; C1 ?b6; C1 ?b7; C1 ?b8; _] =>
          seg_finish ff FR MU WM [b0; b1; b2; b3; b4; b5; b6; b7; b8] [b0; b1; b2; b3; b4; b5; b6; b7; b8] end.
      + (* [comment removed for export] *)
        zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
        zstep. rewrite L7. sb1. gstep ltac:(fun G => exfalso; apply G; reflexivity).
        zstep. zstep.
        lazymatch type of FR with rw_cells _ _ _ [_; _; _; _; C1 ?b0; C1 ?b1; C1 ?b2; CB 6 ?r; _] =>
          seg_finish ff FR MU WM (b0 :: b1 :: b2 :: r) [b0; b1; b2] end.
    - (* [comment removed for export] *)
      zstep. sb1. gstep ltac:(fun G => ubguard G FHI F0 ACV).
      zstep. rewrite L7. sb1. gstep ltac:(fun G => exfalso; apply G; reflexivity).
      zstep. zstep.
      lazymatch type of FR with rw_cells _ _ _ [_; _; _; _; C1 ?b0; C1 ?b1; CB 7 ?r; _] =>
        seg_finish ff FR MU WM (b0 :: b1 :: r) [b0; b1] end.
  Qed.
End S.
End A_vemp4.

Module A_vehtf.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.A_Bits.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSbb4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vemp4.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l c8 c16 c64 lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL : 1 <= l < 2^62.
  Hypothesis HC8 : 0 <= c8 < 256.
  Hypothesis HC16 : 0 <= c16 < 256.
  Hypothesis HC64 : 0 <= c64 < 256.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITLEN_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv tag q ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 1 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITLEN_STACK
             (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj HL (conj HC8 (conj HC16 (conj HC64 (conj VOBJ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EL_C' := EL_C (* [comment removed for export] *) VEP vv tag q vr l c8 c16 c64 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                       AINV00 HL HC8 HC16 HC64 VOBJ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  Local Definition emit_code_seg' := emit_code_seg (* [comment removed for export] *) VEP vv l c8 c16 c64 sp gp tp s11 F fc HL HC8 HC16 HC64.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ VOBJ HC64 HC16 HC8 HL AINV00 AI16"] Lemma EL_B2 : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs10 : word) (d ff : Z) (A1 : AS) (m1 : mem) (md1 : Model)
                       (j32 fj : list byte),
    0 <= d <= 16 -> (bv_unsigned sp - 128 - d) mod 16 = 0 ->
    ainv A1 m1 md1 -> mem_inv rsegs (aview A1 m1) -> amd_frame md0 md1 ->
    stk rsegs (aview A1 m1) lo (bv_unsigned sp - 128 - d) -> stk rsegs (aview A1 m1) (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) ->
    rw_cells rsegs (aview A1 m1) (bv_unsigned sp - 128)
             [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc A0 A1 ff ->
    length fj = 56%nat -> rw_cells rsegs (aview A1 m1) ff [CB 56 fj] ->
    rw_cells rsegs (aview A1 m1) (sh ff) (zcells 8) ->
    vep_obj LPA A1 (aview A1 m1) VEP vv tag q -> vsb_obj LPA A1 (aview A1 m1) S vr false ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) EMITLEN_STACK nowhere (frm ff 0) (aview A0 m0) (aview A1 m1) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 128 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp - 128 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 VEP) (Z_to_bv 64 l) (Z_to_bv 64 c64) (Z_to_bv 64 c16) (Z_to_bv 64 c8)
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) xs10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90844) fc None m1 (seg_rom rsegs)) md1) T.
  Proof.
    touch_all. intros until fj. intros D0 AL16 AINV MI MDF STlo STpad FR FA LFJ FFC SHC VEPO SOBJ1 CF01.
    prelims.
    pose proof FA as FA'. (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PC1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PC1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts. try (unhide_app_of ff).
    pose proof (as_minv LPA A1 _ _ AINV) as [_ MH].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A1 m1 md1 VEP _ AINV VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A1 m1 md1 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A1 m1 md1 S vr false AINV SOBJ1)) as dR_4; dand11 dR_4 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A1 m1 md1 S vr false AINV SOBJ1) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ1) as dR_5; dand6 dR_5 as _ VINV1 VLS VLB VNE _ | pose proof SOBJ1 as (_ & VINV1 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat VEP 312 AINV FF1 VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat _ _ AINV FF1 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat _ _ AINV FF1 VLB) as DJfB.
    change (fsize 0) with 64 in DJfV, DJfS, DJfB.
    pose proof (as_live_disjoint LPA A1 m1 md1 S 40 VEP 312 AINV VLS VLV (not_eq_sym NES)) as DJS.
    pose proof (as_live_disjoint LPA A1 m1 md1 (vb_buf vr) (vb_size vr) VEP 312 AINV VLB VLV (not_eq_sym NEB)) as DJB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    hide DJfV. hide DJfS. hide DJfB. hide DJS. hide DJB. hide DSB. hide VEPC. hide SHV0. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(ff, ff + 24); (sh ff, sh ff + 8); (ff + 32, ff + 41)] (aview A1 m1)) as MU.
    pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    assert (CFP : client_fp LPA A1 (aview A1 m1) [(ff, ff + 24); (sh ff, sh ff + 8); (ff + 32, ff + 41)]).
    { cbn. split; [right; right; left; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0) with 64; lia]|].
      split; [right; right; right; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0 / 8) with 8; lia]|].
      split; [right; right; left; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0) with 64; lia]| exact I]. }
    unfold zcells in SHC. cbn [repeat] in SHC.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (shr3_div8 ff). zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. change (ff / 8 + 2147450880) with (sh ff).
    (* [comment removed for export] *)
    fix_neg. sb1. sb1. sb1. sb1. zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    lazymatch type of FFC with rw_cells _ ?mx _ [C8 ?mg; C8 ?dsc; C8 ?pcw; CB 32 ?jk] =>
      apply (rw_cells_split_CB rsegs mx ff [C8 mg; C8 dsc; C8 pcw] 32 jk [] [8; 9; 15]%nat) in FFC; [| reflexivity];
      cbn [mk_CB_cells app] in FFC end.
    change (0 mod 256) with 0 in SHC. change (1 mod 256) with 1 in SHC.
    assert (ESH : sh (ff + 32) = sh ff + 4) by (unfold sh; replace (ff + 32) with (4 * 8 + ff) by lia; rewrite Z.div_add_l by lia; lia).
    assert (F8 : (ff + 32) mod 8 = 0).
    { rewrite Z.add_mod by lia. replace (ff mod 8) with 0; [reflexivity|]. symmetry.
      pose proof (Z.div_mod ff 32 ltac:(lia)) as Dv. rewrite FAL, Z.add_0_r in Dv. rewrite Dv.
      replace (32 * (ff / 32)) with ((4 * (ff / 32)) * 8) by lia. apply Z_mod_mult. }
    lazymatch type of SHC with rw_cells _ ?mx _ [C1 ?x0; C1 ?x1; C1 ?x2; C1 ?x3; C1 ?y0; C1 ?y1; C1 ?z0; C1 ?z1] =>
      pose proof (proj2 (proj1 SHC)) as BSH; cbn [cells_bytes cbytes app] in BSH;
      change (bytes_at rsegs mx (sh ff) ([x0; x1; x2; x3] ++ ([y0; y1] ++ [z0; z1]))) in BSH;
      apply bytes_at_app in BSH; destruct BSH as [_ BSH]; apply bytes_at_prefix in BSH; change (Z.of_nat (length [x0; x1; x2; x3])) with 4 in BSH;
      rewrite <- ESH in BSH; change [y0; y1] with (shpat 9) in BSH end.
    (* [comment removed for export] *)
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    eapply evt_cut; [eapply emit_code_seg'; [exact FLO_a | exact FHI | exact FAL | exact SH0 | keeplia SH1 | exact FFC | assumption | keeplia VEPlo VEPhi ACV | exact V8] |].
    cbv beta. intros ms' POST.
    (first [ dex13 POST as xt0 xt1 xa0 xa3 xa4 xa5 xa6 xa7 m' j8 w9 j15 code; dand8 POST as -> MUs WMs MI' FR' BSRC LC1 LC2 | dand21 POST as xt0 xt1 xa0 xa3 xa4 xa5 xa6 xa7 m' j8 w9 j15 code -> MUs WMs MI' FR' BSRC LC1 LC2 | destruct POST as (xt0 & xt1 & xa0 & xa3 & xa4 & xa5 & xa6 & xa7 & m' & j8 & w9 & j15 & code & -> & MUs & WMs & MI' & FR' & BSRC & LC1 & LC2) ]).
    clear FFC. lazymatch type of MUs with munch _ ?mq _ => transport_after_call rsegs mq m' MUs WMs; clear MUs WMs; try clear MI; try clear mq end.
    rename FR' into FFC.
    (* [comment removed for export] *)
    unhide DJfV.
    assert (SHD : sh ff + 8 <= sh VEP \/ sh VEP + 39 <= sh ff) by (unfold sh; clear - DJfV; try pose proof alloc_ceiling_val as ACV__; mlia).
    hide DJfV. unhide SHV0. unhide VEPC.
    assert (SHV : bytes_at rsegs m' (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV' || idtac. intros a Ha. cbn. keeplia Ha LZV SHD SHVB FLO. }
    assert (VEPC1 : rw_cells rsegs m' VEP (vep_cells vv tag q)).
    { eapply (rw_cells_munch LPA); [exact VEPC| exact MU| exact WM|]. rewrite (vep_cells_size vv tag q TAG8 PADS). change (Z.of_nat 312) with 312.
      unhide DJfV. intros a Ha. cbn. keeplia Ha DJfV VEPlo SH1. }
    hide SHV0. hide VEPC. hide SHD.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0.
    unfold vep_cells in VEPC1. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized md1 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVb; rename SBq into SBMb;
      lazymatch goal with SHCq : rw_cells _ (aview A1 mq) (sh ff) _ |- _ =>
      (* [comment removed for export] *)
      lazymatch type of SHCq with rw_cells _ ?mx _ [C1 ?x0; C1 ?x1; C1 ?x2; C1 ?x3; C1 ?y0; C1 ?y1; C1 ?z0; C1 ?z1] =>
        pose proof (proj2 (proj1 SHCq)) as BSH; cbn [cells_bytes cbytes app] in BSH;
        change (bytes_at rsegs mx (sh ff) ([x0; x1; x2; x3] ++ ([y0; y1] ++ [z0; z1]))) in BSH;
        apply bytes_at_app in BSH; destruct BSH as [_ BSH]; apply bytes_at_prefix in BSH; change (Z.of_nat (length [x0; x1; x2; x3])) with 4 in BSH;
        rewrite <- ESH in BSH; change [y0; y1] with (shpat 9) in BSH end end;
      unhide DJfS; unhide DJfB;
      eapply (VSB_bcat_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq mdq A1 S (ff + 32) code vr lo T);
      [ exact AINVb | assumption | rewrite ES; reflexivity | reflexivity | reflexivity
      | eapply vsb_obj_munch; [exact SOBJ1| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfS DJfB Slo Blo SH1]
      | exact BSRC | exact LC1
      | right; exists ff, 0, 0%nat, (ff + 32), 9; split; [exact FF1|]; change (fsize 0) with 64;
        split; [lia|]; split; [lia|]; split; [exact F8|];
        split; [lia|]; split; [keeplia LC1| exact BSH]
      | exact EM | rewrite LB1; exact LBM | rewrite NL1; exact NLV | rewrite SC1; exact SCM | rewrite PC1; exact PCM (* [comment removed for export] *) | exact TP
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact AL16
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact STlo | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); ufs; keeplia LO D0 | ]
    end.
    hide DJfS. hide DJfB.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m2 md2 vr2. cbv zeta.
    intros AINV2 MI2 MDF2 SOBJ2 LEN2 SZ2 LIVEq REL FS12 LB2 TC2 NL2 SC2 PC2 ST2 CF2.
    rewrite unsigned_lit in ST2, CF2 by (keeplia SPR LO CEIL ACV D0). ufs.
    replace (ret_pc (Z_to_bv 64 0x909e0)) with (Z_to_bv 64 0x909e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(pose proof (proj1 VINV1); lia) ltac:(exact Bhi)) as SHB. rewrite SHMAX_val in SHB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(lia) ltac:(exact Shi)) as SHS. rewrite SHMAX_val in SHS.
    unhide DJfS. unhide DJfB.
    assert (SHDS : sh ff + 8 <= sh S \/ sh S + (40 + 7) / 8 <= sh ff) by (unfold sh; clear - DJfS; try pose proof alloc_ceiling_val as ACV__; mlia).
    assert (SHDB : sh ff + 8 <= sh (vb_buf vr) \/ sh (vb_buf vr) + (vb_size vr + 7) / 8 <= sh ff) by (unfold sh; clear - DJfB FAL; try pose proof alloc_ceiling_val as ACV__; mlia).
    (* [comment removed for export] *)
    unhide NEB.
    assert (NEB2 : VEP <> vb_buf vr2).
    { destruct REL as [E|[E _]]; [rewrite E; exact NEB|]. intros X. rewrite <- X, VLV in E. discriminate E. }
    assert (LVEP2 : a_live A2 VEP = Some 312) by (rewrite (LIVEq VEP NEB NEB2); exact VLV).
    hide NEB.
    (* [comment removed for export] *)
    lazymatch type of CF2 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      (* [comment removed for export] *)
      lazymatch goal with ST1 : stk _ ma lo _, ST1' : stk _ ma (bv_unsigned sp - 128 - d) _, FRq : rw_cells _ ma (bv_unsigned sp - 128) _ |- _ =>
        pose proof (stk_merge rsegs ma _ _ _ ST1 ST1' ltac:(keeplia D0 LO CEIL ACV)) as STma;
        assert (MPa : mapped ma (bv_unsigned sp - (128 + 16 + (80 + (80 + 8192)))) (128 + 16 + (80 + (80 + 8192))))
          by (eapply (window_mapped LPA _ lo); [exact STma | exact FRq | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]);
        clear STma ST1 end;
      lazymatch goal with STq : stk _ ma (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) |- _ =>
        apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINVb CF2) in STq;
        [ rename STq into STpad2 | keeplia LO CEIL D0 | intros a Ha X; unfold newblk, blk in X; keeplia Ha X Bhi Shi SHB LO CEIL ACV D0 ] end;
      lazymatch goal with FRq : rw_cells _ ma (bv_unsigned sp - 128) ?fcs |- _ =>
        pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp - 128) 128 AINVb ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                      (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRq ltac:(off_image_solve LPA))) as CRF;
        apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 _ fcs) in FRq;
        [ rename FRq into FR2 | exact CRF
        | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0|];
          intros i Hi X; unfold newblk, blk in X; keeplia Hi X Bhi Shi SHB LO CEIL ACV ];
        clear CRF end;
      lazymatch goal with FFCq : rw_cells _ ma ff ?fcs |- _ =>
        pose proof FFCq as [[WFF _] _]; cbn [cells_wf cell_wf] in WFF;
        apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 ff fcs) in FFCq;
        [ rename FFCq into FFC2
        | eapply crange_fframe; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0) with 64; lia| cbn; lia]
        | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia FHI LO CEIL D0|];
          intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJfS DJfB SHB SHS FLO ] end;
      lazymatch goal with SHCq : rw_cells _ ma (sh ff) ?scs |- _ =>
        apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (sh ff) scs) in SHCq;
        [ rename SHCq into SHC2
        | eapply crange_fshadow; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0 / 8) with 8; lia| cbn; lia]
        | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SH1 LO CEIL ACV D0|];
          intros i Hi X; unfold newblk, blk in X; keeplia Hi X SHDS SHDB Slo Blo SH1 ] end;
      assert (VEPO2 : vep_obj LPA A2 mb VEP vv tag q);
      [ unhide DJS; unhide DJB; unhide VEPC; unhide DJfV;
        eapply (vep_obj_ccall LPA A1 A2); [exact AINVb| exact CF2| | keeplia LO CEIL D0| exact LVEP2|];
        [ eapply vep_obj_munch; [exact VEPO| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfV VEPlo SH1]
        | intros a Ha X; unfold newblk, blk in X; keeplia Ha X DJS DJB SHB VEPlo ]
      | hide DJS; hide DJB ]
    end.
    (* [comment removed for export] *)
    destruct (rw_cells_forget rsegs _ _ _ FFC2) as [fj2 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
    pose proof FFC3 as [[WF3 _] _]. cbn [cells_wf cell_wf] in WF3.
    destruct (rw_cells_forget rsegs _ _ _ SHC2) as [shj2 SHC3]. cbn [cells_size csize Nat.add] in SHC3.
    pose proof SHC3 as [[WS3 _] _]. cbn [cells_wf cell_wf] in WS3.
    (* [comment removed for export] *)
    eapply (EL_C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A2 m2 md2 vr2 _ fj2 shj2);
      [ exact D0 | exact AINV2 | exact MI2
      | eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBMb| exact MH| exact MDF2]
      | exact ST2 | exact STpad2 | exact FR2 | exact FA' | exact FS12
      | exact (proj1 WF3) | exact FFC3 | exact (proj1 WS3) | exact SHC3
      | exact VEPO2 | exact SOBJ2 | keeplia LEN2 LC1 LC2 | exact SZ2 | exact REL | exact LIVEq | exact LB2 | exact TC2 | exact NL2 | exact SC2 | exact PC2 | ].
    (* [comment removed for export] *)
    assert (MP2 : mapped (aview A2 m2) (bv_unsigned sp - (128 + 16 + (80 + (80 + 8192)))) (128 + 16 + (80 + (80 + 8192)))).
    { pose proof (stk_merge rsegs (aview A2 m2) _ _ _ ST2 STpad2 ltac:(keeplia D0 LO CEIL ACV)) as STm.
      eapply (window_mapped LPA _ lo); [exact STm | exact FR2 | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
    lazymatch type of CF2 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      assert (CFa : cframe LPA (owned A0) (owned A1) (bv_unsigned sp) (128 + 16 + (80 + (80 + 8192)))
                      (fun a => newblk (vb_buf vr) (vb_size vr) a \/ S <= a < S + 40) (frm ff 0) (aview A0 m0) ma);
      [ eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A0 m0) (aview A1 m1) ma [] _);
        [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF01 | keeplia SPR | keeplia SPR
        | intros a X; destruct X | intros a X; left; exact X | exact MU | | ]
      | eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) ma mb CFa);
        [ eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (128 + 16 + (80 + (80 + 8192)))); [exact CF2| keeplia D0| keeplia D0| exact MP2]
        | ufs; keeplia SPR | ufs; keeplia SPR | exact MP2 | intros a X; exact X | intros a X; right; exact X | ] ]
    end.
    - (* [comment removed for export] *)
      intros a Ha NO. cbn [outside] in NO. right; right. unfold frm. change (fsize 0) with 64. change (64 / 8) with 8. keeplia Ha NO.
    - exact MPa.
    - (* [comment removed for export] *)
      intros a [X|X]; [left; exact X| right; left; exact X].
  Qed.
End S.
End A_vehtf.


Module A_vewqv.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.A_Bits.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSbb4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vemp4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vehtf.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

(* [comment removed for export] *)
Lemma mod16_of_mod32 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l c8 c16 c64 lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL : 1 <= l < 2^62.
  Hypothesis HC8 : 0 <= c8 < 256.
  Hypothesis HC16 : 0 <= c16 < 256.
  Hypothesis HC64 : 0 <= c64 < 256.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITLEN_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv tag q ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 1 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITLEN_STACK
             (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj HL (conj HC8 (conj HC16 (conj HC64 (conj VOBJ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EL_B2' := EL_B2 (* [comment removed for export] *) VEP vv tag q vr l c8 c16 c64 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                        AINV00 HL HC8 HC16 HC64 VOBJ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ VOBJ HC64 HC16 HC8 HL AINV00 vr q tag vv"] Lemma EL_A : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) ->
    a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 c8 -> a3 = Z_to_bv 64 c16 -> a4 = Z_to_bv 64 c64 ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90794) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI Ha0 Ha1 Ha2 Ha3 Ha4 ST. subst a0 a1 a2 a3 a4.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _).
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand7 dR_1 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_2; dand11 dR_2 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear DSB Smap Bmap Simg Bimg.
    pose proof SOBJ as (_ & VINV0 & VLS & VLB & VNE & _).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (uar_cells_of_consts _ (proj1 CE)) as [UARG UARV]. fold_aview. open_map_cells MC.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAP : mapped (aview A0 m0) (bv_unsigned sp - 128) 128) by (eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]).
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - 128, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [lia|]. split; [lia|].
      replace (bv_unsigned sp - (bv_unsigned sp - 128)) with 128 by lia. exact WMAP. }
    clear WMAP.
    ago AINV00. fold_cl_segs.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. rename FR into FRH. carve_frame 32%nat ST. rename FR into FR0.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    assert (AL16a : (bv_unsigned sp + -128) mod 16 = 0).
    { pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as Dv. rewrite SP16, Z.add_0_r in Dv. rewrite Dv.
      replace (16 * (bv_unsigned sp / 16) + -128) with ((bv_unsigned sp / 16 - 8) * 16) by lia. apply Z_mod_mult. }
    (first [ pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dex1 dR_3 as d; dand3 dR_3 as Dd ELAND AL32 | pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dand4 dR_3 as d Dd ELAND AL32 | destruct (land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a) as (d & Dd & ELAND & AL32) ]). clear AL16a.
    rewrite ELAND. clear ELAND. assert (D0 : 0 <= d <= 16) by (try (generalize alloc_ceiling_val); clear - Dd; try pose proof alloc_ceiling_val as ACV__; lia). clear Dd.
    (* [comment removed for export] *)
    do 5 zstep.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). if_false.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    fold_cl_segs.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa end.
    lazymatch goal with STq : stk _ ?ma lo _, MIq : mem_inv _ ?ma |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      rename MIq into MIa;
      assert (MPW : mapped ma (bv_unsigned sp + -128 - d - ASTK) ASTK)
        by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STq | exact CEIL | keeplia LO D0 | keeplia D0]) end.
    eapply (smalloc_acall 0);
      [ exact AINVa | exact MIa | left; reflexivity | reflexivity | change (fsize 0) with 64; lia
      | exact (frames_young_smalloc A0 0 1%nat 0%nat FY (or_introl (conj eq_refl (le_n 1%nat))))
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); apply mod16_of_mod32; exact AL32
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); unfold ASTK; keeplia CEIL LO D0
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A1 mB mdB fj fa fb
           AINV1 MI1 MDF1 LV1 LB1 TC1 NL1 SC1 PC1 NZ FN FF1 AGE NONE GEOM LFJ FFC SHC FRO CF1.
    clear FRO. pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    change (Z.to_nat (fsize 0 - 8)) with 56%nat in LFJ, FFC. change (Z.to_nat (fsize 0 / 8)) with 8%nat in SHC.
    (first [ dand5 GEOM as FAL FLO FHI SH0 SH1 | destruct GEOM as (FAL & FLO & FHI & SH0 & SH1) ]).
    change (fsize 0) with 64 in FHI. change (fsize 0 / 8) with 8 in SH1. unfold kHighMemBeg in FLO. all_app_facts. try (unhide_app_of ff).
    pose proof SH1 as SH1n. rewrite SHMAX_val in SH1n.
    rewrite unsigned_lit in CF1 by (keeplia SPR D0 LO CEIL ACV). unfold ASTK in CF1.
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      lazymatch goal with AIq : ainv A0 ?mq _ |- _ => rename AIq into AINVa end;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -128) 32 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR0 ltac:(off_image_solve LPA))) as CR0;
      lazymatch type of FR0 with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FR0;
        [ | exact CR0 | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CR0;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -96) 96 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CRH;
      lazymatch type of FRH with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FRH;
        [ | exact CRH | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CRH;
      lazymatch goal with STq : stk _ ma lo _ |- _ =>
        apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STq; [rename STq into STB | exact CEIL | intros a Ha X; exact X] end;
      assert (VEPO1 : vep_obj LPA A1 mb VEP vv tag q);
      [ eapply (vep_obj_ccall LPA A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| rewrite (LV1 VEP); exact VLV| intros a Ha X; exact X];
        eapply vep_obj_munch; [exact VOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ VEPhi ACV CEIL LO]
      | ];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| rewrite (LV1 S); exact VLS| rewrite (LV1 (vb_buf vr)); exact VLB| intros a Ha X; exact X];
        eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO]
      | ]
    end.
    fold_cl_segs. clear UARV UARG Che Ghe Cme Gme Cmb Gmb Csh Gsh MIa HID.
    (* [comment removed for export] *)
    release_frame FR0 STB (bv_unsigned sp + -96).
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d + 32) _ STB ltac:(keeplia D0 LO CEIL ACV)) as [STl STr]. clear STB.
    destruct (stk_carve rsegs _ lo _ 32 STl ltac:(keeplia D0 LO CEIL ACV)) as [STlo [jp PAD]]. clear STl.
    change (Z.of_nat 32) with 32 in STlo, PAD.
    replace (bv_unsigned sp + -128 - d + 32 - 32) with (bv_unsigned sp + -128 - d) in STlo, PAD by lia.
    unfold zcells in SHC. cbn [repeat] in SHC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -128 - d, bv_unsigned sp + -128 - d + 32)] (aview A1 mB)) as MU2.
    pose proof (wmono_refl rsegs (aview A1 mB)) as WM2.
    assert (CFP2 : client_fp LPA A1 (aview A1 mB) [(bv_unsigned sp + -128 - d, bv_unsigned sp + -128 - d + 32)]).
    { cbn. split; [| exact I]. left. split; [keeplia CEIL LO D0|]. split; [keeplia SPR D0|].
      replace (bv_unsigned sp + -128 - d + 32 - (bv_unsigned sp + -128 - d)) with (Z.of_nat (cells_size [CB 32 jp])) by (cbn [cells_size csize Nat.add]; lia).
      eapply (rw_cells_mapped LPA); [exact PAD| off_image_solve LPA]. }
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    astop AINV1 MU2 WM2 CFP2.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized mdB ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
    fold_cl_segs.
    (* [comment removed for export] *)
    release_frame PAD STlo (bv_unsigned sp + -128 - d + 32).
    pose proof (stk_merge rsegs _ _ _ _ STlo STr ltac:(keeplia D0 LO CEIL ACV)) as STm. clear STlo STr.
    assert (MPX : mapped (aview A1 mX) (bv_unsigned sp - (128 + 16 + (80 + (80 + 8192)))) (128 + 16 + (80 + (80 + 8192)))).
    { eapply (window_mapped LPA _ lo); [exact STm | exact FRH | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
    destruct (stk_carve rsegs _ lo _ 32 STm ltac:(keeplia D0 LO CEIL ACV)) as [STm' [j32 F32]]. clear STm.
    change (Z.of_nat 32) with 32 in STm', F32.
    replace (bv_unsigned sp + -96 - 32) with (bv_unsigned sp - 128) in STm', F32 by lia.
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d) _ STm' ltac:(keeplia D0 LO CEIL ACV)) as [STlo STpad]. clear STm'.
    assert (FR : rw_cells rsegs (aview A1 mX) (bv_unsigned sp - 128)
                   [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app rsegs _ _ [CB 32 j32] _)). split; [exact F32|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp - 128 + Z.of_nat 32) with (bv_unsigned sp + -96) by lia. exact FRH. }
    clear F32 FRH.
    change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (zcells 8) in SHC.
    change (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in *.
    eapply (EL_B2' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 mX mdX j32 fj);
      [ exact D0 | apply mod16_of_mod32; exact AL32 | exact AINVx | assumption
      | eapply amd_frame_sbm_l; [exact SBMa| exact MH| eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBMx| exact MH1]]]
      | exact STlo | exact STpad | exact FR
      | (* [comment removed for export] *) split; [exact FN|]; split; [exact FF1|]; split; [exact AGE|]; split; [exact NONE|];
        split; [exact LV1|]; split; [exact LB1|]; split; [exact TC1|]; split; [exact NL1|]; split; [exact SC1|]; split; [exact PC1|];
        split; [exact FAL|]; split; [exact FLO_a|]; split; [exact FHI|]; split; [exact SH0| exact SH1]
      | exact LFJ | exact FFC | exact SHC
      | eapply vep_obj_munch; [exact VEPO1| exact MU2| exact WM2| intros a__ Ha__; cbn; keeplia Ha__ VEPhi ACV CEIL LO D0]
      | eapply vsb_obj_munch; [exact SOBJ1| exact MU2| exact WM2| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO D0]
      | ].
    (* [comment removed for export] *)
    ufs. eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) _ _ (aview A1 mX) _ _);
      [ exact MU | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO
      | exact CF1 | keeplia D0 | keeplia D0
      | intros a X; exact X | intros a X; left; exact X
      | exact MU2 | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO D0
      | exact MPX ].
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_emit_len_ok {AI : AsanAlloc LPA} {AI16 : AsanAlloc16} : vep_emit_len_stmt.
Proof.
  unfold vep_emit_len_stmt. intros VEP vv tag q vr l c8 c16 c64 lo. intros.
  eapply (EL_A VEP vv tag q vr l c8 c16 c64 lo); eassumption.
Qed.

End CEIL.
End A_vewqv.


Module A_vep67.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vehtf.
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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma frames_aged_alloc_mid_release : forall (A A1 A2 : AS) m2 md2 ff (n0 n1 : nat),
    a_frame A ff = None -> a_frame A1 ff = Some (0, 0%nat) ->
    (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
        a_frame A1 g = Some (k', if Z.eqb k' 0 then S age' else age')) ->
    (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None) ->
    frames_aged A1 A2 n0 n1 -> ainv A2 m2 md2 ->
    frames_aged A (a_release A2 ff) (S n0) n1.
  Proof.
    intros A A1 A2 m2 md2 ff n0 n1 FN FF AGE NONE [AG NN] AI2.
    (first [ pose proof ((AG ff 0 0%nat FF)) as dR_1; dex1 dR_1 as d2; destruct dR_1 as [HF2 _] | pose proof ((AG ff 0 0%nat FF)) as dR_1; dand3 dR_1 as d2 HF2 _ | destruct (AG ff 0 0%nat FF) as (d2 & HF2 & _) ]).
    (first [ pose proof ((as_release_spec LPA A2 m2 md2 ff 0 _ AI2 HF2)) as dR_2; dand3 dR_2 as RN RO _ | destruct (as_release_spec LPA A2 m2 md2 ff 0 _ AI2 HF2) as (RN & RO & _) ]).
    split.
    - intros g k' age' HG.
      assert (NE : g <> ff) by (intros ->; rewrite FN in HG; discriminate HG).
      rewrite (RO g NE). pose proof (AGE g k' age' NE HG) as HG1.
      (first [ pose proof ((AG g _ _ HG1)) as dR_3; dex1 dR_3 as d; destruct dR_3 as [HG2 Hd] | pose proof ((AG g _ _ HG1)) as dR_3; dand3 dR_3 as d HG2 Hd | destruct (AG g _ _ HG1) as (d & HG2 & Hd) ]). rewrite HG2.
      destruct (Z.eqb_spec k' 0) as [->|NK].
      + exists (S d)%nat. split; [f_equal; f_equal; lia|]. unfold fbound in *. cbn in *. lia.
      + exists d. split; [reflexivity|]. unfold fbound in *. rewrite (proj2 (Z.eqb_neq k' 0) NK) in *.
        destruct (Z.eqb k' 1); lia.
    - intros g HG. destruct (Z.eq_dec g ff) as [->|NE]; [exact RN|].
      rewrite (RO g NE). exact (NN g (NONE g NE HG)).
  Qed.

  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l mark lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis HCRC : crc32_stmt.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL0 : 0 <= l.
  Hypothesis HTOT : vv Fo_total + l < 2^62.
  Hypothesis HT0 : 0 <= vv Fo_total.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis DZ : vv Fdogzip = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 2 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITC_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv' tag q ->
      (   (l = 0 /\ vv' = vv /\ vr' = vr)
       \/ (1 <= l /\ exists c, vv' = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 2 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITC_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj HCRC (conj AINV00 (conj HL0 (conj HTOT (conj HT0 (conj HMK (conj VOBJ (conj DZ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ DZ VOBJ HMK HT0 HTOT HL0 AINV00 HCRC mark"] Lemma EC_D : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 xs6 xs7 xs8 : word) (d ff : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                      (vv2 : vep) (vr2 : vsb_rec) (j32 fj shj : list byte),
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp - 128 - d) -> stk rsegs (aview A2 m2) (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp - 128)
             [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc A0 A1 ff -> frames_aged A1 A2 1 0 ->
    length fj = 56%nat -> rw_cells rsegs (aview A2 m2) ff [CB 56 fj] ->
    length shj = 8%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 8 shj] ->
    vep_obj LPA A2 (aview A2 m2) VEP vv2 tag q ->
    (   (l = 0 /\ vv2 = vv /\ vr2 = vr)
     \/ (1 <= l /\ exists c, vv2 = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
    vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.min 9 (2 + l) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) EMITC_STACK
           (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 0 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 128 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp - 128 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 l) (Z_to_bv 64 VEP) xs5 xs6 xs7
                                    xs8 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x9052c) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 AINV MI MDF STlo STpad FR FA FA12 LFJ FFC LSH SHC VEPO LZ SOBJ2 LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PC2 CF02.
    prelims.
    (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PC1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PC1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts. try (unhide_app_of ff).
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : exists age2, a_frame A2 ff = Some (0, age2)).
    { (first [ pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_5; dex1 dR_5 as d2; destruct dR_5 as [HF2 _] | pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_5; dand3 dR_5 as d2 HF2 _ | destruct (proj1 FA12 ff 0 0%nat FF1) as (d2 & HF2 & _) ]). exists (0 + d2)%nat. exact HF2. }
    destruct FF2 as [age2 FF2].
    (* [comment removed for export] *)
    (first [ pose proof ((fframe_flag A2 m2 md2 ff 0 age2 AINV FF2)) as dR_6; dex2 dR_6 as fa fb; dand6 dR_6 as FAW FB FRO FRW FOW FNI | pose proof ((fframe_flag A2 m2 md2 ff 0 age2 AINV FF2)) as dR_6; dand8 dR_6 as fa fb FAW FB FRO FRW FOW FNI | destruct (fframe_flag A2 m2 md2 ff 0 age2 AINV FF2) as (fa & fb & FAW & FB & FRO & FRW & FOW & FNI) ]).
    change (fsize 0) with 64 in FRO. replace (ff + 64 - 8) with (ff + 56) in FRO by lia.
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_7; dand4 dR_7 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A2 m2 md2 VEP _ AINV VLV)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A2 m2 md2 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2)) as dR_9; dand11 dR_9 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ2) as dR_10; dand6 dR_10 as _ VINV2 VLS VLB VNE _ | pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 age2 VEP 312 AINV FF2 VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 age2 _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 age2 _ _ AINV FF2 VLB) as DJfB.
    change (fsize 0) with 64 in DJfV, DJfS, DJfB.
    pose proof (owned_outside_live A2 m2 md2 VEP 312 _ AINV VLV FOW) as OWV.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLS FOW) as OWS.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLB FOW) as OWB.
    pose proof (owned_outside_fframe A2 m2 md2 ff 0 age2 _ AINV FF2 FOW) as [OWF OWSH].
    change (fsize 0) with 64 in OWF, OWSH. change (64 / 8) with 8 in OWSH.
    hide DJfV. hide DJfS. hide DJfB. hide OWV. hide OWS. hide OWB. hide VEPC. hide DSB. hide LZ. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFR : client_fp_rel LPA A2 [ff] (aview A2 m2) [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)]).
    { unfold client_fp_rel. split; [| split; [| split; [| exact I]]].
      - right; right; right; left. exists ff, 0, age2. split; [exact FF2|]. change (fsize 0 / 8) with 8. lia.
      - right; right; left. exists ff, 0, age2. split; [exact FF2|]. change (fsize 0) with 64. lia.
      - right; right; right; right. exists ff, 0, age2, (Z_to_bv 64 fa). split; [left; reflexivity|]. split; [exact FF2|].
        split; [exact FB|]. rewrite unsigned_lit by (keeplia FAW ACV); split; reflexivity. }
    hide FB.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. fix_neg. do 8 sb1.
    (* [comment removed for export] *)
    zstep. unhide OWV. unhide OWS. unhide OWB. sb1. hide OWV. hide OWS. hide OWB. zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by lia.
    do 12 zstep. zstep.
    try replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with ST1 : stk _ ?mq lo _, ST2 : stk _ ?mq (bv_unsigned sp - 128 - d) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (stk_merge rsegs mq _ _ _ ST1 ST2 ltac:(keeplia D0 LO CEIL ACV)) as STm; clear ST1 ST2 end.
    lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp - 128) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FRq STm (bv_unsigned sp) end.
    (* [comment removed for export] *)
    lazymatch goal with FLq : rw_cells _ ?mq fa [C1 ?b] |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (flag_cleared (Clg:=Clg) mq fa FLq FNI ltac:(keeplia FAW ACV)) as FL end.
    unhide FB. astop_rel1 AINV FF2 FB MU WM CFR FL.
    (first [ pose proof ((as_release_spec LPA A2 m2 md2 ff 0 age2 AINV FF2)) as dR_11; dand11 dR_11 as RN RO RL RLB RTC RSC RPC RNL RH RE ROW | destruct (as_release_spec LPA A2 m2 md2 ff 0 age2 AINV FF2) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW) ]).
    unhide VEPC. unhide LZ.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a_release A2 ff) m1 md1 vv2 vr2);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | assumption
      | (* [comment removed for export] *) split; [rewrite RL; exact VLV|]; split; [| split; [exact TAG8| exact PADS]];
        eapply (rw_cells_munch LPA); [exact VEPC| exact MU| exact WM|];
        rewrite (vep_cells_size vv2 tag q TAG8 PADS); change (Z.of_nat 312) with 312;
        intros a Ha; cbn; keeplia Ha DJfV OWV SH1 VEPlo
      | exact LZ
      | (* [comment removed for export] *)
        (first [ pose proof (SOBJ2) as dR_12; dand6 dR_12 as XC XI XLS XLB XNE XB | pose proof SOBJ2 as (XC & XI & XLS & XLB & XNE & XB) ]); split; [| split; [exact XI| split; [rewrite RL; exact XLS| split; [rewrite RL; exact XLB| split; [exact XNE|]]]]];
        [ eapply (rw_cells_munch LPA); [exact XC| exact MU| exact WM|]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40;
          intros a Ha; cbn; keeplia Ha DJfS OWS SH1 Slo
        | (first [ dex1 XB as bs; dand3 XB as [UB UW] LENx NULx | dand4 XB as bs [UB UW] LENx NULx | destruct XB as (bs & [UB UW] & LENx & NULx) ]); exists bs; split; [| split; [exact LENx| exact NULx]]; split;
          [ eapply (bytes_at_munch LPA); [exact UB| exact MU| rewrite LENx; intros a Ha; cbn; keeplia Ha DJfB OWB SH1 Blo]
          | eapply wr_at_transport; [exact UW| exact WM] ] ]
      | exact LEN2 | exact SZ2
      | destruct REL2 as [E|[E1 E2]]; [left; exact E| right; split; [rewrite <- (LV1 (vb_buf vr2)); exact E1| rewrite RL; exact E2]]
      | intros p Hp1 Hp2; rewrite RL, (LIVEq2 p Hp1 Hp2); apply LV1
      | exact (frames_aged_alloc_mid_release A0 A1 A2 m2 md2 ff 1%nat 0%nat FN FF1 AGE NONE FA12 AINV)
      | rewrite RLB, LB2, LB1; reflexivity
      | rewrite RTC, TC2, TC1; reflexivity
      | rewrite RNL, NL2, NL1; reflexivity
      | rewrite RSC; try (generalize alloc_ceiling_val); clear - SC2 SC1; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite RPC; clear - PC2 PC1; lia (* [comment removed for export] *)
      | ]
    end.
    (* [comment removed for export] *)
    ufs. eapply (cframe_release (owned A0) (owned A2) (owned (a_release A2 ff))); [exact CF02| exact MU| | keeplia LO CEIL ACV| keeplia SPR| | | intros a X; right; exact X].
    - intros a Ha NO. cbn [outside] in NO.
      assert (CS : sh ff <= a < sh ff + 8 \/ ff <= a < ff + 8 \/ a = fa) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
      destruct CS as [X|[X|X]]; [left; left; right; change (fsize 0 / 8) with 8; exact X| left; left; left; change (fsize 0) with 64; keeplia X| right; rewrite X; exact FOW].
    - intros i Hi. cbn. keeplia Hi SH1 FHI FAW LO CEIL ACV.
    - intros a Oa. apply ROW in Oa. destruct Oa as [X|[X|X]]; [left; exact X| right; left; left; change (fsize 0) with 64 in *; keeplia X| right; left; right; exact X].
  Qed.
End S.
End A_vep67.


Module A_vel9u.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vehtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vep67.
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

Ltac icall_consts_in H ::= unfold crc0_post, leaf_post, CRC_STACK in H.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l mark lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis HCRC : crc32_stmt.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL0 : 0 <= l.
  Hypothesis HTOT : vv Fo_total + l < 2^62.
  Hypothesis HT0 : 0 <= vv Fo_total.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis DZ : vv Fdogzip = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 2 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITC_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv' tag q ->
      (   (l = 0 /\ vv' = vv /\ vr' = vr)
       \/ (1 <= l /\ exists c, vv' = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 2 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITC_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj HCRC (conj AINV00 (conj HL0 (conj HTOT (conj HT0 (conj HMK (conj VOBJ (conj DZ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EC_D' := EC_D (* [comment removed for export] *) VEP vv tag q vr l mark lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                        HCRC AINV00 HL0 HTOT HT0 HMK VOBJ DZ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ DZ VOBJ HMK HT0 HTOT HL0 AINV00 HCRC mark"] Lemma EC_C : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (d ff : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                      (vr2 : vsb_rec) (j32 fj shj : list byte),
    0 <= d <= 16 -> 1 <= l ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp - 128 - d) -> stk rsegs (aview A2 m2) (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp - 128)
             [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc A0 A1 ff -> frames_aged A1 A2 1 0 ->
    length fj = 56%nat -> rw_cells rsegs (aview A2 m2) ff [CB 56 fj] ->
    length shj = 8%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 8 shj] ->
    vep_obj LPA A2 (aview A2 m2) VEP vv tag q ->
    vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.min 9 (2 + l) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) EMITC_STACK
           (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 0 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 128 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp - 128 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 l) (Z_to_bv 64 VEP) (Z_to_bv 64 (VEP + 128)) (Z_to_bv 64 (VEP + 120)) (Z_to_bv 64 1)
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x904bc) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 L1 AINV MI MDF STlo STpad FR FA FA12 LFJ FFC LSH SHC VEPO SOBJ2 LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PC2 CF02.
    prelims.
    pose proof FA as FA'. (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PC1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PC1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts. try (unhide_app_of ff).
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : exists age2, a_frame A2 ff = Some (0, age2)).
    { (first [ pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_2; dex1 dR_2 as d2; destruct dR_2 as [HF2 _] | pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_2; dand3 dR_2 as d2 HF2 _ | destruct (proj1 FA12 ff 0 0%nat FF1) as (d2 & HF2 & _) ]). exists (0 + d2)%nat. exact HF2. }
    destruct FF2 as [age2 FF2].
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_3; dand4 dR_3 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A2 m2 md2 VEP _ AINV VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A2 m2 md2 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear Simg Bimg Smap Bmap.
    (first [ pose proof (SOBJ2) as dR_6; dand6 dR_6 as _ VINV2 VLS VLB VNE _ | pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 age2 VEP 312 AINV FF2 VLV) as DJfV. change (fsize 0) with 64 in DJfV.
    (* [comment removed for export] *)
    assert (NEB2 : VEP <> vb_buf vr2).
    { destruct REL2 as [E|[E _]]; [rewrite E; exact NEB|]. intros X. pose proof (proj1 VOBJ : a_live A0 VEP = Some 312) as VLV0. rewrite <- X, (LV1 VEP), VLV0 in E. discriminate E. }
    pose proof (as_live_disjoint LPA A2 m2 md2 S 40 VEP 312 AINV VLS VLV (not_eq_sym NES)) as DJS.
    pose proof (as_live_disjoint LPA A2 m2 md2 (vb_buf vr2) (vb_size vr2) VEP 312 AINV VLB VLV (not_eq_sym NEB2)) as DJB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (cenv_intro A2 m2 md2 AINV) as CE.
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    hide DJfV. hide DJS. hide DJB. hide DSB. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 128 - d - 128, bv_unsigned sp - 128 - d); (VEP, VEP + 312)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (WMAP : mapped (aview A2 m2) (bv_unsigned sp - 128 - d - 128) 128)
      by (eapply (stk_mapped (L:=LPA)); [exact STlo | exact CEIL | keeplia LO D0 | keeplia D0]).
    assert (CFP : client_fp LPA A2 (aview A2 m2) [(bv_unsigned sp - 128 - d - 128, bv_unsigned sp - 128 - d); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [keeplia CEIL LO D0|]; split; [keeplia SPR D0|];
                   replace (bv_unsigned sp - 128 - d - (bv_unsigned sp - 128 - d - 128)) with 128 by lia; exact WMAP |].
      split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I]. }
    clear WMAP.
    unfold vep_cells in VEPC.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    icall (crc32_null HCRC lo) by
      (rewrite ?unsigned_lit by (keeplia SPR LO CEIL ACV D0);
       first [ reflexivity | exact CE | exact STlo | exact CEIL | assumption | keeplia LO D0 ]).
    lazymatch goal with X : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => try clear STlo; rename X into STlo end.
    (* [comment removed for export] *)
    zstep. kdead.
    (* [comment removed for export] *)
    unhide DJfV.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep.
    zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. clear - HTOT HT0 HL0 L1. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (VEP + 112) 8 0.
    zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    lazymatch goal with AIq : ainv A2 ?mq ?mdq, SBq : same_but_materialized md2 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
    fold_cl_segs.
    unhide DJS. unhide DJB.
    lazymatch goal with VEPCq : rw_cells _ (aview A2 mX) VEP _, FRq : rw_cells _ (aview A2 mX) (bv_unsigned sp - 128) _,
                        STp : stk _ (aview A2 mX) (bv_unsigned sp - 128 - d) _, MIq : mem_inv _ (aview A2 mX) |- _ =>
    eapply (EC_D' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A2 mX mdX
              (fupd (fupd (fupd vv Fcrc 0) Fo_crc 0) Fo_total (vv Fo_total + l)) vr2 j32 fj shj);
      [ exact D0 | exact AINVx | exact MIq
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBMx| exact MH]]
      | exact STlo | exact STp | exact FRq | exact FA' | exact FA12
      | exact LFJ | exact FFC | exact LSH | exact SHC
      | (* [comment removed for export] *) split; [exact VLV|]; split; [| split; [exact TAG8| exact PADS]];
        unfold vep_cells, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact VEPCq
      | right; split; [exact L1| exists 0; reflexivity]
      | eapply vsb_obj_munch; [exact SOBJ2| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJS DJB Shi Bhi ACV CEIL LO D0]
      | exact LEN2 | exact SZ2 | exact REL2 | exact LIVEq2 | exact LB2 | exact TC2 | exact NL2 | exact SC2 | exact PC2
      | ]
    end.
    (* [comment removed for export] *)
    ufs. lazymatch type of CF02 with cframe _ _ _ _ _ ?V ?Nn ?ma ?mb =>
      lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mc =>
        lazymatch goal with STp : stk _ mc (bv_unsigned sp - 128 - d) _, FRq : rw_cells _ mc (bv_unsigned sp - 128) _ |- _ =>
          pose proof (stk_merge rsegs mc _ _ _ STlo STp ltac:(keeplia D0 LO CEIL ACV)) as STm;
          assert (MPX : mapped mc (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192)))))
            by (eapply (window_mapped LPA _ lo); [exact STm | exact FRq | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]);
          clear STm
        end;
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ ma mb mc CF02);
        [ eapply (cframe_noalloc LPA); [exact MU| | exact MPX | intros a X; exact X]
        | keeplia SPR | keeplia SPR | exact MPX
        | intros a X; exact X
        | (* [comment removed for export] *) intros a X; right; exact X
        | intros a X; left; exact X ]
      end
    end.
    - intros a Ha NO. cbn [outside] in NO. unfold blk.
      assert (CS : bv_unsigned sp - 128 - d - 128 <= a < bv_unsigned sp - 128 - d \/ VEP <= a < VEP + 312) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia).
      destruct CS as [X|X]; [left; keeplia X D0| right; left; unhide_neqs; split; [| exact X]].
      intros E0. rewrite E0 in VEPlo. keeplia VEPlo.
  Qed.
End S.
End A_vel9u.


Module A_veksn.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vehtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vewqv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vep67 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vel9u.
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
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l mark lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis HCRC : crc32_stmt.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL0 : 0 <= l.
  Hypothesis HTOT : vv Fo_total + l < 2^62.
  Hypothesis HT0 : 0 <= vv Fo_total.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis DZ : vv Fdogzip = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 2 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITC_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv' tag q ->
      (   (l = 0 /\ vv' = vv /\ vr' = vr)
       \/ (1 <= l /\ exists c, vv' = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 2 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITC_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj HCRC (conj AINV00 (conj HL0 (conj HTOT (conj HT0 (conj HMK (conj VOBJ (conj DZ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EC_D' := EC_D (* [comment removed for export] *) VEP vv tag q vr l mark lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                        HCRC AINV00 HL0 HTOT HT0 HMK VOBJ DZ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.
  Local Definition EC_C' := EC_C (* [comment removed for export] *) VEP vv tag q vr l mark lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                        HCRC AINV00 HL0 HTOT HT0 HMK VOBJ DZ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  (* [comment removed for export] *)
  #[using="S sp vv"] Lemma frames_young_alloc : forall A A1 ff, frames_young A 2 0 -> fr_alloc A A1 ff -> frames_young A1 1 0.
  Proof.
    (intros A A1 ff FY0; (first [ intro dR_9; dand5 dR_9 as FN FF AGE NONE _ | intros (FN & FF & AGE & NONE & _) ]); intros g k age HG K01).
    destruct (Z.eq_dec g ff) as [->|NE].
    - rewrite FF in HG. injection HG as <- <-. unfold fbound, fslots. cbn. lia.
    - destruct (a_frame A g) as [[k0 age0]|] eqn:HG0.
      + rewrite (AGE g k0 age0 NE HG0) in HG. injection HG as <- EA.
        pose proof (FY0 g k0 age0 HG0 K01) as Y. unfold fbound in *.
        destruct K01 as [-> | ->]; cbn in *; subst age; cbn; lia.
      + rewrite (NONE g NE HG0) in HG. discriminate HG.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ DZ VOBJ HMK HT0 HTOT HL0 AINV00 HCRC"] Lemma EC_B : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 xs6 xs10 : word) (d ff : Z) (A1 : AS) (m1 : mem) (md1 : Model)
                      (j32 fj : list byte),
    0 <= d <= 16 -> (bv_unsigned sp - 128 - d) mod 16 = 0 ->
    ainv A1 m1 md1 -> mem_inv rsegs (aview A1 m1) -> amd_frame md0 md1 ->
    stk rsegs (aview A1 m1) lo (bv_unsigned sp - 128 - d) -> stk rsegs (aview A1 m1) (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) ->
    rw_cells rsegs (aview A1 m1) (bv_unsigned sp - 128)
             [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc A0 A1 ff ->
    length fj = 56%nat -> rw_cells rsegs (aview A1 m1) ff [CB 56 fj] ->
    rw_cells rsegs (aview A1 m1) (sh ff) (zcells 8) ->
    vep_obj LPA A1 (aview A1 m1) VEP vv tag q -> vsb_obj LPA A1 (aview A1 m1) S vr false ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) EMITC_STACK nowhere (frm ff 0) (aview A0 m0) (aview A1 m1) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 128 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp - 128 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 l) (Z_to_bv 64 VEP) xs5 xs6 (Z_to_bv 64 mark)
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) xs10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x9033c) fc None m1 (seg_rom rsegs)) md1) T.
  Proof.
    touch_all. intros until fj. intros D0 AL16 AINV MI MDF STlo STpad FR FA LFJ FFC SHC VEPO SOBJ1 CF01.
    prelims.
    pose proof FA as FA'. (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PC1 FAL FLO FHI SH0 SH1s | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PC1 & FAL & FLO & FHI & SH0 & SH1s) ]). all_app_facts. try (unhide_app_of ff).
    pose proof SH1s as SH1. rewrite SHMAX_val in SH1.
    pose proof (as_minv LPA A1 _ _ AINV) as [_ MH].
    pose proof (frames_young_alloc A0 A1 ff FY FA') as FY1.
    (* [comment removed for export] *)
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as VLV VEPC TAG8 PADS | pose proof VEPO as (VLV & VEPC & TAG8 & PADS) ]). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A1 m1 md1 VEP _ AINV VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A1 m1 md1 VEP _ AINV VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A1 m1 md1 S vr false AINV SOBJ1)) as dR_4; dand11 dR_4 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A1 m1 md1 S vr false AINV SOBJ1) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear Simg Bimg Smap Bmap.
    (first [ pose proof (SOBJ1) as dR_5; dand6 dR_5 as _ VINV1 VLS VLB VNE _ | pose proof SOBJ1 as (_ & VINV1 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat VEP 312 AINV FF1 VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat _ _ AINV FF1 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff 0 0%nat _ _ AINV FF1 VLB) as DJfB.
    change (fsize 0) with 64 in DJfV, DJfS, DJfB.
    pose proof (as_live_disjoint LPA A1 m1 md1 S 40 VEP 312 AINV VLS VLV (not_eq_sym NES)) as DJS.
    pose proof (as_live_disjoint LPA A1 m1 md1 (vb_buf vr) (vb_size vr) VEP 312 AINV VLB VLV (not_eq_sym NEB)) as DJB.
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHD : sh ff + 8 <= sh VEP \/ sh VEP + 39 <= sh ff) by (unfold sh; clear - DJfV; try pose proof alloc_ceiling_val as ACV__; mlia).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    assert (L7 : Z.land VEP 7 = 0) by (apply land7_of_mod8; [keeplia VEPlo | exact V8]).
    hide DJfS. hide DJfB. hide DJS. hide DJB. hide DSB. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(ff, ff + 24); (sh ff, sh ff + 8)] (aview A1 m1)) as MU.
    pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    assert (CFP : client_fp LPA A1 (aview A1 m1) [(ff, ff + 24); (sh ff, sh ff + 8)]).
    { cbn. split; [right; right; left; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0) with 64; lia]|].
      split; [right; right; right; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0 / 8) with 8; lia]| exact I]. }
    unfold zcells in SHC. cbn [repeat] in SHC.
    unfold vep_cells in VEPC.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (shr3_div8 ff). zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. change (ff / 8 + 2147450880) with (sh ff).
    (* [comment removed for export] *)
    fix_neg. sb1. sb1. sb1. sb1. zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep. kdead. zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      astop AINV MU WM CFP.
      lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized md1 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
        rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
      fold_cl_segs.
      (* [comment removed for export] *)
      destruct (rw_cells_forget rsegs _ _ _ FFC) as [fj2 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
      pose proof FFC3 as [[WF3 _] _]. cbn [cells_wf cell_wf] in WF3.
      destruct (rw_cells_forget rsegs _ _ _ SHC) as [shj2 SHC3]. cbn [cells_size csize Nat.add] in SHC3.
      pose proof SHC3 as [[WS3 _] _]. cbn [cells_wf cell_wf] in WS3.
      assert (MPX : mapped (aview A1 mX) (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))).
      { pose proof (stk_merge rsegs (aview A1 mX) _ _ _ STlo STpad ltac:(keeplia D0 LO CEIL ACV)) as STm.
        eapply (window_mapped LPA _ lo); [exact STm | exact FR | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
      unhide DJfS. unhide DJfB.
      lazymatch goal with MIq : mem_inv _ (aview A1 mX) |- _ =>
      eapply (EC_D' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A1 mX mdX vv vr j32 fj2 shj2);
        [ exact D0 | exact AINVx | exact MIq
        | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBMx| exact MH]]
        | exact STlo | exact STpad | exact FR | exact FA' | apply frames_same_aged; intros g; reflexivity
        | exact (proj1 WF3) | exact FFC3 | exact (proj1 WS3) | exact SHC3
        | eapply vep_obj_munch; [exact VEPO| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfV VEPlo SH1]
        | left; split; [exact KL| split; reflexivity]
        | eapply vsb_obj_munch; [exact SOBJ1| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfS DJfB Slo Blo SH1]
        | keeplia KL | lia | left; reflexivity | intros p _ _; reflexivity | lia | reflexivity | reflexivity | lia | lia (* [comment removed for export] *)
        | ]
      end.
      (* [comment removed for export] *)
      ufs. eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A0 m0) (aview A1 m1) (aview A1 mX) [] _);
        [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF01 | keeplia SPR | keeplia SPR
        | intros a X; destruct X | intros a [X|X]; [left; exact X| right; right; left; exact X] | exact MU | | exact MPX ].
      intros a Ha NO. cbn [outside] in NO. right; right. unfold frm. change (fsize 0) with 64. change (64 / 8) with 8. keeplia Ha NO.
    - (* [comment removed for export] *)
      assert (L1 : 1 <= l) by (try (generalize alloc_ceiling_val); clear - KL HL0; try pose proof alloc_ceiling_val as ACV__; lia). clear KL.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KM; zify_cond KM; rewrite Z.mod_small in KM by (try (generalize alloc_ceiling_val); clear - HMK; try pose proof alloc_ceiling_val as ACV__; unfold bool01 in HMK; lia).
      + (* [comment removed for export] *)
        (* [comment removed for export] *)
        zstep. rewrite L7. zstep. kdead.
        (* [comment removed for export] *)
        vchk SHV0 EzsV 8 0. zstep. zstep. sb1.
        (* [comment removed for export] *)
        do 6 zstep.
        astop AINV MU WM CFP.
        lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized md1 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
          rename AIq into AINVb; rename SBq into SBMb; rename mq into mB; rename mdq into mdB end.
        fold_cl_segs. unhide DJfS. unhide DJfB.
        lazymatch goal with STq : stk _ (aview _ mB) lo _, MIq : mem_inv _ (aview _ mB) |- _ =>
          eapply (vep_emit_len_ok VEP vv tag q vr l 65 66 72 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mB mdB A1 T);
          [ exact AINVb | exact MIq | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | keeplia L1 HTOT HT0 | lia | lia | lia
          | eapply vep_obj_munch; [exact VEPO| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfV VEPlo SH1]
          | eapply vsb_obj_munch; [exact SOBJ1| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfS DJfB Slo Blo SH1]
          | unhide_neqs; assumption | unhide_neqs; assumption | exact EM
          | rewrite LB1; exact LBM | rewrite NL1; exact NLV | rewrite SC1; exact SCM | rewrite PC1; exact PCM (* [comment removed for export] *) | exact FY1 | exact TP
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact AL16
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact STq
          | exact CEIL
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); ufs; keeplia LO D0 | ]
        end.
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m2 md2 vr2. cbv zeta.
        intros AINV2 MI2 MDF2 ST2 VEPO2 SOBJ2 LEN2 SZ2 REL LIVEq FA12 LB2 TC2 NL2 SC2 PC2 CF2.
        rewrite unsigned_lit in ST2, CF2 by (keeplia SPR LO CEIL ACV D0). ufs.
        pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
        pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(pose proof (proj1 VINV1); lia) ltac:(exact Bhi)) as SHB. rewrite SHMAX_val in SHB.
        pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(lia) ltac:(exact Shi)) as SHS. rewrite SHMAX_val in SHS.
        assert (SHDS : sh ff + 8 <= sh S \/ sh S + (40 + 7) / 8 <= sh ff) by (unfold sh; clear - DJfS; try pose proof alloc_ceiling_val as ACV__; mlia).
        assert (SHDB : sh ff + 8 <= sh (vb_buf vr) \/ sh (vb_buf vr) + (vb_size vr + 7) / 8 <= sh ff) by (unfold sh; clear - DJfB FAL; try pose proof alloc_ceiling_val as ACV__; mlia).
        (* [comment removed for export] *)
        lazymatch type of CF2 with cframe _ (owned _) (owned _) _ _ _ _ ?ma _ =>
          lazymatch goal with ST1 : stk _ ma lo _, ST1' : stk _ ma (bv_unsigned sp - 128 - d) _, FRq : rw_cells _ ma (bv_unsigned sp - 128) _ |- _ =>
            pose proof (stk_merge rsegs ma _ _ _ ST1 ST1' ltac:(keeplia D0 LO CEIL ACV)) as STma;
            assert (MPa : mapped ma (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192)))))
              by (eapply (window_mapped LPA _ lo); [exact STma | exact FRq | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]);
            clear STma ST1 end end.
        (* [comment removed for export] *)
        lazymatch type of CF2 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          lazymatch goal with STq : stk _ ma (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) |- _ =>
            apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINVb CF2) in STq;
            [ rename STq into STpad2 | keeplia LO CEIL D0 | intros a Ha X; unfold newblk, blk in X; keeplia Ha X Bhi Shi SHB SHS LO CEIL ACV D0 ] end;
          lazymatch goal with FRq : rw_cells _ ma (bv_unsigned sp - 128) ?fcs |- _ =>
            pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp - 128) 128 AINVb ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                          (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRq ltac:(off_image_solve LPA))) as CRF;
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 _ fcs) in FRq;
            [ rename FRq into FR2 | exact CRF
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X Bhi Shi SHB SHS LO CEIL ACV ];
            clear CRF end;
          lazymatch goal with FFCq : rw_cells _ ma ff ?fcs |- _ =>
            pose proof FFCq as [[WFF _] _]; cbn [cells_wf cell_wf] in WFF;
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 ff fcs) in FFCq;
            [ rename FFCq into FFC2
            | eapply crange_fframe; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0) with 64; lia| cbn; lia]
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia FHI LO CEIL D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJfS DJfB SHB SHS FLO ];
            clear WFF end;
          lazymatch goal with SHCq : rw_cells _ ma (sh ff) ?scs |- _ =>
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (sh ff) scs) in SHCq;
            [ rename SHCq into SHC2
            | eapply crange_fshadow; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0 / 8) with 8; lia| cbn; lia]
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SH1 LO CEIL ACV D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X SHDS SHDB Slo Blo SH1 ] end
        end.
        (* [comment removed for export] *)
        (first [ pose proof (VEPO2) as dR_6; dand3 dR_6 as VLV2 VEPC2 _ | pose proof VEPO2 as (VLV2 & VEPC2 & _) ]). unfold vep_cells in VEPC2.
        pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV2 VLV2) as SHV2. fold_cl_segs. fold_aview.
        change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV2. rewrite <- EzsV in SHV2.
        (first [ pose proof ((vsb_obj_geom LPA A2 _ _ S vr2 false AINV2 SOBJ2)) as dR_7; dand11 dR_7 as _ _ _ _ _ Blo2 Bhi2 _ _ _ _ | pose proof (vsb_obj_geom LPA A2 _ _ S vr2 false AINV2 SOBJ2) as (_ & _ & _ & _ & _ & Blo2 & Bhi2 & _ & _ & _ & _) ]).
        unfold kHighMemBeg in Blo2. all_app_facts. try (unhide_app_of ff).
        assert (FF2 : exists age2, a_frame A2 ff = Some (0, age2)).
        { (first [ pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_8; dex1 dR_8 as d2; destruct dR_8 as [HF2 _] | pose proof ((proj1 FA12 ff 0 0%nat FF1)) as dR_8; dand3 dR_8 as d2 HF2 _ | destruct (proj1 FA12 ff 0 0%nat FF1) as (d2 & HF2 & _) ]). exists (0 + d2)%nat. exact HF2. }
        destruct FF2 as [age2 FF2].
        pose proof (munch_refl [(sh ff, sh ff + 8)] (aview A2 m2)) as MU3.
        pose proof (wmono_refl rsegs (aview A2 m2)) as WM3.
        assert (CFP3 : client_fp LPA A2 (aview A2 m2) [(sh ff, sh ff + 8)]).
        { cbn. split; [right; right; right; exists ff, 0, age2; split; [exact FF2| change (fsize 0 / 8) with 8; lia]| exact I]. }
        assert (MP2 : mapped (aview A2 m2) (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))).
        { pose proof (stk_merge rsegs (aview A2 m2) _ _ _ ST2 STpad2 ltac:(keeplia D0 LO CEIL ACV)) as STm.
          eapply (window_mapped LPA _ lo); [exact STm | exact FR2 | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
        hide DJfS. hide DJfB. hide SHDS. hide SHDB.
        ago AINV2. fold_cl_segs. fix_ret_pc.
        zstep. vchk SHV2 EzsV 4 0. zstep. rewrite DZ. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. kdead2.
        zstep. fix_neg. sb1.
        (* [comment removed for export] *)
        zstep.
        astop AINV2 MU3 WM3 CFP3.
        lazymatch goal with AIq : ainv A2 ?mq ?mdq, SBq : same_but_materialized md2 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
          rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
        fold_cl_segs.
        (* [comment removed for export] *)
        destruct (rw_cells_forget rsegs _ _ _ FFC2) as [fj2 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
        pose proof FFC3 as [[WF3 _] _]. cbn [cells_wf cell_wf] in WF3.
        destruct (rw_cells_forget rsegs _ _ _ SHC2) as [shj2 SHC3]. cbn [cells_size csize Nat.add] in SHC3.
        pose proof SHC3 as [[WS3 _] _]. cbn [cells_wf cell_wf] in WS3.
        assert (MPX : mapped (aview A2 mX) (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))).
        { pose proof (stk_merge rsegs (aview A2 mX) _ _ _ ST2 STpad2 ltac:(keeplia D0 LO CEIL ACV)) as STm.
          eapply (window_mapped LPA _ lo); [exact STm | exact FR2 | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
        (* [comment removed for export] *)
        eapply (EC_C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A2 mX mdX vr2 j32 fj2 shj2);
          [ exact D0 | exact L1 | exact AINVx | assumption
          | eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBMb| exact MH|];
            eapply amd_frame_trans; [exact MDF2| apply amd_frame_sbm; [exact SBMx| exact MH2]]
          | exact ST2 | exact STpad2 | exact FR2 | exact FA' | exact FA12
          | exact (proj1 WF3) | exact FFC3 | exact (proj1 WS3) | exact SHC3
          | eapply vep_obj_munch; [exact VEPO2| exact MU3| exact WM3| intros a__ Ha__; cbn; keeplia Ha__ VEPlo SH1]
          | eapply vsb_obj_munch; [exact SOBJ2| exact MU3| exact WM3| intros a__ Ha__; cbn; keeplia Ha__ Slo Blo2 SH1]
          | exact LEN2 | exact SZ2 | exact REL | exact LIVEq | exact LB2 | exact TC2 | exact NL2 | exact SC2 | exact PC2 | ].
        (* [comment removed for export] *)
        assert (CFa : cframe LPA (owned A0) (owned A1) (bv_unsigned sp) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))
                        nowhere (frm ff 0) (aview A0 m0) (aview A1 mB)).
        { eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A0 m0) (aview A1 m1) (aview A1 mB) [] _);
          [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF01 | keeplia SPR | keeplia SPR
          | intros a X; destruct X | intros a X; left; exact X | exact MU | | exact MPa ].
          intros a Ha NO. cbn [outside] in NO. right; right. unfold frm. change (fsize 0) with 64. change (64 / 8) with 8. keeplia Ha NO. }
        ufs.
        lazymatch goal with |- cframe _ _ _ _ _ ?V ?Nn _ _ =>
          assert (CFab : cframe LPA (owned A0) (owned A2) (bv_unsigned sp) (128 + 16 + (128 + 16 + (80 + (80 + 8192)))) V Nn (aview A0 m0) (aview A2 m2));
          [ eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A1 mB) (aview A2 m2) CFa);
            [ eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))); [exact CF2| keeplia D0| keeplia D0| exact MP2]
            | keeplia SPR | keeplia SPR | exact MP2
            | intros a X; destruct X
            | intros a [X|X]; [right; right; left; exact X| right; right; right; exact X]
            | intros a [X|X]; [left; exact X| right; left; exact X] ]
          | eapply (cframe_release (owned A0) (owned A2) (owned A2)); [exact CFab| exact MU3| | keeplia LO CEIL ACV| keeplia SPR| | intros a X; left; exact X| intros a X; exact X];
            [ intros a Ha NO; cbn [outside] in NO; left; left; right; change (fsize 0 / 8) with 8; keeplia Ha NO
            | intros i Hi; cbn; keeplia Hi SH1 LO CEIL ACV ] ]
        end.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KA; zify_cond KA; rewrite Z.mod_small in KA by (try (generalize alloc_ceiling_val); clear - HMK; try pose proof alloc_ceiling_val as ACV__; unfold bool01 in HMK; lia);
          [exfalso; try (generalize alloc_ceiling_val); clear - KA KM HMK; try pose proof alloc_ceiling_val as ACV__; unfold bool01 in HMK; lia|]. clear KA.
        do 6 zstep.
        astop AINV MU WM CFP.
        lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized md1 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
          rename AIq into AINVb; rename SBq into SBMb; rename mq into mB; rename mdq into mdB end.
        fold_cl_segs. unhide DJfS. unhide DJfB.
        lazymatch goal with STq : stk _ (aview _ mB) lo _, MIq : mem_inv _ (aview _ mB) |- _ =>
          eapply (vep_emit_len_ok VEP vv tag q vr l 97 98 104 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mB mdB A1 T);
          [ exact AINVb | exact MIq | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | keeplia L1 HTOT HT0 | lia | lia | lia
          | eapply vep_obj_munch; [exact VEPO| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfV VEPlo SH1]
          | eapply vsb_obj_munch; [exact SOBJ1| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ DJfS DJfB Slo Blo SH1]
          | unhide_neqs; assumption | unhide_neqs; assumption | exact EM
          | rewrite LB1; exact LBM | rewrite NL1; exact NLV | rewrite SC1; exact SCM | rewrite PC1; exact PCM (* [comment removed for export] *) | exact FY1 | exact TP
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact AL16
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact STq
          | exact CEIL
          | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); ufs; keeplia LO D0 | ]
        end.
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m2 md2 vr2. cbv zeta.
        intros AINV2 MI2 MDF2 ST2 VEPO2 SOBJ2 LEN2 SZ2 REL LIVEq FA12 LB2 TC2 NL2 SC2 PC2 CF2.
        rewrite unsigned_lit in ST2, CF2 by (keeplia SPR LO CEIL ACV D0). ufs.
        pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
        pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(pose proof (proj1 VINV1); lia) ltac:(exact Bhi)) as SHB. rewrite SHMAX_val in SHB.
        pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(lia) ltac:(exact Shi)) as SHS. rewrite SHMAX_val in SHS.
        assert (SHDS : sh ff + 8 <= sh S \/ sh S + (40 + 7) / 8 <= sh ff) by (unfold sh; clear - DJfS; try pose proof alloc_ceiling_val as ACV__; mlia).
        assert (SHDB : sh ff + 8 <= sh (vb_buf vr) \/ sh (vb_buf vr) + (vb_size vr + 7) / 8 <= sh ff) by (unfold sh; clear - DJfB FAL; try pose proof alloc_ceiling_val as ACV__; mlia).
        (* [comment removed for export] *)
        lazymatch type of CF2 with cframe _ (owned _) (owned _) _ _ _ _ ?ma _ =>
          lazymatch goal with ST1 : stk _ ma lo _, ST1' : stk _ ma (bv_unsigned sp - 128 - d) _, FRq : rw_cells _ ma (bv_unsigned sp - 128) _ |- _ =>
            pose proof (stk_merge rsegs ma _ _ _ ST1 ST1' ltac:(keeplia D0 LO CEIL ACV)) as STma;
            assert (MPa : mapped ma (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192)))))
              by (eapply (window_mapped LPA _ lo); [exact STma | exact FRq | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]);
            clear STma ST1 end end.
        (* [comment removed for export] *)
        lazymatch type of CF2 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          lazymatch goal with STq : stk _ ma (bv_unsigned sp - 128 - d) (bv_unsigned sp - 128) |- _ =>
            apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINVb CF2) in STq;
            [ rename STq into STpad2 | keeplia LO CEIL D0 | intros a Ha X; unfold newblk, blk in X; keeplia Ha X Bhi Shi SHB SHS LO CEIL ACV D0 ] end;
          lazymatch goal with FRq : rw_cells _ ma (bv_unsigned sp - 128) ?fcs |- _ =>
            pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp - 128) 128 AINVb ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                          (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRq ltac:(off_image_solve LPA))) as CRF;
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 _ fcs) in FRq;
            [ rename FRq into FR2 | exact CRF
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X Bhi Shi SHB SHS LO CEIL ACV ];
            clear CRF end;
          lazymatch goal with FFCq : rw_cells _ ma ff ?fcs |- _ =>
            pose proof FFCq as [[WFF _] _]; cbn [cells_wf cell_wf] in WFF;
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 ff fcs) in FFCq;
            [ rename FFCq into FFC2
            | eapply crange_fframe; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0) with 64; lia| cbn; lia]
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia FHI LO CEIL D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJfS DJfB SHB SHS FLO ];
            clear WFF end;
          lazymatch goal with SHCq : rw_cells _ ma (sh ff) ?scs |- _ =>
            apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (sh ff) scs) in SHCq;
            [ rename SHCq into SHC2
            | eapply crange_fshadow; [exact AINVb| exact FF1| lia| cbn [Cells.cells_size Cells.csize Nat.add length app]; change (fsize 0 / 8) with 8; lia| cbn; lia]
            | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SH1 LO CEIL ACV D0|];
              intros i Hi X; unfold newblk, blk in X; keeplia Hi X SHDS SHDB Slo Blo SH1 ] end
        end.
        (* [comment removed for export] *)
        ago AINV2. fold_cl_segs. fix_ret_pc. zstep. rewrite L7. zstep.
        try change (Z.b2z (0 =? 0)) with 1. try replace (Z_to_bv 64 (Z.b2z (bv_unsigned (Z_to_bv 64 0) =? 0))) with (Z_to_bv 64 1) by reflexivity.
        zstep. astop0 AINV2.
        lazymatch goal with AIq : ainv A2 ?mq ?mdq, SBq : same_but_materialized md2 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
          rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
        fold_cl_segs.
        (* [comment removed for export] *)
        destruct (rw_cells_forget rsegs _ _ _ FFC2) as [fj2 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
        pose proof FFC3 as [[WF3 _] _]. cbn [cells_wf cell_wf] in WF3.
        destruct (rw_cells_forget rsegs _ _ _ SHC2) as [shj2 SHC3]. cbn [cells_size csize Nat.add] in SHC3.
        pose proof SHC3 as [[WS3 _] _]. cbn [cells_wf cell_wf] in WS3.
        assert (MPX : mapped (aview A2 mX) (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))).
        { pose proof (stk_merge rsegs (aview A2 mX) _ _ _ ST2 STpad2 ltac:(keeplia D0 LO CEIL ACV)) as STm.
          eapply (window_mapped LPA _ lo); [exact STm | exact FR2 | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
        (* [comment removed for export] *)
        eapply (EC_C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A2 mX mdX vr2 j32 fj2 shj2);
          [ exact D0 | exact L1 | exact AINVx | exact MI2
          | eapply amd_frame_trans; [exact MDF|]; eapply amd_frame_sbm_l; [exact SBMb| exact MH|];
            eapply amd_frame_trans; [exact MDF2| apply amd_frame_sbm; [exact SBMx| exact MH2]]
          | exact ST2 | exact STpad2 | exact FR2 | exact FA' | exact FA12
          | exact (proj1 WF3) | exact FFC3 | exact (proj1 WS3) | exact SHC3
          | exact VEPO2 | exact SOBJ2 | exact LEN2 | exact SZ2 | exact REL | exact LIVEq | exact LB2 | exact TC2 | exact NL2 | exact SC2 | exact PC2 | ].
        (* [comment removed for export] *)
        assert (CFa : cframe LPA (owned A0) (owned A1) (bv_unsigned sp) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))
                        nowhere (frm ff 0) (aview A0 m0) (aview A1 mB)).
        { eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A0 m0) (aview A1 m1) (aview A1 mB) [] _);
          [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF01 | keeplia SPR | keeplia SPR
          | intros a X; destruct X | intros a X; left; exact X | exact MU | | exact MPa ].
          intros a Ha NO. cbn [outside] in NO. right; right. unfold frm. change (fsize 0) with 64. change (64 / 8) with 8. keeplia Ha NO. }
        ufs. eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) (aview A1 mB) (aview A2 mX) CFa);
          [ eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))); [exact CF2| keeplia D0| keeplia D0| exact MPX]
          | keeplia SPR | keeplia SPR | exact MPX
          | intros a X; destruct X
          | intros a [X|X]; [right; right; left; exact X| right; right; right; exact X]
          | intros a [X|X]; [left; exact X| right; left; exact X] ].
  Qed.
End S.
End A_veksn.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vekxy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vehtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vewqv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vep67 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_vel9u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vezat.A_veksn.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l mark lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis HCRC : crc32_stmt.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis HL0 : 0 <= l.
  Hypothesis HTOT : vv Fo_total + l < 2^62.
  Hypothesis HT0 : 0 <= vv Fo_total.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis DZ : vv Fdogzip = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis EM : vb_size vr + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 2 0.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITC_STACK <= bv_unsigned sp.
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
           (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) ->
      vep_obj LPA A' v' VEP vv' tag q ->
      (   (l = 0 /\ vv' = vv /\ vr' = vr)
       \/ (1 <= l /\ exists c, vv' = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A0 p) ->
      frames_aged A0 A' 2 0 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) EMITC_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj HCRC (conj AINV00 (conj HL0 (conj HTOT (conj HT0 (conj HMK (conj VOBJ (conj DZ (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM
      (conj NLV (conj SCM (conj PCM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO K))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Definition EC_B' := EC_B (* [comment removed for export] *) VEP vv tag q vr l mark lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                        HCRC AINV00 HL0 HTOT HT0 HMK VOBJ DZ SOBJ NES NEB EM LBM NLV SCM PCM FY TP SP16 CEIL LO K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K LO CEIL SP16 TP FY SCM PCM NLV LBM EM NEB NES SOBJ DZ VOBJ HMK HT0 HTOT HL0 AINV00 HCRC vr q tag vv"] Lemma EC_A : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) ->
    a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 mark ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x90294) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI Ha0 Ha1 Ha2 ST. subst a0 a1 a2.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _).
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand7 dR_1 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_2; dand11 dR_2 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear DSB Smap Bmap Simg Bimg.
    pose proof SOBJ as (_ & VINV0 & VLS & VLB & VNE & _).
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts. try (unhide_app_of ff).
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (uar_cells_of_consts _ (proj1 CE)) as [UARG UARV]. fold_aview. open_map_cells MC.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAP : mapped (aview A0 m0) (bv_unsigned sp - 128) 128) by (eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]).
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - 128, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [lia|]. split; [lia|].
      replace (bv_unsigned sp - (bv_unsigned sp - 128)) with 128 by lia. exact WMAP. }
    clear WMAP.
    ago AINV00. fold_cl_segs.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. rename FR into FRH. carve_frame 32%nat ST. rename FR into FR0.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    assert (AL16a : (bv_unsigned sp + -128) mod 16 = 0).
    { pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as Dv. rewrite SP16, Z.add_0_r in Dv. rewrite Dv.
      replace (16 * (bv_unsigned sp / 16) + -128) with ((bv_unsigned sp / 16 - 8) * 16) by lia. apply Z_mod_mult. }
    (first [ pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dex1 dR_3 as d; dand3 dR_3 as Dd ELAND AL32 | pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dand4 dR_3 as d Dd ELAND AL32 | destruct (land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a) as (d & Dd & ELAND & AL32) ]). clear AL16a.
    rewrite ELAND. clear ELAND. assert (D0 : 0 <= d <= 16) by (try (generalize alloc_ceiling_val); clear - Dd; try pose proof alloc_ceiling_val as ACV__; lia). clear Dd.
    (* [comment removed for export] *)
    do 3 zstep.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). if_false.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP.
    fold_cl_segs.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa end.
    lazymatch goal with STq : stk _ ?ma lo _, MIq : mem_inv _ ?ma |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      rename MIq into MIa;
      assert (MPW : mapped ma (bv_unsigned sp + -128 - d - ASTK) ASTK)
        by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STq | exact CEIL | keeplia LO D0 | keeplia D0]) end.
    eapply (smalloc_acall 0);
      [ exact AINVa | exact MIa | left; reflexivity | reflexivity | change (fsize 0) with 64; lia
      | exact (frames_young_smalloc A0 0 2%nat 0%nat FY (or_introl (conj eq_refl (le_S _ _ (le_n 1%nat)))))
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); apply mod16_of_mod32; exact AL32
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); unfold ASTK; keeplia CEIL LO D0
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A1 mB mdB fj fa fb
           AINV1 MI1 MDF1 LV1 LB1 TC1 NL1 SC1 PC1 NZ FN FF1 AGE NONE GEOM LFJ FFC SHC FRO CF1.
    clear FRO. pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    change (Z.to_nat (fsize 0 - 8)) with 56%nat in LFJ, FFC. change (Z.to_nat (fsize 0 / 8)) with 8%nat in SHC.
    (first [ dand5 GEOM as FAL FLO FHI SH0 SH1 | destruct GEOM as (FAL & FLO & FHI & SH0 & SH1) ]).
    change (fsize 0) with 64 in FHI. change (fsize 0 / 8) with 8 in SH1. unfold kHighMemBeg in FLO. all_app_facts. try (unhide_app_of ff).
    pose proof SH1 as SH1n. rewrite SHMAX_val in SH1n.
    rewrite unsigned_lit in CF1 by (keeplia SPR D0 LO CEIL ACV). unfold ASTK in CF1.
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      lazymatch goal with AIq : ainv A0 ?mq _ |- _ => rename AIq into AINVa end;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -128) 32 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR0 ltac:(off_image_solve LPA))) as CR0;
      lazymatch type of FR0 with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FR0;
        [ | exact CR0 | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CR0;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -96) 96 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CRH;
      lazymatch type of FRH with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FRH;
        [ | exact CRH | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CRH;
      lazymatch goal with STq : stk _ ma lo _ |- _ =>
        apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STq; [rename STq into STB | exact CEIL | intros a Ha X; exact X] end;
      assert (VEPO1 : vep_obj LPA A1 mb VEP vv tag q);
      [ eapply (vep_obj_ccall LPA A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| rewrite (LV1 VEP); exact VLV| intros a Ha X; exact X];
        eapply vep_obj_munch; [exact VOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ VEPhi ACV CEIL LO]
      | ];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| rewrite (LV1 S); exact VLS| rewrite (LV1 (vb_buf vr)); exact VLB| intros a Ha X; exact X];
        eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO]
      | ]
    end.
    fold_cl_segs. clear UARV UARG Che Ghe Cme Gme Cmb Gmb Csh Gsh MIa HID.
    (* [comment removed for export] *)
    release_frame FR0 STB (bv_unsigned sp + -96).
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d + 32) _ STB ltac:(keeplia D0 LO CEIL ACV)) as [STl STr]. clear STB.
    destruct (stk_carve rsegs _ lo _ 32 STl ltac:(keeplia D0 LO CEIL ACV)) as [STlo [jp PAD]]. clear STl.
    change (Z.of_nat 32) with 32 in STlo, PAD.
    replace (bv_unsigned sp + -128 - d + 32 - 32) with (bv_unsigned sp + -128 - d) in STlo, PAD by lia.
    unfold zcells in SHC. cbn [repeat] in SHC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -128 - d, bv_unsigned sp + -128 - d + 32)] (aview A1 mB)) as MU2.
    pose proof (wmono_refl rsegs (aview A1 mB)) as WM2.
    assert (CFP2 : client_fp LPA A1 (aview A1 mB) [(bv_unsigned sp + -128 - d, bv_unsigned sp + -128 - d + 32)]).
    { cbn. split; [| exact I]. left. split; [keeplia CEIL LO D0|]. split; [keeplia SPR D0|].
      replace (bv_unsigned sp + -128 - d + 32 - (bv_unsigned sp + -128 - d)) with (Z.of_nat (cells_size [CB 32 jp])) by (cbn [cells_size csize Nat.add]; lia).
      eapply (rw_cells_mapped LPA); [exact PAD| off_image_solve LPA]. }
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    astop AINV1 MU2 WM2 CFP2.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized mdB ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVx; rename SBq into SBMx; rename mq into mX; rename mdq into mdX end.
    fold_cl_segs.
    (* [comment removed for export] *)
    release_frame PAD STlo (bv_unsigned sp + -128 - d + 32).
    pose proof (stk_merge rsegs _ _ _ _ STlo STr ltac:(keeplia D0 LO CEIL ACV)) as STm. clear STlo STr.
    assert (MPX : mapped (aview A1 mX) (bv_unsigned sp - (128 + 16 + (128 + 16 + (80 + (80 + 8192))))) (128 + 16 + (128 + 16 + (80 + (80 + 8192))))).
    { eapply (window_mapped LPA _ lo); [exact STm | exact FRH | cbn; keeplia SPR | exact CEIL | keeplia LO | keeplia LO]. }
    destruct (stk_carve rsegs _ lo _ 32 STm ltac:(keeplia D0 LO CEIL ACV)) as [STm' [j32 F32]]. clear STm.
    change (Z.of_nat 32) with 32 in STm', F32.
    replace (bv_unsigned sp + -96 - 32) with (bv_unsigned sp - 128) in STm', F32 by lia.
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d) _ STm' ltac:(keeplia D0 LO CEIL ACV)) as [STlo STpad]. clear STm'.
    assert (FR : rw_cells rsegs (aview A1 mX) (bv_unsigned sp - 128)
                   [CB 32 j32; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app rsegs _ _ [CB 32 j32] _)). split; [exact F32|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp - 128 + Z.of_nat 32) with (bv_unsigned sp + -96) by lia. exact FRH. }
    clear F32 FRH.
    change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (zcells 8) in SHC.
    change (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in *.
    eapply (EC_B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 mX mdX j32 fj);
      [ exact D0 | apply mod16_of_mod32; exact AL32 | exact AINVx | assumption
      | eapply amd_frame_sbm_l; [exact SBMa| exact MH| eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBMx| exact MH1]]]
      | exact STlo | exact STpad | exact FR
      | (* [comment removed for export] *) split; [exact FN|]; split; [exact FF1|]; split; [exact AGE|]; split; [exact NONE|];
        split; [exact LV1|]; split; [exact LB1|]; split; [exact TC1|]; split; [exact NL1|]; split; [exact SC1|]; split; [exact PC1|];
        split; [exact FAL|]; split; [exact FLO_a|]; split; [exact FHI|]; split; [exact SH0| exact SH1]
      | exact LFJ | exact FFC | exact SHC
      | eapply vep_obj_munch; [exact VEPO1| exact MU2| exact WM2| intros a__ Ha__; cbn; keeplia Ha__ VEPhi ACV CEIL LO D0]
      | eapply vsb_obj_munch; [exact SOBJ1| exact MU2| exact WM2| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO D0]
      | ].
    (* [comment removed for export] *)
    ufs. eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) _ _ (aview A1 mX) _ _);
      [ exact MU | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO
      | exact CF1 | keeplia D0 | keeplia D0
      | intros a X; exact X | intros a X; left; exact X
      | exact MU2 | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO D0
      | exact MPX ].
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_emit_common_ok {AI : AsanAlloc LPA} {AI16 : AsanAlloc16} : crc32_stmt -> vep_emit_common_stmt.
Proof.
  intros HCRC. unfold vep_emit_common_stmt. intros VEP vv tag q vr l mark lo. intros.
  eapply (EC_A VEP vv tag q vr l mark lo); eassumption.
Qed.

End CEIL.
