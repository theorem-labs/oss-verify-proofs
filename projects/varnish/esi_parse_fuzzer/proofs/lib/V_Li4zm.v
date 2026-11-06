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
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge RzEqv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 V_Co10c.

Module V_Hawz4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge RzEqv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 V_Leaves V_Co10c
     V_VSle5 V_HKit LibIface Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import PeelK.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
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
Definition keptH (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide_neqsH := repeat match goal with H : (?x <> ?y) |- _ => (lazymatch type of H with ?T__ => change (keptH T__) in H end) end.
Ltac hide_slowH := hide_neqsH; repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => (lazymatch type of H with ?T__ => change (keptH T__) in H end) end.
Ltac unhide_slowH := repeat match goal with H : keptH _ |- _ => (lazymatch type of H with keptH ?T__ => change T__ in H | _ => idtac end) end.

Definition harness_entry : Z := 0x18048.

(* [comment removed for export] *)
Ltac hrelease sp ST F_pad F_wsemu F_wsrest F_hd0 F_hdb F_hde F_vsb F_ws F_wrk F_vc F_resp F_req F_cp F_vsclo F_cnt F_vschi F_saved :=
  release_frame F_pad ST (bv_unsigned sp + -3648);
  release_frame F_wsemu ST (bv_unsigned sp + -3616);
  release_frame F_wsrest ST (bv_unsigned sp + -2624);
  release_frame F_hd0 ST (bv_unsigned sp + -2608);
  release_frame F_hdb ST (bv_unsigned sp + -2600);
  release_frame F_hde ST (bv_unsigned sp + -2592);
  release_frame F_vsb ST (bv_unsigned sp + -2584);
  release_frame F_ws ST (bv_unsigned sp + -2544);
  release_frame F_wrk ST (bv_unsigned sp + -2360);
  release_frame F_vc ST (bv_unsigned sp + -2288);
  release_frame F_resp ST (bv_unsigned sp + -2232);
  release_frame F_req ST (bv_unsigned sp + -2176);
  release_frame F_cp ST (bv_unsigned sp + -1424);
  release_frame F_vsclo ST (bv_unsigned sp + -120);
  release_frame F_cnt ST (bv_unsigned sp + -104);
  release_frame F_vschi ST (bv_unsigned sp + -56);
  release_frame F_saved ST (bv_unsigned sp).

(* [comment removed for export] *)
Ltac xfer_stack F AINV CF :=
  lazymatch type of CF with cframe _ _ _ _ _ _ _ ?m ?m' =>
  lazymatch type of F with rw_cells _ _ ?a ?cs =>
    let F' := fresh in
    assert (F' : rw_cells rsegs m' a cs);
    [ eapply (rw_cells_ccall_stack LayoutP0 _ _ m _ m'); [exact AINV| exact CF| exact F| | |]
    | clear F; rename F' into F ]
  end end.

(* [comment removed for export] *)
Ltac flag_bound :=
  repeat match goal with |- context [Z.b2z (?f ?a ?c)] => destruct (f a c) end;
  match goal with |- 0 <= ?e < 16 => let v := eval vm_compute in e in change e with v end; lia.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HWSI : WS_Init_stmt.
  Hypothesis HVI : VEP_Init_stmt.
  Hypothesis HVP : VEP_Parse_stmt.
  Hypothesis HVF : VEP_Finish_stmt.
  Hypothesis HWR : WS_Rollback_stmt.

  (* [comment removed for export] *)
  Definition VHset (sp : Z) (a : Z) : Prop := (0x41830 <= a < 0x41830 + 16) \/ (sp + -3664 <= a < sp).

  #[using="HWR"] Lemma harness_tail :
    forall (E : option (Z * Z)) (N : Z -> Prop) (A Ak : AS) (m mk : mem) (md mdk : Model) (H : henv)
           (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word)
           (j1 j3 j4 j6 j7 j14 jhi : list byte) (T : TSet),
      H = HENV (bv_unsigned sp + -3664) 0x41830 ->
      tp = al_tp LayoutP0 -> bv_unsigned ra mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
      alloc_ceiling + 65536 + 16384 <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^47 ->
      ainv Ak mk mdk -> mem_inv rsegs mk -> md_frame md mdk ->
      stk rsegs mk (bv_unsigned sp - 16384) (bv_unsigned sp + -3664) ->
      match E with None => ws0_obj LayoutP0 H mk | Some (wa, vep) => ws1_obj LayoutP0 H Ak mk wa vep end ->
      match E with None => True | Some (wa, vep) => a_live A wa = None /\ a_live A vep = None /\
                                                   forall a, (blk wa 40 a \/ blk vep 312 a) -> N a end ->
      henv_ok LayoutP0 VI0 H mk -> img_ok0 mk ->
      rw_cells rsegs mk (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs mk (bv_unsigned sp + -3664) [CB 16 j1] ->
      rw_cells rsegs mk (bv_unsigned sp + -3616) [CB 992 j3] ->
      rw_cells rsegs mk (bv_unsigned sp + -2624) [CB 16 j4] ->
      rw_cells rsegs mk (bv_unsigned sp + -2600) [CB 8 j6] ->
      rw_cells rsegs mk (bv_unsigned sp + -2592) [CB 8 j7] ->
      rw_cells rsegs mk (bv_unsigned sp + -1424) [CB 1304 j14] ->
      rw_cells rsegs mk (bv_unsigned sp + -104) [CB 48 jhi] ->
      cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp + -3664) 12720 (VHset (bv_unsigned sp)) N m mk ->
      (forall p n, a_live A p = Some n -> a_live Ak p = Some n) ->
      (* [comment removed for export] *)
      (a_livebytes Ak = a_livebytes A + match E with None => 0 | Some _ => 352 end /\
       a_nlive Ak = a_nlive A + match E with None => 0 | Some _ => 2 end) ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          (forall p n, a_live A p = Some n -> a_live A' p = Some n) ->
          a_livebytes A' = a_livebytes A -> a_nlive A' = a_nlive A ->
          stk rsegs m' (bv_unsigned sp - 16384) (bv_unsigned sp) ->
          img_ok0 m' ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) 16384 (fun a => 0x41830 <= a < 0x41830 + 16) nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -3664)) gp tp xt0 xt1 xt2 xs0 xs1
                                      xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                                 bvmap_empty (Z_to_bv 64 0x181f8) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    intros until T. intros EH TP RA4 SP16 SPLO SPHI AINV MI MDF ST WS EFACTS HNV IMG F_saved F_pad F_wsrest F_hd0 F_hde F_vsb F_vsclo F_vschi CF LIVE BUDk K.
    subst H.
    pose proof (as_lazy_nil Ak mk mdk AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    assert (HG : henv_geom (HENV (bv_unsigned sp + -3664) 0x41830)) by (unfold henv_geom, HFRAME; cbn; lia).
    assert (Ews : h_ws (HENV (bv_unsigned sp + -3664) 0x41830) = bv_unsigned sp + -2584) by (unfold h_ws; cbn; lia).
    assert (Esp : h_sp (HENV (bv_unsigned sp + -3664) 0x41830) = bv_unsigned sp + -3664) by reflexivity.
    (* [comment removed for export] *)
    assert (EGEOM : match E with None => True | Some (wa, vep) => 4096 <= wa /\ wa + 40 <= alloc_ceiling /\
                                                                   4096 <= vep /\ vep + 312 <= alloc_ceiling /\
                       (wa + 40 <= 0x10000 \/ 0x63000 <= wa) /\ (vep + 312 <= 0x10000 \/ 0x63000 <= vep) end).
    { destruct E as [[wa vep]|]; [|exact I]. (first [ dex2 WS as id pad; dand7 WS as _ _ _ _ LVwa _ LVvep | dand9 WS as id pad _ _ _ _ LVwa _ LVvep | destruct WS as (id & pad & _ & _ & _ & _ & LVwa & _ & LVvep) ]).
      (first [ pose proof ((live_geom LayoutP0 Ak mk mdk wa 40 AINV LVwa)) as dR_2; dand6 dR_2 as _ _ X1 X2 X5 _ | destruct (live_geom LayoutP0 Ak mk mdk wa 40 AINV LVwa) as (_ & _ & X1 & X2 & X5 & _) ]).
      (first [ pose proof ((live_geom LayoutP0 Ak mk mdk vep 312 AINV LVvep)) as dR_3; dand6 dR_3 as _ _ X3 X4 X6 _ | destruct (live_geom LayoutP0 Ak mk mdk vep 312 AINV LVvep) as (_ & _ & X3 & X4 & X6 & _) ]).
      unfold off_image in X5, X6. cbn [al_image_lo al_image_hi LayoutP0] in X5, X6. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 16384, bv_unsigned sp + -3664)] mk) as MU.
    pose proof (wmono_refl rsegs mk) as WM.
    assert (CFP : client_fp LayoutP0 Ak [(bv_unsigned sp - 16384, bv_unsigned sp + -3664)]) by (cbn; split; [left; lia| exact I]).
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. apply rz_stop.
    pose_cranges LayoutP0 Ak mk AINV.
    eapply (HWR (HENV (bv_unsigned sp + -3664) 0x41830) E (bv_unsigned sp - 16384));
      [ exact AINV | exact MI | rewrite Ews; reflexivity | reflexivity | exact WS | exact (proj1 HNV) | exact HG | exact IMG | exact TP
      | rewrite unsigned_lit by lia; klia SP16
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST
      | lia
      | rewrite unsigned_lit by lia; unfold_stacks; lia
      | rewrite unsigned_lit by lia; rewrite Esp; reflexivity
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m2 md2 AINV2 MI2 MDF2 ST2 GLOB2 WS2 LIVE2 FRK.
    pose proof (as_lazy_nil A2 m2 md2 AINV2) as [MDL2 MDH2].
    rewrite unsigned_lit in ST2 by lia.
    hnorm_in FRK.
    (* [comment removed for export] *)
    assert (HOBJ2 : hobj_ok LayoutP0 VI0 (HENV (bv_unsigned sp + -3664) 0x41830) m2).
    { eapply (hobj_ok_ccall LayoutP0 VI0 _ Ak A2 mk mdk m2); [exact AINV| exact FRK| exact HG| exact (proj2 HNV)| cbn; lia|].
      unfold h_vc, h_wrk, h_req, h_resp, h_hd. cbn [h_sp]. intros a Ha X.
      destruct E as [[wa vep]|]; unfold blk in X; lia. }
    assert (IMG2 : img_ok0 m2).
    { eapply (img_ok0_ccall Ak A2 mk mdk m2); [exact AINV| exact FRK| unfold IMG0_HI; lia| | exact IMG].
      intros a Ha X. unfold IMG0_LO, IMG0_HI in Ha. destruct E as [[wa vep]|]; unfold blk in X; lia. }
    (* [comment removed for export] *)
    assert (FRKw : cframe LayoutP0 (owned Ak) (owned A2) (bv_unsigned sp + -3664) (48 + 32 + 8192)
                     (fun a => bv_unsigned sp + -2584 <= a < bv_unsigned sp + -2544 \/
                               bv_unsigned sp + -3648 <= a < bv_unsigned sp + -3616 \/ a < alloc_ceiling) nowhere mk m2).
    { eapply (cframe_weaken LayoutP0); [exact FRK| lia| exact (proj1 (proj2 FRK))| | intros a X; destruct X].
      intros a X; destruct X as [X|[X|X]]; [left; lia| right; left; lia| right; right; destruct E as [[wa vep]|]; unfold blk in X; lia]. }
    hide_slowH. acall_xfer FRKw. unhide_slowH. clear CR CR0 CR1 CR2 CR3 CR4 CR5 CR6 FRKw.
    assert (CF2 : cframe LayoutP0 (owned A) (owned A2) (bv_unsigned sp + -3664) 12720 (VHset (bv_unsigned sp)) N m m2).
    { eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m mk m2 CF FRK); [lia| lia
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
        | intros a X; exact X
        | intros a X; destruct X as [X|[X|X]]; [right; unfold VHset; lia| right; unfold VHset; lia|];
          destruct E as [[wa vep]|]; [left; apply (proj2 (proj2 EFACTS)); exact X| destruct X]
        | intros a X; left; exact X ]. }
    clear CF FRK.
    rz_resume MDH2 MDL2.
    (* [comment removed for export] *)
    zstep. zstep. do 7 zstep. zstep. zstep.
    try replace (bv_unsigned sp + -3664 + 1632 + 2032) with (bv_unsigned sp) by lia.
    try replace (bv_unsigned sp + -2032 + 2032) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    (first [ dex1 WS2 as wsid; dand3 WS2 as WSID F_ws F_wsemu | dand4 WS2 as wsid WSID F_ws F_wsemu | destruct WS2 as (wsid & WSID & F_ws & F_wsemu) ]). rewrite Ews in F_ws. unfold h_wsbuf in F_wsemu. cbn [h_sp] in F_wsemu.
    cbn [al_segs LayoutP0] in F_ws, F_wsemu.
    (first [ dand5 HOBJ2 as (p1 & r1 & _ & _ & F_vc) (p2 & r2 & _ & _ & F_wrk) (mi1 & tl1 & pd1 & _ & _ & _ & F_req) (hd2 & mi2 & tl2 & pd2 & _ & _ & _ & F_resp) F_hdb | destruct HOBJ2 as ((p1 & r1 & _ & _ & F_vc) & (p2 & r2 & _ & _ & F_wrk) & (mi1 & tl1 & pd1 & _ & _ & _ & F_req) &
                       (hd2 & mi2 & tl2 & pd2 & _ & _ & _ & F_resp) & F_hdb) ]).
    unfold h_vc, h_wrk, h_req, h_resp, h_hd in F_vc, F_wrk, F_req, F_resp, F_hdb. cbn [h_sp al_segs LayoutP0] in F_vc, F_wrk, F_req, F_resp, F_hdb.
    norm_base F_hdb. norm_base F_wsemu. norm_base F_vc. norm_base F_wrk. norm_base F_req. norm_base F_resp.
    (first [ dand4 GLOB2 as _ _ F_cp [cntb F_cnt] | destruct GLOB2 as (_ & _ & F_cp & [cntb F_cnt]) ]). unfold h_cp, h_vsc in F_cp, F_cnt. cbn [h_sp al_segs LayoutP0] in F_cp, F_cnt.
    norm_base F_cnt. norm_base F_cp.
    (* [comment removed for export] *)
    unfold ws_cells, ws_rec_of in F_ws. unfold wsemu_cells, wsemu_WS0 in F_wsemu. unfold vc_cells in F_vc. unfold wrk_cells in F_wrk.
    unfold http_cells in F_req, F_resp.
    hrelease sp ST F_pad F_wsemu F_wsrest F_hd0 F_hdb F_hde F_vsb F_ws F_wrk F_vc F_resp F_req F_cp F_vsclo F_cnt F_vschi F_saved.
    cps_done.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 m2 md2);
      [ exact AINV2 | exact MI2 | eapply md_frame_trans; [exact MDF| exact MDF2] |
      | destruct BUDk as [B1 _]; destruct E as [[wa vep]|]; [destruct LIVE2 as (_ & _ & _ & L2 & _)| destruct LIVE2 as (_ & L2 & _)]; revert B1 L2; clear; intros; lia
      | destruct BUDk as [_ B2]; destruct E as [[wa vep]|]; [destruct LIVE2 as (_ & _ & _ & _ & L2)| destruct LIVE2 as (_ & _ & L2)]; revert B2 L2; clear; intros; lia
      | exact ST | exact IMG2 | ].
    - intros p n Hp. pose proof (LIVE p n Hp) as Hk.
      destruct E as [[wa vep]|].
      + (first [ dand3 EFACTS as Fwa Fvep _ | destruct EFACTS as (Fwa & Fvep & _) ]). destruct LIVE2 as (_ & _ & EQ & _). rewrite EQ; [exact Hk| |]; intros ->; congruence.
      + rewrite (proj1 LIVE2). exact Hk.
    - (* [comment removed for export] *)
      assert (MAP : mapped m2 (bv_unsigned sp - 16384) 16384) by (eapply (stk_mapped (L:=LayoutP0)); [exact ST| lia| lia| lia]).
      pose proof (cframe_reframe LayoutP0 _ _ _ _ (bv_unsigned sp) 16384 _ _ _ _ CF2 ltac:(lia) ltac:(lia) MAP) as CF3.
      pose proof (cframe_absorb_window LayoutP0 _ _ _ _ _ (fun a => 0x41830 <= a < 0x41830 + 16) _ _ _ CF3
                    ltac:(intros a X; unfold VHset in X; destruct X as [X|X]; [left; exact X| right; lia])) as CF4.
      exact (cframe_weaken LayoutP0 _ _ _ _ 16384 _ _ _ nowhere _ _ CF4 ltac:(lia) MAP ltac:(intros a X; exact X) ltac:(intros a X; destruct X)).
  Qed.

  (* [comment removed for export] *)
  #[using="HWR HVF HVP HVI HWSI"] Lemma harness_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (DATA : Z) (inp : list byte) (e g : word) (v1 v2 : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 DATA -> a1 = Z_to_bv 64 (Z.of_nat (length inp)) ->
      tp = al_tp LayoutP0 -> bv_unsigned ra mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
      alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^47 ->
      stk rsegs m (bv_unsigned sp - LIB_STACK) (bv_unsigned sp) ->
      rw_cells rsegs m 0x420b4 [C4 e] ->
      rw_cells rsegs m 0x41830 [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2)] ->
      img_ok0 m -> rw_cells rsegs m 0x623c8 [C8 g] ->
      Z.of_nat (length inp) < 2^26 ->
      (length inp <> 0%nat -> a_live A DATA = Some (Z.of_nat (length inp)) /\ bytes_at rsegs m DATA inp) ->
      (* [comment removed for export] *)
      a_livebytes A + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX -> a_nlive A + LIB_NLIVE <= NLIVE_MAX ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          (forall p n, a_live A p = Some n -> a_live A' p = Some n) ->
          (* [comment removed for export] *)
          a_livebytes A' = a_livebytes A -> a_nlive A' = a_nlive A ->
          stk rsegs m' (bv_unsigned sp - LIB_STACK) (bv_unsigned sp) ->
          img_ok0 m' ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) LIB_STACK (fun a => 0x41830 <= a < 0x41830 + 16) nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 harness_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI A0 A1 TP RA4 SP16 SPLO SPHI ST ERR BSS IMG GRD LEN INP LBUD NBUD K.
    unfold LIB_LIVE in LBUD. unfold LIB_NLIVE in NBUD.
    rewrite A0, A1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    unfold LIB_STACK in *. unfold harness_entry.
    pose proof (munch_refl [(bv_unsigned sp - 16384, bv_unsigned sp); (0x41830, 0x41830 + 16)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 16384, bv_unsigned sp); (0x41830, 0x41830 + 16)]).
    { cbn. split; [left; lia|]. split; [|exact I]. right; right; right. split; [lia|]. split; [lia|].
      intros a Ha. unfold p0_static, p0_shared. lia. }
    (* [comment removed for export] *)
    destruct (Nat.eq_dec (length inp) 0) as [LEN0|LENp].
    { (* [comment removed for export] *)
      clear INP.
      apply rz_go; [exact MDH | exact MDL |].
      carve_frame 56%nat ST.
      zstep; do 7 zstep; zstep. rename FR into F_saved.
      zstep. if_cases KS; zify_cond KS. 2:{ exfalso. lia. }
      zstep. zstep. do 7 zstep. zstep. zstep.
      try replace (bv_unsigned sp + -3664 + 1632 + 2032) with (bv_unsigned sp) by lia.
      try replace (bv_unsigned sp + -2032 + 2032) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame F_saved ST (bv_unsigned sp).
      cps_done.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ A _ md);
        [ exact (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) | exact MI | apply md_frame_refl; [exact MDL| exact MDH]
        | intros p n Hp; exact Hp | reflexivity | reflexivity | exact ST
        | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
        | ].
      eapply (cframe_noalloc LayoutP0); [exact MU | | | intros a X; destruct X].
      - intros a Ha NO. cbn [outside] in NO. lia.
      - eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]. }
    (* [comment removed for export] *)
    destruct (INP LENp) as [LIVE BS]. clear INP.
    (first [ pose proof ((live_geom LayoutP0 A m md DATA _ AINV LIVE)) as dR_9; dand7 dR_9 as _ D16 Dlo Dhi Dimg _ _ | pose proof (live_geom LayoutP0 A m md DATA _ AINV LIVE) as (_ & D16 & Dlo & Dhi & Dimg & _ & _) ]).
    (* [comment removed for export] *)
    pose proof Dimg as Dimg'. unfold off_image in Dimg'. cbn [al_image_lo al_image_hi LayoutP0] in Dimg'.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    carve_frame 56%nat ST.
    (* [comment removed for export] *)
    zstep; do 7 zstep; zstep. rename FR into F_saved.
    carve_frame (Z.to_nat 3608) ST. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (rw_cells_head_split rsegs _ _ _ _ [] [16;32;Z.to_nat 992;16;8;8;8;40;184;72;56;56;Z.to_nat 752;Z.to_nat 1304;16;48]%nat) in FR; [|reflexivity].
    (* [comment removed for export] *)
    cbn [app] in FR; rewrite ?app_nil_r in FR.
    peelk FR F_pad. peelk FR F_wsemu. peelk FR F_wsrest. peelk FR F_hd0. peelk FR F_hdb. peelk FR F_hde. peelk FR F_vsb.
    peelk FR F_ws. peelk FR F_wrk. peelk FR F_vc. peelk FR F_resp. peelk FR F_req. peelk FR F_cp. peelk FR F_vsclo.
    peelk FR F_cnt. cbn [mk_CB_cells] in FR. rename FR into F_vschi.
    lazymatch type of F_vschi with rw_cells _ _ _ [CB _ ?bs] => set (junk_hi := bs) in F_vschi; clearbody junk_hi end.
    clear junk0.
    (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS. { exfalso. lia. } clear KS.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KD; zify_cond KD. { exfalso. klia KD. } clear KD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact F_cp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    (* [comment removed for export] *)
    destruct inp as [|b0 inp1] eqn:EINP; [cbn in LENp; lia|]. rewrite <- EINP in *. 
    assert (NTH0 : nth_error inp 0 = Some b0) by (rewrite EINP; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8ro_read rsegs mx DATA inp 0 b0 _ BS NTH0 ltac:(lia) eq_refl) as RD0 end.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (evt_cut rsegs (fun ms => exists (f : Z) (xa0 xa1 : word), 0 <= f < 16 /\ ms =
      MS (mkR (Z_to_bv 64 98472) (Z_to_bv 64 (bv_unsigned sp + -3664)) gp tp x x0 x1
              (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 DATA) xa0 xa1 x3 x4 x5 x6 x7 x8
              (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12)
         bvmap_empty (Z_to_bv 64 0x18104) (Z_to_bv 32 0) None mx (seg_rom rsegs)))
    end.
    { assert (NTH : forall i, (i < length inp)%nat -> exists b, nth_error inp i = Some b).
      { intros i Hi. destruct (nth_error inp i) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { apply evt_done. eexists _, _, _. split; [|reflexivity]. flag_bound. }
      destruct (NTH 1%nat ltac:(lia)) as [b1 NTH1].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my DATA inp 1 b1 _ BS NTH1 ltac:(lia) eq_refl) as RD1 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases K2; zify_cond K2.
      { apply evt_done. eexists _, _, _. split; [|reflexivity]. flag_bound. }
      destruct (NTH 2%nat ltac:(lia)) as [b2 NTH2].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my DATA inp 2 b2 _ BS NTH2 ltac:(lia) eq_refl) as RD2 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases K3; zify_cond K3.
      { apply evt_done. eexists _, _, _. split; [|reflexivity]. flag_bound. }
      destruct (NTH 3%nat ltac:(lia)) as [b3 NTH3].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my DATA inp 3 b3 _ BS NTH3 ltac:(lia) eq_refl) as RD3 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists _, _, _. split; [|reflexivity]. flag_bound. }
    (intros ms1; (first [ intro dR_17; dex3 dR_17 as flags xa0 xa1; destruct dR_17 as [FL ->] | intro dR_17; dand5 dR_17 as flags xa0 xa1 FL -> | intros (flags & xa0 & xa1 & FL & ->) ])). clear RD0 NTH0.
    (* [comment removed for export] *)
    set (H := HENV (bv_unsigned sp + -3664) 0x41830).
    assert (HG : henv_geom H) by (unfold henv_geom, HFRAME; cbn; lia).
    assert (Ews : h_ws H = bv_unsigned sp + -2584) by (unfold h_ws; cbn; lia).
    assert (Ewsbuf : h_wsbuf H = bv_unsigned sp + -3648) by (unfold h_wsbuf; cbn; lia).
    assert (Evsc : h_vsc H = bv_unsigned sp + -1424) by (unfold h_vsc; cbn; lia).
    assert (Ecp : h_cp H = bv_unsigned sp + -2176) by (unfold h_cp; cbn; lia).
    assert (Evc : h_vc H = bv_unsigned sp + -2360) by (unfold h_vc; cbn; lia).
    assert (Ewrk : h_wrk H = bv_unsigned sp + -2544) by (unfold h_wrk; cbn; lia).
    assert (Eresp : h_resp H = bv_unsigned sp + -2288) by (unfold h_resp; cbn; lia).
    assert (Ereq : h_req H = bv_unsigned sp + -2232) by (unfold h_req; cbn; lia).
    assert (Ehd : h_hd H = bv_unsigned sp + -2624) by (unfold h_hd; cbn; lia).
    assert (Evsbloc : h_vsbloc H = bv_unsigned sp + -2592) by (unfold h_vsbloc; cbn; lia).
    assert (Esp : h_sp H = bv_unsigned sp + -3664) by reflexivity.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (GLOB : glob_ok LayoutP0 VI0 H mx)
        by (split; [reflexivity|]; split; [rewrite Evsc, Ecp; exact BSS|]; split;
            [rewrite Ecp; exact POST| rewrite Evsc; eexists; eapply (rwc_eq _ _ _ _ _ F_cnt); lia])
    end.
    callh (HWSI H).
    1:{ rewrite Ews; reflexivity. } 1:{ reflexivity. } 1:{ rewrite Ewsbuf; reflexivity. } 1:{ reflexivity. }
    1:{ rewrite Ews; exact F_ws. } 1:{ rewrite Ewsbuf; exact F_wsemu. }
    1:{ exact GLOB. } 1:{ exact HG. }
    1:{ eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]. }
    1:{ rewrite Esp, unsigned_lit by lia; reflexivity. }
    1:{ rewrite unsigned_lit by lia. exact ST. } 1:{ rewrite unsigned_lit by lia; unfold WSINIT_STACK; lia. } 1:{ lia. } 1:{ assumption. }
    clear GLOB. rename PC into ST. rewrite unsigned_lit in ST by lia. rename PC0 into WS0. rename POST0 into GLOB.
    clear F_cnt BSS POST.
    (* [comment removed for export] *)
    (first [ dex1 WS0 as wsid; dand3 WS0 as WSID WSC WEC | dand4 WS0 as wsid WSID WSC WEC | destruct WS0 as (wsid & WSID & WSC & WEC) ]). rewrite Ews in WSC. rewrite Ewsbuf in WEC.
    (first [ dand4 GLOB as _ BSS GCP [cntb GCNT] | destruct GLOB as (_ & BSS & GCP & [cntb GCNT]) ]). rewrite Evsc, Ecp in BSS. rewrite Ecp in GCP. rewrite Evsc in GCNT.
    change (h_bss H) with 0x41830 in BSS. cbn [al_segs LayoutP0] in WSC, WEC, BSS, GCP, GCNT. norm_base GCNT.
    unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC. rewrite Ewsbuf in WSC.
    unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    (* [comment removed for export] *)
    hide_slowH.
    zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact F_req. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    rename POST into F_req. fold_to_nat_in F_req.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact F_resp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    rename POST into F_resp. fold_to_nat_in F_resp.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact F_wrk. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    rename POST into F_wrk. fold_to_nat_in F_wrk.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact F_vc. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    rename POST into F_vc. fold_to_nat_in F_vc.
    zstep. zstep. zstep. zstep. zstep.
    unhide_slowH.
    (* [comment removed for export] *)
    apply (rw_cells_recast rsegs _ _ _ (wrk_cells (repeat (Z_to_bv 8 0) 28) (repeat (Z_to_bv 8 0) 144))) in F_wrk;
      [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | vm_compute; reflexivity].
    apply (rw_cells_recast rsegs _ _ _ (http_cells 0 (repeat (Z_to_bv 8 0) 24) (bv_unsigned sp + -2584) (repeat (Z_to_bv 8 0) 8)
                                                    (repeat (Z_to_bv 8 0) 4))) in F_resp;
      [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | cbn [cells_bytes cbytes app http_cells]; reflexivity].
    rewrite <- Evc, <- Eresp, <- Ewrk in F_vc. rewrite <- Ewrk in F_wrk. rewrite <- Ereq, <- Ehd, <- Ews in F_req.
    rewrite <- Eresp, <- Ews in F_resp.
    eassert (HOBJ : hobj_ok LayoutP0 VI0 H _).
    { eapply hobj_ok_intro; try exact F_vc; try exact F_wrk; try exact F_req; try exact F_resp; try reflexivity.
      rewrite Ehd. eapply (rwc_eq _ _ _ _ _ F_hdb). lia. }
    clear F_vc F_wrk F_req F_resp F_hdb.
    eassert (GLOB : glob_ok LayoutP0 VI0 H _).
    { eapply glob_ok_intro; [reflexivity | rewrite Evsc, Ecp; exact BSS | rewrite Ecp; exact GCP | rewrite Evsc; eapply (rwc_eq _ _ _ _ _ GCNT); lia]. }
    clear BSS GCP GCNT.
    eassert (WS0 : ws0_obj LayoutP0 H _).
    { eapply (ws0_obj_intro LayoutP0 H _ wsid WSID).
      - rewrite Ews. unfold ws_cells, ws_rec_of. cbn [ws_id ws_s ws_f ws_r ws_e]. rewrite Ewsbuf. exact WSC.
      - rewrite Ewsbuf. exact WEC. }
    clear WSC WEC.
    (* [comment removed for export] *)
    do 5 zstep. zstep. apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1;
      pose proof (img_ok0_munch _ m mx MU ltac:(intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia) IMG) as IMG1;
      pose_cranges LayoutP0 A mx AINV1
    end.
    eapply (HVI H flags (bv_unsigned sp - 16384));
      [ exact AINV1 | exact MI | exists DATA, (Z.of_nat (length inp)); exact LIVE
      | rewrite Evc; reflexivity | rewrite Ereq; reflexivity | reflexivity | reflexivity | reflexivity | exact FL
      | exact WS0 | exact (conj GLOB HOBJ) | exact HG | exact IMG1
      | revert LBUD; clear; intros; lia | revert NBUD; clear; intros; lia
      | exact TP
      | rewrite unsigned_lit by lia; klia SP16
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST
      | lia
      | rewrite unsigned_lit by lia; unfold_stacks; lia
      | rewrite unsigned_lit by lia; rewrite Esp; reflexivity
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r Ax m1 md1 AINV' MI' MDF ST1 HENV1 IMG2 OUT.
    pose proof (as_lazy_nil Ax m1 md1 AINV') as [MDL1 MDH1].
    rewrite unsigned_lit in ST1 by lia.
    (* [comment removed for export] *)
    set (VH := fun a : Z => (0x41830 <= a < 0x41830 + 16) \/ (bv_unsigned sp + -3664 <= a < bv_unsigned sp)).
    lazymatch type of MU with munch _ m ?mx =>
      assert (CF0 : cframe LayoutP0 (owned A) (owned A) (bv_unsigned sp + -3664) 12720 VH nowhere m mx)
        by (eapply (cframe_stores LayoutP0); [exact MU | intros a Ha NO; subst VH; cbn [outside] in NO; cbn beta; lia
            | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia] ])
    end.
    pose proof (crange_block (L:=LayoutP0) A _ md DATA (Z.of_nat (length inp)) DATA (Z.of_nat (length inp)) AINV1 LIVE
                  ltac:(lia) ltac:(lia) ltac:(lia)) as CRD.
    (* [comment removed for export] *)
    destruct OUT as (wa & tag & q & b & NZ & WS1 & S & VEPO & SNZ & VSBO & FRS & FRb & NSr & Nbr & NSwa & Nbwa & FRwa & FRr & LIVEq & LBx & NLx & FRK).
    - (* [comment removed for export] *)
      hnorm_in FRK. hide_slowH. acall_xfer FRK. unhide_slowH. clear AINV1 CR CR0 CR1 CR2 CR3 CR4 CR5 CR6.
      assert (CF1 : cframe LayoutP0 (owned A) (owned Ax) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) m m1).
      { eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m _ m1 CF0 FRK); [lia| lia
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
          | intros a X; exact X | intros a X; right; subst VH; cbn beta; lia | intros a X; right; left; exact X]. }
      clear CF0 FRK.
      (first [ pose proof ((live_geom LayoutP0 Ax m1 md1 r 312 AINV' (proj1 VEPO))) as dR_12; dand6 dR_12 as _ R16 Rlo Rhi Rimg _ | pose proof (live_geom LayoutP0 Ax m1 md1 r 312 AINV' (proj1 VEPO)) as (_ & R16 & Rlo & Rhi & Rimg & _) ]).
      (first [ pose proof ((vsb_obj_geom LayoutP0 Ax m1 md1 S _ false AINV' VSBO)) as dR_13; dand8 dR_13 as _ Slo Shi _ _ Blo Bhi _ | pose proof (vsb_obj_geom LayoutP0 Ax m1 md1 S _ false AINV' VSBO) as (_ & Slo & Shi & _ & _ & Blo & Bhi & _) ]). cbn [vb_buf vb_size vsb_fresh] in Blo, Bhi.
      rz_resume MDH1 MDL1.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
      zstep. zstep. zstep. zstep. apply rz_stop.
      assert (NDr : DATA <> r) by (intros ->; rewrite FRr in LIVE; discriminate).
      assert (NDS : DATA <> S) by (intros ->; rewrite FRS in LIVE; discriminate).
      assert (NDb : DATA <> b) by (intros ->; rewrite FRb in LIVE; discriminate).
      assert (NDwa : DATA <> wa) by (intros ->; rewrite FRwa in LIVE; discriminate).
      assert (LIVE1 : a_live Ax DATA = Some (Z.of_nat (length inp))) by (rewrite LIVEq; [exact LIVE| | | |]; congruence).
      pose_cranges LayoutP0 Ax m1 AINV'.
      eapply (HVP H r S b flags wa DATA inp tag q (bv_unsigned sp - 16384));
        [ exact AINV' | exact MI' | reflexivity | reflexivity | reflexivity | exact FL
        | exact VEPO | exact SNZ | exact VSBO | exact WS1 | split; [exact LIVE1| split; [exact BS| lia]]
        | exact HENV1 | exact HG | exact IMG2
        | congruence | congruence | congruence | congruence | congruence | congruence | congruence | congruence
        | unfold PARSE_LIVE; revert LBUD LBx; clear; intros; lia | unfold PARSE_NLIVE; revert NBUD NLx; clear; intros; lia
        | exact TP
        | rewrite unsigned_lit by lia; klia SP16
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | lia
        | rewrite unsigned_lit by lia; unfold_stacks; lia
        | rewrite unsigned_lit by lia; rewrite Esp; reflexivity
        | ].
      intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A3 m3 md3 v' tag' q' vv' va vi n
             AINV3 MI3 MDF3 ST3 HENV3 IMG3 PW VSBS VERP WS3 DOB3 PL1 PL2 LB3 NL3 FRK3.
      pose proof (as_lazy_nil A3 m3 md3 AINV3) as [MDL3 MDH3].
      rewrite unsigned_lit in ST3 by lia. hnorm_in FRK3.
      assert (FRKw : cframe LayoutP0 (owned Ax) (owned A3) (bv_unsigned sp + -3664) (176 + (112 + (64 + 64 + (48 + 8256))))
                       (fun a => bv_unsigned sp + -120 <= a < bv_unsigned sp + -104 \/ a < alloc_ceiling) nowhere m1 m3).
      { eapply (cframe_weaken LayoutP0); [exact FRK3| lia| exact (proj1 (proj2 FRK3))| | intros a X; destruct X].
        intros a X. unfold parse_changed, blk in X. rewrite Evsc in X. clear - X Rhi Shi Bhi SPLO ACV. lia. }
      hide_slowH. acall_xfer FRKw. unhide_slowH. clear FRKw CR CR0 CR1 CR2 CR3 CR4 CR5 CR6.
      assert (CF2 : cframe LayoutP0 (owned A) (owned A3) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => (blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a) m m3).
      { eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m m1 m3 CF1 FRK3); [lia| lia
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
          | intros a X; exact X
          | intros a X; unfold parse_changed in X; destruct X as [X|[X|[X|X]]];
            [ left; right; left; exact X | left; right; right; left; exact X | left; right; right; right; exact X
            | right; subst VH; cbn beta; rewrite Evsc in X; lia]
          | intros a [X|X]; [left; exact X| right; left; exact X] ]. }
      clear CF1 FRK3.
      rz_resume MDH3 MDL3.
      (* [comment removed for export] *)
      zstep. zstep. apply rz_stop.
      pose_cranges LayoutP0 A3 m3 AINV3.
      eapply (HVF H r wa n (Z.of_nat (length inp)) DATA v' tag' q' vv' va vi (bv_unsigned sp - 16384));
        [ exact AINV3 | exact MI3 | reflexivity | exact PW | exact WS3 | exact HENV3 | exact HG | exact IMG3
        | exact (proj1 DOB3) | lia | exact VERP | exact NDr | rewrite VSBS; exact NDS
        | intros X; destruct (PL2 DATA X) as [E|E]; [exact (NDb E)| rewrite LIVE1 in E; discriminate]
        | pose proof (proj2 (parsed_world_room _ _ _ _ _ _ _ _ _ _ _ _ _ PW)) as WBB; unfold FIN_LIVE; revert LBUD LBx LB3 WBB; clear; intros; lia
        | pose proof (world_nlive_nonneg va vi) as WNL; revert NBUD NLx NL3 WNL; clear; intros; lia
        | exact TP
        | rewrite unsigned_lit by lia; klia SP16
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | lia
        | rewrite unsigned_lit by lia; unfold_stacks; lia
        | rewrite unsigned_lit by lia; rewrite Esp; reflexivity
        | ].
      intros t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y r0 A4 m4 md4 v4 vr AINV4 MI4 MDF4 ST4 HENV4 IMG4 VEPO4 WS4 RES FL1 LB4 NL4 FRK4.
      pose proof (as_lazy_nil A4 m4 md4 AINV4) as [MDL4 MDH4].
      rewrite unsigned_lit in ST4 by lia. hnorm_in FRK4.
      assert (FRKw : cframe LayoutP0 (owned A3) (owned A4) (bv_unsigned sp + -3664) (32 + (48 + (48 + (32 + (48 + (48 + 8256))))))
                       (fun a => bv_unsigned sp + -120 <= a < bv_unsigned sp + -104 \/ a < alloc_ceiling) nowhere m3 m4).
      { eapply (cframe_weaken LayoutP0); [exact FRK4| lia| exact (proj1 (proj2 FRK4))| | intros a X; destruct X].
        intros a X. destruct (finish_changed_bound H A3 m3 r v' tag' q' vv' va vi wa n _ md3 a AINV3 PW X) as [Y|Y]; [left; rewrite Evsc in Y; lia| right; lia]. }
      hide_slowH. acall_xfer FRKw. unhide_slowH. clear FRKw CR CR0 CR1 CR2 CR3 CR4 CR5 CR6.
      assert (CF3 : cframe LayoutP0 (owned A) (owned A4) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a)
                               \/ (r0 <> 0 /\ vsb_blocks r0 vr a)) m m4).
      { eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m m3 m4 CF2 FRK4); [lia| lia
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
          | intros a X; exact X
          | intros a X; destruct (finish_changed_cases H r v' vv' va vi a X) as [Y|[Y|[Y|Y]]];
            [ left; left; right; left; exact Y | left; left; rewrite VSBS in Y; right; right; left; exact Y | left; right; exact Y
            | right; subst VH; cbn beta; rewrite Evsc in Y; lia]
          | intros a [X|X]; [left; exact X| right; left; exact X] ]. }
      clear CF2 FRK4.
      (* [comment removed for export] *)
      assert (LIVE4 : forall p k, a_live A p = Some k -> a_live A4 p = Some k).
      { intros p k Hp.
        assert (Hp1 : a_live Ax p = Some k) by (rewrite LIVEq; [exact Hp| | | |]; intros ->; congruence).
        assert (Hp3 : a_live A3 p = Some k) by (apply PL1; [exact Hp1| intros ->; congruence]).
        apply FL1; [exact Hp3| rewrite VSBS; intros ->; congruence|].
        intros X. destruct (PL2 p X) as [->|Y]; congruence. }
      (* [comment removed for export] *)
      assert (RGEOM : r0 <> 0 -> 4096 <= r0 /\ r0 + 40 <= alloc_ceiling /\ 4096 <= vb_buf vr /\ vb_buf vr + vb_size vr <= alloc_ceiling /\
                      (r0 + 40 <= 0x10000 \/ 0x63000 <= r0) /\ (vb_buf vr + vb_size vr <= 0x10000 \/ 0x63000 <= vb_buf vr)).
      { intros Hr. destruct RES as [E0|(_ & _ & VO & _)]; [exfalso; exact (Hr E0)|].
        pose proof (vsb_obj_geom LayoutP0 A4 m4 md4 r0 vr true AINV4 VO) as (_ & ? & ? & X1 & _ & ? & ? & X2 & _).
        unfold off_image in X1, X2. cbn [al_image_lo al_image_hi LayoutP0] in X1, X2. lia. }
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (munch_refl [(bv_unsigned sp + -2592, bv_unsigned sp + -2584)] mx) as MU5;
        pose proof (wmono_refl rsegs mx) as WM5 end.
      (* [comment removed for export] *)
      destruct RES as [E0 | (NZ0 & ER0 & VO & VAP & VBUF0)].
      + (* [comment removed for export] *)
        subst r0. change (0 =? 0) with true in LB4, NL4. cbv iota in LB4, NL4.
        rz_resume MDH4 MDL4.
        hide_slowH. zstep. unhide_slowH. zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. klia KZ. } clear KZ.
        apply rz_stop.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          assert (HENV5 : henv_ok LayoutP0 VI0 H mx)
            by (eapply (henv_ok_munch LayoutP0); [exact HENV4| exact MU5| exact WM5|];
                intros a Ha; unfold h_bss, h_hd, h_wrk, h_req, h_vsc in Ha; cbn [h_sp H] in Ha; cbn [outside]; subst H; cbn in Ha; lia);
          assert (WS5 : ws1_obj LayoutP0 H A4 mx wa r)
            by (eapply (ws1_obj_munch LayoutP0); [exact WS4| exact MU5| exact WM5|];
                intros a Ha; unfold h_ws, h_wsbuf in Ha; subst H; cbn in Ha; cbn [outside];
                destruct (live_geom LayoutP0 Ax m1 md1 wa 40 AINV' ltac:(destruct WS1 as (? & ? & ? & ? & ? & ? & LV & ?); exact LV)) as (_ & _ & ? & ? & _); lia);
          assert (IMG5 : img_ok0 mx)
            by (eapply (img_ok0_munch _ _ mx MU5); [intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG4]);
          assert (CF4 : cframe LayoutP0 (owned A) (owned A4) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a)
                               \/ (0 <> 0 /\ vsb_blocks 0 vr a)) m mx)
            by (eapply (cframe_seq LayoutP0 _ _ _ _ _ 12720 _ _ _ _ _ _ _ m m4 mx CF3);
                [ eapply (cframe_stores LayoutP0 _ _ 12720 (fun a => bv_unsigned sp + -2592 <= a < bv_unsigned sp + -2584));
                    [exact MU5| intros a Ha NO; cbn [outside] in NO; right; lia
                    | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia] ]
                | lia | lia | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
                | intros a X; exact X | intros a X; cbn beta in X; right; subst VH; cbn beta; lia | intros a X; left; exact X ])
        end.
        eapply (harness_tail (Some (wa, r))
                  (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a) \/ (0 <> 0 /\ vsb_blocks 0 vr a))
                  A A4 m _ md md4 H);
          [ reflexivity | exact TP | exact RA4 | exact SP16 | lia | exact SPHI | exact (ainv_munch LayoutP0 A4 m4 _ md4 _ AINV4 MU5 WM5 ltac:(cbn; split; [left; lia| exact I]))
          | assumption | eapply md_frame_trans; [exact MDF| eapply md_frame_trans; [exact MDF3| exact MDF4]] | exact ST
          | exact WS5 | split; [exact FRwa| split; [exact FRr| intros a X; cbn beta; left; left; destruct X as [X|X]; [left; exact X| right; left; exact X]]] | exact HENV5 | exact IMG5
          | exact F_saved | exact F_pad | exact F_wsrest | exact F_hd0 | exact F_hde | exact (rw_cells_C8_CB _ _ _ _ F_vsb) | exact F_vsclo | exact F_vschi
          | exact CF4 | exact LIVE4
          | split; [revert LBx LB3 LB4; clear; intros; lia| revert NLx NL3 NL4; clear; intros; lia]
          | exact K ].
      + (* [comment removed for export] *)
        replace (r0 =? 0) with false in LB4, NL4 by (symmetry; apply Z.eqb_neq; exact NZ0).
        specialize (RGEOM NZ0). (first [ dand6 RGEOM as R0lo R0hi RBlo RBhi R0img RBimg | destruct RGEOM as (R0lo & R0hi & RBlo & RBhi & R0img & RBimg) ]).
        pose proof VO as VO'. vsb_open VO'. (first [ dex1 VBUF as bsr; dand3 VBUF as U8r LBSr NULr | dand4 VBUF as bsr U8r LBSr NULr | destruct VBUF as (bsr & U8r & LBSr & NULr) ]). cbn [al_segs LayoutP0] in U8r.
        rz_resume MDH4 MDL4.
        hide_slowH. zstep. unhide_slowH. zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
        zstep. zstep. apply rz_stop. hide_slowH.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          assert (HENV5 : henv_ok LayoutP0 VI0 H mx)
            by (eapply (henv_ok_munch LayoutP0); [exact HENV4| exact MU5| exact WM5|];
                intros a Ha; unfold h_bss, h_hd, h_wrk, h_req, h_vsc in Ha; subst H; cbn in Ha; cbn [outside]; lia);
          assert (WS5 : ws1_obj LayoutP0 H A4 mx wa r)
            by (eapply (ws1_obj_munch LayoutP0); [exact WS4| exact MU5| exact WM5|];
                intros a Ha; unfold h_ws, h_wsbuf in Ha; subst H; cbn in Ha; cbn [outside];
                destruct (live_geom LayoutP0 Ax m1 md1 wa 40 AINV' ltac:(destruct WS1 as (? & ? & ? & ? & ? & ? & LV & ?); exact LV)) as (_ & _ & ? & ? & _); lia);
          assert (IMG5 : img_ok0 mx)
            by (eapply (img_ok0_munch _ _ mx MU5); [intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG4]);
          assert (CF4 : cframe LayoutP0 (owned A) (owned A4) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a)
                               \/ (r0 <> 0 /\ vsb_blocks r0 vr a)) m mx)
            by (eapply (cframe_seq LayoutP0 _ _ _ _ _ 12720 _ _ _ _ _ _ _ m m4 mx CF3);
                [ eapply (cframe_stores LayoutP0 _ _ 12720 (fun a => bv_unsigned sp + -2592 <= a < bv_unsigned sp + -2584));
                    [exact MU5| intros a Ha NO; cbn [outside] in NO; right; lia
                    | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia] ]
                | lia | lia | eapply (stk_mapped (L:=LayoutP0)); [exact ST | lia | lia | lia]
                | intros a X; exact X | intros a X; cbn beta in X; right; subst VH; cbn beta; lia | intros a X; left; exact X ]);
          pose proof (ainv_munch LayoutP0 A4 m4 mx md4 _ AINV4 MU5 WM5 ltac:(cbn; split; [left; lia| exact I])) as AINV5;
          pose_cranges LayoutP0 A4 mx AINV5
        end.
        clear CF3 MU5 WM5. unhide_slowH. hide_neqsH.
        eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -2592) r0 vr true (bv_unsigned sp - 16384));
          [ exact AINV5 | assumption | reflexivity | exact F_vsb
          | left; rewrite unsigned_lit by lia; lia
          | split; [exact VSBC|]; split; [exact VINV|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
            exists bsr; split; [exact U8r|]; split; [exact LBSr| exact NULr]
          | exact TP
          | rewrite unsigned_lit by lia; klia SP16
          | rewrite unsigned_lit by lia; reflexivity
          | rewrite unsigned_lit by lia; exact ST
          | lia
          | rewrite unsigned_lit by lia; unfold DESTROY_STACK, FREE_STACK; lia
          | rewrite unsigned_lit by lia; lia
          | ].
        intros t0z t1z t2z a0z a1z a2z a3z a4z a5z a6z a7z t3z t4z t5z t6z A6 m6 md6 AINV6 MI6 MDF6 ST6 PSC DEAD1 DEAD2 LIVEq6 LB6 NL6 FRK6.
        unhide_slowH.
        pose proof (as_lazy_nil A6 m6 md6 AINV6) as [MDL6 MDH6].
        rewrite unsigned_lit in ST6, FRK6 by lia.
        (* [comment removed for export] *)
        assert (LIVE6 : forall p k, a_live A p = Some k -> a_live A6 p = Some k).
        { intros p k Hp.
          assert (Hp1 : a_live Ax p = Some k) by (rewrite LIVEq; [exact Hp| | | |]; intros ->; congruence).
          assert (Hp3 : a_live A3 p = Some k) by (apply PL1; [exact Hp1| intros ->; congruence]).
          rewrite LIVEq6; [exact (LIVE4 p k Hp)| rewrite ER0, VSBS; intros ->; congruence |].
          intros E0. rewrite E0 in Hp, Hp1, Hp3. destruct VBUF0 as [E|E].
          * destruct (PL2 _ E) as [E2|E2]; [rewrite E2 in Hp; congruence| congruence].
          * congruence. }
        clear VBUF0 PL2 Dimg'.
        (* [comment removed for export] *)
        (first [ pose proof ((live_geom LayoutP0 Ax m1 md1 wa 40 AINV' ltac:(destruct WS1 as (? & ? & ? & ? & ? & ? & LV & ?); exact LV))) as dR_16; dand5 dR_16 as _ _ Wlo Whi _ | destruct (live_geom LayoutP0 Ax m1 md1 wa 40 AINV' ltac:(destruct WS1 as (? & ? & ? & ? & ? & ? & LV & ?); exact LV)) as (_ & _ & Wlo & Whi & _) ]).
        pose proof (VAP wa (or_intror (or_introl eq_refl))) as [NE1 NE2].
        assert (LVwa4 : a_live A4 wa = Some 40) by (destruct WS5 as (? & ? & ? & ? & ? & ? & LV & ?); exact LV).
        lazymatch type of FRK6 with cframe _ _ _ _ _ _ _ ?mx _ =>
          pose proof (as_live_disjoint (L:=LayoutP0) A4 mx md4 wa 40 r0 40 AINV5 LVwa4 VLS (fun E => NE1 (eq_sym E))) as D1;
          pose proof (as_live_disjoint (L:=LayoutP0) A4 mx md4 wa 40 (vb_buf vr) (vb_size vr) AINV5 LVwa4 VLB (fun E => NE2 (eq_sym E))) as D2;
          assert (HENV6 : henv_ok LayoutP0 VI0 H m6);
          [ split;
            [ eapply (glob_ok_ccall LayoutP0 VI0 H A4 A6 mx md4 m6); [exact AINV5| exact FRK6| exact HG| exact (proj1 HENV5)
                | rewrite Esp; clear - SPLO; lia| clear - SPLO ACV; unfold DESTROY_STACK, FREE_STACK; lia| subst H; cbn; clear - SPLO; lia| subst H; cbn; clear - SPLO; lia
                | intros i Hi; subst H; cbn; unfold p0_static; clear - Hi; lia| subst H; cbn; change (al_errno LayoutP0) with 0x420b4; clear - SPLO; lia|];
              intros a Ha X; unfold h_bss, h_cp, h_vsc in Ha; subst H; cbn in Ha; unfold blk in X; clear - Ha X R0hi RBhi R0img RBimg SPLO ACV; lia
            | eapply (hobj_ok_ccall LayoutP0 VI0 H A4 A6 mx md4 m6); [exact AINV5| exact FRK6| exact HG| exact (proj2 HENV5)| rewrite Esp; clear - SPLO; lia|];
              intros a Ha X; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; subst H; cbn in Ha; unfold blk in X; clear - Ha X R0hi RBhi SPLO ACV; lia ]
          | ];
          assert (WS6 : ws1_obj LayoutP0 H A6 m6 wa r);
          [ eapply (ws1_obj_ccall LayoutP0 H A4 A6 mx md4 m6); [exact AINV5| exact FRK6| exact HG| exact WS5| rewrite Esp; clear - SPLO; lia| clear - SPLO ACV; unfold DESTROY_STACK, FREE_STACK; lia
              | rewrite LIVEq6; [exact LVwa4| intros EE; exact (NE1 (eq_sym EE))| intros EE; exact (NE2 (eq_sym EE))]
              | rewrite LIVEq6; [destruct WS5 as (? & ? & ? & ? & ? & ? & ? & ? & LV2); exact LV2| intros EE; exact (proj1 (VAP r (or_introl eq_refl)) (eq_sym EE))| intros EE; exact (proj2 (VAP r (or_introl eq_refl)) (eq_sym EE))]
              |];
            intros a Ha X; unfold h_ws, h_wsbuf in Ha; subst H; cbn in Ha; unfold blk in X; clear - Ha X Wlo Whi D1 D2 R0hi RBhi SPLO ACV; lia
          | ];
          assert (IMG6 : img_ok0 m6);
          [ eapply (img_ok0_ccall A4 A6 mx md4 m6); [exact AINV5| exact FRK6| clear - SPLO ACV; unfold IMG0_HI, DESTROY_STACK, FREE_STACK; lia| | exact IMG5];
            intros a Ha X; unfold IMG0_LO, IMG0_HI in Ha; unfold blk in X; clear - Ha X R0img RBimg SPLO ACV; lia
          | ]
        end.
        (* [comment removed for export] *)
        xfer_stack F_saved AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_pad AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_wsrest AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_hd0 AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_hde AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_vsclo AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        xfer_stack F_vschi AINV5 FRK6; [clear - SPLO ACV; lia| right; clear - SPLO; lia| intros ya Hya Ya; cbn in Hya; unfold blk in Ya; clear - Hya Ya R0hi RBhi SPLO ACV; lia|].
        assert (CF5 : cframe LayoutP0 (owned A) (owned A6) (bv_unsigned sp + -3664) 12720 VH
                     (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a)
                               \/ (r0 <> 0 /\ vsb_blocks r0 vr a)) m m6).
        { eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m _ m6 CF4 FRK6); [clear - SPLO; lia| clear - SPLO; unfold DESTROY_STACK, FREE_STACK; lia
            | eapply (stk_mapped (L:=LayoutP0)); [exact ST6 | clear - SPLO ACV; lia | clear - SPLO ACV; lia | clear - SPLO ACV; lia]
            | intros a X; exact X
            | intros a X; destruct X as [X|[X|X]];
              [ left; rewrite ER0, VSBS in X; left; left; right; right; left; exact X
              | left; right; split; [exact NZ0| right; exact X]
              | right; subst VH; cbn beta; clear - X; lia ]
            | intros a X; left; exact X ]. }
        clear CF4 FRK6 AINV5.
        rz_resume MDH6 MDL6.
        apply rz_stop.
        eapply (harness_tail (Some (wa, r))
                  (fun a => ((blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) \/ parse_new v' vv' va vi a) \/ (r0 <> 0 /\ vsb_blocks r0 vr a))
                  A A6 m m6 md md6 H);
          [ reflexivity | exact TP | exact RA4 | exact SP16 | clear - SPLO; lia | exact SPHI | exact AINV6 | exact MI6
          | eapply md_frame_trans; [exact MDF| eapply md_frame_trans; [exact MDF3| eapply md_frame_trans; [exact MDF4| exact MDF6]]] | exact ST6
          | exact WS6 | split; [exact FRwa| split; [exact FRr| intros a X; cbn beta; left; left; destruct X as [X|X]; [left; exact X| right; left; exact X]]] | exact HENV6 | exact IMG6
          | exact F_saved | exact F_pad | exact F_wsrest | exact F_hd0 | exact F_hde | exact (rw_cells_C8_CB _ _ _ _ PSC) | exact F_vsclo | exact F_vschi
          | exact CF5 | exact LIVE6
          | split; [revert LBx LB3 LB4 LB6; clear; intros; lia| revert NLx NL3 NL4 NL6; clear; intros; lia]
          | exact K ].
  Qed.
End S.
End V_Hawz4.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require LibIface Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Li4zm.V_Hawz4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition LL0 : LibLayout := mkLibLayout LayoutP0 0x18048 0x41830 img_ok0 0x30270 0x31580 img_ok0_intro 0x623c8.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HWSI : WS_Init_stmt.
  Hypothesis HVI : VEP_Init_stmt.
  Hypothesis HVP : VEP_Parse_stmt.
  Hypothesis HVF : VEP_Finish_stmt.
  Hypothesis HWR : WS_Rollback_stmt.

  Theorem lib_call_ok0 : lib_call_ok LL0.
  Proof.
    intros R m md A data inp T PRE K.
    destruct PRE as [A0 A1 TP RA4 SP16 SPLO SPHI MI ST [e ERR] [w1 [w2 BSS]] IMG [g GRD] LEN INP AINV [LBUD NBUD]].
    cbn [ll_alloc ll_entry ll_bss ll_img_ok ll_guard LL0] in A0, A1, TP, RA4, SP16, SPLO, SPHI, MI, ST, ERR, BSS, IMG, GRD, LEN, INP, AINV, K.
    change (al_errno LayoutP0) with 0x420b4 in ERR.
    rewrite <- (Z_to_bv_bv_unsigned w1), <- (Z_to_bv_bv_unsigned w2) in BSS.
    eapply (realizes_of_mkR rsegs R); [reflexivity .. |].
    rewrite mkst_MS.
    eapply (harness_cps HWSI HVI HVP HVF HWR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              m md A data inp e g (bv_unsigned w1) (bv_unsigned w2) T
              AINV MI A0 A1 TP RA4 SP16 SPLO SPHI ST ERR BSS IMG GRD LEN INP LBUD NBUD).
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF LIVE LBq NLq ST' IMG' CF.
    (* [comment removed for export] *)
    lazymatch type of RA4 with ?xr mod 4 = 0 =>
      assert (E2 : xr mod 2 = 0) by
        (pose proof (Z.div_mod xr 4 ltac:(lia)) as DM; rewrite RA4, Z.add_0_r in DM;
         rewrite DM; replace (4 * (xr / 4)) with ((2 * (xr / 4)) * 2) by lia; apply Z.mod_mul; lia)
    end.
    lazymatch goal with |- context [ret_pc ?xr] =>
      assert (RP : ret_pc xr = xr) by
        (rewrite <- (Z_to_bv_bv_unsigned xr) at 1; pose proof (bv_unsigned_in_range 64 xr) as RR;
         rewrite ret_pc_even; [apply Z_to_bv_bv_unsigned| unfold bv_modulus in RR; cbn in RR; lia| exact E2]);
      rewrite RP
    end.
    rewrite <- mkst_MS.
    apply (K (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0' t1' t2' (getr R 8) (getr R 9) (Z_to_bv 64 0)
                  a1' a2' a3' a4' a5' a6' a7' (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23)
                  (getr R 24) (getr R 25) (getr R 26) (getr R 27) t3' t4' t5' t6') m' md' A').
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV. unfold LIB_STACK in *.
    split; cbn [ll_alloc ll_entry ll_bss ll_img_ok ll_guard LL0].
    - intros r Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr.
    - reflexivity.
    - exact MDF.
    - exact AINV'.
    - (* [comment removed for export] *) exact (conj LBq NLq).
    - exact LIVE.
    - (* [comment removed for export] *)
      intros p n i LP Hi. (first [ dand3 CF as C1 _ _ | destruct CF as (C1 & _ & _) ]).
      (first [ pose proof ((live_geom LayoutP0 A m md p n AINV LP)) as dR_2; dand7 dR_2 as N0 _ PLO PHI PIMG MP NOW | destruct (live_geom LayoutP0 A m md p n AINV LP) as (N0 & _ & PLO & PHI & PIMG & MP & NOW) ]).
      unfold off_image in PIMG. cbn [al_image_lo al_image_hi LayoutP0] in PIMG.
      apply (C1 (p + i)); [lia| apply NOW; lia| left; apply MP; lia| lia| change (al_errno LayoutP0) with 0x420b4; lia| cbn beta; lia].
    - exact MI'.
    - exact ST'.
    - apply rw_errno_any.
    - apply rw_bss_any.
    - exact IMG'.
    - apply rw_guard_any.
    - exact CF.
  Qed.
End S.
