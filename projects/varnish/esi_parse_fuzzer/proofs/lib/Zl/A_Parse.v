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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.

Module A_Payh8.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma stA_range : forall s, 0 < stA s < 2^64.
  Proof. intros s; destruct s; cbn; lia. Qed.

  Lemma dispatch_ok : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model)
      (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md ->
    evt rsegs (fun ms' => ms' = disp_ms E x ra t1 t2 s1 a2 a3 a4 a5 a6 s6 s10 t3 t4 t5 t6 (aview A m))
        (head_ms E x ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 (aview A m)).
  Proof.
    intros until t6. intros PE PI AINV.
    world_open PE PI AINV.
    (* [comment removed for export] *)
    unfold head_ms, disp_ms; cbv zeta; unfold loop_ms, PC_HEAD, S9, T0; cbn [vi_st VIA]. rewrite EFP in *.
    pose proof (stA_range (x_st x)) as CR.
    assert (VPR : 0 <= x_v x Fver_p <= x_p x /\ x_p x < 2^64)
      by (try (generalize alloc_ceiling_val); clear - VERP PLE Dlo Dhi EE; intros; unfold pe_e, pe_N in *; lia).
    hide_neqs.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0.
    (* [comment removed for export] *)
    set (c := stA (x_st x)) in *.
    (* [comment removed for export] *)
    hot_qset.
    zstep. zstep. zstep. if_cases K; zify_cond K; try rewrite (Z.mod_small c 18446744073709551616 ltac:(clear - CR; lia)) in K.
    2:{ exfalso. clear - K CR. lia. }
    clear K.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 160) 8 0.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    2:{ exfalso. unsign K. clear - K VPR. lia. }
    clear K.
    (* [comment removed for export] *)
    clear - MI FR FRB CR c VEPlo VEPhi VEPB ACV.
    repeat (zstep;
      try (let K := fresh "K" in
           if_cases K; zify_cond K; try rewrite (Z.mod_small c 18446744073709551616 ltac:(clear - CR; lia)) in K;
           first
           [ lazymatch type of K with c = _ =>
               subst c; revert K; destruct (x_st x); intros K; cbn [stA] in K;
               first [ discriminate K
                     | clear K;
                       cbn [disp_pc disp_a1 disp_a2 disp_a6 disp_s1 disp_s6 disp_s10 disp_pos oreg vi_st VIA stA];
                       first [ finish | zstep; finish | fail 2 "dispatch: state mismatch at a handler entry (disp_* tables?)" ] ]
             end
           | lazymatch goal with
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x8b8dc) _ _ _ _) =>   (* [comment removed for export] *)
                 exfalso; subst c; destruct (x_st x); cbn [stA] in *;
                 match goal with H : ?a <> ?a |- _ => exact (H eq_refl) end
             | _ => idtac
             end ])).
    all: hot_qend.
  Qed.
End S.
End A_Payh8.


Module A_Pabq5.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Parse.A_Payh8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis HND : forall st, st <> S_MatchBuf -> handler_stmt st.

  (* [comment removed for export] *)
  Lemma latch_bounds : forall E x A m md,
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md ->
    0 <= x_p x <= pe_e E /\ pe_e E < 2^64.
  Proof.
    intros E x A m md PE PI AINV.
    pose proof (pi_pe _ _ _ _ PI) as PLE. pose proof (pi_verp _ _ _ _ PI) as VERP.
    (first [ pose proof ((pi_data _ _ _ _ PI)) as dR_1; dand3 dR_1 as LD _ _ | pose proof (pi_data _ _ _ _ PI) as (LD & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LD)) as dR_2; dand5 dR_2 as _ _ Dlo Dhi _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LD) as (_ & _ & Dlo & Dhi & _) ]).
    pose proof alloc_ceiling_num as ACV.
    unfold kHighMemBeg in Dlo. all_app_facts.
    unfold pe_e, pe_N in *. clear - PLE VERP Dlo Dhi ACV. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_ok : forall (n : nat) (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 : word),
    (Z.to_nat (phi E x) < n)%nat ->
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
    x_st x <> S_MatchBuf -> x_p x < pe_e E ->
    exit_K E T ->
    srealizes rsegs (mkCfg (head_ms E x ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    induction n as [|n IH]; intros until t6; intros PHI PE PI AINV MDF NMB PLT KX; [exfalso; lia|].
    (* [comment removed for export] *)
    unfold head_ms, loop_ms. ago AINV. fold_cl_segs.
    eapply evt_cut; [eapply (dispatch_ok E x A m md); eassumption|].
    intros ms' ->.
    cbv beta zeta delta [disp_ms loop_ms]. astop0 AINV. fold_cl_segs.
    (* [comment removed for export] *)
    lazymatch goal with AINVh : ainv A ?mh ?mdh |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mh _) ?mdh) _ =>
      apply (HND (x_st x) NMB E x A mh mdh T);
      [ exact PE | exact PI | exact AINVh | eapply amd_frame_sbm_r; [exact MDF | eassumption]
      | reflexivity | exact PLT | | exact KX ]
    end.
    (* [comment removed for export] *)
    unfold latch_K.
    intros x' A' m' md' ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' PI' AINV' MDF' DEC.
    pose proof (latch_bounds E x' A' m' md' PE PI' AINV') as (XP & EE).
    unfold latch_ms, loop_ms, PC_LATCH.
    ago AINV'. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      unsign K. destruct (DEC ltac:(clear - K XP EE; lia)) as [PHI' NMB'].
      astop0 AINV'. fold_cl_segs.
      change (Z_to_bv 64 0x8b730) with (Z_to_bv 64 PC_HEAD).
      lazymatch goal with AINVh : ainv A' ?mh ?mdh |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mh _) ?mdh) _ =>
        apply (IH E x' A' mh mdh T);
        [ pose proof (rank_bound E x) as RB; pose proof (rank_bound E x') as RB'; unfold phi in *; clear - PHI PHI' XP EE PLT RB RB'; lia
        | exact PE | exact PI' | exact AINVh | eapply amd_frame_sbm_r; [exact MDF' | eassumption]
        | exact NMB' | clear - K XP EE; lia | exact KX ]
      end.
    - (* [comment removed for export] *)
      unsign K. zstep. astop0 AINV'. fold_cl_segs.
      change (Z_to_bv 64 0x8d7f8) with (Z_to_bv 64 PC_EXIT).
      lazymatch goal with AINVh : ainv A' ?mh ?mdh |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mh _) ?mdh) _ =>
        apply (KX x' A' mh mdh);
        [ exact PI' | exact AINVh | eapply amd_frame_sbm_r; [exact MDF' | eassumption] | clear - K XP EE; lia ]
      end.
  Qed.
End S.
End A_Pabq5.


Module A_Pattc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold crc_post, CRC_STACK in H.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HCRC : crc32_stmt.

  (* [comment removed for export] *)
  Definition xcall_ms (E : penv) (pc p : Z) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (m : mem) :=
    let V := pe_VEP E in
    MS (mkR ra (Z_to_bv 64 (pe_fp E)) (pe_gp E) (cl_tp LPA) t0 t1 t2
            (Z_to_bv 64 V) s1 a0 a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 p) (Z_to_bv 64 (V + 64)) (Z_to_bv 64 2147450880) s5 s6
            (Z_to_bv 64 (pe_e E)) (Z_to_bv 64 (V + 208)) (S9 E) s10 s11 t3 t4 t5 t6)
       (pe_F E) (Z_to_bv 64 pc) (pe_fc E) None m (seg_rom rsegs).

  #[using="HMC"] Lemma mark_call_x : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ps p' mark ret : Z)
      (t0 t1 t2 s1 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
    x_p x <= p' -> p' <= pe_e E -> bool01 mark -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (x_st x = S_Attr \/ x_st x = S_Match -> p' = x_p x) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m2 : mem) (md1 : Model)
            (v1 : vep) (vv1 : vsb_rec) (x1 : pst),
        x1 = after_mark x p' v1 vv1 ->
        pinv E x1 A1 (aview A1 m2) -> ainv A1 m2 md1 -> amd_frame (pe_md0 E) md1 ->
        vkeep (x_v x) v1 MARK_FIELDS -> v1 Fver_p = p' -> v1 Flast_mark = mark -> v1 Fo_pending = 0 ->
        0 <= v1 Fcrc < 2^64 -> 0 <= v1 Fcrcp < 2^64 ->
        srealizes rsegs (mkCfg (xcall_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' s1 a0' a1' a2' a3' a4' a5' a6' a7' s5 s6 s10 s11 t3' t4' t5' t6' m2) md1) T) ->
    srealizes rsegs (mkCfg (xcall_ms E vep_mark_common_entry ps (Z_to_bv 64 ret) t0 t1 t2 s1
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p') (Z_to_bv 64 mark) a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV MDF0 LEP PLE' BM RR RET SAME K.
    pose proof PI as PI0. (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_1; dand4 dR_1 as OUT' WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT' & WBB & LEN0 & SZ0) ]). (first [ pose proof ((pinv_seccred _ _ _ _ PI)) as dR_2; dand3 dR_2 as SCB SCN SC15 | pose proof (pinv_seccred _ _ _ _ PI) as (SCB & SCN & SC15) ]). pose proof (pinv_primcred _ _ _ _ PI) as (PCB & PCD & PCR).   (* [comment removed for export] *)
    world_open PE PI AINV. unfold xcall_ms in K |- *. cbv zeta in K |- *. rewrite EFP in *.
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LDATA)) as dR_3; dand3 dR_3 as _ D16 _ | destruct (live_geomP LPA _ _ _ _ _ AINV LDATA) as (_ & D16 & _) ]).
    pose proof (vsb_extendsize_tight (vb_size (x_vv x) + 9)) as EXT.
    pose proof (world_nlive_nonneg (x_va x) (x_vio x)) as WNL.
    unfold PARSE_LIVE, pe_N in BUDL. unfold PARSE_NLIVE in BUDN.
    eapply (HMC (pe_VEP E) (x_v x) (x_tag x) (x_q x) (x_vv x) (pe_H E)
                p' mark (x_v x Fver_p - pe_DATA E) (pslice E (x_v x Fver_p) p') (pe_lo E));
      [ exact AINV | exact MI | reflexivity | reflexivity | reflexivity | exact BM
      | exact (pi_vep _ _ _ _ PI0)
      | exact BASE | exact HENV
      | exact B_lm | exact CNT | klia VERP | unfold NMAX; klia VERP PLE' EE NN
      | rewrite VSBF; exact VSBO | rewrite VSBF; exact NE1 | exact D_VB
      | unfold EXT_MAX; klia ROOM OUT' OA0 OI0 NN EE
      | klia LB BUDL WBB EXT NN EE SZ0 ROOM OUT' OA0 OI0
      | klia NL BUDN WNL
      | klia SC15
      | exact PCR (* [comment removed for export] *)
      | apply lib_frames_young; eapply frames_same_lib; [exact FRS| exact LIBF]
      | apply pslice_bytes; [exact DBY| klia VERP| klia VERP LEP| exact PLE']
      | apply pslice_length; [klia VERP| klia VERP LEP| exact PLE']
      | klia Dlo VERP
      | klia Dhi PLE' EE
      | exists (pe_DATA E), (Z.of_nat (length (pe_inp E))); split; [exact (as_live_shadow LPA _ _ _ _ _ AINV LDATA)|];
        split; [try (generalize alloc_ceiling_val); clear - D16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]; klia Dlo VERP PLE' EE Dhi LEP
      | right; exists (pe_DATA E), (Z.of_nat (length (pe_inp E))); split; [exact LDATA|];
        split; [klia NN|]; split; [klia VERP|]; split; [klia PLE' EE|]; split; [exact NE3|]; split; [rewrite VSBF; exact NE4| exact (not_eq_sym D_BD)]
      | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK
      | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite MARK_STACK_val; klia LOP
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1. cbv zeta.
    intros AINV1 MI1 MDF1 ST1 VO1 VK VERP1 LM1 OP1 CNT1 CRC1 CRCP1 VSO1 LEN1 SZ1 REL LIVE1 FA1 LB1 TC1 NL1 SCC1 PCC1 HENV1 DBY1 CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by (klia FRB). rewrite VSBF in VSO1, CF1. rewrite MARK_STACK_val in CF1.
    rewrite (ret_pc_even ret RR RET).
    assert (CV1 : vcover (pe_H E) A [pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         (fun a => blk (pe_VEP E) 312 a \/ newblk (vb_buf (x_vv x)) (vb_size (x_vv x)) a \/ (pe_S E <= a < pe_S E + 40))).
    { intros a [Ha|[Ha|Ha]].
      - eapply cover_blk; [exact LVEP| wz_not_in| exact Ha].
      - eapply cover_newblk; [exact LVB| wz_not_in| exact Ha].
      - eapply cover_rng; [exact LVS| wz_not_in| exact Ha]. }
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8800) by (klia LOP CEIL).
    assert (W0 : 0 <= 8800) by (clear; lia).
    assert (FR2 : rw_cells rsegs (aview A1 m2) (pe_sp E - 320) (pframe E j0 j8)).
    { eapply (pframe_call E A A1 m md _ _ _ _ _ _ j0 j8);
        [exact PE| exact AINV| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| exact CV1| unfold pframe; cbv zeta; exact FR]. }
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| exact (not_eq_sym D_BD)]. }
    assert (DATA1 : data_obj LPA A1 (aview A1 m2) (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| in_list| exact LDATA1| exact DATA]. }
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact WAL| exact D_WB]. }
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVEP| exact D_VB]. }
    assert (NB_V : pe_VEP E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact D_VB]).
    assert (NB_W : pe_wa E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact D_WB]).
    assert (NB_D : pe_DATA E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_BD)]).
    assert (SS1 : stack_shadow LPA (aview A1 m2) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
    { eapply (stack_shadow_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS]. }
    (* [comment removed for export] *)
    assert (VA2 : match x_va x with None => True | Some ya =>
                    vsb_obj LPA A1 (aview A1 m2) (x_v x Fattr_vsb) ya false /\ x_v x Fattr_vsb <> vb_buf vv1 /\ vb_buf ya <> vb_buf vv1 end).
    { destruct (x_va x) as [ya|] eqn:EQa; [| exact I]. (first [ dand5 VA as ANZ AO ASZ ALEN AAP | destruct VA as (ANZ & AO & ASZ & ALEN & AAP) ]).
      (first [ pose proof (AO) as dR_5; dand5 dR_5 as _ _ LAS LAB _ | pose proof AO as (_ & _ & LAS & LAB & _) ]).
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
      split; [| split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LAS| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LAB| exact N2]]].
      eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN);
        [ exact CV1 | in_list | in_list
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LAS| exact N1]
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LAB| exact N2]
        | exact AO ]. }
    assert (VI2 : match x_vi x with None => True | Some yi =>
                    vsb_obj LPA A1 (aview A1 m2) (x_v x Finclude_src) yi true /\ x_v x Finclude_src <> vb_buf vv1 /\ vb_buf yi <> vb_buf vv1 end).
    { destruct (x_vi x) as [yi|] eqn:EQi; [| exact I]. (first [ dand7 VI as INZ IO IE0 ISZ ILEN IAP IAP2 | destruct VI as (INZ & IO & IE0 & ISZ & ILEN & IAP & IAP2) ]).
      (first [ pose proof (IO) as dR_7; dand5 dR_7 as _ _ LIS LIB _ | pose proof IO as (_ & _ & LIS & LIB & _) ]).
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
      split; [| split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIS| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIB| exact N2]]].
      eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN);
        [ exact CV1 | in_list | in_list
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIS| exact N1]
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIB| exact N2]
        | exact IO ]. }
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVS)) as dR_8; dand4 dR_8 as _ _ Slo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LVS) as (_ & _ & Slo & _) ]). unfold kHighMemBeg in Slo. all_app_facts.
    pose proof (lib_frames_same A A1 2%nat 0%nat (frames_same_lib _ _ FRS LIBF) FA1) as FS1.
    assert (PI1 : pinv E (after_mark x p' v1 vv1) A1 (aview A1 m2)).
    { unfold after_mark. apply Build_pinv; psimp; vk_norm VK; psimp.
      - exact VO1.
      - unfold vep_base; vk_norm VK; unfold vep_base in BASE; exact BASE.
      - exact FLG. - exact VSBF. - exact STUP. - exact STATE.
      - rewrite VERP1. replace (p' - pe_DATA E) with (x_v x Fver_p - pe_DATA E + (p' - x_v x Fver_p)) by (clear; lia). exact CNT1.
      - rewrite VERP1. klia VERP LEP.
      - exact PLE'.
      - rewrite LM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | exact BM].
      - exact TAGI.
      - split; [exact DELIM1| exact DELIM2].
      - exact ESIC. - exact UNTL. - exact MTCH. - exact DOST. - exact ARMED. - exact ATTR. - exact ATTRST. - exact MATTR.
      - intros X Y Z. rewrite (SAME (or_introl X)) in Z |- *. unfold look in LOOKA |- *. cbn [x_p]. exact (LOOKA X Y Z).
      - intros X Y Z. rewrite (SAME (or_intror X)) in Z |- *. unfold look in LOOKM |- *. cbn [x_p]. exact (LOOKM X Y Z).
      - exact VSO1.
      - klia SZ1 ROOM LEN1.
      - revert OUT LEN1 LEP VERP. clear. cbv [oacost oicost x_va x_vi]. destruct (x_st x), (x_va x), (x_vi x); intros; lia.
      - intros y Hy. split; [apply (proj1 (APART y Hy))|].
        cbn in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D].
      - exact WAL1.
      - exact AVSB.
      - clear - VA VA2 LEP; try pose proof alloc_ceiling_val. destruct (x_va x) as [ya|]; [|exact VA].
        (first [ dand5 VA as Q1 _ Q3 Q4 Q5 | destruct VA as (Q1 & _ & Q3 & Q4 & Q5) ]). (first [ dand3 VA2 as R1 R2 R3 | destruct VA2 as (R1 & R2 & R3) ]).
        refine (conj Q1 (conj R1 (conj Q3 (conj _ _)))); [lia|].
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply Q5; cbn; auto 10.
        split; [exact R2| exact R3].
      - clear - VI VI2 LEP; try pose proof alloc_ceiling_val. destruct (x_vi x) as [yi|]; [|exact VI].
        (first [ dand7 VI as I1 _ I3 I4 I5 I6 I7 | destruct VI as (I1 & _ & I3 & I4 & I5 & I6 & I7) ]). (first [ dand3 VI2 as R1 R2 R3 | destruct VI2 as (R1 & R2 & R3) ]).
        refine (conj I1 (conj R1 (conj I3 (conj I4 (conj _ (conj _ I7)))))); [lia|].
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply I6; cbn; auto 10.
        split; [exact R2| exact R3].
      - exact DATA1.
      - exact HENV1.
      - rewrite EFP. exact ST1.
      - exists j0, j8. rewrite EFP. exact FR2.
      - exact MI1.
      - exact SS1.
      - revert LB LB1. clear. unfold world_bytes, x_vio. destruct (x_va x), (x_vi x); cbn [option_map]; intros; lia.
      - rewrite NL1. exact NL.
      - rewrite TC1. exact TC.
      - intros ff. rewrite (FS1 ff). apply FRS.
      - intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA.
        eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LA|].
        intros ->. destruct (NEW (vb_buf (x_vv x)) ltac:(unfold parse_blocks; left; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
      - intros p Hp. unfold parse_blocks in Hp. vk_norm_in VK Hp. destruct Hp as [Hp|Hp].
        + subst p. destruct REL as [EQ|[E1 E2]].
          * rewrite EQ. apply NEW. unfold parse_blocks. left. reflexivity.
          * destruct (Z.eq_dec (vb_buf vv1) (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
            destruct (a_live (pe_A0 E) (vb_buf vv1)) as [k|] eqn:EK; [| reflexivity].
            pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in E1. discriminate E1.
        + apply NEW. unfold parse_blocks. right. exact Hp.
      - eapply (cframe_step_call E x (after_mark x p' v1 vv1) A A1 _ _ (pe_sp E - 320) 8800);
          [ exact CF | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
          | eapply parse_window_mapped; [exact PE| rewrite EFP; exact ST1| rewrite EFP; exact FR2]
          | intros a [Ha|[Ha|Ha]]; unfold pzone, parse_changed, parse_new;
            [ left; left; exact Ha | right; left; exact Ha | left; right; left; split; [klia Slo| exact Ha] ]
          | intros a Ha; unfold after_mark in Ha; unfold parse_new in Ha; cbn [x_v x_vv x_va x_vi x_vio option_map] in Ha;
            vk_norm_in VK Ha; destruct Ha as [Ha|Ha]; [left; exact Ha| right; unfold pzone; right; unfold parse_new; right; exact Ha] ].
      - exact CR0.
      - klia WL LEP.
      - lazymatch goal with |- _ - (_ + _ + ?s' / 4096) <= _ <= _ =>
          lazymatch type of SC with _ - (_ + _ + ?s / 4096) <= _ <= _ =>
            assert (DV : s / 4096 <= s' / 4096) by (apply Z.div_le_mono; klia LEP) end end.
        revert SC SCC1 DV. clear. intros; lia.
      - exact PR0.
      - exact PPH.
      - (* [comment removed for export] *)
        eapply (pc_xfer _ _ _ _ _ _ _ _ PC PCC1). unfold after_mark. pc_unfold. cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi]. vk_norm VK. klia LEP. }
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m2 md1 v1 vv1 _ eq_refl PI1 AINV1 (amd_frame_trans _ _ _ MDF0 MDF1) VK VERP1 LM1 OP1 CRC1 CRCP1).
  Qed.

  (* [comment removed for export] *)
  Definition ret_ms (E : penv) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
    MS (mkR (pe_ra E) (Z_to_bv 64 (pe_sp E)) (pe_gp E) (cl_tp LPA) t0 t1 t2 (pe_s0 E) (pe_s1 E)
            a0 a1 a2 a3 a4 a5 a6 a7 (pe_s2 E) (pe_s3 E) (pe_s4 E) (pe_s5 E) (pe_s6 E) (pe_s7 E) (pe_s8 E) (pe_s9 E)
            (pe_s10 E) (pe_s11 E) t3 t4 t5 t6)
       (pe_F E) (ret_pc (pe_ra E)) (pe_fc E) None m (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition ret_K (E : penv) (T : TSet) : Prop :=
    forall (x2 : pst) (A2 : AS) (m2 : mem) (md2 : Model)
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E x2 A2 (aview A2 m2) -> ainv A2 m2 md2 -> amd_frame (pe_md0 E) md2 ->
      x_p x2 = pe_e E -> x_v x2 Fver_p = pe_e E ->
      stk rsegs (aview A2 m2) (pe_lo E) (pe_sp E) ->
      srealizes rsegs (mkCfg (ret_ms E t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2) md2) T.

  (* [comment removed for export] *)
  Lemma exit_tail : forall (E : penv) (T : TSet) (x1 : pst) (A1 : AS) (m1 : mem) (md1 : Model) (off : Z)
      (xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    penv_ok E -> ret_K E T ->
    pinv E x1 A1 (aview A1 m1) -> ainv A1 m1 md1 -> amd_frame (pe_md0 E) md1 ->
    x_p x1 = pe_e E -> x_v x1 Fver_p = pe_e E -> (off = 292 \/ off = 300) ->
    srealizes rsegs
      (mkCfg (MS (mkR xra (Z_to_bv 64 (pe_fp E)) (pe_gp E) (cl_tp LPA) xt0 xt1 xt2
                      (Z_to_bv 64 (pe_VEP E)) xs1 (Z_to_bv 64 off) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      xs2 xs3 (Z_to_bv 64 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                 (pe_F E) (Z_to_bv 64 0x8d854) (pe_fc E) None m1 (seg_rom rsegs)) md1) T.   (* [comment removed for export] *)
  Proof.
    intros until xt6. intros PE KR PI1 AINV1 MDF1 EP1 EV1 OFF. pose proof PI1 as PI10.
    world_open PE PI1 AINV1. rewrite EFP in *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m1)) as MU. pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m1) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    destruct OFF as [-> | ->].
    - (* [comment removed for export] *)
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      do 13 zstep. zstep. zstep.
      pose proof FR as FRc. pose proof STK as STKc. release_frame FRc STKc (pe_sp E).
      replace (pe_sp E - 320 + 320) with (pe_sp E) by (clear; lia).
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KR (PST (pe_e E) (x_st x1) (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) rewrite <- EP1. exact VERP.
        * (* [comment removed for export] *) split; [exact DELIM1| exact DELIM2].
        * (* [comment removed for export] *) intros _ _ X. exfalso. clear - X. lia.
        * (* [comment removed for export] *) intros _ _ X. exfalso. clear - X. lia.
        * (* [comment removed for export] *) revert OUT. rewrite EP1. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        * (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + reflexivity.
      + psimp. exact EV1.
      + exact STKc.
    - (* [comment removed for export] *)
      ago AINV1. fold_cl_segs.
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep.
      do 13 zstep. zstep. zstep.
      pose proof FR as FRc. pose proof STK as STKc. release_frame FRc STKc (pe_sp E).
      replace (pe_sp E - 320 + 320) with (pe_sp E) by (clear; lia).
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KR (PST (pe_e E) (x_st x1) (fupd (x_v x1) Fnm_pending (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_pending))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) rewrite <- EP1. exact VERP.
        * (* [comment removed for export] *) split; [exact DELIM1| exact DELIM2].
        * (* [comment removed for export] *) intros _ _ X. exfalso. clear - X. lia.
        * (* [comment removed for export] *) intros _ _ X. exfalso. clear - X. lia.
        * (* [comment removed for export] *) revert OUT. rewrite EP1. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        * (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + reflexivity.
      + psimp. exact EV1.
      + exact STKc.
  Qed.

  #[using="HCRC HMC"] Lemma parse_exit : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s5 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md -> x_p x = pe_e E ->
    ret_K E T ->
    srealizes rsegs (mkCfg (exit_ms E x ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s5 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF PEQ KR. pose proof PI as PI0.
    world_open PE PI AINV.
    unfold exit_ms, call_ms, PC_EXIT. cbv zeta. rewrite EFP in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_sp E - 320 - 128, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 320 - 128, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 320 - 128, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (R1 : 0 <= x_p x < 2^64) by (try (generalize alloc_ceiling_val); clear - VERP PLE Dlo Dhi EE; intros; unfold pe_e, pe_N in *; lia).
    assert (R2 : 0 <= x_v x Fver_p < 2^64) by (try (generalize alloc_ceiling_val); clear - VERP PLE Dlo Dhi EE; intros; unfold pe_e, pe_N in *; lia).
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_bound (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    assert (SHDD : shadowed LPA (aview A m) (pe_DATA E) (Z.of_nat (length (pe_inp E)))).
    { exists (pe_DATA E), (Z.of_nat (length (pe_inp E))). split; [exact SHD|].
      split; [try (generalize alloc_ceiling_val); clear - D16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|].
      clear - Dlo Dhi. lia. }
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 160) 8 0.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KP; zify_cond KP.
    - (* [comment removed for export] *)
      do 13 zstep. zstep. zstep.
      pose proof FR as FRc. pose proof STK as STKc. release_frame FRc STKc (pe_sp E).
      replace (pe_sp E - 320 + 320) with (pe_sp E) by (clear; lia).
      astop0 AINV. fold_cl_segs.
      eapply (KR x A _ _); [exact PI0 | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM] | exact PEQ | | exact STKc].
      clear - KP PEQ VERP R1 R2. lia.
    - (* [comment removed for export] *)
      assert (SKIP : forall (xa0 xa2 xa3 : word),
        evt rsegs (EvtAcct.srz_at_r rsegs (ahull A) (alhull A) (aeager A) m md T)
          (MS (mkR ra (Z_to_bv 64 (pe_sp E - 320)) (pe_gp E) (cl_tp LPA) (T0 E) t1 t2 (Z_to_bv 64 (pe_VEP E)) s1
                   xa0 (Z_to_bv 64 (x_v x Fver_p)) xa2 xa3 a4 a5 a6 (Z_to_bv 64 (pe_VEP E + 160))
                   (Z_to_bv 64 (x_p x)) (Z_to_bv 64 (pe_VEP E + 64)) (Z_to_bv 64 2147450880) s5 s6
                   (Z_to_bv 64 (pe_e E)) (Z_to_bv 64 (pe_VEP E + 208)) (S9 E) s10 s11
                   t3 t4 t5 t6)
              (pe_F E) (Z_to_bv 64 0x8d840) (pe_fc E) None (aview A m) (seg_rom rsegs))).
      { intros xa0 xa2 xa3.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        astop0 AINV.
        eapply (mark_call_x E x A _ _ T (x_p x) (x_p x) 1 0x8d850);   (* [comment removed for export] *)
          [ exact PE | exact PI0 | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
          | clear; lia | rewrite PEQ; clear; lia | right; reflexivity | clear; lia | reflexivity
          | intros _; reflexivity | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
        assert (EP1 : x_p x1 = pe_e E) by (rewrite EX1, <- PEQ; reflexivity).
        assert (EV1 : x_v x1 Fver_p = pe_e E) by (rewrite EX1, <- PEQ; cbn [x_v after_mark]; exact VERP1).
        clear - HMC HCRC PE KR PI1 AINV1 MDF1 EP1 EV1.
        unfold xcall_ms. cbv zeta.
        (* [comment removed for export] *)
        ago AINV1. fold_cl_segs. fix_ret_pc. zstep. astop0 AINV1.
        eapply (exit_tail E T x1 A1); [exact PE | exact KR | exact PI1 | assumption
          | eapply amd_frame_sbm_r; [exact MDF1 | eassumption] | exact EP1 | exact EV1 | left; reflexivity]. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      destruct B_ie as [IE|IE].
      + (* [comment removed for export] *)
        zstep. rewrite IE, (sx32_small 0) by (clear; lia). zstep. zstep. kdead.
        (* [comment removed for export] *)
        vchk SHV0 EzsV 4 0.
        destruct B_rm as [RM|RM].
        * (* [comment removed for export] *)
          zstep. rewrite RM, (sx32_small 0) by (clear; lia). zstep. kdead2.
          assert (LTP : x_v x Fver_p < x_p x) by (clear - KP VERP R1 R2; lia).
          (* [comment removed for export] *)
          zstep. kdead.
          zstep. zstep. if_cases KL0; zify_cond KL0.
          { exfalso. rewrite (proj2 (Z.ltb_lt 0 _)) in KL0 by lia. rewrite (proj2 (Z.ltb_lt _ _)) in KL0 by lia. discriminate KL0. }
          clear KL1 KL2.
          (* [comment removed for export] *)
          zstep. vchk SHV0 EzsV 4 0.
          zstep. zstep. rewrite (swrap32_small (x_p x - x_v x Fver_p)) by (clear - LTP R1 R2 NN PLE VERP EE; unfold pe_e, pe_N in *; lia). zstep.
          icall (crc32_buf HCRC (x_v x Fver_p) (pslice E (x_v x Fver_p) (x_p x)) (pe_lo E)) by
            (rewrite ?unsigned_lit by (clear - FRB LTP R1 R2; lia);
             lazymatch goal with
             | |- @eq (bv _) _ _ => reflexivity
             | |- _ mod _ = _ =>
                 rewrite (pslice_length E (x_v x Fver_p) (x_p x)) by (clear - VERP PLE LTP; unfold pe_e, pe_N in *; lia);
                 rewrite Z.mod_small by (clear - LTP NN PLE VERP EE; unfold pe_e, pe_N in *; lia); reflexivity
             | |- bytes_at _ _ _ _ => apply pslice_bytes; [exact DBY| clear - VERP; lia| clear - VERP; lia| exact PLE]
             | |- shadowed _ _ _ _ =>
                 rewrite (pslice_length E (x_v x Fver_p) (x_p x)) by (clear - VERP PLE LTP; unfold pe_e, pe_N in *; lia);
                 eapply shadowed_sub; [exact SHDD| clear - VERP; lia| clear - VERP PLE; unfold pe_e, pe_N in *; lia]
             | |- cenv _ => exact CE
             | |- stk _ _ _ _ => exact STK
             | |- mem_inv _ _ => exact MI
             | |- _ => unfold CRC_STACK; clear - LOP CEIL; lia
             end).
          lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
          (* [comment removed for export] *)
          vrechk SHV0 EzsV (pe_VEP E + 136) 4 0. zstep.
          (* [comment removed for export] *)
          zstep. vrechk SHV0 EzsV (pe_VEP E + 160) 8 0. zstep.
          (* [comment removed for export] *)
          zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep.
          zstep. if_cases KU; zify_cond KU.
          { exfalso. unfold vep_cnt in CNT. revert KU. clear - CNT VERP PLE NN LTP. intros KU.
            rewrite !Z.mod_small in KU by lia. revert KU. dead_b2z. }
          clear KU.
          vrechk SHV0 EzsV (pe_VEP E + 104) 8 0. zstep.
          (* [comment removed for export] *)
          zstep. zstep.
          astop AINV MU WM CFP. fold_cl_segs.
          lazymatch goal with VEPC : rw_cells _ (aview _ ?mx) (pe_VEP E) ?cs |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
            lazymatch cs with context [C4 ?w :: CB 4 (p140 _) :: _] =>
              rewrite <- (Z_to_bv_bv_unsigned w) in VEPC;
              eapply (exit_tail E T
                        (PST (x_p x) (x_st x)
                             (fupd (fupd (fupd (x_v x) Fcrcp (bv_unsigned w)) Fver_p (x_p x))
                                   Fo_pending (x_v x Fo_pending + (x_p x - x_v x Fver_p)))
                             (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _ 300)
            end end.
          -- exact PE.
          -- exact KR.
          -- apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
             ++ (* [comment removed for export] *) revert CNT VERP LTP. clear. unfold vep_cnt. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. intros; lia.
             ++ (* [comment removed for export] *) clear - VERP LTP. lia.
             ++ (* [comment removed for export] *) split; [exact DELIM1| exact DELIM2].
             ++ (* [comment removed for export] *) cf_stores CF MU PE0 STq FR. left; left. unfold blk. lia.
          -- assumption.
          -- eapply amd_frame_sbm_r; [exact MDF | exact SBM].
          -- psimp. exact PEQ.
          -- psimp. exact PEQ.
          -- right; reflexivity.
        * (* [comment removed for export] *)
          zstep. rewrite RM, (sx32_small 1) by (clear; lia). zstep. kdead. apply SKIP.
      + (* [comment removed for export] *)
        zstep. rewrite IE, (sx32_small 1) by (clear; lia). zstep. zstep. kdead2. apply SKIP.
  Qed.
End S.
End A_Pattc.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Parse.A_Payh8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Parse.A_Pabq5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Parse.A_Pattc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_peel : forall segs m A c cs,
  rw_cells segs m A (c :: cs) -> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs H. change (c :: cs) with ([c] ++ cs) in H.
  apply (proj1 (rw_cells_app segs m A [c] cs)) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  change (2 ^ (8 * Z.of_nat 8))%Z with 18446744073709551616%Z in H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
Qed.

(* [comment removed for export] *)
Lemma CB16_two_C8 : forall segs m a (junk : list byte) cs,
  rw_cells segs m a (CB 16 junk :: cs) ->
  exists j0 j8, rw_cells segs m a (C8 j0 :: C8 j8 :: cs).
Proof.
  intros segs m a junk cs RC.
  pose proof (rw_cells_peel _ _ _ _ _ RC) as [H1 _]. pose proof (rw_CB_length _ _ _ _ _ H1) as LEN.
  exists (le_bytes_to_word (firstn 8 junk)), (le_bytes_to_word (skipn 8 junk)).
  eapply rw_cells_recast; [exact RC| |].
  - cbn. destruct RC as [[WF _] _]. cbn in WF. tauto.
  - cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia).
    rewrite (app_assoc (firstn 8 junk)). rewrite (firstn_skipn 8 junk). reflexivity.
Qed.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HCRC : crc32_stmt.
  Hypothesis HND : forall st, st <> S_MatchBuf -> handler_stmt st.

  (* [comment removed for export] *)
  #[using="HND HCRC HMC"] Lemma parse_from_head : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
    x_st x <> S_MatchBuf -> x_p x < pe_e E ->
    ret_K E T ->
    srealizes rsegs (mkCfg (head_ms E x ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV MDF NMB PLT KR.
    eapply (loop_ok HND (S (Z.to_nat (phi E x)))); [lia| exact PE| exact PI| exact AINV| exact MDF| exact NMB| exact PLT|].
    intros x' A' m' md' ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s5' s6' s10' s11' t3' t4' t5' t6' PI' AINV' MDF' PEQ.
    eapply (parse_exit HMC HCRC E x' A' m' md' T); [exact PE| exact PI'| exact AINV'| exact MDF'| exact PEQ| exact KR].
  Qed.

  #[using="HND HCRC HMC"] Theorem VEP_Parse_ok : VEP_Parse_stmt.
  Proof.
    intros H VEP S b flags wa DATA inp tag q lo SB N. intros until T. cbv zeta.
    intros AINV MI Ha0 Ha1 Ha2 FL VEPO NS0 VSO WS1 DATA0 HENV NE_VS NE_Vb NE_wS NE_wb NE_DV NE_DS NE_Db NE_Dw
           LBM NLV SCC PCC LF TP SP16 SPHI STK CEIL LOP STKSH K.   (* [comment removed for export] *)
    set (E := PENV H VEP S b flags wa DATA inp lo (bv_unsigned sp) gp F fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A (aview A m) md SB N).
    (* [comment removed for export] *)
    pose proof (henv_geom_of_frame LPA A m md H AINV (proj1 HENV)) as HG.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE in G3. pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as LVEP VEPC TAG PADS | pose proof VEPO as (LVEP & VEPC & TAG & PADS) ]).
    (first [ pose proof (DATA0) as dR_3; dand3 dR_3 as LDATA DBY DLEN | pose proof DATA0 as (LDATA & DBY & DLEN) ]).
    pose proof VSO as VSOx. (first [ dand6 VSOx as VSC VINV LVS LVB SNB (bs0 & U8 & LBS & NUL0) | destruct VSOx as (VSC & VINV & LVS & LVB & SNB & (bs0 & U8 & LBS & NUL0)) ]).
    cbn [vb_buf vb_size vb_len vsb_fresh] in LVB, SNB, U8, LBS.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as wid wpad; dand7 WS1x as _ _ _ _ LWA _ _ | dand9 WS1x as wid wpad _ _ _ _ LWA _ _ | destruct WS1x as (wid & wpad & _ & _ & _ & _ & LWA & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVEP)) as dR_6; dand7 dR_6 as _ VEP16 VEPlo VEPhi VEPimg _ _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LDATA)) as dR_7; dand7 dR_7 as _ D16 Dlo Dhi Dimg _ _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LDATA) as (_ & D16 & Dlo & Dhi & Dimg & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVS)) as dR_8; dand7 dR_8 as _ S16 Slo Shi Simg _ _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LVS) as (_ & S16 & Slo & Shi & Simg & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVB)) as dR_9; dand7 dR_9 as _ _ Blo Bhi Bimg _ _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LVB) as (_ & _ & Blo & Bhi & Bimg & _ & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LWA)) as dR_10; dand7 dR_10 as _ _ Wlo Whi Wimg _ _ | pose proof (live_geomP LPA _ _ _ _ _ AINV LWA) as (_ & _ & Wlo & Whi & Wimg & _ & _) ]).
    assert (NE_Vw : VEP <> wa) by (intros X; rewrite X, LWA in LVEP; discriminate LVEP).
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVEP LVS NE_VS) as DJ_VS.
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVEP LVB NE_Vb) as DJ_VB.
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVEP LDATA (not_eq_sym NE_DV)) as DJ_VD.
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVEP LWA NE_Vw) as DJ_VW.
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVS LWA (not_eq_sym NE_wS)) as DJ_SW.
    pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVB LWA (not_eq_sym NE_wb)) as DJ_BW.
    (* [comment removed for export] *)
    pose proof (proj1 HENV) as HFR. pose proof HFR as [ageh HFh].
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVEP) as DJfV.
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LWA) as DJfW.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfW.
    unfold kHighMemBeg in VEPlo, Dlo, Slo, Blo, Wlo, G2. all_app_facts.
    pose proof (sh_bound (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) G3) as SHFB. rewrite SHMAX_val in SHFB. change ((8192 + 7) / 8) with 1024 in SHFB.
    assert (PE : penv_ok E).
    { unfold penv_ok; cbn [pe_H pe_flags pe_lo pe_VEP pe_S pe_wa pe_DATA pe_ra pe_inp pe_sp pe_A0 pe_N E].
      split; [exact HG|]. split; [exact FL|]. split; [unfold pe_N; cbn [pe_inp E]; unfold NMAX; clear - DLEN; lia|].
      split; [exact CEIL|]. split; [exact LOP|]. split; [exact SPHI|]. split; [exact SP16|].
      split; [exact NE_VS|]. split; [exact NE_wS|]. split; [exact NE_DV|]. split; [exact NE_DS|]. split; [exact NE_Dw|]. split; [exact NE_Vw|].
      split; [exact LBM|]. split; [exact NLV|]. split; [exact LF|]. split; [exact LVB| exact LVS]. }
    assert (EE : pe_e E = DATA + Z.of_nat (length inp)) by reflexivity.
    (* [comment removed for export] *)
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    rewrite Ha0, Ha1, Ha2, TP. rewrite TP in K.
    rewrite PARSE_STACK_val in LOP.
    unfold VEP_Parse_entry. unfold vep_cells in VEPC. cbn [vep_init_map] in VEPC.
    (* [comment removed for export] *)
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    pose proof (sh_bound (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ _ 312 AINV LVEP) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 320, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 320)) with 320 by lia;
                   eapply (stk_mapped (L:=LPA)); [exact STK | exact CEIL | lia | lia] |].
      split; [right; left; exists VEP, 312; split; [exact LVEP| lia]| exact I]. }
    hide U8. hide VSC. hide DBY.
    hide VEPimg. hide Dimg. hide Simg. hide Bimg. hide Wimg. hide DJ_VS. hide DJ_VB. hide DJ_VD. hide DJ_VW. hide DJ_SW. hide DJ_BW.
    hide DJfV. hide DJfS. hide DJfB. hide DJfW.
    hide_neqs.
    pose proof MI as MIw. pose proof STK as STw.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    carve_frame 320%nat STw.
    do 14 zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. unsign K0. clear - K0 VEPlo. lia. } clear K0.
    zstep. zstep.
    zstep. if_cases KU; zify_cond KU. 2:{ exfalso. apply KU. apply land7_of_mod8; [clear - VEPlo; lia| exact (mod8_of_mod16 VEP VEP16)]. } clear KU.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear. unfold VEP_MAGIC. vm_compute. congruence. } clear K0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. unsign K0. clear - K0 DLEN. lia. } clear K0.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0.
    zstep. rewrite (sx32_small 1) by (clear; lia). zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 208 ?j :: _) => set (junk208 := j) in FR; clearbody junk208 end.   (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mPRO end.   (* [comment removed for export] *)
    set (v0 := fupd (fupd (vep_init_map H VEP S flags) Fver_p LIT_empty) Flast_mark 1).
    pose proof (vsb_extendsize_tight (16 + 9)) as EXT.
    lazymatch goal with AINVq : ainv A ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
    eapply (HMC VEP v0 tag q (vsb_fresh b) H LIT_empty 0 0 [] lo);
      [ exact AINVq
      | exact MIw
      | reflexivity
      | unfold LIT_empty; cbn [vi_empty VIA]; reflexivity
      | reflexivity
      | left; reflexivity
      | split; [exact LVEP|]; split; [subst v0; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; unfold LIT_empty; cbn [vi_empty VIA]; exact VEPC
                             | split; [exact TAG| exact PADS]]
      | subst v0; unfold vep_base; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity
      | eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__;
        cbn [outside]; unhide DJfV; clear - Ha__ SHFB VEPlo VEPhi ACV G2 DJfV LOP CEIL SPR; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; right; reflexivity
      | subst v0; unfold vep_cnt; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; clear; lia
      | clear; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; unfold NMAX; clear; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map];
        eapply vsb_obj_munch; [exact VSO| exact MU| exact WM|];
        cbn [vb_buf vb_size vsb_fresh]; intros a__ Ha__; cbn [outside]; unhide DJ_VS; unhide DJ_VB; clear - Ha__ Shi Bhi Slo Blo DJ_VS DJ_VB ACV LOP CEIL SPR; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; unhide NE_VS; exact NE_VS
      | cbn [vb_buf vsb_fresh]; unhide NE_Vb; exact NE_Vb
      | cbn [vb_size vsb_fresh]; unfold EXT_MAX; clear; lia
      | cbn [vb_size vsb_fresh]; unfold PARSE_LIVE in LBM; clear - LBM EXT; lia
      | unfold PARSE_NLIVE in NLV; clear - NLV; lia
      | unfold PARSE_CRED in SCC; clear - SCC; pose proof (Z.div_pos (Z.of_nat (length inp)) 682); lia
      | revert PCC; clear; unfold PARSE_PRIM, PRIM_ROOM, PPOT_CAP, PVB_MAX; intros; lia (* [comment removed for export] *)
      | apply lib_frames_young; exact LF
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; apply bytes_at_nil; unfold LIT_empty; cbn [vi_empty VIA]; clear; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb length Z.of_nat]; clear; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; unfold LIT_empty; cbn [vi_empty VIA]; clear; lia
      | unfold LIT_empty; cbn [vi_empty VIA]; clear - ACV; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite Z.sub_diag;
        eapply shadowed_sub; [apply shadowed_empty; exact (consts_hold_ainv LPA A _ _ AINVq)| unfold LIT_empty; clear; lia| unfold LIT_empty; clear; lia]
      | left; subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; reflexivity
      | reflexivity
      | rewrite unsigned_lit by (clear - SPR LOP CEIL ACV; lia); replace (bv_unsigned sp + -320) with (bv_unsigned sp - 320) by (clear; lia);
        rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (clear - SPR LOP CEIL ACV; lia); exact STw
      | exact CEIL
      | rewrite unsigned_lit by (clear - SPR LOP CEIL ACV; lia); rewrite MARK_STACK_val; clear - LOP; lia
      | ]
    end.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1. cbv zeta.
    intros AINV1 MI2 MDF ST2 VO1 VK VERP1 LM1 OP1 CNT1 CRC1 CRCP1 VSO1 LEN1 SZ1 REL LIVE1 FA1 LB1 TC1 NL1 SCC1 PCC1 HENV1 DBY1 CF1.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite MARK_STACK_val in CF1. rewrite unsigned_lit in ST2, CF1 by (clear - SPR LOP CEIL ACV; lia).
    subst v0. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map vb_buf vb_size vb_len vsb_fresh] in VK, VERP1, LM1, OP1, CNT1, VSO1, LEN1, SZ1, REL, LIVE1, DBY1, CF1, SCC1, LB1.
    (first [ pose proof (VO1) as dR_11; dand4 dR_11 as LVEP1 VEPC1 _ _ | pose proof VO1 as (LVEP1 & VEPC1 & _ & _) ]).
    assert (LDATA1 : a_live A1 DATA = Some (Z.of_nat (length inp))) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| unhide NE_Db; exact NE_Db]).
    assert (LWA1 : a_live A1 wa = Some 40) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LWA| unhide NE_wb; exact NE_wb]).
    assert (NB_D : DATA <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| unhide NE_Db; exact NE_Db]).
    assert (NB_W : wa <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LWA| unhide NE_wb; exact NE_wb]).
    assert (NB_V : VEP <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| unhide NE_Vb; exact NE_Vb]).
    (first [ pose proof (VSO1) as dR_12; dand6 dR_12 as _ VINV1 LVS1 LVB1 SNB1 _ | pose proof VSO1 as (_ & VINV1 & LVS1 & LVB1 & SNB1 & _) ]).
    assert (CV1 : vcover H A [DATA; wa] (fun a => blk VEP 312 a \/ newblk b 16 a \/ (S <= a < S + 40))).
    { unhide NE_DV; unhide NE_Vw; unhide NE_Db; unhide NE_wb; unhide NE_DS; unhide NE_wS. intros a [Ha|[Ha|Ha]].
      - eapply cover_blk; [exact LVEP| cbn [In]; intros [X|[X|[]]]; [exact (NE_DV X)| exact (NE_Vw (eq_sym X))]| exact Ha].
      - eapply cover_newblk; [exact LVB| cbn [In]; intros [X|[X|[]]]; [exact (NE_Db X)| exact (NE_wb X)]| exact Ha].
      - eapply cover_rng; [exact LVS| cbn [In]; intros [X|[X|[]]]; [exact (NE_DS X)| exact (NE_wS X)]| exact Ha]. }
    assert (WIN1 : alloc_ceiling <= bv_unsigned sp + -320 - 8800) by (clear - LOP CEIL; lia).
    assert (W0 : 0 <= 8800) by (clear; lia).
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ (aview A ?mq) _ =>
      lazymatch goal with AINVq : ainv A mq ?mdq |- _ => pose proof AINVq as AINVc end end.
    assert (FR2 : rw_cells rsegs (aview A1 m2) (bv_unsigned sp + -320)
              [CB 208 junk208; C8 (Z_to_bv 64 (VEP + 160)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_call_stack H A A1 _ _ _ _ _ _ _ [DATA; wa] AINVc CF1 HFR WIN1 W0); [exact CV1| exact FR| clear; lia| cbn; clear - SPR; lia]. }
    assert (DATA2 : data_obj LPA A1 (aview A1 m2) DATA inp).
    { eapply (data_obj_call H A A1 _ _ _ _ _ _ _ [DATA; wa] AINVc CF1 HFR WIN1); [exact CV1| cbn; left; reflexivity| exact LDATA1|].
      split; [exact LDATA|]. split; [| exact DLEN]. unhide DBY.
      eapply (bytes_at_munch LPA); [exact DBY| exact MU|]. intros a__ Ha__. cbn [outside]. unhide DJ_VD. clear - Ha__ Dhi Dlo DJ_VD ACV DLEN LOP CEIL SPR. lia. }
    assert (SS2 : stack_shadow LPA (aview A1 m2) SB N (bv_unsigned sp - PARSE_STACK - 64) (bv_unsigned sp + 64)).
    { eapply (stack_shadow_call H A A1 _ _ _ _ _ _ _ [DATA; wa] AINVc CF1 HFR WIN1); [exact CV1| rewrite PARSE_STACK_val; clear - LOP CEIL ACV; lia|].
      (first [ dand6 STKSH as B_ N0_ Lq_ Hh_ SLO_ T_ | destruct STKSH as (B_ & N0_ & Lq_ & Hh_ & SLO_ & T_) ]). split; [| exact (conj N0_ (conj Lq_ (conj Hh_ (conj SLO_ T_))))].
      eapply (bytes_at_munch LPA); [exact B_| exact MU|]. rewrite repeat_length, Z2Nat.id by (clear - N0_; lia).
      intros a__ Ha__. cbn [outside]. unfold kHighMemBeg in T_. clear - Ha__ T_ VEPlo LOP CEIL ACV SPR. lia. }
    assert (WS1_2 : ws1_obj LPA H A1 (aview A1 m2) wa VEP).
    { eapply (ws1_obj_ccall LPA H A A1 _ _ _ _ _ _ _ wa VEP AINVc HFR CF1); [ | exact WIN1 | exact LWA1| exact LVEP1| ].
      - eapply ws1_obj_munch; [exact WS1| exact MU| exact WM|]. intros a__ Ha__. unfold h_ws, h_wsbuf in Ha__. cbn [outside].
        unhide DJ_VW; unhide DJfV. clear - Ha__ VEPhi VEPlo Whi Wlo G2 ACV DJ_VW DJfV LOP CEIL SPR. lia.
      - unhide DJ_VW; unhide DJ_BW; unhide DJ_SW; unhide DJfV; unhide DJfB; unhide DJfS.
        intros a__ Ha__ [X|[X|X]]; unfold newblk, blk in X; try (change ((16 + 7) / 8) with 2 in X); unfold h_ws, h_wsbuf in Ha__;
        clear - Ha__ X VEPhi VEPlo Bhi Blo Blo_l Shi Slo Whi Wlo G2 ACV DJ_VW DJ_BW DJ_SW DJfV DJfB DJfS; lia. }
    (* [comment removed for export] *)
    rename FR into FRm1. hide FRm1. clear CV1.
    pose proof (as_live_shadow LPA _ _ _ _ 312 AINV1 LVEP1) as SHV1. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
    assert (MAP2 : mapped (aview A1 m2) (bv_unsigned sp - 320) 320).
    { eapply (window_mapped LPA _ lo (bv_unsigned sp + -320) (bv_unsigned sp) 320);
        [exact ST2| exact FR2| cbn; clear; lia| exact CEIL| clear - LOP; lia| clear; lia]. }
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (VEP, VEP + 312)] (aview A1 m2)) as MU2.
    pose proof (wmono_refl rsegs (aview A1 m2)) as WM2.
    assert (CFP2 : client_fp LPA A1 (aview A1 m2) [(bv_unsigned sp - 320, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [clear - LOP CEIL ACV; lia|]; split; [clear - SPR; lia|];
                   replace (bv_unsigned sp - (bv_unsigned sp - 320)) with 320 by (clear; lia); exact MAP2 |].
      split; [right; left; exists VEP, 312; split; [exact LVEP1| clear; lia]| exact I]. }
    unfold vep_cells in VEPC1. vk_norm_in VK VEPC1. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map] in VEPC1.
    rewrite VERP1, LM1, OP1 in VEPC1. fold_cl_segs.
    hide REL. hide SZ1. hide LIVE1. hide DBY1.
    pose proof MI2 as MIv. pose proof ST2 as ST2c. hide ST2c. pose proof FR2 as FR2c. hide FR2c.
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    vrechk SHV1 EzsV (VEP + 72) 4 0. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV1 EzsV 8 0. zstep. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    vrechk SHV1 EzsV (VEP + 152) 8 0. zstep.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (shr3_div8 (VEP + 160)). vrechk SHV1 EzsV (VEP + 160) 8 0.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KU; zify_cond KU. 2:{ exfalso. unsign KU. clear - KU Dlo Dhi DLEN ACV. lia. } clear KU.
    zstep. if_cases KU; zify_cond KU. 2:{ exfalso. unsign KU. clear - KU Dlo Dhi DLEN ACV. lia. } clear KU.
    zstep. if_cases KU; zify_cond KU. 2:{ exfalso. unsign KU. clear - KU Dlo Dhi DLEN ACV. lia. } clear KU.
    (* [comment removed for export] *)
    do 53 zstep.
    rewrite ?(shr3_div8 (VEP + 64)).
    (* [comment removed for export] *)
    astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ => rename mx into m3; rename mdx into md3 end.
    lazymatch goal with X : ainv A1 m3 md3 |- _ => rename X into AINV3 end.
    (first [ pose proof ((CB16_two_C8 _ _ _ _ _ FR2)) as dR_14; dex2 dR_14 as j0 j8; rename dR_14 into FR3 | pose proof ((CB16_two_C8 _ _ _ _ _ FR2)) as dR_14; dand3 dR_14 as j0 j8 FR3 | destruct (CB16_two_C8 _ _ _ _ _ FR2) as (j0 & j8 & FR3) ]). clear FR2.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    lazymatch goal with S1 : same_but_materialized md ?mda, AF : amd_frame ?mda' md1, S2 : same_but_materialized md1 ?mdb |- _ =>
      assert (MDF2 : amd_frame md mdb) by (eapply (amd_frame_sbm_l _ _ _ S1 MH); eapply amd_frame_sbm_r; [exact AF| exact S2]) end.
    assert (HENV3 : henv_ok LPA VIA H A1 (aview A1 m3));
    [ eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
      intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__;
      cbn [outside]; unhide DJfV; clear - Ha__ SHFB VEPlo VEPhi ACV G2 DJfV LOP CEIL SPR; lia |];
    assert (VSO3 : vsb_obj LPA A1 (aview A1 m3) S vv1 false);
    [ (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV1 LVS1)) as dR_15; dand5 dR_15 as _ _ Slo1 Shi1 _ | pose proof (live_geomP LPA _ _ _ _ _ AINV1 LVS1) as (_ & _ & Slo1 & Shi1 & _) ]);
      (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV1 LVB1)) as dR_16; dand5 dR_16 as _ _ Blo1 Bhi1 _ | pose proof (live_geomP LPA _ _ _ _ _ AINV1 LVB1) as (_ & _ & Blo1 & Bhi1 & _) ]);
      pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV1 LVEP1 LVS1 ltac:(unhide NE_VS; exact NE_VS)) as DJ1;
      pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV1 LVEP1 LVB1 NB_V) as DJ2;
      unfold kHighMemBeg in Slo1, Blo1; all_app_facts;
      eapply vsb_obj_munch; [exact VSO1| exact MU2| exact WM2|]; intros a__ Ha__; cbn [outside]; clear - Ha__ Shi1 Slo1 Bhi1 Blo1 DJ1 DJ2 ACV LOP CEIL SPR; lia |];
    assert (DATA3 : data_obj LPA A1 (aview A1 m3) DATA inp);
    [ (first [ dand3 DATA2 as LD2 DBY2 _ | destruct DATA2 as (LD2 & DBY2 & _) ]); split; [exact LD2|]; split; [| exact DLEN];
      pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV1 LVEP1 LDATA1 ltac:(unhide NE_DV; exact (not_eq_sym NE_DV))) as DJ3;
      eapply (bytes_at_munch LPA); [exact DBY2| exact MU2|]; intros a__ Ha__; cbn [outside]; clear - Ha__ Dhi Dlo DJ3 ACV DLEN LOP CEIL SPR; lia |];
    assert (SS3 : stack_shadow LPA (aview A1 m3) SB N (bv_unsigned sp - PARSE_STACK - 64) (bv_unsigned sp + 64));
    [ (first [ dand6 SS2 as B_ N0_ Lq_ Hh_ SLO_ T_ | destruct SS2 as (B_ & N0_ & Lq_ & Hh_ & SLO_ & T_) ]); split; [| exact (conj N0_ (conj Lq_ (conj Hh_ (conj SLO_ T_))))];
      eapply (bytes_at_munch LPA); [exact B_| exact MU2|]; rewrite repeat_length, Z2Nat.id by (clear - N0_; lia);
      intros a__ Ha__; cbn [outside]; unfold kHighMemBeg in T_; clear - Ha__ T_ VEPlo LOP CEIL ACV SPR; lia |];
    assert (WS1_3 : ws1_obj LPA H A1 (aview A1 m3) wa VEP);
    [ (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV1 LWA1)) as dR_19; dand5 dR_19 as _ _ Wlo1 Whi1 _ | pose proof (live_geomP LPA _ _ _ _ _ AINV1 LWA1) as (_ & _ & Wlo1 & Whi1 & _) ]);
      pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV1 LVEP1 LWA1 ltac:(unhide NE_Vw; exact NE_Vw)) as DJW1;
      unfold kHighMemBeg in Wlo1; all_app_facts;
      eapply ws1_obj_munch; [exact WS1_2| exact MU2| exact WM2|]; intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn [outside];
      unhide DJfV; clear - Ha__ VEPhi VEPlo Whi1 Wlo1 G2 ACV DJW1 DJfV LOP CEIL SPR; lia |];
    assert (MAP3 : mapped (aview A1 m3) (bv_unsigned sp - PARSE_STACK) PARSE_STACK);
    [ rewrite PARSE_STACK_val; eapply (window_mapped LPA _ lo (bv_unsigned sp + -320) (bv_unsigned sp) 9120);
      [exact ST2| exact FR3| cbn; clear; lia| exact CEIL| clear - LOP; lia| clear; lia] |].
    set (v2 := fupd (fupd (fupd v1 Fstartup 0) Fhack_p DATA) Fver_p DATA).
    set (x0 := PST DATA S_Start v2 tag q vv1 None None).
    pose proof CNT1 as CNT1'. unfold vep_cnt, LIT_empty in CNT1'.
    assert (PI0 : pinv E x0 A1 (aview A1 m3)).
    { subst x0 v2. apply Build_pinv; cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp pe_sp pe_A0 pe_v0 pe_md0 pe_SB pe_NS pe_b E];
        unfold va_world, vi_world, in_tag_cluster, attr_states, avsb_states, oacost, oicost, walen, wilen, wpot, x_vio;
        cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp pe_sp pe_A0 pe_v0 pe_md0 pe_SB pe_NS pe_b E option_map].
      all: try (vk_norm VK; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]).
      - split; [exact LVEP1|]. split; [| split; [exact TAG| exact PADS]].
        unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. vk_norm VK. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map].
        rewrite ?LM1, ?OP1. exact VEPC1.
      - unfold vep_base; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. vk_norm VK. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold vep_cnt; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. clear - CNT1' OP1. lia.
      - clear; lia.
      - unfold pe_e, pe_N; cbn [pe_DATA pe_inp E]. clear - DLEN; lia.
      - rewrite LM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; left; reflexivity.
      - clear; lia.
      - split; [intros _; reflexivity| intros X; discriminate X].
      - left; split; reflexivity.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - left; reflexivity.
      - intros X; destruct X.
      - left; reflexivity.
      - intros X; destruct X.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - exact VSO3.
      - unhide SZ1. clear - SZ1 LEN1. lia.
      - clear - LEN1. lia.
      - unhide NE_VS; unhide NE_wS; unhide NE_DS. intros y Hy. destruct Hy as [<-|[<-|[<-|[]]]]; split.
        + exact (not_eq_sym NE_VS). + exact (not_eq_sym NB_V).
        + exact (not_eq_sym NE_wS). + exact (not_eq_sym NB_W).
        + exact (not_eq_sym NE_DS). + exact (not_eq_sym NB_D).
      - exact LWA1.
      - intros X; apply X; reflexivity.
      - reflexivity.
      - reflexivity.
      - exact DATA3.
      - exact HENV3.
      - unfold pe_fp, PARSE_FRAME; cbn [pe_sp E]. replace (bv_unsigned sp - 320) with (bv_unsigned sp + -320) by (clear; lia). exact ST2.
      - exists j0, j8. unfold pframe, pe_fp, PARSE_FRAME; cbn [pe_VEP pe_sp pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pe_ra E].
        replace (bv_unsigned sp - 320) with (bv_unsigned sp + -320) by (clear; lia).
        rewrite (zb_lxor_ones (VEP + 256)) in FR3 by (clear - VEPlo VEPhi ACV; lia).   (* [comment removed for export] *)
        exact FR3.
      - assumption.
      - exact SS3.
      - unfold world_bytes. clear - LB1. lia.
      - unfold world_nlive. clear - NL1. lia.
      - exact TC1.
      - eapply lib_frames_same; [exact LF| exact FA1].
      - intros p k Hp Nb. unhide LIVE1; unhide REL. eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact Hp| exact Nb].
      - intros p Hp. unfold parse_blocks in Hp. destruct Hp as [->|[[]|[]]]. unhide REL. destruct REL as [EB|[F1 _]]; [left; exact EB| right; exact F1].
      - (* [comment removed for export] *)
        unhide FRm1. unhide ST2c.
        assert (MAP1 : mapped (aview A mPRO) (bv_unsigned sp - PARSE_STACK) PARSE_STACK).
        { rewrite PARSE_STACK_val. eapply (window_mapped LPA _ lo (bv_unsigned sp + -320) (bv_unsigned sp) 9120);
            [exact STw| exact FRm1| cbn; clear; lia| exact CEIL| clear - LOP; lia| clear; lia]. }
        assert (MAP2' : mapped (aview A1 m2) (bv_unsigned sp - PARSE_STACK) PARSE_STACK).
        { rewrite PARSE_STACK_val. eapply (window_mapped LPA _ lo (bv_unsigned sp + -320) (bv_unsigned sp) 9120);
            [exact ST2c| exact FR2c| cbn; clear; lia| exact CEIL| clear - LOP; lia| clear; lia]. }
        assert (C_a : cframe LPA (owned A) (owned A) (bv_unsigned sp) PARSE_STACK (parse_changed H VEP S b) nowhere (aview A m) (aview A mPRO)).
        { eapply (cframe_stores LPA _ _ _ _ (aview A m) (aview A mPRO)); [exact MU| | exact MAP1].
          intros a Ha NO. cbn [outside] in NO. unfold parse_changed, blk.
          destruct (Classical_Prop.classic (bv_unsigned sp + -320 <= a < bv_unsigned sp)) as [X|X]; [left; rewrite PARSE_STACK_val; clear - X; lia|].
          right; left. clear - Ha NO X VEPlo. lia. }
        assert (C_b : cframe LPA (owned A) (owned A1) (bv_unsigned sp) PARSE_STACK
                        (fun a => blk VEP 312 a \/ newblk b 16 a \/ S <= a < S + 40) (newblk (vb_buf vv1) (vb_size vv1)) (aview A mPRO) (aview A1 m2)).
        { eapply (cframe_reframe LPA); [exact CF1| rewrite PARSE_STACK_val; clear; lia| clear; lia| exact MAP2']. }
        assert (C_ab : cframe LPA (owned A) (owned A1) (bv_unsigned sp) PARSE_STACK (parse_changed H VEP S b) (newblk (vb_buf vv1) (vb_size vv1)) (aview A m) (aview A1 m2)).
        { eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A mPRO) (aview A1 m2) C_a C_b); [apply Z.le_refl| apply Z.le_refl| exact MAP2'| intros a X; exact X| |].
          - unhide NS0. intros a [X|[X|X]]; right; unfold parse_changed; [left; exact X| right; right; left; exact X| right; left; split; [exact NS0| exact X]].
          - intros a X; right; left; exact X. }
        assert (C_c : cframe LPA (owned A1) (owned A1) (bv_unsigned sp) PARSE_STACK (parse_changed H VEP S b) nowhere (aview A1 m2) (aview A1 m3)).
        { eapply (cframe_stores LPA _ _ _ _ (aview A1 m2) (aview A1 m3)); [exact MU2| | exact MAP3].
          intros a Ha NO. cbn [outside] in NO. unfold parse_changed, blk.
          destruct (Classical_Prop.classic (bv_unsigned sp - 320 <= a < bv_unsigned sp)) as [X|X]; [left; rewrite PARSE_STACK_val; clear - X; lia|].
          right; left. clear - Ha NO X VEPlo. lia. }
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 m2) (aview A1 m3) C_ab C_c);
          [apply Z.le_refl| apply Z.le_refl| exact MAP3| intros a X; exact X| intros a X; right; exact X| ].
        intros a X. unfold parse_new in X. cbn [option_map] in X. destruct X as [X|[[]|[]]]. left. exact X.
      - exact SCC.
      - clear; lia.
      - unfold vsb_pot in SCC1 |- *. cbn [vb_size vsb_fresh] in SCC1. clear - SCC1. lia.
      - exact PCC.
      - split; exact I.
      - (* [comment removed for export] *)
        unfold pcharge, pbank, ptag, pbva, pbvi, phead, in_incl_tag, wppot, walen, wilen.
        cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb pe_DATA pe_A0 E negb Z.eqb].
        rewrite vsb_ppot_fresh in PCC1. clear - PCC1. lia. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 (bv_unsigned sp + -320)) with (Z_to_bv 64 (pe_fp E)).
    change (Z_to_bv 64 (DATA + Z.of_nat (length inp))) with (Z_to_bv 64 (pe_e E)).
    change (Z_to_bv 64 0x8b730) with (Z_to_bv 64 PC_HEAD).
    eapply (parse_from_head E x0 A1 m3 md3 T);
      [ exact PE| exact PI0| exact AINV3| exact MDF2| subst x0; cbn [x_st]; discriminate
      | subst x0; unfold pe_e, pe_N; cbn [x_p pe_DATA pe_inp E]; clear - DLEN; lia|].
    (* [comment removed for export] *)
    unfold ret_K. intros x2 A2 m4 md4 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 PI2 AINV4 MDF4 PEQ2 VEQ2 STK4.
    unfold ret_ms. cbn [pe_ra pe_sp pe_gp pe_F pe_fc pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 E].
    rewrite (Z_to_bv_bv_unsigned sp).
    unfold pe_e, pe_N in PEQ2, VEQ2. cbn [pe_DATA pe_inp pe_lo pe_H pe_md0 E] in PEQ2, VEQ2, STK4, MDF4.
    pose proof (ocosts_nonneg _ _ _ _ PI2) as [OA2 OI2].
    (first [ pose proof ((pinv_seccred _ _ _ _ PI2)) as dR_20; dand3 dR_20 as _ SCX _ | pose proof (pinv_seccred _ _ _ _ PI2) as (_ & SCX & _) ]). unfold pe_N in SCX. cbn [pe_A0 pe_inp E] in SCX. pose proof (pinv_primcred _ _ _ _ PI2) as (PCX & _ & _). unfold pe_N in PCX. cbn [pe_A0 pe_inp E] in PCX.   (* [comment removed for export] *)
    pose proof PI2 as PI2c.
    destruct PI2c as [VEPO2 BASE2 FLG2 VSBF2 STUP2 STATE2 CNT2 VERP2 PLE2 B012 TAGI2 DELIM2 ESIC2 UNTL2 MTCH2 DOST2 ARMED2 ATTR2 ATTRST2
                      MATTR2 LOOKA2 LOOKM2 VSBO2 ROOM2 OUT2 APART2 WAL2 AVSB2 VA2 VI2 DATA4 HENV4 STK4' FRAME4 MI4 SS4 LB4 NL4 TC4 FR4 KEEP4 NEW4 CF4 CR04 WL4 SC4 PR04 PPH4 PC4].   (* [comment removed for export] *)
    cbn [pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp pe_sp pe_A0 pe_v0 pe_md0 pe_SB pe_NS pe_b E] in VEPO2, BASE2, FLG2, VSBF2, CNT2, VERP2, PLE2, VSBO2, OUT2, APART2, WAL2, VA2, VI2, DATA4, HENV4, SS4, LB4, NL4, TC4, FR4, KEEP4, NEW4, CF4, SC4.
    unfold va_world in VA2. unfold vi_world in VI2. cbn [pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp E] in VA2, VI2.
    unfold pe_e, pe_N in VA2, VI2. cbn [pe_DATA pe_inp E] in VA2, VI2.
    rewrite VEQ2 in CNT2. replace (DATA + Z.of_nat (length inp) - DATA) with (Z.of_nat (length inp)) in CNT2 by (clear; lia).
    assert (LVV : 0 <= vb_len (x_vv x2)) by ((first [ dand3 VSBO2 as _ VIx _ | destruct VSBO2 as (_ & VIx & _) ]); unfold vsb_inv in VIx; clear - VIx; lia).
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 A2 m4 md4 (x_v x2) (x_tag x2) (x_q x2) (x_vv x2) (x_va x2) (x_vio x2) (Z.of_nat (length inp))).
    - exact AINV4.
    - exact MI4.
    - exact MDF4.
    - exact STK4.
    - exact HENV4.
    - (* [comment removed for export] *)
      unfold parsed_world. pose proof CNT2 as CNT2'. unfold vep_cnt in CNT2'.
      split; [exact VEPO2|]. split; [exact BASE2|]. split; [exists (x_st x2); exact STATE2|].
      split; [exact (proj1 B012)|]. split; [exact (proj1 (proj2 B012))|].
      split; [exact CNT2|]. split; [clear - DLEN; lia|]. split; [unfold NMAX; clear - DLEN; lia|].
      split; [rewrite VEQ2; clear - Dlo Dhi DLEN; lia|].
      split; [rewrite VSBF2; exact VSBO2|].
      split; [split; [exact ROOM2| revert OUT2 OA2 OI2 CNT2' PEQ2; clear; intros; destruct (x_st x2); lia]|].
      split; [rewrite VSBF2; intros y Hy; apply APART2; revert Hy; clear; cbn [In]; tauto|].
      split.
      + destruct (x_va x2) as [ya|] eqn:EVA; [|exact VA2]. (first [ dand5 VA2 as ANZ AO ASZ ALEN AAP | destruct VA2 as (ANZ & AO & ASZ & ALEN & AAP) ]).
        split; [exact AO|]. split; [unfold EXT_MAX; clear - ASZ ALEN DLEN PEQ2; lia|].
        split; [split; [exact ASZ| clear - ALEN PEQ2; lia]|].
        rewrite VSBF2. intros y Hy; apply AAP; revert Hy; clear; cbn [In]; tauto.
      + unfold x_vio. destruct (x_vi x2) as [yi|] eqn:EVI; cbn [option_map]; [|exact VI2]. (first [ dand7 VI2 as INZ IO IERR ISZ ILEN IAP IAP2 | destruct VI2 as (INZ & IO & IERR & ISZ & ILEN & IAP & IAP2) ]).
        split; [exact IO|]. split; [split; [exact ISZ| clear - ILEN PEQ2; lia]|].
        split; [rewrite VSBF2; intros y Hy; apply IAP; revert Hy; clear; cbn [In]; tauto|].
        destruct (x_va x2) as [ya|]; [exact IAP2| exact I].
    - exact VSBF2.
    - rewrite VEQ2. clear - DLEN; lia.
    - (* [comment removed for export] *)
      eapply (ws1_obj_ccall LPA H A A2 m md _ _ _ _ _ wa VEP AINV HFR CF4);
        [exact WS1| rewrite PARSE_STACK_val; clear - LOP CEIL; lia| exact WAL2| exact (proj1 VEPO2)|].
      unhide DJ_VW; unhide DJ_BW; unhide DJ_SW; unhide DJfV; unhide DJfB; unhide DJfS; unhide DJfW.
      intros a__ Ha__ X; unfold parse_changed, newblk, blk, h_vsc in X; try (change ((16 + 7) / 8) with 2 in X); unfold h_ws, h_wsbuf in Ha__.
      clear - Ha__ X VEPhi VEPlo Bhi Blo Blo_l Shi Slo Whi Wlo G2 ACV DJ_VW DJ_BW DJ_SW DJfV DJfB DJfS DJfW; lia.
    - exact DATA4.
    - exact KEEP4.
    - exact NEW4.
    - exact FR4.
    - exact LB4.
    - exact TC4.
    - exact NL4.
    - unfold PARSE_CRED. clear - SCX SC4. pose proof (Z.div_pos (Z.of_nat (length inp)) 682). lia.
    - exact PCX.   (* [comment removed for export] *)
    - exact CF4.
  Qed.
End S.
