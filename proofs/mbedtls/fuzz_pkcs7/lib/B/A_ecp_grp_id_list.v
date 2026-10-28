(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ecp_grp_id_list.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_ecp_grp_id_list () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_ids_state"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_grp_id_list_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition A_ECP_GRP_ID_LIST : Z := 0xcad68.   (* [comment removed for export] *)
Definition A_ECP_IDS_DONE : Z := 0x63c0a0.     (* [comment removed for export] *)  (* [comment removed for export] *)
Definition A_ECP_IDS : Z := 0x63c0c0.          (* [comment removed for export] *)  (* [comment removed for export] *)

Definition ecp_grp_id_list_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY IDONE IDS : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_grp_id_list ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))P,(4.O5.O2.O1.R1.)P,(5.O5.R2.)P,(6.$0.(7.(8.&40.R24.)+2.)=)P,(9.O4.)P,(:.O4.R27.)(;.O5.O4.R28.(<.O5.O2.O1.R27.R26.R25.R24.R21.R20.R1?.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)(=.(>.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R8.(?.&40.O3.)R7.(10.(1.&40.))R6.(11.O5.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Ltac finishA :=
    apply evtA_done; unfold ecp_grp_id_list_post;
    repeat (lazymatch goal with |- ex _ => eexists end);
    split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end; try assumption.

  #[using="IMG"] Lemma A_ecp_grp_id_list_spec : ecp_grp_id_list_stmtA asegs AL A_ECP_GRP_ID_LIST A_ECP_IDS_DONE A_ECP_IDS.
  Proof.
    unfold ecp_grp_id_list_stmtA, A_ECP_GRP_ID_LIST, A_ECP_IDS_DONE, A_ECP_IDS.
    intros until m. (intros dd_H; ddestruct dd_H as (b & bs & HF & HA & HINV); intros MI RA ALWF CSOK).
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'.
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof HA as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LBS _].
    pose proof (munch_refl [(0x63c0a0, 0x63c0a0 + 1); (0x63c0c0, 0x63c0c0 + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. finishA; [exact HF| exact K0| rewrite (HINV K0) in HA; exact HA].
    - (* [comment removed for export] *)
      do 28 zstep.
      try (if_cases KB; zify_cond KB; [exfalso; clear - KB; rewrite ?unsigned_lit in KB by lia; lia|]).
      do 5 zstep.
      finishA.
      + match goal with H : rw_cells asegs ?mx 0x63c0a0 _ |- _ => eapply rw_cells_reshape; [exact H| cbn; tauto| reflexivity] end.
      + vm_compute. discriminate.
      + match goal with H : rw_cells asegs ?mx 0x63c0c0 ?cs |- _ =>
          pose proof (rw_cells_merge asegs mx 0x63c0c0 [] cs []) as R; cbn [app] in R; rewrite ?app_nil_r in R; specialize (R H) end.
        match type of R with rw_cells _ _ _ [CB ?n ?bs] => change n with 56%nat in R;
          replace bs with ecp_ids_bytes in R by (apply bytes_eq_of_unsigned; vm_compute; reflexivity) end.
        exact R.
  Qed.
End Walk.
