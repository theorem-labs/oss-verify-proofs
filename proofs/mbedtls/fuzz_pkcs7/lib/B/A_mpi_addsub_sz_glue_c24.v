(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_mpi_opnd A_mpi_journey A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_add_int A_mpi_sub_int A_mpi_add_abs_sz A_mpi_sub_abs_sz A_mpi_add_sub_sz A_mpi_add_int_sz A_mpi_sub_int_sz A_mpi_addsub_sz_glue A_mpi_stmtA_c24 A_mpi_add_sub_sz_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_add_sub_stmtSZ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
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
Ltac2 gd_tbl_A_mpi_addsub_sz_glue_c24 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz_c24.add_sub_mpi_stmtA_oz_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_add_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_sub_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_MPI"].


(* [comment removed for export] *)
Lemma A_add_sub_mpi_spec_osz_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_addsub_sz_glue_c24 ()) "Pflip,$0.P,(1.(2.$0.R1.+1.)(2.$0.R1.-1.))PR,$3.PHIA,(4.$5.R1.)P,(6.R4.$5.R2.R1.$7.)(8.R5.$5.R3.R2.$7.)")
(* [comment removed for export] *).
Proof.
  intros flip FL R HIA H. unfold A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz. intros until d.
  intros HH HK MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF C24 E0 E1 E2 E3.
  unfold add_sub_mpi_stmtA_oz_c, mpi_addsub_stmtA_o_c in H.
  exact (H h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo dX dA dB lo d
           HH HK MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA OBA IA1 IA2 IB2 A47B BUD UW UWX UWA UWB BUDF ltac:(clear - C24; unfold A_mpi_stmtA_sz.C24_ADDSUB, C24_ADD_SUB_c in *; lia) E0 E1 E2 E3).
Qed.

(* [comment removed for export] *)

Theorem A_mpi_add_mpi_sz_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_addsub_sz_glue_c24 ()) "PR,$3.PHIA,(4.$5.R1.)P,(6.+1.$5.R2.R1.$7.)(9.$5.R3.R2.$:.)")
(* [comment removed for export] *).
Proof.
  intros R HIA HAS. unfold mpi_add_mpi_stmtA_sz, mpi_binop_stmtA_sz, A_MPI_ADD_MPI.
  intros until slo.
  intros HH HK LFB MX MA MB SXA SXB SAB NST NBH OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SSH TOP SPA TPV MI RAE OXA OAA OBA IMA IMB BUD UW UWX UWA UWB BUDF C24 -> -> ->.
  pose proof (arl_need_ecp_rt R) as NE.
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
  apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  intros mo1 [HK1 MF1].
  eapply aevtS_mono.
  { unfold add_sub_mpi_stmtA_oz_c, mpi_addsub_stmtA_o_c in HAS.
    eapply HAS with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
      first [ eassumption | reflexivity | exact BUD | exact BUDF | (apply opnd_atA_mpd; assumption)
            | (intros _ O; exact (IMA O)) | (intros O _; exact (IMA O)) | (intros O _; exact (IMB O))
            | (intros O; exact (mpd_at_static47 _ _ _ MB O)) | (clear - SLO NE; lia) | (clear - C24; unfold C24_ADDSUB, C24_ADD_SUB_c in *; lia)
            | match goal with |- ?g => idtac "ADDSUBSZ-LEFT:" g end ]. }
  intros c PO. eapply binop_postA_mono; [exact MF1| | exact PO]. intros r dd. apply wrap_Rsz_add.
Qed.
Theorem A_mpi_sub_mpi_sz_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_addsub_sz_glue_c24 ()) "PR,$3.PHIA,(4.$5.R1.)P,(6.-1.$5.R2.R1.$7.)(;.$5.R3.R2.$<.)")
(* [comment removed for export] *).
Proof.
  intros R HIA HAS. unfold mpi_sub_mpi_stmtA_sz, mpi_binop_stmtA_sz, A_MPI_SUB_MPI.
  intros until slo.
  intros HH HK LFB MX MA MB SXA SXB SAB NST NBH OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SSH TOP SPA TPV MI RAE OXA OAA OBA IMA IMB BUD UW UWX UWA UWB BUDF C24 -> -> ->.
  pose proof (arl_need_ecp_rt R) as NE.
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
  apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  intros mo1 [HK1 MF1].
  eapply aevtS_mono.
  { unfold add_sub_mpi_stmtA_oz_c, mpi_addsub_stmtA_o_c in HAS.
    eapply HAS with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
      first [ eassumption | reflexivity | exact BUD | exact BUDF | (apply opnd_atA_mpd; assumption)
            | (intros _ O; exact (IMA O)) | (intros O _; exact (IMA O)) | (intros O _; exact (IMB O))
            | (intros O; exact (mpd_at_static47 _ _ _ MB O)) | (clear - SLO NE; lia) | (clear - C24; unfold C24_ADDSUB, C24_ADD_SUB_c in *; lia)
            | match goal with |- ?g => idtac "ADDSUBSZ-LEFT:" g end ]. }
  intros c PO. eapply binop_postA_mono; [exact MF1| | exact PO]. intros r dd. apply wrap_Rsz_sub.
Qed.

