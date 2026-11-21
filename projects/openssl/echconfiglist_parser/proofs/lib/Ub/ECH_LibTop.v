(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the library is closed at the run instance HeapSRVC.HRv over the run's segment list, under the launch facts vdso_run_facts; fuzz_closed is stated as fuzz_vc_type, from heap_sr_hyps_x_vc and time_sr_vc). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Vdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Rep
     ECH_C4_stmt ECH_C3_stmt ECH_C14_stmt ECH_Iface ECH_C14_readcfg ECH_C14_entry ECH_C14_b64arm ECH_Certs F_time MallocSR MallocSR_closed.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RVdsoSegs HeapSRVC F_timeRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import CertA_ubsan CertO3_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section G.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem readcfg_closed : heap_sr_hyps_x H -> time_sr_stmt H -> readcfg_stmt H.
  Proof.
    intros HX TIME. eapply (readcfg_spec H HX (egs_fresh_cert H HX) TIME).
    - intros. eapply (rp_entry H HX (egs_fresh_cert H HX)); eassumption.
    - intros. eapply (rp_b64arm H HX (egs_fresh_cert H HX) (getdefctx_fresh_cert H HX)); try eassumption.
      intros. eapply (rp_entry H HX (egs_fresh_cert H HX)); eassumption.
  Qed.

  Theorem fuzz_closed_x : heap_sr_hyps_x H -> time_sr_stmt H -> fuzz_stmt H.
  Proof. intros HX TIME. exact (fuzz_spec_x H HX (readcfg_closed HX TIME)). Qed.
End G.

(* The launch facts the run instance is closed under: every hypothesis of [HeapSRVC]'s Section VC
   and of [F_timeRun]'s Section TimeRun, for the run's tail [tail] (the vDSO/vvar pair
   [Run.vdso_segments], Run.v:290-306) and the pair's base [vlo], text base [vmid] and top [vhi].
   [VdsoLaunch.vdso_launch_facts] proves them from the launch. *)
Record vdso_run_facts {HCEIL : HeapCeil} (tail : list Segment) (vlo vmid vhi : Z) : Prop := mk_vdso_run_facts {
  vr_nx : forall s, In s tail -> seg_executable s = false;
  vr_nw : forall s, In s tail -> seg_writable s = false;
  vr_vi : vdso_image usegs = None;
  vr_w : (0x358000 <= vlo /\ vlo <= vmid /\ vmid <= vhi /\ vhi <= hceil)%Z;
  vr_wlt : (vlo < vhi)%Z;
  vr_tw : forall (x : Z) s, find_segment tail x 1 = Some s -> (vlo <= x < vhi)%Z;
  vr_cov : forall (x : Z), (vlo <= x < vhi)%Z -> find_segment tail x 1 <> None;
  vr_rom : rvdso_rom (rvsegs tail) vmid;
  vr_vb : hvdso = (vmid + 1460)%Z;
  vr_ent : vdso_entry_fn (usegs ++ tail) (Z_to_bv 64 hvdso) = Some VdsoClockGettime;
  vr_unm : forall ms, ms_pc ms = Z_to_bv 64 hvdso -> RiscvSemantics.step (usegs ++ tail) ms = MachineUnmodeled }.

(* The statement the ubsan binary's library is closed at. *)
Definition fuzz_vc_type : Prop :=
  forall (HCEIL : HeapCeil) (HSEC : HeapSecret) (tail : list Segment) (vlo vmid vhi : Z),
    @vdso_run_facts HCEIL tail vlo vmid vhi -> @ECH_Iface.fuzz_stmt HCEIL (@HRv HCEIL HSEC tail vlo vmid vhi).

(* [HeapSRVC.heap_sr_hyps_x_vc] and [F_timeRun.time_sr_vc] at the record's fields. *)
Lemma heap_vc_of_facts : forall (HCEIL : HeapCeil) (HSEC : HeapSecret) (tail : list Segment) (vlo vmid vhi : Z),
  @vdso_run_facts HCEIL tail vlo vmid vhi -> heap_sr_hyps_x (@HRv HCEIL HSEC tail vlo vmid vhi).
Proof. intros HCEIL HSEC tail vlo vmid vhi R. destruct R. eapply heap_sr_hyps_x_vc; eassumption. Qed.

Lemma time_vc_of_facts : forall (HCEIL : HeapCeil) (HSEC : HeapSecret) (tail : list Segment) (vlo vmid vhi : Z),
  @vdso_run_facts HCEIL tail vlo vmid vhi -> time_sr_stmt (@HRv HCEIL HSEC tail vlo vmid vhi).
Proof. intros HCEIL HSEC tail vlo vmid vhi R. destruct R. eapply time_sr_vc; eassumption. Qed.

Theorem fuzz_closed : fuzz_vc_type.
Proof.
  intros HCEIL HSEC tail vlo vmid vhi R.
  exact (@fuzz_closed_x HCEIL (@HRv HCEIL HSEC tail vlo vmid vhi)
           (heap_vc_of_facts HCEIL HSEC tail vlo vmid vhi R) (time_vc_of_facts HCEIL HSEC tail vlo vmid vhi R)).
Qed.

Print Assumptions fuzz_closed.
