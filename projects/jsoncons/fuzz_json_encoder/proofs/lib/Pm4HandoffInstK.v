(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the launch input's kernel build): changed GAP, HSA, HSA_brklin and 24 more; added Hapc, Hbrk, Hfit and 24 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8HandoffInstK.v, lines 16-86, 96-125. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4DefsK Pm4PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge Pm4HandoffK
  Pm4HSK_0 Pm4HSK_1 Pm4MainTableK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
(* STATEMENT CHANGED, old beside new, throughout this block: the hand-off states are
   indexed by the run's CONFIG_RSEQ flag [b].
     OLD  HSA h, HS_0, HS_1, HS_as0 h
     NEW  HSA b h, HS_0 b, HS_1 b, HS_as0 b h
   The startup plan is certified once per flag (an earlier port's Pm4CertK_* /
   Pm4HSK_* / Pm4MainTableK interface: [cert_* : forall b, ...], [HS_0 b], [HS_1 b],
   [HS_as0 b h]).  Every closed check below destructs [b] ABOVE its [vm_compute], so
   no computation runs under an open binder. *)
Definition HSA (b : bool) (h : nat) : acs := match h with O => HS_0 b | _ => HS_1 b end.
Lemma HSA_some : forall b h, (h < 2)%nat -> HS_as0 b h = Some (HSA b h).
Proof. intros b [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.
Lemma HSA_none : forall b h, (2 <= h)%nat -> HS_as0 b h = None.
Proof. intros b [|[|h]] H; [lia|lia|reflexivity]. Qed.
Lemma HSA_nofog : forall b h, (h < 2)%nat -> no_fog (a_maps (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vm_compute; reflexivity]. Qed.
Lemma HSA_mapslin : forall b h, (h < 2)%nat -> amaps_lin (kn (HSA b h)) (a_maps (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vm_compute; reflexivity]. Qed.
Lemma HSA_vislin : forall b h, (h < 2)%nat -> vis_lin (kn (HSA b h)) (a_vis (HSA b h) ++ a_ghost (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vm_compute; reflexivity]. Qed.
Lemma HSA_brklin : forall b h, (h < 2)%nat -> lin_nowrapR (kn (HSA b h)) (a_brk (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vm_compute; reflexivity]. Qed.
Lemma HSA_fd : forall b h, (h < 2)%nat -> a_fd (HSA b h) = FdStd.
Proof. intros [|] [|[|h]] H; first [lia | reflexivity]. Qed.

Lemma as0_chk_0 : forall b, as0_chk (HS_0 b) = true.
Proof. intros [|]; vmc_refl. Qed.
Lemma as0_chk_1 : forall b, as0_chk (HS_1 b) = true.
Proof. intros [|]; vmc_refl. Qed.
Lemma as0_chk_HSA : forall b h, (h < 2)%nat -> as0_chk (HSA b h) = true.
Proof. intros b [|[|h]] H; [exact (as0_chk_0 b) | exact (as0_chk_1 b) | lia]. Qed.

(* The four bounds are read off the regenerated HS_0/HS_1 (COMPUTED probe
   a build round, source an earlier revision, all eight states).  [a_eager],
   [a_abytes] and the map count are the pre-revision literals unchanged.  [a_totsz] GREW
   by exactly [resx_bytes ASAN0] = 20 pages: the initial plan state's total size is
   [img_hi - img_lo + resx_bytes A] (AsanPlanCoreK.v:3579) and [p_resx ASAN0 = 20] is the
   upper end of [State.vdso_len_bounds].  The bound is therefore stated DERIVED, so that
   it follows [p_resx] instead of pinning a measured number; [resx0] is by [reflexivity],
   so a move of [p_resx] breaks the build rather than silently weakening the bound. *)
Lemma resx0 : APCK.resx_bytes ASAN0 = 81920.
Proof. reflexivity. Qed.

Lemma HSA_numbers : forall b h, (h < 2)%nat ->
  a_totsz (HSA b h) <= 17729665372160 + APCK.resx_bytes ASAN0 /\ a_eager (HSA b h) <= 16515072 /\ a_abytes (HSA b h) <= 2461523968 /\ length (a_maps (HSA b h)) = 17%nat.
Proof. intros [|] [|[|h]] H; first [lia | vm_compute; repeat split; discriminate || reflexivity]. Qed.

Section Inst.
  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva;
            SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw.
       NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order, as
            [Pm4HandoffK]'s As0Handoff ([ifs] the input's filesystem, [fs] the plan's
            FS0).  The proofs already call [as0_bridge_static]/[as0_binv_main] by
            [eapply ...; try eassumption], so only this header moves. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461523968 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  (* 21 -> 23: the reserved count the bridge takes is now
     length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs) = 4 + 2 + 17. *)
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665372160 + APCK.resx_bytes ASAN0 + BUDGET) + (23 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_inst_bud : forall b h, (h < 2)%nat -> a_eager (HSA b h) + a_abytes (HSA b h) + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Proof. intros b h Hh. destruct (HSA_numbers b h Hh) as (_ & N2 & N3 & _). lia. Qed.
  Lemma as0_inst_gap : forall b h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + LENMAX + (a_totsz (HSA b h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps (HSA b h))) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros b h Hh. destruct (HSA_numbers b h Hh) as (N1 & _ & _ & N4). rewrite resx0 in N1, GAP. rewrite N4, asan0_res_eq. cbn [length Nat.add n_resx ASAN0].
    change (Z.of_nat 23) with 23. assert (0 <= LENMAX + 4095) by lia. nia.
  Qed.

  Theorem as0_handoff_static : forall b h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA b h) R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros b h Hh E R FULL model HC.
    eapply as0_bridge_static; try eassumption;
      first [ exact (as0_chk_HSA b h Hh) | exact (as0_inst_gap b h Hh) ].
  Qed.

  Theorem as0_handoff_binv : forall b h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA b h) R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) (as0_BASE EXTRA (HSA b h)) BUDGET [] (as0_A0 EXTRA (HSA b h) E) FULL model.
  Proof.
    intros b h Hh E R FULL model HC.
    eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := KMAX); try eassumption;
      first [ exact (as0_chk_HSA b h Hh) | exact (as0_inst_bud b h Hh) | exact (as0_inst_gap b h Hh) ].
  Qed.
End Inst.
