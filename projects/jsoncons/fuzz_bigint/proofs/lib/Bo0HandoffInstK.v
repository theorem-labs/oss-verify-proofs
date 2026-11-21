(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the main phase's entry states are the ones computed in Bo0CertK_202.v for each CONFIG_RSEQ flag in place of the recorded Bo0HSK_0, Bo0HSK_1 and Bo0MainTableK, each fact is checked at both flag values, and the sections take the full launch input that AsanInitK's start state reads and the launch's extra reservations (n_resx). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Bo0DefsK Bo0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge Bo0HandoffK
  Bo0CertK_201 Bo0CertK_202 PlanRegenK.   (* [PlanRegenK.hstate] reads the computed states *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* The main phase's entry states, per rz: computed in [Bo0CertK_202.v] from the
   202 run, not recorded.  Every fact below is checked by
   computation at each of the two flag values. *)
Definition HSA_0 (h : nat) : acs := hstate HSL_202_0 HS_202_0 h.
Definition HSA_1 (h : nat) : acs := hstate HSL_202_1 HS_202_1 h.
Definition HSA (r : Z) (h : nat) : acs := if Z.eqb r 1 then HSA_1 h else HSA_0 h.
Lemma HSA_some : forall r h, (h < 2)%nat -> HS_as0 r h = Some (HSA r h).
Proof. intros r [|[|h]] H; [| |lia]; unfold HS_as0, HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma HSA_none : forall r h, (2 <= h)%nat -> HS_as0 r h = None.
Proof. intros r [|[|h]] H; [lia|lia|]; unfold HS_as0; destruct (Z.eqb r 1); reflexivity. Qed.
Lemma HSA_nofog : forall r h, (h < 2)%nat -> no_fog (a_maps (HSA r h)) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma HSA_mapslin : forall r h, (h < 2)%nat -> amaps_lin (kn (HSA r h)) (a_maps (HSA r h)) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma HSA_vislin : forall r h, (h < 2)%nat -> vis_lin (kn (HSA r h)) (a_vis (HSA r h) ++ a_ghost (HSA r h)) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma HSA_brklin : forall r h, (h < 2)%nat -> lin_nowrapR (kn (HSA r h)) (a_brk (HSA r h)) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma HSA_fd : forall r h, (h < 2)%nat -> a_fd (HSA r h) = FdStd.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

Lemma as0_chk_HSA : forall r h, (h < 2)%nat -> as0_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma HSA_numbers : forall r h, (h < 2)%nat ->
  a_totsz (HSA r h) <= 17729664880640 /\ a_eager (HSA r h) <= 16515072 /\ a_abytes (HSA r h) <= 2460878848 /\ length (a_maps (HSA r h)) = 17%nat.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; repeat split; discriminate || reflexivity. Qed.

Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     sixteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as [HandoffBridgeK.v:614-624]. *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variables abrt sdf : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable apc : N.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2460878848 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729664880640 + BUDGET) + (23 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_inst_bud : forall r h, (h < 2)%nat -> a_eager (HSA r h) + a_abytes (HSA r h) + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Proof. intros r h Hh. destruct (HSA_numbers r h Hh) as (_ & N2 & N3 & _). lia. Qed.
  Lemma as0_inst_gap : forall r h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + LENMAX + (a_totsz (HSA r h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps (HSA r h))) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros r h Hh. destruct (HSA_numbers r h Hh) as (N1 & _ & _ & N4). rewrite N4, asan0_res_eq. change (n_resx ASAN0) with 2%nat. cbn [length Nat.add].
    change (Z.of_nat 23) with 23. assert (0 <= LENMAX + 4095) by lia. nia.
  Qed.

  Theorem as0_handoff_static : forall r h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros r h Hh E R FULL model HC.
    eapply as0_bridge_static; try eassumption.
    - exact (as0_chk_HSA r h Hh).
    - exact (as0_inst_gap r h Hh).
  Qed.

  Theorem as0_handoff_binv : forall r h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) (as0_BASE EXTRA (HSA r h)) BUDGET [] (as0_A0 EXTRA (HSA r h) E) FULL model.
  Proof.
    intros r h Hh E R FULL model HC.
    eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := KMAX); try eassumption.
    - exact (as0_chk_HSA r h Hh).
    - exact (as0_inst_bud r h Hh).
    - exact (as0_inst_gap r h Hh).
  Qed.
End Inst.
