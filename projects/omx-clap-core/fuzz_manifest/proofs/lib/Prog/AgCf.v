(* Shared facts for the cut-free (agreement) twins of fuzz_manifest's plain proofs (AGREES.md, 'Slot forms for
   allocating targets'): the agreement room at a malloc site, turned into room_cf by the frame's room_cf_of_limit under
   the source limit (2^34 <= vm_limit at every allocator state), the register-canonical evt lift on this image, and a
   measured loop rule for SRcf. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO03.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Exec RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0 Contract AllocSlots SlotAgree AgreeLift.
Import ListNotations.
Local Open Scope Z_scope.

(* The room a malloc site needs in the cut-free run: the halts room, the agreement cap, and the live bytes after the
   request within 2^29 (the premises of SlotAgree.room_cf_of_limit). *)
Definition room_ag (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

(* The agreement cap is within the halts cap, so room_slots facts carry over without unfolding CAP_AG. *)
Lemma CAP_AG_le_CAPMAX : CAP_AG <= CAPMAX.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma room_ag_of : forall b n, room_slots b n -> 0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 29 -> room_ag b n.
Proof. intros b n HR Hc Hb. exact (conj HR (conj Hc Hb)). Qed.

Section Lim.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
(* The source limit at every allocator state (AgreeZlib.zlib_limit gives it for the agreement's allocator). *)
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Lemma room_cf_of : forall L A mem md b n, aa_MR API L A mem md -> room_ag b n -> room_cf md b n.
Proof using LIMLAW.
  intros L A mem md b n HM (H1 & H2 & H3).
  apply room_cf_of_limit; [exact (LIMLAW L A mem md HM) | exact H1 | exact H2 | exact H3].
Qed.
End Lim.

Section Run.
Variable B : malloc_syms.
Hypothesis HSEGS : ms_segs B = rsegs.

Lemma evt_SRcf_canon_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using HSEGS.
  intros ms Q md P HE. rewrite <- HSEGS in HE. exact (evt_SRcf_canon B ms Q md P HE).
Qed.

Lemma evt_SRcf_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SRcf B (mkCfg ms' md) P) -> SRcf B (mkCfg ms md) P.
Proof using HSEGS.
  intros ms Q md P HE. rewrite <- HSEGS in HE. exact (evt_SRcf B ms Q md P HE).
Qed.
End Run.

Lemma SRcf_loop : forall (B : malloc_syms) (W : Type) (m : W -> nat) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SRcf B c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SRcf B c Q.
Proof.
  intros B W m P Q Hb w.
  induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof W m)).
  intros c HP T HKt. apply (Hb w c HP T). intros c' [HQ | (w' & Hlt & HP')].
  - exact (HKt c' HQ).
  - exact (IH w' Hlt c' HP' T HKt).
Qed.
