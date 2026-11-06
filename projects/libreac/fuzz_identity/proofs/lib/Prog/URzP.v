From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Exec RegisterBridge Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract.
Import ListNotations.
Local Open Scope Z_scope.

Definition SRcfS (segs : list Segment) (c : config) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') -> realizes segs c T /\ cut_free segs c.

Section CF.
Variable segs : list Segment.

Lemma cfs_instr : forall ms model ms',
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  cut_free segs (mkCfg ms' model) -> cut_free segs (mkCfg ms model).
Proof using.
  intros ms model ms' Hh Hl Hsvc Hstep Hc tr c' Hstar.
  inversion Hstar as [c0 | c1 evs c2 tr' c3 Hs Hst]; subst.
  - exact (budget_refused_at_no_lazy_instr segs ms model Hl Hsvc).
  - destruct (node_instr segs ms model ms' Hh Hl Hsvc Hstep) as [_ Hall].
    destruct (Hall evs (SNext c2) Hs) as [[] [_ Heq]].
    injection Heq as ->. exact (Hc tr' c' Hst).
Qed.

Lemma cfs_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  cut_free segs (mkCfg ms' model) -> cut_free segs (mkCfg ms model).
Proof using.
  intros ms ms' model Hh Hl Hms; induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  exact (cfs_instr ms model ms1 Hh Hl Hsvc Hstep (IH Hc)).
Qed.

Lemma evt_SRcfS_canon : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcfS segs (mkCfg ms' md) P) ->
  SRcfS segs (mkCfg ms md) P.
Proof using.
  intros ms Q md P H Hh Hl K.
  destruct (RegisterBridge.canonical_contract_transport segs Q ms H) as [final [Hs HQ]].
  intros T HK. destruct (K final HQ T HK) as [Hr Hc]. split.
  - exact (rz_msteps segs ms final md T Hh Hl (lib_msteps_frame segs ms final Hs) Hr).
  - exact (cfs_msteps ms final md Hh Hl (lib_msteps_frame segs ms final Hs) Hc).
Qed.

Lemma SRcfS_ret : forall c (Q : config -> Prop), Q c -> SRcfS segs c Q.
Proof using. intros c Q HQ T HK. exact (HK c HQ). Qed.

Lemma SRcfS_bind : forall c (R Q : config -> Prop),
  SRcfS segs c R -> (forall c', R c' -> SRcfS segs c' Q) -> SRcfS segs c Q.
Proof using. intros c R Q H1 H2 T HK. apply H1. intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRcfS_mono : forall c (Q Q' : config -> Prop),
  SRcfS segs c Q -> (forall c', Q c' -> Q' c') -> SRcfS segs c Q'.
Proof using. intros c Q Q' H HQQ T HK. apply H. intros c' HQ. exact (HK c' (HQQ c' HQ)). Qed.
End CF.

Class RzC := {
  Rz : list Segment -> config -> (config -> Prop) -> Prop;
  rz_evt_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
    Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
    (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> Rz segs (mkCfg ms' md) P) ->
    Rz segs (mkCfg ms md) P;
  rz_ret : forall segs c (Q : config -> Prop), Q c -> Rz segs c Q;
  rz_bind : forall segs c (R Q : config -> Prop), Rz segs c R -> (forall c', R c' -> Rz segs c' Q) -> Rz segs c Q;
  rz_mono : forall segs c (Q Q' : config -> Prop), Rz segs c Q -> (forall c', Q c' -> Q' c') -> Rz segs c Q'
}.

Definition rzC_SR : RzC :=
  {| Rz := SR; rz_evt_canon := evt_SR_canon; rz_ret := SR_ret; rz_bind := SR_bind; rz_mono := SR_mono |}.

Definition rzC_CF : RzC :=
  {| Rz := SRcfS; rz_evt_canon := evt_SRcfS_canon; rz_ret := SRcfS_ret; rz_bind := SRcfS_bind;
     rz_mono := SRcfS_mono |}.

Section RA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RzCi : RzC}.

Class RzA (B : malloc_syms) (API : AllocAPI B) := {
  RzRoom : Model -> sbound -> Z -> Prop;
  rz_sroom : sbound -> Prop;
  rz_room_of : forall L A mem md b0 xl xb n, aa_MR API L A mem md -> rz_sroom b0 ->
    0 <= xl <= 16 -> 0 <= xb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
    RzRoom md (SB (sb_live b0 + xl) (sb_bytes b0 + xb) (sb_cap b0)) n;
  rz_malloc : forall L A regs mem md n b,
    call_pre B (aa_MR API) L A regs mem md -> ro_agree (ms_segs B) mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> RzRoom md b n ->
    Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md)
      (malloc_ret B API ALLOC_STACK L A regs mem md n b);
  rz_free : forall L A regs mem md p n b,
    call_pre B (aa_MR API) L A regs mem md -> ro_agree (ms_segs B) mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    res_ok_slots A b ->
    Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
         call_post B (aa_MR API) L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_free b n))
}.
End RA.
