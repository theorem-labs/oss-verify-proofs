From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract SlotAgree AllocRoom AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
Import ListNotations.
Local Open Scope Z_scope.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma room_of_slots : forall b0 xl xb n, slot_room b0 ->
  0 <= xl <= 16 -> 0 <= xb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
  room_slots (SB (sb_live b0 + xl) (sb_bytes b0 + xb) (sb_cap b0)) n.
Proof.
  intros b0 xl xb n (HL & HB & HC) Hxl Hxb Hn.
  unfold room_slots. cbn [sb_live sb_bytes sb_cap].
  split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
Qed.

Definition rzA_SR (MAL : malloc_contract B API) (FRE : free_contract B API) : @RzA fx rc rzC_SR B API :=
  @Build_RzA fx rc rzC_SR B API (fun _ b n => room_slots b n) slot_room
    (fun L A mem md b0 xl xb n _ H1 H2 H3 H4 => room_of_slots b0 xl xb n H1 H2 H3 H4) MAL FRE.

Definition sroom_ag (b : sbound) : Prop := slot_room b /\ sb_cap b = CAP_AG.

Lemma room_of_cf : (forall L A mem md, aa_MR API L A mem md -> 2 ^ 39 <= vm_limit (m_vmmaps md)) ->
  forall L A mem md b0 xl xb n, aa_MR API L A mem md -> sroom_ag b0 ->
  0 <= xl <= 16 -> 0 <= xb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
  room_cf md (SB (sb_live b0 + xl) (sb_bytes b0 + xb) (sb_cap b0)) n.
Proof.
  intros LIM L A mem md b0 xl xb n HMR (HS & HC) Hxl Hxb Hn.
  split; [exact (room_of_slots b0 xl xb n HS Hxl Hxb Hn)|].
  cbn [sb_cap sb_bytes]. rewrite HC.
  pose proof (LIM L A mem md HMR) as HV. pose proof CAP_AG_fits as HF.
  destruct HS as (_ & HB & _).
  assert (HM : LIVE_BOUND CAP_AG (sb_bytes b0 + xb + n) <= LIVE_BOUND CAP_AG (2 ^ 29)) by (unfold LIVE_BOUND; lia).
  lia.
Qed.

Definition rzA_CF (MAL : malloc_contract_cf B API) (FRE : free_contract_cf B API)
    (LIM : forall L A mem md, aa_MR API L A mem md -> 2 ^ 39 <= vm_limit (m_vmmaps md)) : @RzA fx rc rzC_CF B API :=
  @Build_RzA fx rc rzC_CF B API (fun md b n => room_cf md b n) sroom_ag (room_of_cf LIM) MAL FRE.

Lemma rzC_SR_realizes : forall segs c Q T, @Rz rzC_SR segs c Q -> (forall c', Q c' -> realizes segs c' T) ->
  realizes segs c T.
Proof. intros segs c Q T H K. exact (H T K). Qed.

Lemma rzC_CF_crealizes : forall segs c Q T, @Rz rzC_CF segs c Q ->
  (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') -> realizes segs c T /\ cut_free segs c.
Proof. intros segs c Q T H K. exact (H T K). Qed.
End I.
