From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocMB AllocPack AllocPackRoom Contract SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPackGSF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import ZAllocator AllocPackCf AllocReallocCf ReallocCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreeLim.
Import ListNotations.
Local Open Scope Z_scope.

Definition pack_ag_form : ResForm := {|
  rf_R := pbound; rf_ok := fun A b => res_ok_pack A b /\ GSF A;
  rf_room := fun b n => room_pack b n /\ LIVE2c (pb_cap b) (pb_bytes b + n) + NONHEAP_CF <= AgreeLim.LIM_AG;
  rf_malloc := pb_malloc; rf_free := pb_free; rf_realloc := pb_realloc |}.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma pack_ag_malloc_contract : AgreeLim.limlaw_at AgreeLim.LIM_AG B API -> pack_malloc_contract_cf B API ->
  SRCF.malloc_contract_r B API pack_ag_form.
Proof using.
  intros HL HM L A regs mem md n b Hpre Hro Hn Hok [Hroom Hlim].
  apply SRCF.SRcf_SR.
  pose proof Hpre as (HMR & _).
  exact (HM L A regs mem md n b Hpre Hro Hn Hok (conj Hroom (Z.le_trans _ _ _ Hlim (HL L A mem md HMR)))).
Qed.

Lemma pack_ag_free_contract : pack_free_contract_cf B API -> SRCF.free_contract_r B API pack_ag_form.
Proof using.
  intros HF L A regs mem md p n b Hpre Hro Hin Hp Hok.
  apply SRCF.SRcf_SR. exact (HF L A regs mem md p n b Hpre Hro Hin Hp Hok).
Qed.

Lemma pack_ag_free_null_contract : pack_free_null_contract_cf B -> SRCF.free_null_contract B.
Proof using.
  intros HN regs mem md H1 H2 H3 H4. apply SRCF.SRcf_SR. exact (HN regs mem md H1 H2 H3 H4).
Qed.

Lemma pack_ag_realloc_contract (pc : Z) : AgreeLim.limlaw_at AgreeLim.LIM_AG B API ->
  pack_realloc_contract_cf B API pc -> SRCF.realloc_contract_r B API pack_ag_form pc.
Proof using.
  intros HL HR L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen Hok [Hroom Hlim].
  apply SRCF.SRcf_SR.
  pose proof Hpre as (HMR & _).
  exact (HR L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen Hok
    (conj Hroom (Z.le_trans _ _ _ Hlim (HL L A mem md HMR)))).
Qed.

Lemma pack_ag_realloc_null_contract (pc : Z) : AgreeLim.limlaw_at AgreeLim.LIM_AG B API ->
  pack_realloc_null_contract_cf B API pc -> SRCF.realloc_null_contract_r B API pack_ag_form pc.
Proof using.
  intros HL HN L A regs mem md n b Hpre Hro H10 H11 Hra Hok [Hroom Hlim].
  apply SRCF.SRcf_SR.
  pose proof Hpre as (HMR & _).
  exact (HN L A regs mem md n b Hpre Hro H10 H11 Hra Hok (conj Hroom (Z.le_trans _ _ _ Hlim (HL L A mem md HMR)))).
Qed.

End I.

Section Z.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zlib_ag_malloc_contract : AgreeLim.limlaw_at AgreeLim.LIM_AG src0_msyms zlib_API ->
  SRCF.malloc_contract_r src0_msyms zlib_API pack_ag_form.
Proof using. intros HL. exact (pack_ag_malloc_contract src0_msyms zlib_API HL zlib_pack_malloc_contract_cf). Qed.

Theorem zlib_ag_free_contract : SRCF.free_contract_r src0_msyms zlib_API pack_ag_form.
Proof using. exact (pack_ag_free_contract src0_msyms zlib_API zlib_pack_free_contract_cf). Qed.

Theorem zlib_ag_free_null_contract : SRCF.free_null_contract src0_msyms.
Proof using. exact (pack_ag_free_null_contract src0_msyms zlib_pack_free_null_contract_cf). Qed.

Theorem zlib_ag_realloc_contract : forall pc, ms_realloc src0_msyms = Some pc ->
  AgreeLim.limlaw_at AgreeLim.LIM_AG src0_msyms zlib_API -> SRCF.realloc_contract_r src0_msyms zlib_API pack_ag_form pc.
Proof using.
  intros pc Hpc HL. exact (pack_ag_realloc_contract src0_msyms zlib_API pc HL (zlib_pack_realloc_contract_cf pc Hpc)).
Qed.

Theorem zlib_ag_realloc_null_contract : forall pc, ms_realloc src0_msyms = Some pc ->
  AgreeLim.limlaw_at AgreeLim.LIM_AG src0_msyms zlib_API ->
  SRCF.realloc_null_contract_r src0_msyms zlib_API pack_ag_form pc.
Proof using.
  intros pc Hpc HL.
  exact (pack_ag_realloc_null_contract src0_msyms zlib_API pc HL (zlib_pack_realloc_null_contract_cf pc Hpc)).
Qed.

End Z.
