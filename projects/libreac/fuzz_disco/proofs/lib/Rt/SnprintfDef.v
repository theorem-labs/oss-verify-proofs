From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnSx SnFF.
Import ListNotations.
Local Open Scope Z_scope.
Definition VFPRINTF_ICPT_STK : Z := 1024 + 2 * ESTACK.
Definition VSNPRINTF_ICPT_STK : Z := 2160 + 304 + VFPRINTF_ICPT_STK.
Definition SNPRINTF_STK : Z := 96 + VSNPRINTF_ICPT_STK.
Section s. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition consts_view (W : world segs) (mem : word -> option byte) (cr : list (Z * Z)) : Prop :=
forall a, Exists (in_zr a) cr -> aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition asnprintf_realizes {fx : YK11.FPState} (gc gv img_lo img_hi flo fhi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
SnShared.sh_asnprintf_realizes (fx := fx) segs B (SnFF.FF_disco flo fhi) SNPRINTF_STK gc gv img_lo img_hi cr pc.
Lemma asnprintf_of_shared_K : forall {fx : YK11.FPState} K gc gv img_lo img_hi flo fhi cr pc, K <= SNPRINTF_STK ->
  SnShared.sh_asnprintf_realizes (fx := fx) segs B (SnFF.FF_disco flo fhi) K gc gv img_lo img_hi cr pc ->
  asnprintf_realizes (fx := fx) gc gv img_lo img_hi flo fhi cr pc.
Proof.
intros fx K gc gv img_lo img_hi flo fhi cr pc HK H.
exact (SnSx.sh_asnprintf_mono (fx := fx) segs B _ K SNPRINTF_STK gc gv img_lo img_hi cr pc (SnFF.FF_disco_mono flo fhi) HK H).
Qed.
End s.
