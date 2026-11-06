(* reac-pw/fuzz_headamp, build asan (image A, fuzz_headamp.asan pin f3e0669d2819): the strcmp wrapper's contract in
   the frame-hole form of lib/A/HPgHole.v, hd_astrcmp_hole at the trampoline __interceptor_trampoline_strcmp 0x41ba0
   (lib/A/Rt/StrcmpDef.v STRCMP_ENTRY_A), for the parse's three calls inside its poisoned real-stack frame (image A
   0x84a50, 0x84a6c, 0x84a80). It is lib/A/Rt/Strcmp.v's walk (fuzz_identity's, ported) at U = hU fr pat:
   strcmp_srrU holds AR at unpoison U mem and states every other premise and post over the real memory, which is
   hd_astrcmp_hole's form; the hole's bytes lie in the shadow band below the stack (HPgHole.v hole_band), so they are
   at or above kHighShadowBeg (strcmp_srrU's premise) and outside the wrapper's stack window, where the post keeps
   every byte, so the pattern hpat is kept. Proves function ___interceptor_strcmp (kind: contract in hole form). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
Require Import OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AB1v OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require StrcmpDef Strcmp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem strcmp_hole_contract : forall B, AR_laws tfibsegs B -> TfibSyms B ->
hd_astrcmp_hole tfibsegs B StrcmpDef.STRCMP_ENTRY_A.
Proof.
intros B LAWS TB. unfold hd_astrcmp_hole.
intros ly S W regs mem md x y k c1 c2 fr pat HPRE G10 G11 Hx Hy Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby
Hamx Hamy Hrax Hhx Hray Hhy.
destruct HPRE as (HPRE & HOK & HPAT & HSLO & HPRES).
assert (HLY : layout_ok ly) by exact (am_layout B ly S _ (proj1 (proj1 HPRE))).
assert (HUlo : forall s, FMupoison.in_ush (hU fr pat) s = true -> kHighShadowBeg <= s).
{ intros s Hs. apply in_hU in Hs. exact (proj1 (proj1 (hole_band ly fr pat HLY HOK s Hs))). }
pose proof (Strcmp.strcmp_srrU B LAWS TB Strcmp.STRCMP_TRAMP Strcmp.r_A_tramp (hU fr pat) ly S W regs mem md
  x y k c1 c2 HUlo HPRE HSLO HPRES G10 G11 Hx Hy Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy) as HW.
change (cfg_at tfibsegs StrcmpDef.STRCMP_ENTRY_A regs mem md) with (cfg_at tfibsegs Strcmp.STRCMP_TRAMP regs mem md).
eapply SRr_mono; [exact HW|].
intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & Hpr & Hsbm & G & Hfr & Hpm).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HAR'|]. split.
- intros i Hi.
  pose proof (hole_band ly fr pat HLY HOK (shadow_addr fr + i) ltac:(lia)) as (_ & Hlo & _ & _ & Hr).
  rewrite Hfr; [exact (HPAT i Hi) | exact Hr | lia].
- split; [exact Hpr|]. split; [exact Hsbm|]. split; [exact G|]. split; [exact Hfr | exact Hpm].
Qed.
End h.

Print Assumptions strcmp_hole_contract.
