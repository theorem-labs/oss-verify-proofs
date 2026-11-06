(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v at 6ebe35ba632; the contract is lib/A/PPgWrap.v's astrcspn_realizes for reac-pw/fuzz_pin.asan's strcspn wrapper (trampoline 0x4191c -> 0x42cb8, musl strcspn 0x91864, __strchrnul 0x9174c), proved from the pieces lib/A/FMstrcspn_front.v (trampoline to 0x42d38, with the loops of __strchrnul from lib/A/FMstrcspn_musl.v) and lib/A/FMstrcspn.v (0x42d38 to the return, with the range checks of lib/A/FMstrcspn_chk1.v and lib/A/FMstrcspn_chk2.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import FMcs0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require FMstrcspn_musl FMstrcspn_chk1 FMstrcspn_chk2 FMstrcspn_front FMstrcspn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgWrap.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The address the program calls (reac_box_pin_parse `jal 4191c` at 0x80c84): __interceptor_trampoline_strcspn. *)
Lemma CS_ENTRY_eq : CS_ENTRY = 0x4191c. Proof. reflexivity. Qed.
Theorem strcspn_icpt_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> astrcspn_realizes tfibsegs B 0x4191c.
Proof.
intros B LAWS TB. unfold astrcspn_realizes.
intros ly S W regs mem md x y str set HPRE Hslo Hpres G10 G11 Hstr Hset Hlen Hro.
destruct set as [|c [|c' rest]]; [cbn in Hlen; discriminate | | cbn in Hlen; discriminate].
rewrite <- CS_ENTRY_eq.
eapply SRr_bind.
{ exact (FMstrcspn_front.cs_front B LAWS TB FMstrcspn_musl.cs_musl_loops ly S W regs mem md x y str c
    HPRE Hslo Hpres G10 G11 Hstr Hset Hro). }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Hmid).
eapply SRr_mono.
{ exact (FMstrcspn.cs_back B LAWS TB (FMstrcspn_chk1.cs_chk1 B LAWS TB) (FMstrcspn_chk2.cs_chk2 B LAWS TB)
    ly S W regs mem md x y str c regs1 mem1 md1 HPRE Hslo Hpres Hstr Hset Hmid). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hpr & Hsbm & H10 & Hfr & Hp).
unfold awrap_post. split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hc|]. split; [exact HAR|]. split; [exact Hpr|]. split; [exact Hsbm|]. split; [exact H10|].
split; [exact Hfr | exact Hp].
Qed.
End d.
