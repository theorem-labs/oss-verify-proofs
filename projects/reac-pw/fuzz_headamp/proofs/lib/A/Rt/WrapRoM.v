(* The comments in this file are libreac/fuzz_identity's lib/A/Rt/WrapRoM.v, unchanged apart from names and this unit's image and values. reac-pw/fuzz_headamp, image A: from the wrappers' read-only premise (lib/A/Rt/WrapRo.v aro_unowned) to the
   musl constants the strlen and memchr walks read (lib/A/AE39.v mconsts_view: 0x10368 .. 0x10388). Those 32 bytes
   lie in a read-only segment (AE39.v mc_in_rom), are not in Tfib_owned_static (checked range by range below, so a
   core whose list covers them fails here and not in a walk), and are not errno. This replaces cgif's
   mconsts_of_rom_view (AE39.v:40), whose premise rom_view a caller cannot carry across __asan_stack_malloc_*. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Rt/WrapRoM.v at origin/ossv/recipes 09c6822d886 for reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pin f3e0669d2819); module paths changed; addresses moved to fuzz_headamp.asan by alreloc a5c53bb2bed4 in the code only (every comment is the source's, verbatim: its addresses are fuzz_identity.asan's or those of the image it names). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AE39.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mconsts_of_aro : forall B (W : world tfibsegs) mem, TfibSyms B ->
aro_unowned tfibsegs B (aview tfibsegs (w_H W) mem) -> mconsts_view W mem.
Proof.
intros B W mem TB Hro a Ha. pose proof mc_bounds as [M1 M2].
apply Hro.
- exact (mc_in_rom a Ha).
- rewrite (ts_owned B TB). intros Hex. apply Exists_exists in Hex as (r & Hr & Hz).
unfold Tfib_owned_static in Hr. unfold in_zr in Hz.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hz; clear - Ha M1 M2 Hz; lia |]). destruct Hr.
- rewrite (ts_errno B TB). unfold TFIB_ERRNO. clear - Ha M1 M2. lia.
Qed.
End b.
