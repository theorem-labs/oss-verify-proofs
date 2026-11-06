(* reac-repacer/fuzz_uci, build asan: from the wrappers' read-only premise (lib/A/Rt/WrapRo.v aro_unowned) to the
   musl constants the strlen and memchr walks read (lib/A/AE39.v mconsts_view: 0x10350 .. 0x10370). Those 32 bytes
   lie in a read-only segment (AE39.v mc_in_rom), are not in Tfib_owned_static (checked range by range below, so a
   core whose list covers them fails here and not in a walk), and are not errno. This replaces cgif's
   mconsts_of_rom_view (AE39.v:40), whose premise rom_view a caller cannot carry across __asan_stack_malloc_*. *)
(* Modified by Theorem Labs, 2026-10-29: for r-identity's acceptance (cold/h-rw-ide-6-wrapacc), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE 05:31Z: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_identity lib/A/Rt/WrapRoM.v (origin/ossv/recipes 70952e1c8c9)
   to reac-repacer/fuzz_uci image A (fuzz_uci.asan, sha256 6ea017c24525) on the fuzz_uci A core (276afc86670b): module
   paths; record class TfibSyms -> UciSyms (code only; the donor's own Modified-by lines are kept as its record).
   Numerals moved by symbol + offset from the fuzz_identity unstripped twin to the fuzz_uci unstripped twin (each
   function is the same code up to pc-relative fields: bytecmp 7daa0e2a03d9 with repin_check 9cbc3553c09e's target pass); a .got slot moves to the slot that
   holds the same symbol. Every changed numeral, old -> new, symbol + offset in fuzz_identity.asan [occurrences]:
     (none: this file has no numeral that changes)
   Unchanged on purpose: 0x10350, 0x10368, 0x10370 (musl's HIGHS/ONES constants and their end: the same address in
   both images, read by the auipc/ld pairs at strlen+0x3c..0x48 and memchr+0x58..0x64).
   This file only. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AB1v
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AF0m
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AE39.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mconsts_of_aro : forall B (W : world tfibsegs) mem, UciSyms B ->
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
