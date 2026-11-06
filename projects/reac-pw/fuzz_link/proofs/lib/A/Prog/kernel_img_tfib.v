(* reac-pw/fuzz_link, image A: the closed instance of kernel_img.v's KernImg at the image the build loads
   (tfibsegs = Asan.M.loaded_segments, fuzz_link.asan sha256 059dae63e07c) and the frame's asyms PcapB
   (lib/A/AD2l.v): every byte of the jump table 0x20f78 and of the three magic multipliers 0x10380, 0x10310,
   0x10318 lies in the read-only PT_LOAD 0x10000..0x3026c, outside Tfib_owned_static and errno (0x631b6c), and
   seg_rom gives the word kernel_img.v names; the texts table's 11 words (relro) and the 12 strings likewise; seg_rom
   is defined on the whole image (AB13.v tfib_rom_all). By computation.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YG00 YG0f YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB13 AF0m AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_img.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* over any asyms with the image's symbols (AF0m.v PcapSyms; AD2l.v PcapB_syms gives PcapB's) *)
Lemma kernel_img_syms : forall B, PcapSyms B -> KernImg tfibsegs B.
Proof.
  intros B HS.
  constructor.
  13: exact tfib_rom_all.
  all: unfold ki_words_ok, ki_rwords_ok, ki_strs_ok, ki_ro_ok, ki_rel_ok;
    try rewrite (@ts_owned B HS); try rewrite (@ts_errno B HS); vm_compute; reflexivity.
Qed.

Lemma kernel_img_pcapB : KernImg tfibsegs PcapB.
Proof. exact (kernel_img_syms PcapB PcapB_syms). Qed.
End a.
