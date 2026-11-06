From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import IInst IImgB.
Import ListNotations.
Open Scope Z_scope.

Definition N_exact_asan_ubsan : list (Z * Z) := [
  KV 0x21334 0x52104;
  KV 0x21738 0x52100;
  KV 0x21920 0x42a40;
  KV 0x1ae48 0x42a88;
  KV 0x1ae04 0x42a8c;
  KV 0x7f000400 0x42a70].

Definition N_sym_asan_ubsan (k : Z) : Z :=
  match zlookup k N_exact_asan_ubsan with Some v => v | None => N_sym k end.

Definition N_img_asan_ubsan : RImg := {| img_segs := rsegs; sym := N_sym_asan_ubsan |}.
