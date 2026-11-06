From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import IInst IImgA.
Import ListNotations.
Open Scope Z_scope.

Definition N_exact_asan : list (Z * Z) := [
  KV 0x21334 0x5208c;
  KV 0x21738 0x52088;
  KV 0x21920 0x429c8;
  KV 0x1ae48 0x42a10;
  KV 0x1ae04 0x42a14;
  KV 0x7f000400 0x429f8].

Definition N_sym_asan (k : Z) : Z :=
  match zlookup k N_exact_asan with Some v => v | None => N_sym k end.

Definition N_img_asan : RImg := {| img_segs := rsegs; sym := N_sym_asan |}.
