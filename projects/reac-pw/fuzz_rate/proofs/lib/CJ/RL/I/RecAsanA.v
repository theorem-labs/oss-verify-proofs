(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/CJ/RL/I/RecAsanA.v at 2d2ff01bb6f2; module paths changed; the values moved to reac-pw/fuzz_rate's ASan image A by symbol + offset (ledger provenance/reloc/A-Snp.tsv), the keys kept; it names the map IImgAG.v in place of IImgA.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Import IInst IImgAG.
Import ListNotations.
Open Scope Z_scope.

Definition N_exact_asan : list (Z * Z) := [
  KV 0x21334 0x5185c;
  KV 0x21738 0x51858;
  KV 0x21920 0x42198;
  KV 0x1ae48 0x421e0;
  KV 0x1ae04 0x421e4;
  KV 0x7f000400 0x421c8].

Definition N_sym_asan (k : Z) : Z :=
  match zlookup k N_exact_asan with Some v => v | None => N_sym k end.

Definition N_img_asan : RImg := {| img_segs := rsegs; sym := N_sym_asan |}.
