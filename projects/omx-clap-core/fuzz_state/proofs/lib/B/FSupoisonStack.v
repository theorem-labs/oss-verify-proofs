(* The image-B twin of the image lemmas of lib/A/FSupoisonStack.v (POISON-U lane, a Theorem Labs lane,
   a working branch d37bcb51c52): fsw_ARU_img_end_fs and fsw_ARU_rodata_ra, the two lemmas there that
   are stated over image A (AB1v.tfibsegs, AF0x.TFIB_IMG_END, FSupoisonARX.fs_img_end).  Every other lemma of
   lib/A/FSupoisonStack.v is generic in its segments and asyms (Section s: Variable segs, Variable B) and is
   imported from there as it is.  The two are stated here over fuzz_state's image B (fuzz_state.asan-ubsan,
   sha256 5ac5ce0954f8...) under the SAME names, with B's segments (lib/B/YB1v.v tfibsegs), B's image end
   (lib/B/YF0x.v TFIB_IMG_END = 0x5fd000) and B's ledger fact (lib/B/FSupoisonARX.v fs_img_end).
   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison.
(* the generic stack / image-shadow lemmas (fsw_ARU_img_ra and the rest) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB1v YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonARX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* lib/B's FSupoisonARX, named by its full path: lib/A has a module of the same short name. *)
Module BARX := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonARX.

(* fs image B: the image's end is at or above TFIB_IMG_END = 0x5fd000 (lib/B FSupoisonARX.fs_img_end, from
   ALedger.al_img), so the premise on the image's end becomes a literal bound. AR is ARU's first conjunct. *)
Lemma fsw_ARU_img_end_fs : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B ly S U W mem md,
  FSupoison.ARU YB1v.tfibsegs B ly S U W mem md -> YF0x.TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof. intros fx rc B ly S U W mem md (HAR & _). exact (BARX.fs_img_end B ly S W (unpoison U mem) md HAR). Qed.
Lemma fsw_ARU_rodata_ra : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B ly S U W mem md H lo n,
  FSupoison.ARU YB1v.tfibsegs B ly S U W mem md -> 0 <= lo -> lo + n + 8 <= YF0x.TFIB_IMG_END ->
  range_addressable (aview YB1v.tfibsegs H (unpoison U mem)) SHADOW_OFF lo n <->
  range_addressable (aview YB1v.tfibsegs H mem) SHADOW_OFF lo n.
Proof.
intros fx rc B ly S U W mem md H lo n HU Hlo HE. pose proof (fsw_ARU_img_end_fs B ly S U W mem md HU) as IE.
unfold YF0x.TFIB_IMG_END in *. apply (fsw_ARU_img_ra YB1v.tfibsegs B ly S U W mem md H lo n HU); lia.
Qed.
