From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require ACej.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The allocation-trace carrier of image A: the fixed traces of ACej.v (universe.py --carrier univ) and ONE wild prefix.
   The malloc call of text_of at 0x87fec records a trace whose third element is not fixed by the image: text_of keeps
   its second argument in s0 (0x87e04 `mv s0, a1`), and its callers pass a result slot of LLVMFuzzerTestOneInput's
   frame (a1 = s1 + 0x130 at 0x82e20 / 0x837d4, s1 + 0x128 at 0x82e30), so the fast unwinder takes the word below that
   slot (the bytes left of the input, or an earlier text_of result) as a return address when it is 4096 or more
   (UnwindFast 0x74b78, the test at 0x74c40). The stored trace is [0x5436c; 0x87ff0] followed by any tail, so the prefix
   [0x5436c; 0x87ff0] is wild (route (ii) of the trace-universe decision: ACej.v stays the tool's output, this file
   adds the wild prefix).
   The two numerals, each read from the image (proofs/reac-pw/fuzz_link/provenance/evidence/startgen/acej-wild-listing.txt):
   - 0x5436c, the trace start of malloc: the return address of the call of __sanitizer::StackTrace::GetCurrentPc
     (0x74b70) at 0x54368 in ___interceptor_malloc (acej-wild-listing.txt:17-18); F_getpc_call / D_getpc_call below.
   - 0x87ff0, the return address of text_of's call 0x87fec of __interceptor_trampoline_malloc 0x540cc
     (acej-wild-listing.txt:22), whose one instruction jumps to ___interceptor_malloc 0x542a4 (acej-wild-listing.txt:4);
     F_text_of_call / D_text_of_call and F_trampoline / D_trampoline below. *)

Definition Tfib_wild : list (list Z) := [[0x5436c; 0x87ff0]].
Definition Tfib_univ : Univ := univ_of ACej.Tfib_universe Tfib_wild.

Lemma Tfib_univ_fix : u_fix Tfib_univ = ACej.Tfib_universe.
Proof. reflexivity. Qed.
Lemma Tfib_univ_wild : u_wild Tfib_univ = [[0x5436c; 0x87ff0]].
Proof. reflexivity. Qed.
Lemma Tfib_univ_wmax : u_wmax Tfib_univ = 4064%nat.
Proof. vm_compute. reflexivity. Qed.
(* universe_ok reads u_fix and u_wmax only; univ_of's u_wmax does not depend on the wild list *)
Lemma Tfib_univ_ok : universe_ok Tfib_univ.
Proof. exact ACej.Tfib_universe_ok. Qed.
(* the fixed trace [0x5436c; 0x87ff0] (the walk ends at the first record) is a fixed row and also the wild prefix *)
Lemma Tfib_univ_wild_fixed : In [0x5436c; 0x87ff0] (u_fix Tfib_univ).
Proof. rewrite Tfib_univ_fix. apply ACej.memZL_In. vm_compute. reflexivity. Qed.

(* The image ties of the two numerals. *)
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
(* 0x54368: jal ra, +0x20808 (to GetCurrentPc 0x74b70); its return address is 0x5436c *)
Definition W_getpc_call : bv 32 := 0x009200ef.
Lemma F_getpc_call : fetch_word Asan.M.loaded_segments (0x54368 : word) = Some W_getpc_call.
Proof. vm_refl. Qed.
Lemma D_getpc_call : decode_any W_getpc_call = Some (Jal 1 133128, 4%Z).
Proof. vm_refl. Qed.
(* 0x87fec: jal ra, -0x33f20 (to the malloc trampoline 0x540cc); its return address is 0x87ff0 *)
Definition W_text_of_call : bv 32 := 0x8e0cc0ef.
Lemma F_text_of_call : fetch_word Asan.M.loaded_segments (0x87fec : word) = Some W_text_of_call.
Proof. vm_refl. Qed.
Lemma D_text_of_call : decode_any W_text_of_call = Some (Jal 1 1884384, 4%Z).
Proof. vm_refl. Qed.
(* 0x540cc: j +0x1d8 (to ___interceptor_malloc 0x542a4) *)
Definition W_trampoline : bv 32 := 0x1d80006f.
Lemma F_trampoline : fetch_word Asan.M.loaded_segments (0x540cc : word) = Some W_trampoline.
Proof. vm_refl. Qed.
Lemma D_trampoline : decode_any W_trampoline = Some (Jal 0 472, 4%Z).
Proof. vm_refl. Qed.
Close Scope bv_scope.
(* the targets and return addresses, with the 21-bit offsets read as signed *)
Lemma wild_prefix_addresses :
  0x54368 + 133128 = 0x74b70 /\ 0x54368 + 4 = 0x5436c /\
  0x87fec + (1884384 - 2 ^ 21) = 0x540cc /\ 0x87fec + 4 = 0x87ff0 /\
  0x540cc + 472 = 0x542a4.
Proof. lia. Qed.
