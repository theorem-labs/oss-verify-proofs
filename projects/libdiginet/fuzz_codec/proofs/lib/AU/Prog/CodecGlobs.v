(* Modified by Theorem Labs, 2026-10: the concrete list of registered globals, in the form of
   proofs/libreac/fuzz_identity/lib/A/Prog/IdentEntryLink.v:150-168 (origin/ossv/recipes 4b6f0df50aa7: IDENT_GLOBS and
   globs_In_b), for libdiginet/fuzz_codec's ASan + UBSan build (image B). *)
(* The registered globals of fuzz_codec.asan-ubsan (sha256 73109e32e77b...): the (beg, size) of each of the 40
   descriptors of its asan_globals section (0xa2ce0, 64 bytes each), in section order, read with pyelftools from the
   image's own bytes. The same 40 (beg, size, size_with_redzone) words are the descriptor cells
   z8 (ANum (0xa2ce0 + 64 i)) / (+ 8) / (+ 16) of the image's start-up file YF0m.v's Tfib_const_abs. Row i, by the
   unstripped twin's symbol at beg:
     0 LLVMFuzzerTestOneInput.DESK, 1-31 the literals .str, .str.2, .str.4 .. .str.6, .str.8 .. .str.33 of one
     compilation unit, 32-33 the literals .str, .str.1 of a second one, 34 switch.table.diginet_seg7,
     35 LLVMFuzzerTestOneInput.SPEC_DESK, 36 SPEC_C24, 37 SPEC_PC, 38 owed_seg7.GLYPH, 39 personalities.
   The sizes are image A's, row for row (lib/A/Prog/CodecGlobs.v); the addresses are B's. This is the list G of the
   walks' `globs_marked G` premise (lib/AU/Prog/CodecRo.v); only the start-up certificate that the runtime marks each
   of them (lib/AU/CodecStartupFacts.v) stays a premise. *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition CODEC_GLOBS : list (Z * Z) :=
[(0x20fa0, 12); (0x20fc0, 9); (0x20fe0, 9); (0x21000, 8); (0x21020, 10); (0x21040, 1); (0x21060, 7);
 (0x21080, 3); (0x210a0, 6); (0x210c0, 6); (0x210e0, 5); (0x21100, 6); (0x21120, 7); (0x21140, 4);
 (0x21160, 8); (0x21180, 7); (0x211a0, 7); (0x211c0, 6); (0x211e0, 5); (0x21200, 6); (0x21220, 6);
 (0x21240, 5); (0x21260, 6); (0x21280, 5); (0x212a0, 5); (0x212c0, 4); (0x212e0, 5); (0x21300, 6);
 (0x21320, 3); (0x21340, 6); (0x21360, 6); (0x21380, 2); (0x213c0, 9); (0x213e0, 9); (0x21400, 364);
 (0x9df80, 24); (0x9dfc0, 16); (0x9dfe0, 16); (0x9e000, 464); (0x9e240, 48)].

Lemma codec_globs_length : length CODEC_GLOBS = 40%nat.
Proof. reflexivity. Qed.

Lemma globs_In_b : forall a n l, existsb (fun p => (fst p =? a) && (snd p =? n)) l = true -> In (a, n) l.
Proof.
intros a n l H. apply existsb_exists in H as ((x & y) & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
Qed.

(* The tables the own functions read (rows 0 and 34-39). *)
Lemma cg_DESK : In (0x20fa0, 12) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SEG7 : In (0x21400, 364) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_DESK : In (0x9df80, 24) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_C24 : In (0x9dfc0, 16) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_PC : In (0x9dfe0, 16) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_GLYPH : In (0x9e000, 464) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_PERS : In (0x9e240, 48) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
