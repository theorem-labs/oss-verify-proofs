(* Modified by Theorem Labs, 2026-10: the concrete list of registered globals, in the form of
   proofs/libreac/fuzz_identity/lib/A/Prog/IdentEntryLink.v:150-168 (origin/ossv/recipes 4b6f0df50aa7: IDENT_GLOBS and
   globs_In_b), for libdiginet/fuzz_codec's ASan build (image A). *)
(* The registered globals of fuzz_codec.asan (sha256 7d470194ffdb...): the (beg, size) of each of the 40 descriptors of
   its asan_globals section (0xa23c0, 64 bytes each), in section order, read with pyelftools from the image's own bytes.
   The same 40 (beg, size, size_with_redzone) words are the descriptor cells z8 (ANum (0xa23c0 + 64 i)) /
   (+ 8) / (+ 16) of lib/A/AF0m.v's Tfib_const_abs. Row i, by the unstripped twin's symbol at beg:
     0 LLVMFuzzerTestOneInput.DESK, 1-31 the literals .str, .str.2, .str.4 .. .str.32 of one compilation unit,
     32-33 the literals .str, .str.1 of a second one, 34 switch.table.diginet_seg7, 35 LLVMFuzzerTestOneInput.SPEC_DESK, 36 SPEC_C24,
     37 SPEC_PC, 38 owed_seg7.GLYPH, 39 personalities.
   This is the list G of the walks' `globs_marked G` premise (lib/A/Prog/CodecRo.v); the membership facts a walk takes
   are proved from it by computation (globs_In_b), so only the start-up certificate that the runtime marks each of
   them (lib/A/CodecStartupFacts.v) stays a premise. *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition CODEC_GLOBS : list (Z * Z) :=
[(0x20f40, 12); (0x20f60, 9); (0x20f80, 9); (0x20fa0, 8); (0x20fc0, 10); (0x20fe0, 1); (0x21000, 7);
 (0x21020, 3); (0x21040, 6); (0x21060, 6); (0x21080, 5); (0x210a0, 6); (0x210c0, 7); (0x210e0, 4);
 (0x21100, 8); (0x21120, 7); (0x21140, 7); (0x21160, 6); (0x21180, 5); (0x211a0, 6); (0x211c0, 6);
 (0x211e0, 5); (0x21200, 6); (0x21220, 5); (0x21240, 5); (0x21260, 4); (0x21280, 5); (0x212a0, 6);
 (0x212c0, 3); (0x212e0, 6); (0x21300, 6); (0x21320, 2); (0x21360, 9); (0x21380, 9); (0x213a0, 364);
 (0x9d660, 24); (0x9d6a0, 16); (0x9d6c0, 16); (0x9d6e0, 464); (0x9d920, 48)].

Lemma codec_globs_length : length CODEC_GLOBS = 40%nat.
Proof. reflexivity. Qed.

Lemma globs_In_b : forall a n l, existsb (fun p => (fst p =? a) && (snd p =? n)) l = true -> In (a, n) l.
Proof.
intros a n l H. apply existsb_exists in H as ((x & y) & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
Qed.

(* The tables the own functions read (rows 0 and 34-39). *)
Lemma cg_DESK : In (0x20f40, 12) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SEG7 : In (0x213a0, 364) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_DESK : In (0x9d660, 24) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_C24 : In (0x9d6a0, 16) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_SPEC_PC : In (0x9d6c0, 16) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_GLYPH : In (0x9d6e0, 464) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
Lemma cg_PERS : In (0x9d920, 48) CODEC_GLOBS.
Proof. apply globs_In_b. vm_compute. reflexivity. Qed.
