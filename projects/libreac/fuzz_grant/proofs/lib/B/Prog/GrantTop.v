(* Image B of libreac/fuzz_grant (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e): its
   loaded segments and the two bounds of its image, computed from those segments (the PT_LOADs elf-snapshot reads).
   The walk layer of lib/B/Prog states every image range with IMG_LO_B / IMG_TOP_B and never with a numeral; the two
   value lemmas check the computed bounds against the program headers (lowest PT_LOAD 0x10000, last PT_LOAD
   0x9f3c8 + 0x55ae28 = 0x5fa1f0, page-rounded 0x5fb000). Image A's top is a different number (0x5fa000). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.libreac.fuzz_grant.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

(* The same term as lib/B/GrantTFIBB.v:18's grantsegsB0, restated here so that the
   walk layer's closure holds no top-level file. The two are convertible. *)
Definition grantsegsB0 : list Segment := AsanUbsan.M.loaded_segments.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).
Definition IMG_PAGE : Z := 4096.

(* The lowest segment start, rounded down to a page, and the highest segment end, rounded up to a page. *)
Definition img_lo_of (segs : list Segment) : Z :=
  match segs with
  | [] => 0
  | s :: r => fold_left (fun m t => Z.min m (seg_lo t)) r (seg_lo s) / IMG_PAGE * IMG_PAGE
  end.
Definition img_top_of (segs : list Segment) : Z :=
  (fold_left (fun m t => Z.max m (seg_hi t)) segs 0 + IMG_PAGE - 1) / IMG_PAGE * IMG_PAGE.

Definition IMG_LO_B : Z := img_lo_of grantsegsB0.
Definition IMG_TOP_B : Z := img_top_of grantsegsB0.

Lemma IMG_LO_B_val : IMG_LO_B = 0x10000.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_B_val : IMG_TOP_B = 0x5fb000.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_LO_B_lt_TOP : IMG_LO_B < IMG_TOP_B.
Proof. rewrite IMG_LO_B_val, IMG_TOP_B_val. lia. Qed.

(* ---- image B's initial bytes, read from its segments --------------------------------------------------------- *)
Definition romB8 (a : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (seg_rom grantsegsB0 (Z_to_bv 64 a)).
Definition romB32 (a : Z) : option Z :=
  match romB8 a, romB8 (a + 1), romB8 (a + 2), romB8 (a + 3) with
  | Some b0, Some b1, Some b2, Some b3 => Some (b0 + 256 * (b1 + 256 * (b2 + 256 * b3)))
  | _, _, _, _ => None
  end.
Definition romB64 (a : Z) : option Z :=
  match romB32 a, romB32 (a + 4) with Some lo, Some hi => Some (lo + 2 ^ 32 * hi) | _, _ => None end.

(* ---- image B's registered globals -----------------------------------------------------------------------------
   The 13 descriptors of the array __asan_register_elf_globals registers (asan_globals 0xa1f80..0xa22c0, 64 bytes
   each), as (beginning, size), checked against image B's bytes by computation: POLL, HEAD_ACK, HEAD_MARK, __const.check_groupa.frame, .str.4, GRANT_GROUPB, TMPL_BOX_HB, TMPL_HEADAMP, GRANT_HEAD_ACK, GRANT_HEAD_MARK, JOIN_0013, JOIN_0014, CTRL_FRAMES.
   CTRL_FRAMES (0x9d3e0, 264 bytes) is the control-frame table; its redzone starts at 0x9d4e8. *)
Definition grant_globs_lo : Z := 0xa1f80.
Definition GRANT_GLOBS_B : list (Z * Z) :=
  [(0x20ec0, 18); (0x20f00, 34); (0x20f60, 34); (0x20fc0, 50); (0x21060, 7); (0x21080, 204); (0x21180, 32); (0x211c0, 32); (0x21200, 34); (0x21260, 34); (0x21300, 32); (0x21340, 32); (0x9d3e0, 264)].
Definition globs_ok (lo : Z) (G : list (Z * Z)) : bool :=
  forallb (fun j => let g := nth j G (0, 0) in
    match romB64 (lo + 64 * Z.of_nat j), romB64 (lo + 64 * Z.of_nat j + 8) with
    | Some b, Some n => (b =? fst g) && (n =? snd g)
    | _, _ => false
    end)%bool (seq 0 (length G)).
Lemma grant_globs_check : globs_ok grant_globs_lo GRANT_GLOBS_B = true /\ length GRANT_GLOBS_B = 13%nat /\
  grant_globs_lo + 64 * 13 = 0xa22c0.
Proof. split; [vm_compute; reflexivity | split; reflexivity]. Qed.
