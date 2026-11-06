(* libreac/fuzz_identity's image range, one named place for every file that states it.
   Both pinned ASan images (index/binaries.tsv: fuzz_identity.asan c954b804..., fuzz_identity.asan-ubsan baf1a4d0...)
   load from 0x10000; their last loaded segments end at 0x5f9830 (asan) and 0x5f9b30 (asan-ubsan), which both round
   up to the page 0x5fa000. The checks against each image's segment list are ident_img_range / ident_img_cover
   (lib/A/Prog/IdentImg.v) and identb_img_range / identb_img_cover (lib/B/Prog/IdentBImg.v), which state these names.
   Notations, not definitions, so that lia and vm_compute see the numerals in every proof that uses them. *)
From Stdlib Require Import ZArith.
Notation IMG_LO := 0x10000%Z (only parsing).
Notation IMG_TOP := 0x5fa000%Z (only parsing).
(* The image top divided by 8 (its shadow offset), as the runtime walks state it. *)
Notation IMG_TOP_SH8 := 783360%Z (only parsing).
Lemma img_top_sh8 : (IMG_TOP / 8)%Z = IMG_TOP_SH8. Proof. reflexivity. Qed.
