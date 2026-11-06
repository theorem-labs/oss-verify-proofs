(* Modified by Theorem Labs, 2026-10: derived forms stated by the relocated ASan core (CORE-PREP.md, img_top patch),
   split out of YImgTop.v so that file stays as -pa has it: the shadow of the image top (IMG_TOP / 8) and its 4 KiB
   page index (IMG_TOP / 4096). Notations for the same reason as YImgTop's; the checks tie each numeral to IMG_TOP. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
Notation IMG_TOP_D8 := 781312%Z (only parsing).
Notation IMG_TOP_PG := 1526%Z (only parsing).
Lemma IMG_TOP_D8_ok : (IMG_TOP / 8 = IMG_TOP_D8)%Z. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_PG_ok : (IMG_TOP / 4096 = IMG_TOP_PG)%Z. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_page : (IMG_TOP mod 4096 = 0)%Z. Proof. vm_compute. reflexivity. Qed.
