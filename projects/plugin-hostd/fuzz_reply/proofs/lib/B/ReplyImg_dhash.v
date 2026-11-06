From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
Open Scope Z_scope.

(* dhash_img at reply B (REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record) row img-dhash-B; CF-UNIT-HYPS.md:45 (sha256 77b3f94c95d2; internal record)). The cf layer takes the
   depot hash field as the witness-only premise `forall t, as_dhash B t = <unit dhash> t` of depot_spec_a / depot_spec_d
   (cgif: YGcfInstF1Wcgif.v:131 / :135, with B := its instance). At reply B the instance is TfibB (lib/B/YD2l.v:15),
   whose field is `as_dhash := tfib_dhash` (lib/B/YD2l.v:33): the image-free hash of lib/Reusable/YF0p.v:14. So the
   premise holds by computation, with no image data and no start-up fact. Stem `dhash_img`, as the A twin's
   (a Theorem Labs lane, row img-dhash-A: lib/A/ReplyImg_dhash.v dhash_img_A), so lane W's A -> B relocation maps it by name. *)
Lemma dhash_img_B : forall t : list Z, as_dhash TfibB t = tfib_dhash t.
Proof. reflexivity. Qed.
