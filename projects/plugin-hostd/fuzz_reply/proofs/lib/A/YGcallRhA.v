(* The A image's discharge of the two Section Hypotheses that a Theorem Labs lane's Reusable/YGcallRh.v states on its dead set DS,
   at the core's per-call dead set DS := YGcfRehidePost.dead_shadow_new (this tree's lib/A copy of the F1 core). This
   file proves nothing: both lemmas are citations of the core's lemmas, which a Theorem Labs lane's F1 core states and proves.
   - DS_not_low (YGcallRh.v Section P, read by free_post_img_presence_rh / free_post_img_presence_null_rh): a dead-set
     byte lies above kLowMemEnd. It is the core's dead_shadow_new_not_low.
   - DS_ceil (YGcallRh.v Section R, read by YCbqRh.ajournal_x_sub_rh and acall_kept_of_journal_x_rh; also the premise
     of W_journal_rh.v's <rule>_rh_of): a dead-set byte lies below alloc_ceiling. It is the core's
     dead_shadow_new_below_ceiling.
   Both are stated in the text of the hypotheses with DS := dead_shadow_new, over the Section's RunCeil instance rc, and
   each citation is at that same rc: dead_shadow_new (through in_app), its zone RZ_cf (through ASAN_CEIL) and
   alloc_ceiling all read that one rc. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost.
Local Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.

(* YGcallRh.v Section P's DS_not_low at DS := dead_shadow_new. *)
Lemma DS_not_low : forall ly S S' a, dead_shadow_new ly S S' a -> kLowMemEnd < a.
Proof. exact (@dead_shadow_new_not_low rc). Qed.

(* YGcallRh.v Section R's DS_ceil at DS := dead_shadow_new. *)
Lemma DS_ceil : forall ly S S' a, dead_shadow_new ly S S' a -> a < YM05.alloc_ceiling.
Proof. exact (@dead_shadow_new_below_ceiling rc). Qed.
End g.
