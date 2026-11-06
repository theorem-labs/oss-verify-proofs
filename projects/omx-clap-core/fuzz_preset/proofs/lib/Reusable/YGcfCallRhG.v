(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfCallRhG.v at commit 5034424e29db (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t + pf_cells_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* The cf call post under the re-hide, generic in the dead set of one call. IMAGE-FREE: no lib/A or lib/B file is
   Required, so a unit's Reusable layer and the core both state their posts through it.
   DS : alayout -> astate -> astate -> Z -> Prop is the set the call from S to S' may hide, read with the call's pre
   layout and both states. After a free that recycles a secondary, YG0dcf.acall_post_cf changes in two conjuncts: the
   hidden set grows only inside DS ly S S' (wle_in), and the view frame has the last antecedent ~ DS ly S S' a.
   YGcfRehidePost.acall_post_cf_rh is this post at DS := dead_shadow_new. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Variable DS : alayout -> astate -> astate -> Z -> Prop.

(* YG0dcf.v acall_post_cf with wle -> wle_in segs (DS ly S S') and the frame's last antecedent ~ DS ly S S' a. *)
Definition acall_post_cf_rh (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARcf segs B ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
wle_in segs (DS ly S S') W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
~ DS ly S S' a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* A call that re-hides nothing gives the twin from the released post. *)
Lemma acall_post_cf_rh_of : forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
acall_post_cf_rh stk ly S Hp W regs mem md E ly' S' W' regs' mem' md'.
Proof.
intros stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7).
split; [exact H1|]. split; [exact H2|].
split; [intros a Ha; left; exact (H3 a Ha)|].
split; [exact H4|]. split; [exact H5|]. split; [|exact H7].
intros a A1 A2 A3 A4 A5 _. exact (H6 a A1 A2 A3 A4 A5).
Qed.
End G.
