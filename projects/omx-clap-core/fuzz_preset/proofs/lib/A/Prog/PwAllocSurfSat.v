(* Theorem Labs, 2026-10: the INSTANCE WITNESS (fuzz_preset unit ruling, c-omx-hpreset 16:45Z) for PwAllocSurf.v's one image
   premise PST_unowned (PwAllocSurf.v:774): it HOLDS at the real image-A' (#102) instance, B := AD2l.TfibB (the A'
   asyms record: as_owned_static = AF0m.v's Tfib_owned_static, generated from the #102 twin bff8519bbe3e), PIA :=
   prh_img_A (lib/A/PRH_Img.v, the #102 table). By computation: every one of the seven harness static ranges in
   prh_pst is disjoint from every range in Tfib_owned_static. Relocated 2026-10-29 from the old-pin file
   (origin/cold/h-w6rep-2-allocsurf c47ea1638ed6); the statement and proof are unchanged, the instance under them is
   A'. Print Assumptions PST_unowned_at_TfibB: closed under the global context. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img AD2l.
Import ListNotations.
Local Open Scope Z_scope.

Definition sat_dj (r s : Z * Z) : bool := (fst r + snd r <=? fst s) || (fst s + snd s <=? fst r).

Lemma sat_dj_ok : forall r s a, sat_dj r s = true -> in_zr a r -> ~ in_zr a s.
Proof.
intros r s a H Hr Hs. unfold sat_dj, in_zr in *. apply orb_true_iff in H.
destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma sat_disjoint : forall (P S : list (Z * Z)), forallb (fun r => forallb (sat_dj r) S) P = true ->
  forall a, Exists (in_zr a) P -> ~ Exists (in_zr a) S.
Proof.
intros P S H a HP HS. apply Exists_exists in HP as [r [Hr Har]]. apply Exists_exists in HS as [s [Hs Has]].
rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
exact (sat_dj_ok r s a (H s Hs) Har Has).
Qed.

(* PST_unowned, PwAllocSurf.v:774, at the real instance *)
Lemma PST_unowned_at_TfibB : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ Exists (in_zr a) (as_owned_static AD2l.TfibB).
Proof. apply sat_disjoint. vm_compute. reflexivity. Qed.
