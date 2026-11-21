(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag and the new auxv layout). *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxEntryRel AxEntry AsanWEb.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxEntryS AxEntryFacts.
(* AsanWEbLoad supplies AUX_OFF, which FL2 uses at :18-19.  Requiring AxEntryFacts does
   not bring it: that file Requires (not Exports) AsanWEbLoad for the same reason, so
   the name does not travel.  Measured as "The reference AUX_OFF was not found in the
   current environment" at :18 chars 21-28, identically in all three trees
   (one farm round each). *)
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWEbLoad.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition FL2 (r : bool) (blo bhi : Z) : list (lin * (Z * Z)) :=
  FL r blo bhi ++ [((AUX_OFF r + 10, sp_terms ++ [(v_argc, 8); (v_envc, 8); (v_g, 1); (lenvar 0, 1); (lenvar 1, 1)]),
                  (140735340871680 + AUX_OFF r + 26, 140737488355328))].

Lemma total_first2 (L : list (list byte)) : L <> [] ->
  Z.of_nat (length (nth 0 L [])) + Z.of_nat (length (nth 1 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros H. destruct L as [|a [|b L]]; [congruence| |]; unfold total_arg_bytes; cbn [fold_right nth length].
  - lia.
  - pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
Qed.

Section Sat.
Variables (segs : list Segment) (inp : ProcInput) (sp brk0 mbase pcw : word) (draw : EntryDraw) (blo bhi : Z).
Hypothesis Hinp : valid_input inp.
Hypothesis Hcw : launch_cache_words (in_kernel inp) = launch_cache_words default_kernel.
Hypothesis Hmss : min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp).
Hypothesis Hsp : valid_sp_va Sv48 sp.
Hypothesis Hl : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hblo : blo <= reserved_top (segments_reserved segs) / 4096.
Hypothesis Hbhi : (reserved_top (segments_reserved segs) + brk_aslr_max) / 4096 <= bhi.

Notation ρ := (enc_b inp sp mbase pcw draw brk0).
Notation av := (in_argv inp).
Let r := kb_rseq (in_kernel inp).

Theorem FL2_sat : Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) (FL2 r blo bhi).
Proof.
  apply Forall_app. split; [exact (FL_sat segs inp sp brk0 mbase pcw draw blo bhi Hinp Hcw Hmss Hsp Hl Hbrk Hblo Hbhi)|].
  constructor; [|constructor]. cbn [fst snd].
  pose proof (fs_facts inp sp brk0 mbase pcw draw Hinp Hcw Hmss Hsp Hl) as HF.
  pose proof (fs_spval inp sp brk0 mbase pcw draw Hinp Hcw Hl) as Hspv.
  pose proof HF as (Hc & He & Ha & _ & Hta & Hte & Hpar & Hg & (Hxl & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2).
  assert (EA : dec_argv ρ = in_argv inp) by (unfold enc_b; apply dec_argv_enc; exact (proj1 Hinp)).
  assert (EE : dec_envp ρ = in_envp inp) by (unfold enc_b; apply dec_envp_enc; exact (proj1 (proj2 Hinp))).
  rewrite EA in Hta. rewrite EE in Hte. pose proof (total_arg_bytes_nonneg (in_envp inp)).
  assert (EL0 : ρ (lenvar 0) = Z.of_nat (length (nth 0 av [])))
    by (unfold enc_b; rewrite (enc_lenvar inp sp mbase pcw draw _ 0) by lia; reflexivity).
  assert (EL1 : ρ (lenvar 1) = Z.of_nat (length (nth 1 av [])))
    by (unfold enc_b; rewrite (enc_lenvar inp sp mbase pcw draw _ 1) by lia; reflexivity).
  assert (EAc : ρ v_argc = Z.of_nat (length av)) by reflexivity.
  pose proof (total_first2 av ltac:(intros E; rewrite E in EAc; cbn in EAc; lia)) as HT2.
  unfold dec_top, str_off in Hs2. rewrite Hspv in Hs1, Hs2.
  (* FL2 (:23-24) states its span with the Definition `AUX_OFF r`, while `unfold
     dec_top, str_off` above leaves Hs2 carrying the unfolded `24 + Z.of_nat
     (auxv_size r)`.  lia sees two atoms and reports "Cannot find witness"
     (chars 96-99).  The unfold
     has to come AFTER the rewrites below, not before it: until `cbn [teval]` has run,
     the goal still carries FL2 folded and AUX_OFF does not occur in it to unfold. *)
  unfold sp_window_lo, sp_window_hi in *.
  unfold leval; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. rewrite Hspv.
  (* `r` here is this section's Let (:48, kb_rseq (in_kernel inp)), while fs_facts
     states Hs2 over kb_rseq (in_kernel inp) written out.  After unfolding AUX_OFF the
     two sides read `Z.of_nat (auxv_size r)` and `Z.of_nat (auxv_size (kb_rseq
     (in_kernel inp)))`, which lia still counts as two atoms -- the second "Cannot find
     witness" (:75 chars 23-26).  Unfolding the Let makes
     them one term. *)
  unfold AUX_OFF, r in *. lia.
Qed.

End Sat.
