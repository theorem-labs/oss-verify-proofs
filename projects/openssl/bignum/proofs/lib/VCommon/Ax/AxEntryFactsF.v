(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxEntryRel AxEntry AsanWEb.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxEntryS AxEntryFacts.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition FL2 (blo bhi : Z) : list (lin * (Z * Z)) :=
  FL blo bhi ++ [((201, sp_terms ++ [(v_argc, 8); (v_envc, 8); (lenvar 0, 1); (lenvar 1, 1)]), (140733193388233, 140737488355328))].

Lemma total_first2 (L : list (list byte)) : L <> [] ->
  Z.of_nat (length (nth 0 L [])) + Z.of_nat (length (nth 1 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros H. destruct L as [|a [|b L]]; [congruence| |]; unfold total_arg_bytes; cbn [fold_right nth length].
  - lia.
  - pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
Qed.

Section Sat.
Variables (segs : list Segment) (inp : ProcInput) (sp brk0 : word) (draw : EntryDraw) (blo bhi : Z).
Hypothesis Hinp : valid_input inp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hblo : blo <= reserved_top (segments_reserved segs) / 4096.
Hypothesis Hbhi : (reserved_top (segments_reserved segs) + brk_aslr_max) / 4096 <= bhi.

Notation ρ := (enc_b inp sp draw brk0).
Notation av := (in_argv inp).
Notation ev := (in_envp inp).

Theorem FL2_sat : Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) (FL2 blo bhi).
Proof.
  apply Forall_app. split; [exact (FL_sat segs inp sp brk0 draw blo bhi Hinp Hsp Hbrk Hfit Hblo Hbhi)|].
  constructor; [|constructor]. cbn [fst snd].
  pose proof (fs_sp inp sp Hsp Hfit) as (Hs1 & Hs2 & Hs3). pose proof (fs_span segs inp) as Hspan.
  pose proof (fs_spval inp sp brk0 draw Hsp Hfit) as Hspv.
  pose proof (fs_argv inp Hinp) as ([Ha1 Ha2] & Ha3 & _). pose proof (fs_envp inp Hinp) as [He1 He2].
  pose proof (total_arg_bytes_nonneg av). pose proof (total_arg_bytes_nonneg ev).
  assert (EL0 : ρ (lenvar 0) = Z.of_nat (length (nth 0 av []))) by (unfold enc_b; rewrite enc_lenvar by lia; reflexivity).
  assert (EL1 : ρ (lenvar 1) = Z.of_nat (length (nth 1 av []))) by (unfold enc_b; rewrite enc_lenvar by lia; reflexivity).
  pose proof (total_first2 av ltac:(intros E; rewrite E in Ha1; cbn in Ha1; lia)) as HT2.
  assert (EAc : ρ v_argc = Z.of_nat (length av)) by reflexivity.
  assert (EEc : ρ v_envc = Z.of_nat (length ev)) by reflexivity.
  unfold sp_window_lo, sp_window_hi in *.
  unfold leval; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. lia.
Qed.

End Sat.
