(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack layout lemmas restated over the launch input ProcInput: pointers from the stack top and AT_EXECFN, the auxv of launch_auxv with the CONFIG_RSEQ entry count, AT_RANDOM placed by block_head_size, and the bound 2101782); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac ArgvEnv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv.

Module DU_Img.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30600_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198144) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 96916)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30730_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30738_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198456) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 97176)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30740_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198464) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 140380)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30748_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198472) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 142572)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30750_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198480) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307a0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198560) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 271400)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403328)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403320)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 198152)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198592) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 198144)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_307c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 198600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403304)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_31b28_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 203560) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_31b50_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 203600) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62510_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402704) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62520_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402720) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62528_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402728) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62770_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 403312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62798_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 403352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_627b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 403376) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End DU_Img.

Module D_Img.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30260_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197216) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 96864)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30390_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30398_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197528) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 97124)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_303a0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197536) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 139452)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_303a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197544) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 141644)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_303b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197552) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30400_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 270472)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30408_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 402400)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30410_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 402392)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30418_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197656) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 197224)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30420_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197664) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 197216)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_30428_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 197672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 402376)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_31788_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 202632) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_317b0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 202672) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62170_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 401776) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62180_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 401792) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62188_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 401800) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_623d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402384) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_623f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_62410_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 402448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End D_Img.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base top av ev execfn) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo)
    (entry uid gid hwcap at_random at_execfn : word) : list word :=
  flat_map (fun e => [fst e; snd e])
    (auxv_entries la ph entry uid gid hwcap at_random at_execfn).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall la ph entry uid gid hwcap ar ae,
  auxv_bytes la ph entry uid gid hwcap ar ae
  = flat_map word_le8 (auxv_words la ph entry uid gid hwcap ar ae).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall la ph entry uid gid hwcap ar ae,
  length (auxv_words la ph entry uid gid hwcap ar ae)
  = (2 * auxv_count (la_rseq la))%nat.
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hwcap ar ae; reflexivity.
Qed.

Section Layout.

  Variable segs : list Segment.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable ph : PhdrInfo.
  Variable entry : word.
  Variable sp brk : word.
  (* the entry draw: ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable rdraw : EntryDraw.

  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* the mapped image: Linux's whole block, from sp to the stack VMA's end *)
  Let bsb := entry_stack_image inp mbase ph entry sp rdraw.
  Let stk := stack_to_mem sp (entry_stack_image inp mbase ph entry sp rdraw).

  Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof.
    unfold bsb.
    exact (bsb_nw v inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_decomp : exists head_tail,
    bsb = (word_le8 (len_word (in_argv inp))
           ++ flat_map word_le8
                (fst (string_addrs
                        (cat_string_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                           (in_execfn inp)) (in_argv inp))))
          ++ word_le8 (Z_to_bv 64 0)
          ++ flat_map word_le8
               (fst (string_addrs
                       (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                          (in_execfn inp)) (in_envp inp)))
          ++ word_le8 (Z_to_bv 64 0)
          ++ auxv_bytes (launch_auxv inp sp mbase) ph entry
               (in_uid inp) (in_gid inp) (in_hwcap inp)
               (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
               (at_execfn_ptr (ed_top rdraw) (in_execfn inp))
          ++ head_tail.
  Proof.
    unfold bsb, entry_stack_image, build_stack_bytes, cat_env_base, cat_string_base.
    cbv zeta.
    rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
    rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma len_argc_argv :
    length (word_le8 (len_word (in_argv inp))
            ++ flat_map word_le8
                 (fst (string_addrs
                         (cat_string_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                            (in_execfn inp)) (in_argv inp))))
    = (8 + 8 * length (in_argv inp))%nat.
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8,
      length_string_addrs_fst. lia.
  Qed.

  Lemma len_envp_ptrs :
    length (flat_map word_le8
              (fst (string_addrs
                      (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                         (in_execfn inp)) (in_envp inp))))
    = (8 * length (in_envp inp))%nat.
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length (in_argv inp))) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                  _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr_k : forall k, (k < length (in_envp inp))%nat ->
    rdn segs stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
    = Some (word_le8 (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                        (in_execfn inp) k)).
  Proof.
    intros k Hk.
    destruct bsb_decomp as [tl E].
    assert (Hk' : (k < length (fst (string_addrs
                     (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                        (in_execfn inp)) (in_envp inp))))%nat)
      by (rewrite length_string_addrs_fst; exact Hk).
    rewrite (flat_map_le8_decomp _ k Hk') in E.
    rewrite <- !app_assoc in E.
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H.
    rewrite !length_flat_map_le8 in H.
    rewrite length_string_addrs_fst in H.
    rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
    rewrite !length_n_to_le_8 in H.
    unfold envp_off, cat_envp_ptr.
    replace (8 + 8 * (length (in_argv inp) + 1) + 8 * k)%nat
      with (8 + (8 * length (in_argv inp) + (8 + 8 * k)))%nat by lia.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_null :
    rdn segs stk
      (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold envp_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
        replace (8 + 8 * (length (in_argv inp) + 1)
                 + 8 * length (in_envp inp))%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_all :
    rdn segs stk (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp)))
        (auxv_size (kb_rseq (in_kernel inp)))
    = Some (auxv_bytes (launch_auxv inp sp mbase) ph entry
              (in_uid inp) (in_gid inp) (in_hwcap inp)
              (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
              (at_execfn_ptr (ed_top rdraw) (in_execfn inp))).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3 ++ p4) mid rest
                      (auxv_size (kb_rseq (in_kernel inp)))) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_auxv_bytes _ _ _ _ _ _ _ _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold auxv_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) _ = _ =>
        replace (8 + 8 * (length (in_argv inp) + 1)
                 + 8 * (length (in_envp inp) + 1))%nat with n by lia
    end.
    exact H.
  Qed.
  Lemma lay_rseq : la_rseq (launch_auxv inp sp mbase) = kb_rseq (in_kernel inp).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_word : forall j,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn segs stk
      (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8%nat
    = Some (word_le8
              (nth j (auxv_words (launch_auxv inp sp mbase) ph entry
                        (in_uid inp) (in_gid inp) (in_hwcap inp)
                        (at_random_ptr sp (kb_rseq (in_kernel inp))
                           (in_argv inp) (in_envp inp))
                        (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                   (Z_to_bv 64 0))).
  Proof.
    intros j Hj.
    rewrite <- nat_to_word_add_merge.
    rewrite (rdn_skipn segs stk (auxv_size (kb_rseq (in_kernel inp)))
               _ _ (8 * j) 8 read_auxv_all)
      by (unfold auxv_size, auxv_count in *;
          destruct (kb_rseq (in_kernel inp)); lia).
    f_equal. rewrite auxv_bytes_words.
    rewrite (flat_map_le8_decomp _ j)
      by (rewrite length_auxv_words, lay_rseq; exact Hj).
    rewrite skipn_app_exact
      by (rewrite length_flat_map_le8, firstn_length_le
            by (rewrite length_auxv_words, lay_rseq; lia); lia).
    apply firstn_app_exact. apply length_n_to_le_8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_random_split : exists pre post,
    bsb = pre ++ at_random_bytes (ed_random rdraw) ++ post
    /\ length pre = (block_head_size (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp) - 16)%nat.
  Proof.
    unfold bsb, entry_stack_image.
    eexists. eexists. split; [apply build_stack_bytes_split_random|].
    unfold block_below_random. cbv zeta.
    rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
    rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
    rewrite !length_app, !repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes.
    cbn [launch_auxv la_rseq].
    unfold block_head_size, block_items. lia.
  Qed.

  Lemma at_random_off : exists off : nat,
    at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
    = sp + nat_to_word off
    /\ off = (block_head_size (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp) - 16)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs stk
           (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
            + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    destruct bsb_random_split as [pre [post [E Hlen]]].
    unfold bsb in E.
    exists (block_head_size (kb_rseq (in_kernel inp))
              (in_argv inp) (in_envp inp) - 16)%nat.
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold block_head_size, block_items, auxv_size, auxv_count.
      pose proof (Nat.mod_upper_bound
                    (length (in_argv inp) + length (in_envp inp) + 3) 2 ltac:(lia)).
      destruct (kb_rseq (in_kernel inp));
        [ replace (8 * (length (in_argv inp) + length (in_envp inp) + 3)
                   + 16 * 29
                   + 8 * ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)
                   + 16 - 16)%nat
            with (8 * ((length (in_argv inp) + length (in_envp inp) + 3)
                       + 58
                       + ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)))%nat
            by lia
        | replace (8 * (length (in_argv inp) + length (in_envp inp) + 3)
                   + 16 * 27
                   + 8 * ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)
                   + 16 - 16)%nat
            with (8 * ((length (in_argv inp) + length (in_envp inp) + 3)
                       + 54
                       + ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)))%nat
            by lia ];
        rewrite Nat2Z.inj_mul; change (Z.of_nat 8) with 8%Z;
        rewrite Z.mul_comm, Z_mod_mult; reflexivity. }
    intros j n Hjn.
    unfold at_random_ptr. rewrite <- Hlen, nat_to_word_add_merge.
    rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
    rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
    pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                  (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                  (firstn n (skipn j (at_random_bytes (ed_random rdraw))))
                  (skipn n (skipn j (at_random_bytes (ed_random rdraw))) ++ post)
                  n) as H.
    assert (Hl : length (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                 = (length pre + j)%nat).
    { rewrite length_app, firstn_length_le; [reflexivity|].
      rewrite length_at_random_bytes. lia. }
    rewrite Hl in H.
    apply H;
      [ rewrite E; rewrite <- !app_assoc; reflexivity
      | rewrite firstn_length_le; [reflexivity|];
        rewrite length_skipn, length_at_random_bytes; lia
      | exact lay_bsb_nw ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2101782)%Z.
  Proof.
    unfold bsb. exact (bsb_bound v inp mbase ph entry sp brk rdraw Hvl Hlau).
  Qed.
  Lemma lay_head_bound :
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
     <= length bsb)%nat.
  Proof.
    unfold bsb, entry_stack_image. rewrite length_build_stack_bytes.
    cbn [launch_auxv la_rseq]. lia.
  Qed.

  Lemma auxv_off_bound :
    (auxv_off (in_argv inp) (in_envp inp)
     + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length bsb)%nat.
  Proof.
    pose proof lay_head_bound.
    unfold auxv_off, block_head_size, block_items in *. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cat_envp_ptr_eq : forall k, (k < length (in_envp inp))%nat ->
    cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k
    = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                          (in_argv inp) (in_envp inp) (in_execfn inp)
                        + total_arg_bytes_nat (in_argv inp)
                        + total_arg_bytes_nat (firstn k (in_envp inp))).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base.
    rewrite (cat_string_base_offset v inp mbase sp brk rdraw Hlau).
    rewrite !nat_to_word_add_merge. f_equal. f_equal. lia.
  Qed.

  Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k (in_envp inp))) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k (in_envp inp)). lia.
  Qed.

  Lemma struct_av_bound :
    (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
       (in_argv inp) (in_envp inp) (in_execfn inp)
     + total_arg_bytes_nat (in_argv inp)
     + total_arg_bytes_nat (in_envp inp)
     <= length bsb)%nat.
  Proof.
    unfold bsb, entry_stack_image. rewrite length_build_stack_bytes.
    unfold cat_string_off, launch_string_bytes.
    cbn [launch_auxv la_rseq]. rewrite !length_flatten_strings. lia.
  Qed.

  Lemma u_cat_envp_ptr : forall k, (k < length (in_envp inp))%nat ->
    bv_unsigned (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k)
    = (bv_unsigned sp
       + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                     (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (in_argv inp)
                   + total_arg_bytes_nat (firstn k (in_envp inp))))%Z.
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof lay_bsb_nw.
    pose proof (total_arg_bytes_firstn_le k (in_envp inp)).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma cat_envp_ptr_nz : forall k, (k < length (in_envp inp))%nat ->
    bv_unsigned (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk.
    unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  Lemma u_cat_argv_ptr : forall k, (k < length (in_argv inp))%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k)
    = (bv_unsigned sp
       + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                     (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (firstn k (in_argv inp))))%Z.
  Proof.
    intros k Hk.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp)
               (in_execfn inp) k Hk),
            (cat_string_base_offset v inp mbase sp brk rdraw Hlau).
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof lay_bsb_nw.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma argv_str_len : forall k, (k < length (in_argv inp))%nat ->
    (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z.
  Proof. intros k Hk. exact (valid_argv_str_len (in_argv inp) k Hva Hk). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
    (bv_unsigned sp
     <= bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)))%Z
    /\ (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)) + 16
        <= bv_unsigned sp + Z.of_nat (length bsb))%Z
    /\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn segs stk
            (Z_to_bv 64 (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                                        (in_argv inp) (in_envp inp))
                         + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    intros Hal.
    destruct at_random_off as [off [Hp [Hoff [Hmod Hrd]]]].
    pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
    pose proof lay_head_bound as Hhead.
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    assert (Hoff16 : (off + 16
                      <= block_head_size (kb_rseq (in_kernel inp))
                           (in_argv inp) (in_envp inp))%nat).
    { rewrite Hoff. unfold block_head_size. lia. }
    assert (Hu : bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                                (in_argv inp) (in_envp inp))
                 = (bv_unsigned sp + Z.of_nat off)%Z).
    { rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
    rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - rewrite Z.add_mod by lia.
      replace (bv_unsigned sp mod 8)%Z with 0%Z.
      2:{ symmetry.
          rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity).
          rewrite Hal. reflexivity. }
      rewrite Hmod. reflexivity.
    - intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
  Qed.

End Layout.
