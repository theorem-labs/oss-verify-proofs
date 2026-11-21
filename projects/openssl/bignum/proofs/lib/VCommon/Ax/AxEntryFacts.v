(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag and the new auxv layout). *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxEntryRel AxEntry AsanWEb.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxEntryS.
(* AsanWEbLoad supplies AUX_OFF, which FL uses at :31-34.  ct and bndiv both omit this
   Require and so cannot compile this file at any revision; their farm rounds never
   reached it (ct stops at Spec/KStep.v, bndiv at VCommon/Ax/AxGrant.v).  Fault class
   three of the same spread: a name used without the Require that provides it. *)
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWEbLoad.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* The entry store's box facts over the 08b1429 block: the sp digits, the brk page, the
   launch's draws and counts, the gap bit and pad, and two address bounds (the end of
   the AT_RANDOM bytes, and argv[1]'s start plus the 9 bytes above the strings). *)
Definition FL (r : bool) (blo bhi : Z) : list (lin * (Z * Z)) :=
  [ (lvar v_x0 1, (0, 3)); (lvar v_x1 1, (0, 63)); (lvar v_x2 1, (0, 7)); (lvar v_x3 1, (4294901760, 4294967296));
    ((0, sp_terms), (140735340871680, 140737488355328));
    (lvar v_b 1, (blo, bhi));
    (lvar v_r0 1, (0, 18446744073709551615)); (lvar v_r1 1, (0, 18446744073709551615));
    (lvar v_hw 1, (4397, 2101549)); (lvar v_uid 1, (0, 4294967295)); (lvar v_gid 1, (0, 4294967295));
    (lvar v_argc 1, (1, 1024)); (lvar v_envc 1, (0, 256));
    (lvar v_ta 1, (1, 2097152)); (lvar v_te 1, (0, 131072));
    (lvar (lenvar 0) 1, (0, 131071)); (lvar (lenvar 1) 1, (0, 131071));
    (lvar v_par 1, (0, 1)); (lvar v_g 1, (16, 4134)); (lvar v_xl 1, (0, 4114)); (lvar v_mss 1, (1088, 1664));
    (lvar v_ent 1, (0, 18446744073709551615)); (lvar v_vd 1, (0, 18446744073709551615));
    ((AUX_OFF r + 16, sp_terms ++ [(v_argc, 8); (v_envc, 8); (v_par, 8)]),
     (140735340871680 + AUX_OFF r + 16, 140737488355328));
    ((AUX_OFF r + 10, sp_terms ++ [(v_argc, 8); (v_envc, 8); (v_g, 1); (lenvar 0, 1)]),
     (140735340871680 + AUX_OFF r + 26, 140737488355328));
    ((0, [(v_par, -8); (v_g, 1)]), (16, 4126));
    ((0, [(v_ta, 1); (lenvar 0, -1)]), (1, 2097152)) ].

Definition s0_usage (r : bool) (blo bhi : Z) : store := shole (entry_store (FL r blo bhi)) (lvar v_argc 1) 1 3.

Lemma teval_app' (ρ : valuation) (a b : terms) : teval ρ (a ++ b) = teval ρ a + teval ρ b.
Proof. induction a as [|[x k] a IH]; cbn [app teval]; [lia | rewrite IH; lia]. Qed.

Lemma leval_lvar1 (ρ : valuation) (x : int) : leval ρ (lvar x 1) = ρ x.
Proof. unfold leval, lvar. cbn [fst snd teval]. lia. Qed.

Lemma total_first (L : list (list byte)) : L <> [] -> Z.of_nat (length (nth 0 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros H. destruct L as [|a L]; [congruence|]. unfold total_arg_bytes; cbn [fold_right nth].
  pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
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

Lemma fs_facts : eb_facts r ρ.
Proof using Hinp Hcw Hmss Hsp Hl.
  unfold enc_b. exact (eb_facts_enc inp sp mbase pcw brk0 draw _ Hinp Hcw Hmss Hl Hsp).
Qed.

Lemma fs_spval : sp_val ρ = bv_unsigned sp.
Proof using Hinp Hcw Hl. unfold enc_b. exact (ei_spval inp sp mbase pcw brk0 draw _ Hinp Hcw Hl). Qed.

Lemma fs_brk : blo <= ρ v_b <= bhi.
Proof using Hbrk Hblo Hbhi.
  rewrite enc_b_vb. destruct Hbrk as (B1 & B2 & B3). unfold page_size in B3.
  split.
  - apply (Z.le_trans _ _ _ Hblo). apply Z.div_le_mono; lia.
  - apply (Z.le_trans _ ((reserved_top (segments_reserved segs) + brk_aslr_max) / 4096)); [apply Z.div_le_mono; lia | exact Hbhi].
Qed.

Lemma fs_len0 : ρ (lenvar 0) + 1 <= ρ v_ta.
(* `segs` is in the closure through fs_facts; -vos never checks a `Proof using` clause,
   so this was only reachable once the proofs above it compiled. *)
Proof using Hinp Hcw Hmss Hsp Hl segs.
  pose proof fs_facts as HF. pose proof (facts_argc r (mkPhdrInfo 0 0 0) ρ HF). pose proof (len_av r (mkPhdrInfo 0 0 0) ρ HF). pose proof (len_k r (mkPhdrInfo 0 0 0) ρ HF 0 ltac:(lia)) as L0.
  destruct HF as (_ & _ & _ & _ & Ht & _). rewrite Ht. change (Z.to_nat 0) with 0%nat in L0. rewrite <- L0.
  apply total_first. intros E. rewrite E in *. cbn in *. lia.
Qed.

Theorem FL_sat : Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) (FL r blo bhi).
Proof.
  pose proof fs_facts as HF. pose proof fs_spval as Hspv. pose proof fs_brk as Hb. pose proof fs_len0 as HL0.
  (* the 17th conjunct is the v_mss RANGE; it must not shadow the section's Hmss, which is
     the pinned-field equation line 114 rewrites with.  ct and bndiv both name it Hmss here
     and so cannot compile this file either. *)
  pose proof HF as (Hc & He & Ha & Hv & Hta & Hte & Hpar & Hg & (Hxl & _) & Hr0 & Hr1 & Hu & Hh & Hgid & Hent & Hvd & Hmssrng & Hs1 & Hs2).
  pose proof (Ha 0 ltac:(lia)) as [HL0r _].
  assert (Eac : ρ v_argc = Z.of_nat (length av)) by reflexivity.
  assert (El1 : ρ (lenvar 1) = Z.of_nat (length (nth 1 av [])))
    by (unfold enc_b; rewrite (enc_lenvar inp sp mbase pcw draw _ 1) by lia; reflexivity).
  assert (HL1r : 0 <= ρ (lenvar 1) <= 131071).
  { destruct (Z.lt_ge_cases 1 (ρ v_argc)) as [H2|H2]; [exact (proj1 (Ha 1 ltac:(lia)))|].
    rewrite El1, nth_overflow by lia. cbn. lia. }
  assert (EA : dec_argv ρ = in_argv inp) by (unfold enc_b; apply dec_argv_enc; exact (proj1 Hinp)).
  assert (EE : dec_envp ρ = in_envp inp) by (unfold enc_b; apply dec_envp_enc; exact (proj1 (proj2 Hinp))).
  pose proof Hinp as (HA & HE & _ & _ & _ & (Hcu & Hcg) & _ & _ & Hhw & _).
  destruct HA as (_ & HAt & _). destruct HE as (_ & HEt & _).
  rewrite EA in Hta. rewrite EE in Hte.
  assert (Hhwr : 4397 <= ρ v_hw <= 2101549).
  { unfold enc_b. rewrite (enc_hw inp sp mbase pcw draw). destruct Hhw as [E|E]; rewrite E; vm_compute; split; discriminate. }
  assert (Hmssr : 1088 <= ρ v_mss <= 1664).
  { unfold enc_b. rewrite (enc_mss inp sp mbase pcw draw). rewrite Hmss, mss_default.
    destruct (hwcap_has_v (in_hwcap inp)); lia. }
  assert (Hurange : 0 <= ρ v_uid <= 4294967295 /\ 0 <= ρ v_gid <= 4294967295).
  { unfold enc_b. rewrite (enc_uid inp sp mbase pcw draw), (enc_gid inp sp mbase pcw draw).
    unfold valid_id in Hcu, Hcg. pose proof (u64_range (in_uid inp)). pose proof (u64_range (in_gid inp)). lia. }
  assert (Hparr : 0 <= ρ v_par <= 1) by (rewrite Hpar; pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)); lia).
  assert (EX0 : ρ v_x0 = (bv_unsigned sp / 16) mod 4) by reflexivity.
  assert (EX1 : ρ v_x1 = (bv_unsigned sp / 64) mod 64) by reflexivity.
  assert (EX2 : ρ v_x2 = (bv_unsigned sp / 4096) mod 8) by reflexivity.
  assert (EX3 : ρ v_x3 = bv_unsigned sp / 32768) by reflexivity.
  (* Both are needed: Hta and Hte were rewritten to the in_argv/in_envp form by EA and EE
     above, so lia sees v_ta and v_te only through these two bounds.  The argv one was
     absent, which is why the AUX_OFF+16 bullet below could not close: its upper bound
     needs 7 + 8*v_par <= v_g + v_ta + v_te + v_xl, and Hg gives 16 + 8*v_par <= v_g only
     once v_ta, v_te and v_xl are known non-negative. *)
  pose proof (total_arg_bytes_nonneg (in_argv inp)).
  pose proof (total_arg_bytes_nonneg (in_envp inp)).
  unfold dec_top, str_off in Hs2. rewrite Hspv in Hs1, Hs2.
  unfold sp_window_lo, sp_window_hi in *.
  unfold FL. repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?leval_lvar1|]); [..|apply Forall_nil].
  - rewrite EX0. pose proof (Z.mod_pos_bound (bv_unsigned sp / 16) 4 ltac:(lia)). lia.
  - rewrite EX1. pose proof (Z.mod_pos_bound (bv_unsigned sp / 64) 64 ltac:(lia)). lia.
  - rewrite EX2. pose proof (Z.mod_pos_bound (bv_unsigned sp / 4096) 8 ltac:(lia)). lia.
  - rewrite EX3. lia.
  - unfold leval. cbn [fst snd]. fold (sp_val ρ). lia.
  - exact Hb.
  - lia.
  - lia.
  - exact Hhwr.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact HL1r.
  - exact Hparr.
  - lia.
  - lia.
  - exact Hmssr.
  - lia.
  - lia.
  (* `unfold AUX_OFF` is required, not cosmetic: line 134 unfolds dec_top and str_off in
     Hs2, so Hs2 speaks of `24 + Z.of_nat (auxv_size r)` while these two goals still carry
     the folded `AUX_OFF r`.  lia treats the two as unrelated atoms and reports
     `Cannot find witness`.  Unfolded, both sides share Z.of_nat (auxv_size r). *)
  - unfold leval, AUX_OFF; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. lia.
  - unfold leval, AUX_OFF; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. lia.
  - unfold leval; cbn [fst snd teval]. lia.
  - unfold leval; cbn [fst snd teval]. lia.
Qed.

Theorem s0_usage_sat : length av <> 2%nat -> sat ρ (s0_usage r blo bhi).
Proof.
  intros H2. unfold s0_usage. apply sat_shole; [apply sat_entry_store; exact FL_sat|].
  rewrite leval_lvar1. change (ρ v_argc) with (Z.of_nat (length av)). lia.
Qed.

End Sat.
