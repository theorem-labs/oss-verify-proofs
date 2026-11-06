(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxEntryRel AxEntry AsanWEb.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxEntryS.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition FL (blo bhi : Z) : list (lin * (Z * Z)) :=
  [ (lvar v_x0 1, (0, 3)); (lvar v_x1 1, (0, 63)); (lvar v_x2 1, (0, 7)); (lvar v_x3 1, (4294901760, 4294967296));
    ((0, sp_terms), (140735340871680, 140737488355328));
    (lvar v_b 1, (blo, bhi));
    (lvar v_r0 1, (0, 18446744073709551615)); (lvar v_r1 1, (0, 18446744073709551615));
    (lvar v_hw 1, (4397, 2101549)); (lvar v_uid 1, (0, 4294967295));
    (lvar v_argc 1, (1, 1024)); (lvar v_envc 1, (0, 256));
    (lvar v_ta 1, (1, 2097152)); (lvar v_te 1, (0, 131072)); (lvar v_q 1, (1, 278528));
    (lvar (lenvar 0) 1, (0, 131071)); (lvar (lenvar 1) 1, (0, 131071));
    ((200, sp_terms ++ [(v_argc, 8); (v_envc, 8); (v_q, 8)]), (140735340871896, 140737488355328));
    ((201, sp_terms ++ [(v_argc, 8); (v_envc, 8); (lenvar 0, 1)]), (140735340871889, 140737488355328));
    ((0, [(v_q, 8); (v_ta, -1); (v_te, -1)]), (0, 7));
    ((0, [(v_ta, 1); (lenvar 0, -1)]), (1, 2097152)) ].

(* [comment removed for export] *)
Definition s0_usage (blo bhi : Z) : store := shole (entry_store (FL blo bhi)) (lvar v_argc 1) 1 3.

Lemma teval_app' (ρ : valuation) (a b : terms) : teval ρ (a ++ b) = teval ρ a + teval ρ b.
Proof. induction a as [|[x k] a IH]; cbn [app teval]; [lia | rewrite IH; lia]. Qed.

Lemma leval_lvar1 (ρ : valuation) (x : int) : leval ρ (lvar x 1) = ρ x.
Proof. unfold leval, lvar. cbn [fst snd teval]. lia. Qed.

Lemma fs_span (segs : list Segment) (inp : ProcInput) :
  entry_stack_span (in_argv inp) (in_envp inp) =
  207 + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + total_arg_bytes (in_argv inp) + total_arg_bytes (in_envp inp).
Proof. unfold entry_stack_span, auxv_size. lia. Qed.

Lemma total_first (L : list (list byte)) : L <> [] -> Z.of_nat (length (nth 0 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros H. destruct L as [|a L]; [congruence|]. unfold total_arg_bytes; cbn [fold_right nth].
  pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
Qed.

Lemma nth_len_bound (L : list (list byte)) (k : nat) : Forall (fun a => Z.of_nat (length a) <= 131071) L ->
  0 <= Z.of_nat (length (nth k L [])) <= 131071.
Proof.
  intros H. split; [lia|]. destruct (nth_in_or_default k L []) as [Hin|E]; [|rewrite E; cbn; lia].
  rewrite Forall_forall in H. exact (H _ Hin).
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

Lemma fs_sp : sp_window_lo <= bv_unsigned sp /\ bv_unsigned sp + entry_stack_span av ev <= sp_window_hi /\ bv_unsigned sp mod 16 = 0.
Proof using Hsp Hfit. destruct Hsp as (H1 & H2 & H3). split; [exact H1|]. split; [exact Hfit | exact H3]. Qed.

Lemma fs_spval : sp_val ρ = bv_unsigned sp.
Proof using Hsp Hfit. pose proof Hfit as _. apply sp_val_enc. exact (proj2 (proj2 fs_sp)). Qed.

Lemma fs_argv : (1 <= Z.of_nat (length av) <= 1024) /\ (1 <= total_arg_bytes av <= 2097152) /\
  Forall (fun a => Z.of_nat (length a) <= 131071) av.
Proof using Hinp.
  clear Hbrk Hblo Hbhi Hsp Hfit.
  destruct Hinp as ((Ha1 & Ha2 & Ha3 & _) & _). split; [exact Ha1|]. split; [|exact Ha3].
  split; [|exact Ha2]. pose proof (total_first av ltac:(intros E; rewrite E in Ha1; cbn in Ha1; lia)). lia.
Qed.

Lemma fs_envp : (0 <= Z.of_nat (length ev) <= 256) /\ (0 <= total_arg_bytes ev <= 131072).
Proof using Hinp.
  clear Hbrk Hblo Hbhi Hsp Hfit.
  destruct Hinp as (_ & (He1 & He2 & _) & _). split; [lia|]. split; [apply total_arg_bytes_nonneg | exact He2].
Qed.

Lemma fs_brk : blo <= ρ v_b <= bhi.
Proof using Hbrk Hblo Hbhi.
  rewrite enc_b_vb. destruct Hbrk as (B1 & B2 & B3). unfold page_size in B3.
  split.
  - apply (Z.le_trans _ _ _ Hblo). apply Z.div_le_mono; lia.
  - apply (Z.le_trans _ ((reserved_top (segments_reserved segs) + brk_aslr_max) / 4096)); [apply Z.div_le_mono; lia | exact Hbhi].
Qed.

Theorem FL_sat : Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) (FL blo bhi).
Proof.
  pose proof fs_sp as (Hs1 & Hs2 & Hs3). pose proof (fs_span segs inp) as Hspan. pose proof fs_spval as Hspv.
  pose proof fs_argv as ([Ha1 Ha2] & [Ha3 Ha4] & Ha5). pose proof fs_envp as ([He1 He2] & [He3 He4]). pose proof fs_brk as Hb.
  pose proof (total_first av ltac:(intros E; rewrite E in Ha1; cbn in Ha1; lia)) as HT1.
  assert (EL0 : ρ (lenvar 0) = Z.of_nat (length (nth 0 av []))) by (unfold enc_b; rewrite enc_lenvar by lia; reflexivity).
  assert (EL1 : ρ (lenvar 1) = Z.of_nat (length (nth 1 av []))) by (unfold enc_b; rewrite enc_lenvar by lia; reflexivity).
  pose proof (nth_len_bound av 0 Ha5) as HL0. pose proof (nth_len_bound av 1 Ha5) as HL1.
  assert (EAc : ρ v_argc = Z.of_nat (length av)) by reflexivity.
  assert (EEc : ρ v_envc = Z.of_nat (length ev)) by reflexivity.
  assert (ETa : ρ v_ta = total_arg_bytes av) by reflexivity.
  assert (ETe : ρ v_te = total_arg_bytes ev) by reflexivity.
  assert (EQ : ρ v_q = (total_arg_bytes av + total_arg_bytes ev + 7) / 8) by reflexivity.
  assert (EX0 : ρ v_x0 = (bv_unsigned sp / 16) mod 4) by reflexivity.
  assert (EX1 : ρ v_x1 = (bv_unsigned sp / 64) mod 64) by reflexivity.
  assert (EX2 : ρ v_x2 = (bv_unsigned sp / 4096) mod 8) by reflexivity.
  assert (EX3 : ρ v_x3 = bv_unsigned sp / 32768) by reflexivity.
  assert (ER0 : ρ v_r0 = bv_unsigned (ed_random draw) mod 2 ^ 64) by reflexivity.
  assert (ER1 : ρ v_r1 = bv_unsigned (ed_random draw) / 2 ^ 64) by reflexivity.
  assert (EHw : ρ v_hw = bv_unsigned (in_hwcap inp)) by reflexivity.
  assert (EUid : ρ v_uid = bv_unsigned (in_uid inp)) by reflexivity.
  pose proof (bv_unsigned_in_range 128 (ed_random draw)) as HR. change (bv_modulus 128) with (2 ^ 128) in HR.
  assert (Hhw : 4397 <= bv_unsigned (in_hwcap inp) <= 2101549).
  { destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & [E|E] & _); rewrite E; vm_compute; split; discriminate. }
  assert (Huid : 0 <= bv_unsigned (in_uid inp) <= 4294967295).
  { pose proof (eb_facts_enc inp sp draw (fun v => if (v =? 4)%uint63 then bv_unsigned brk0 / 4096 else 0) Hinp Hsp Hfit) as HF.
    destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hu & _). change (enc inp sp draw _) with ρ in Hu. rewrite EUid in Hu. lia. }
  unfold sp_window_lo, sp_window_hi in *.
  unfold FL. repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?leval_lvar1|]); [..|apply Forall_nil].
  - rewrite EX0. pose proof (Z.mod_pos_bound (bv_unsigned sp / 16) 4 ltac:(lia)). lia.
  - rewrite EX1. pose proof (Z.mod_pos_bound (bv_unsigned sp / 64) 64 ltac:(lia)). lia.
  - rewrite EX2. pose proof (Z.mod_pos_bound (bv_unsigned sp / 4096) 8 ltac:(lia)). lia.
  - rewrite EX3. lia.
  - unfold leval. cbn [fst snd]. fold (sp_val ρ). lia.
  - exact Hb.
  - rewrite ER0. pose proof (Z.mod_pos_bound (bv_unsigned (ed_random draw)) (2 ^ 64) ltac:(lia)). lia.
  - rewrite ER1. split; [apply Z.div_pos; lia|]. assert (bv_unsigned (ed_random draw) / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia). lia.
  - rewrite EHw. exact Hhw.
  - rewrite EUid. exact Huid.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite EQ. lia.
  - lia.
  - lia.
  - unfold leval; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. lia.
  - unfold leval; cbn [fst snd]. rewrite teval_app'. fold (sp_val ρ). cbn [teval]. lia.
  - unfold leval; cbn [fst snd teval]. lia.
  - unfold leval; cbn [fst snd teval]. lia.
Qed.

Theorem s0_usage_sat : length av <> 2%nat -> sat ρ (s0_usage blo bhi).
Proof.
  intros H2. unfold s0_usage. apply sat_shole; [apply sat_entry_store; exact FL_sat|].
  rewrite leval_lvar1. change (ρ v_argc) with (Z.of_nat (length av)). lia.
Qed.

End Sat.
