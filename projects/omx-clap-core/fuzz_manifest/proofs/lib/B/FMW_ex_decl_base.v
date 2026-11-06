(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v, with its module paths and module names changed; 305 of its 367 lines of code are new or changed and 869 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_ex_tok_base.v; 567 of its 633 lines of code are new or changed and 301 lines of the source are left out. *)
(* G4.ExDecl, IMAGE B (fm.asan-ubsan, pin ca61e5c9eabc0050): ex_seg_P (FMW_ex_base.v:191) cut into sub-segments.
   B twin of lib/A/FMW_ex_decl_base.v at 06d82004dc3: the model lemmas (dm_*, dd_cstr_suffix, dd_byte_val) are A's
   unchanged; the cuts, the registers, the frame slots and the exits are read from B's own code
   (internal path). From EX_P (0x814cc: s5 = text + i, s7 = i, a0 = a1)
   the declaration body of expected (fuzz_manifest.c:145-170) runs three byte loops, strchr, strncmp and the program
   call plain. B returns to the scan through one shared block: EX_JUMP 0x81690 (s7 = a1 - a6) and EX_NEXT 0x81694
   (s7 += 1; s5 = a6 + s7; the UBSan guard 0x816a0 bgeu ~text, s7, else the trap 0x8194c) -> EX_L. The walk is cut at
   the loop heads, after each call and at that block; every cut carries a semantic invariant (dat_* below), and every
   sub-segment file proves its dseg_* from the ones it jumps to:
     FMW_ex_decl_n.v   EX_NEXT -> EX_L (j + 1); EX_JUMP -> EX_NEXT         (dseg_N, dseg_J)
     FMW_ex_decl_p.v   EX_P -> {EX_NEXT (i), D1 0}
     FMW_ex_decl_d1.v  D1 k -> {D1 (k + 1), D2 0}                         (the loop by induction)
     FMW_ex_decl_d2.v  D2 j -> {D2 (j + 1), EX_NEXT (i), D3 0}
     FMW_ex_decl_d3.v  D3 m -> {D3 (m + 1), EX_NEXT (i), D3c}
     FMW_ex_decl_d3c.v D3c  -> {D4}                                       (strchr)
     FMW_ex_decl_d4.v  D4   -> {EX_R (a0 = 0), EX_JUMP (close), D5}       (strncmp)
     FMW_ex_decl_d5.v  D5   -> {EX_JUMP (close), D6}                      (plain, a program call)
     FMW_ex_decl_d6.v  D6   -> {EX_JUMP (close), EX_R (a0 = 1), EX_T}
   FMW_ex_decl.v composes them into ex_seg_P_holds. The model positions follow ManifestModel.decl's let-chain
   (p0 = i + a1, p1 after the spaces, p2 = ':' after the name, p3 = '<' after the spaces, ns = p3 + 1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cut pcs inside ex_seg_P (B) ---- *)
Definition EX_D1 : Z := 0x81500.   (* the spaces after the head word, fuzz_manifest.c:147-148 (A 0x81380) *)
Definition EX_D2 : Z := 0x8155c.   (* the name up to NUL, ':' or a space, :149 (A 0x813dc) *)
Definition EX_D3 : Z := 0x815d8.   (* the spaces after ':', :154 (A 0x81454) *)
Definition EX_D3c : Z := 0x81630.  (* '<' found: s7 = ns = text + p3 + 1, strchr (ns, '>') next, :156-159 (A 0x81490) *)
Definition EX_D4 : Z := 0x8163c.   (* after strchr (ns, '>'), :159 (A 0x8149c) *)
Definition EX_D5 : Z := 0x81664.   (* after strncmp (uri, ns, ns_len), :162 (A 0x814c0) *)
Definition EX_D6 : Z := 0x816c0.   (* after plain (uri + ns_len), :162 (A 0x8150c) *)

(* ---- pure model: count_while over a suffix, the declaration's positions ---- *)
Module MM := ManifestModel.

Lemma dm_cw_step : forall f (l : list Z) p, (p < length l)%nat ->
  MM.count_while f (skipn p l) =
  if f (MM.byte_at l p) then S (MM.count_while f (skipn (S p) l)) else O.
Proof.
  intros f l p Hp. revert l Hp. induction p as [|p IH]; intros [|x l] Hp; cbn in Hp |- *; try lia.
  - reflexivity.
  - unfold MM.byte_at in *. cbn [nth]. apply IH. lia.
Qed.

Lemma dm_cw_end : forall f (l : list Z) p, (length l <= p)%nat -> MM.count_while f (skipn p l) = O.
Proof. intros f l p Hp. rewrite skipn_all2 by exact Hp. reflexivity. Qed.

Lemma dm_cw_le : forall f (l : list Z) p, (MM.count_while f (skipn p l) <= length l - p)%nat.
Proof.
  intros f l p. destruct (Nat.lt_ge_cases p (length l)) as [Hp|Hp]; [|rewrite dm_cw_end by exact Hp; lia].
  remember (length l - p)%nat as r eqn:Hr. revert p Hp Hr. induction r as [|r IH]; intros p Hp Hr; [lia|].
  rewrite (dm_cw_step f l p Hp). destruct (f (MM.byte_at l p)); [|lia].
  destruct (Nat.lt_ge_cases (S p) (length l)) as [Hp'|Hp']; [specialize (IH (S p) Hp' ltac:(lia)); lia|].
  rewrite dm_cw_end by exact Hp'. lia.
Qed.

Lemma dm_cw_shift : forall f (l : list Z) p k, (k <= MM.count_while f (skipn p l))%nat ->
  MM.count_while f (skipn p l) = (k + MM.count_while f (skipn (p + k) l))%nat.
Proof.
  intros f l p k. revert p. induction k as [|k IH]; intros p Hk; [rewrite Nat.add_0_r; reflexivity|].
  destruct (Nat.lt_ge_cases p (length l)) as [Hp|Hp]; [|rewrite dm_cw_end in Hk by exact Hp; lia].
  rewrite (dm_cw_step f l p Hp) in Hk |- *. destruct (f (MM.byte_at l p)); [|lia].
  replace (p + S k)%nat with (S p + k)%nat by lia. rewrite (IH (S p) ltac:(lia)). lia.
Qed.

(* the loop exits: the byte at p + k stops the count *)
Lemma dm_cw_exact : forall f (l : list Z) p k, (k <= MM.count_while f (skipn p l))%nat ->
  f (MM.byte_at l (p + k)) = false -> MM.count_while f (skipn p l) = k.
Proof.
  intros f l p k Hk Hf. rewrite (dm_cw_shift f l p k Hk).
  destruct (Nat.lt_ge_cases (p + k) (length l)) as [H|H].
  - rewrite (dm_cw_step f l (p + k) H), Hf. lia.
  - rewrite dm_cw_end by exact H. lia.
Qed.

(* the loops' back edges: the byte at p + k continues the count (f 0 = false: the NUL stops every loop) *)
Lemma dm_cw_next : forall f (l : list Z) p k, f 0 = false -> (k <= MM.count_while f (skipn p l))%nat ->
  f (MM.byte_at l (p + k)) = true -> (S k <= MM.count_while f (skipn p l))%nat.
Proof.
  intros f l p k H0 Hk Hf. rewrite (dm_cw_shift f l p k Hk).
  destruct (Nat.lt_ge_cases (p + k) (length l)) as [H|H].
  - rewrite (dm_cw_step f l (p + k) H), Hf. lia.
  - rewrite expected_m.byte_at_ge in Hf by exact H. congruence.
Qed.

(* within the count, the bytes are inside the list (f 0 = false) *)
Lemma dm_cw_in : forall f (l : list Z) p k, (k < MM.count_while f (skipn p l))%nat -> (p + k < length l)%nat.
Proof. intros f l p k Hk. pose proof (dm_cw_le f l p). lia. Qed.

Lemma dm_space0 : MM.is_space 0 = false. Proof. reflexivity. Qed.
Lemma dm_name0 : MM.name_ok 0 = false. Proof. reflexivity. Qed.

Lemma dm_head_lt : forall t i p, MM.head t i = Some p -> (i < p)%nat.
Proof.
  intros t i p H. unfold MM.head in H.
  repeat match type of H with context [if ?c then _ else _] => destruct c end; inversion H; lia.
Qed.

(* the declaration at i, step by step: DNone at each failed test, else DCut / DFound by the '>' search *)
Lemma dm_decl_sp : forall t i p0, MM.head t i = Some p0 -> MM.is_space (MM.byte_at t p0) = false ->
  MM.decl t i = MM.DNone.
Proof. intros t i p0 Hh Hs. unfold MM.decl. rewrite Hh. cbv beta iota. rewrite Hs. reflexivity. Qed.

Lemma dm_decl_colon : forall t i p0 p1 p2, MM.head t i = Some p0 -> MM.is_space (MM.byte_at t p0) = true ->
  p1 = (p0 + MM.count_while MM.is_space (skipn p0 t))%nat ->
  p2 = (p1 + MM.count_while MM.name_ok (skipn p1 t))%nat ->
  MM.byte_at t p2 <> 58 -> MM.decl t i = MM.DNone.
Proof.
  intros t i p0 p1 p2 Hh Hs E1 E2 Hc. subst p1 p2. unfold MM.decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs, (proj2 (Z.eqb_neq _ _) Hc). reflexivity.
Qed.

Lemma dm_decl_lt : forall t i p0 p1 p2 p3, MM.head t i = Some p0 -> MM.is_space (MM.byte_at t p0) = true ->
  p1 = (p0 + MM.count_while MM.is_space (skipn p0 t))%nat ->
  p2 = (p1 + MM.count_while MM.name_ok (skipn p1 t))%nat ->
  p3 = (S p2 + MM.count_while MM.is_space (skipn (S p2) t))%nat ->
  MM.byte_at t p2 = 58 -> MM.byte_at t p3 <> 60 -> MM.decl t i = MM.DNone.
Proof.
  intros t i p0 p1 p2 p3 Hh Hs E1 E2 E3 Hc Hl. subst p1 p2 p3. unfold MM.decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs, Hc, (proj2 (Z.eqb_neq _ _) Hl). reflexivity.
Qed.

Lemma dm_decl_gt : forall t i p0 p1 p2 p3, MM.head t i = Some p0 -> MM.is_space (MM.byte_at t p0) = true ->
  p1 = (p0 + MM.count_while MM.is_space (skipn p0 t))%nat ->
  p2 = (p1 + MM.count_while MM.name_ok (skipn p1 t))%nat ->
  p3 = (S p2 + MM.count_while MM.is_space (skipn (S p2) t))%nat ->
  MM.byte_at t p2 = 58 -> MM.byte_at t p3 = 60 ->
  MM.decl t i = match MM.find_idx (fun c => c =? 62) (skipn (S p3) t) with
                | None => MM.DCut
                | Some o => MM.DFound p1 (p2 - p1) (S p3) o (S p3 + o)
                end.
Proof.
  intros t i p0 p1 p2 p3 Hh Hs E1 E2 E3 Hc Hl. subst p1 p2 p3. unfold MM.decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs, Hc, Hl. reflexivity.
Qed.

(* strchr's answer as the model's '>' search *)
Lemma dm_find_none : forall l, ~ In 62 l -> MM.find_idx (fun c => c =? 62) l = None.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [MM.find_idx].
  destruct (Z.eqb_spec x 62) as [->|Hx]; [exfalso; apply H; left; reflexivity|].
  rewrite IH by (intros Hin; apply H; right; exact Hin). reflexivity.
Qed.

Lemma dm_find_some : forall l j, first_at l 62 j -> MM.find_idx (fun c => c =? 62) l = Some j.
Proof.
  induction l as [|x l IH]; intros j (Hj & Hn & Hf); cbn in Hj; [lia|]. cbn [MM.find_idx].
  destruct j as [|j]; cbn [nth firstn] in Hn, Hf.
  - subst x. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec x 62) as [->|Hx]; [exfalso; apply Hf; left; reflexivity|].
    rewrite (IH j); [reflexivity|]. split; [lia|]. split; [exact Hn|]. intros Hin. apply Hf. right. exact Hin.
Qed.

(* strncmp (uri, ns, nl2) = 0 as the model's comparison (nl2 < |uri|, ns + nl2 <= |text|) *)
Lemma dm_strn : forall (tb ub : list Z) ns nl2, (nl2 < length ub)%nat -> (ns + nl2 <= length tb)%nat ->
  strn_eq nl2 ub (skipn ns tb) <-> firstn nl2 (skipn ns tb) = firstn nl2 ub.
Proof.
  intros tb ub ns nl2 Hu Ht. unfold strn_eq.
  rewrite (firstn_app nl2 ub [0]), (firstn_app nl2 (skipn ns tb) [0]).
  replace (nl2 - length ub)%nat with O by lia. rewrite length_skipn.
  replace (nl2 - (length tb - ns))%nat with O by lia. cbn [firstn]. rewrite !app_nil_r.
  split; intros H; symmetry; exact H.
Qed.

Lemma dm_matches : forall tb ub ns nl2,
  MM.matches tb ub ns nl2 = true <->
  (nl2 < length ub)%nat /\ firstn nl2 (skipn ns tb) = firstn nl2 ub /\ MM.plain_name (skipn nl2 ub) = true.
Proof.
  intros tb ub ns nl2. unfold MM.matches. rewrite !andb_true_iff, Nat.ltb_lt, MM.zl_eqb_eq. tauto.
Qed.

(* ---- C strings: a suffix of a cstr_ok string is cstr_ok, its bytes (after G3's FMW_rd_lp.v lp_cstr_ok_suffix,
   lp_byte_val, lp_cstr_pos, a working branch) ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma dd_nth_skipn : forall (l : list Z) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros l m; revert l; induction m as [|m IH]; intros [|x l] n d; cbn; try reflexivity;
    [destruct n; reflexivity | apply IH].
Qed.

Lemma dd_div8_mono : forall a b, a <= b -> a / 8 * 8 <= b / 8 * 8.
Proof. intros a b H. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma dd_cstr_suffix : forall (W : world tfibsegs) mem p l k, cstr_ok tfibsegs W mem p l -> (k <= length l)%nat ->
  cstr_ok tfibsegs W mem (p + Z.of_nat k) (skipn k l).
Proof.
  intros W mem p l k ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl) Hk.
  assert (HL : Z.of_nat (length (skipn k l)) = Z.of_nat (length l) - Z.of_nat k) by (rewrite length_skipn; lia).
  unfold cstr_ok, cstr. rewrite HL.
  split; [split|].
  { intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite length_skipn in Hj.
    destruct (Hg (k + j)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [V R].
    assert (E : nth j (skipn k l ++ [0]) 0 = nth (k + j) (l ++ [0]) 0).
    { assert (S0 : skipn k (l ++ [0]) = skipn k l ++ [0])
        by (rewrite skipn_app; replace (k - length l)%nat with 0%nat by lia; reflexivity).
      rewrite <- S0, dd_nth_skipn. reflexivity. }
    rewrite E. split; [|exact R]. replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. exact V. }
  { clear -Hnz. revert l Hnz. induction k as [|k IH]; intros l H; [exact H|].
    destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [skipn]. apply IH. assumption. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  { intros x Hx. apply Hra. lia. }
  split.
  { intros s Hs. apply Hhv.
    assert (Hsa : shadow_addr p <= shadow_addr (p + Z.of_nat k)).
    { unfold shadow_addr. pose proof (Z.div_le_mono p (p + Z.of_nat k) 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (dd_div8_mono _ _ Hsa) as M.
    replace (p + (Z.of_nat (length l) + 1) - 1) with (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k + 1) - 1)
      by lia.
    lia. }
  intros a Ha. apply Htl.
  replace (p + Z.of_nat (length l)) with (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k)) by lia. exact Ha.
Qed.

(* the byte at p + j (j <= |l|: the NUL at j = |l|), as the model reads it *)
Lemma dd_byte_val : forall (W : world tfibsegs) mem p l j, cstr_ok tfibsegs W mem p l -> (j <= length l)%nat ->
  val_mem tfibsegs (rdW W mem) (p + Z.of_nat j) 1 (MM.byte_at l j) /\ 0 <= MM.byte_at l j < 256.
Proof.
  intros W mem p l j ((Hg & _) & _) Hj.
  assert (E : nth j (l ++ [0]) 0 = MM.byte_at l j).
  { unfold MM.byte_at. destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl].
    - apply app_nth1. exact Hl.
    - rewrite app_nth2 by lia. replace (j - length l)%nat with 0%nat by lia. rewrite (nth_overflow l) by lia.
      reflexivity. }
  rewrite <- E. apply Hg. rewrite length_app. cbn [length]. lia.
Qed.

(* the NUL is the only zero byte up to |l| *)
Lemma dd_byte_end : forall (W : world tfibsegs) mem p l j, cstr_ok tfibsegs W mem p l -> (j <= length l)%nat ->
  MM.byte_at l j = 0 -> j = length l.
Proof.
  intros W mem p l j ((Hg & Hnz) & _) Hj H0. destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl]; [|lia].
  rewrite Forall_forall in Hnz. exfalso. apply (Hnz (MM.byte_at l j)); [|exact H0].
  unfold MM.byte_at. apply nth_In. exact Hl.
Qed.
End s.

(* ---- register values as 64-bit words (the p_den_ lemmas of A's FMW_ex_decl_p.v) ---- *)
Section v. Context {fx : YK11.FPState}.
Lemma dd_den_off : forall E n c x, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
  intros E n c x H. cbn [sv_denot]. rewrite H, unsigned_lit. apply Z_to_bv64_eq_mod.
  unfold zcanon, M64. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma dd_den_off0 : forall E n x, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof. intros E n x H. rewrite (dd_den_off E n 0 x H), Z.add_0_r. reflexivity. Qed.
Lemma dd_den_add : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zalu64_sound. unfold zalu64. cbn [zalu_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma dd_den_sub : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_SUB a b) = Z_to_bv 64 (x - y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zalu64_sound. unfold zalu64. cbn [zalu_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma dd_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma dd_den_mul : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SMd M_MUL a b) = Z_to_bv 64 (x * y).
Proof.
  intros E a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb, zmd64_sound. unfold zmd64. cbn [zmd_raw].
  rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite <- Zmult_mod. reflexivity.
Qed.

(* the guard 0x816a0 `bgeu ~text, s7` is taken when s7 <= ~text *)
Lemma dd_geu_taken : forall E a b, U E b <= U E a -> branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = true.
Proof. intros E a b H. rewrite branch_geu_U. apply negb_true_iff, Z.ltb_ge. exact H. Qed.
End v.

Lemma dd_w64_add : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
  intros x k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l; [reflexivity|]. unfold bv_modulus. lia.
Qed.

(* a - t for the executor's subtraction a + t * (2^64 - 1) (A's FMW_ex_decl_d6.v d6_sub_canon) *)
Lemma dd_sub_canon : forall a t, 0 <= a - t < M64 ->
  zcanon (a + zcanon (t * 18446744073709551615)) = a - t.
Proof.
  intros a t Ha. unfold zcanon, M64 in *. change (2 ^ 64) with 18446744073709551616 in *.
  replace (t * 18446744073709551615) with (- t + t * 18446744073709551616) by ring.
  rewrite Z_mod_plus_full, Z.add_mod_idemp_r by lia.
  replace (a + - t) with (a - t) by ring. apply Z.mod_small. exact Ha.
Qed.

(* frame slots as a symbolic region: chunk (offset, j) holds extra atom 32 + j (A's FMW_ex_ret.v ex_slot_chunks,
   kept here so that the decl files do not wait on B's FMW_ex_ret.v) *)
Definition dd_slot_chunks (cs : list (Z * nat)) : list YP09.chunk :=
  map (fun c => YP09.mkChunk (fst c) (CVal 8 (SOff (32 + snd c) 0))) cs.

Section f. Context {fx : YK11.FPState}.
Lemma dd_chunks_ok : forall E m b cs,
  Forall (fun c => val_mem tfibsegs m (b + fst c) 8 (bv_unsigned (ew E (32 + snd c)))) cs ->
  Forall (YP09.chunk_ok tfibsegs E m b) (dd_slot_chunks cs).
Proof.
  intros E m b cs H. induction H as [|c cs Hc _ IH]; [constructor|]. constructor; [|exact IH].
  apply (chunk_ok_val tfibsegs E m b (fst c) 8 (SOff (32 + snd c) 0) (bv_unsigned (ew E (32 + snd c)))).
  - cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range _ (ew E (32 + snd c))) as R. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R.
    exact R.
  - cbn. lia.
  - exact Hc.
Qed.
End f.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the declaration's model positions at i: the head word ends at p0 = i + a1 on a space, p1 after the spaces,
   p2 the ':' after the name, p3 the '<' after the spaces *)
Definition dm_p0 (cx : ecx) (i a1 : nat) : Prop :=
  MM.head (cx_tb cx) i = Some (i + a1)%nat /\ (a1 = 6 \/ a1 = 7)%nat /\
  MM.is_space (MM.byte_at (cx_tb cx) (i + a1)) = true.
Definition dm_p1 (cx : ecx) (i a1 p1 : nat) : Prop :=
  dm_p0 cx i a1 /\ p1 = (i + a1 + MM.count_while MM.is_space (skipn (i + a1) (cx_tb cx)))%nat.
Definition dm_p2 (cx : ecx) (i a1 p1 p2 : nat) : Prop :=
  dm_p1 cx i a1 p1 /\ p2 = (p1 + MM.count_while MM.name_ok (skipn p1 (cx_tb cx)))%nat /\
  MM.byte_at (cx_tb cx) p2 = 58.
Definition dm_p3 (cx : ecx) (i a1 p1 p2 p3 : nat) : Prop :=
  dm_p2 cx i a1 p1 p2 /\ p3 = (S p2 + MM.count_while MM.is_space (skipn (S p2) (cx_tb cx)))%nat /\
  MM.byte_at (cx_tb cx) p3 = 60.

(* what every cut of ex_seg_P carries: expected's entry and common facts, the slots with declared = d, B's
   callee-saved scan constants s3 = 5, s11 = ' ', s0 = -1 (ex_sregs), the scan's model state at i *)
Definition dd_com (cx : ecx) (i d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_scan cx i d f /\ (i < length (cx_tb cx))%nat.

(* D1 (0x81500): k spaces after p0 = i + a1 skipped, q = p0 + k: a0 = s4 = text + q, a2 = text + 1 + q,
   s8 = text + 2 + q, s10 = uri - 2 - text - q; s7 = i and the caller-saved constants (ex_cregs) for EX_NEXT *)
Definition dat_D1 (cx : ecx) (i d f a1 k : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ ex_cregs cx regs3 /\ dm_p0 cx i a1 /\
  (k <= MM.count_while MM.is_space (skipn (i + a1) (cx_tb cx)))%nat /\
  getr regs3 10 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) /\ getr regs3 20 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) /\
  getr regs3 12 = w64 (cx_t cx + 1 + Z.of_nat (i + a1 + k)) /\
  getr regs3 24 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k)) /\
  getr regs3 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat (i + a1 + k)) /\
  getr regs3 23 = w64 (Z.of_nat i).

(* D2 (0x8155c): the name from p1 on, j bytes taken, a1 = the byte at p1 + j: a0 = s4 = text + p1, s5 = j,
   s2 = 1 + j, s6 = s1 = text + 1 + j, a2 = text + 1 + p1 + j, s8 = text + 2 + p1 + j,
   s10 = uri - 2 - text - p1 - j; s7 = i *)
Definition dat_D2 (cx : ecx) (i d f a1 p1 j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ ex_cregs cx regs3 /\ dm_p1 cx i a1 p1 /\
  (j <= MM.count_while MM.name_ok (skipn p1 (cx_tb cx)))%nat /\
  getr regs3 11 = w64 (MM.byte_at (cx_tb cx) (p1 + j)) /\
  getr regs3 10 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 21 = w64 (Z.of_nat j) /\ getr regs3 18 = w64 (1 + Z.of_nat j) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat j) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat j) /\
  getr regs3 12 = w64 (cx_t cx + 1 + Z.of_nat p1 + Z.of_nat j) /\
  getr regs3 24 = w64 (cx_t cx + 2 + Z.of_nat p1 + Z.of_nat j) /\
  getr regs3 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat p1 - Z.of_nat j) /\
  getr regs3 23 = w64 (Z.of_nat i).

(* D3 (0x815d8): ':' at p2, m spaces after it skipped: s4 = text + p1, s5 = p2 - p1, s2 = 1 + s5,
   s6 = s1 = text + 1 + s5, a2 = text + 1 + p2 + m, s8 = text + 2 + p2 + m, s10 = uri - 2 - text - p2 - m; s7 = i *)
Definition dat_D3 (cx : ecx) (i d f a1 p1 p2 m : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ ex_cregs cx regs3 /\ dm_p2 cx i a1 p1 p2 /\
  (m <= MM.count_while MM.is_space (skipn (S p2) (cx_tb cx)))%nat /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 21 = w64 (Z.of_nat (p2 - p1)) /\ getr regs3 18 = w64 (1 + Z.of_nat (p2 - p1)) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\
  getr regs3 12 = w64 (cx_t cx + 1 + Z.of_nat p2 + Z.of_nat m) /\
  getr regs3 24 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat m) /\
  getr regs3 26 = w64 (cx_u cx - 2 - cx_t cx - Z.of_nat p2 - Z.of_nat m) /\
  getr regs3 23 = w64 (Z.of_nat i).

(* D3c (0x81630): the '<' at p3: s4 = text + p1, s5 = p2 - p1, s2 = 1 + s5, s6 = s1 = text + 1 + s5,
   s7 = s8 = text + p3 + 1 = ns, s10 = uri - text - p3 - 1 *)
Definition dat_D3c (cx : ecx) (i d f a1 p1 p2 p3 : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ dm_p3 cx i a1 p1 p2 p3 /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 21 = w64 (Z.of_nat (p2 - p1)) /\ getr regs3 18 = w64 (1 + Z.of_nat (p2 - p1)) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\
  getr regs3 23 = w64 (cx_t cx + Z.of_nat (S p3)) /\ getr regs3 24 = w64 (cx_t cx + Z.of_nat (S p3)) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat (S p3)).

(* D4 (0x8163c): strchr (ns, '>') answered r: the declaration is DCut (r = 0) or DFound name nl ns nl2 close
   (r = text + close); s4 = text + name, s5 = nl, s2 = 1 + nl, s6 = s1 = text + 1 + nl, s7 = s8 = text + ns,
   s10 = uri - text - ns *)
Definition dat_D4 (cx : ecx) (i d f name nl ns nl2 close : nat) (r : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  ((MM.decl (cx_tb cx) i = MM.DCut /\ r = 0) \/
   (MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ r = cx_t cx + Z.of_nat close)) /\
  getr regs3 10 = w64 r /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 18 = w64 (1 + Z.of_nat nl) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 23 = w64 (cx_t cx + Z.of_nat ns) /\ getr regs3 24 = w64 (cx_t cx + Z.of_nat ns) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat ns).

(* D5 (0x81664): s8 = ns_len = nl2 < n, F+0x40 = text + close; strncmp (uri, ns, nl2) answered v *)
Definition dat_D5 (cx : ecx) (i d f name nl ns nl2 close : nat) (v : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ (nl2 < length (cx_ub cx))%nat /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x40) 8 (cx_t cx + Z.of_nat close) /\
  getr regs3 10 = w64 v /\ 0 <= v < 2 ^ 64 /\
  (v = 0 <-> firstn nl2 (skipn ns (cx_tb cx)) = firstn nl2 (cx_ub cx)) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 18 = w64 (1 + Z.of_nat nl) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 24 = w64 (Z.of_nat nl2) /\ getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat ns).

(* D6 (0x816c0): the namespace equals the uri's first nl2 bytes; plain (uri + nl2) answered; F+0x20 = local =
   uri + nl2, F+0x40 = text + close *)
Definition dat_D6 (cx : ecx) (i d f name nl ns nl2 close : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ (nl2 < length (cx_ub cx))%nat /\
  firstn nl2 (skipn ns (cx_tb cx)) = firstn nl2 (cx_ub cx) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x40) 8 (cx_t cx + Z.of_nat close) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x20) 8 (cx_u cx + Z.of_nat nl2) /\
  getr regs3 10 = w64 (if MM.plain_name (skipn nl2 (cx_ub cx)) then 1 else 0) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 18 = w64 (1 + Z.of_nat nl) /\
  getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 24 = w64 (Z.of_nat nl2).

(* EX_NEXT (0x81694): the scan goes on at j + 1 (s7 = j); EX_JUMP (0x81690): the same with a1 = text + j
   (s7 = a1 - a6 = j first) *)
Definition dat_N (cx : ecx) (j d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_cregs cx regs3 /\ ex_scan cx (S j) d f /\ getr regs3 23 = w64 (Z.of_nat j).
Definition dat_J (cx : ecx) (j d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_cregs cx regs3 /\ ex_scan cx (S j) d f /\ getr regs3 11 = w64 (cx_t cx + Z.of_nat j).

(* ---- the sub-segment statements: every cut reaches expected's post ---- *)
Definition dseg_N : Prop :=
  forall cx i j d f ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> (i <= j)%nat -> dat_N cx j d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_NEXT regs3 mem3 md3) (ex_post B cx).
Definition dseg_J : Prop :=
  forall cx i j d f ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> (i <= j)%nat -> dat_J cx j d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_JUMP regs3 mem3 md3) (ex_post B cx).
Definition dseg_D1 : Prop :=
  forall cx i d f a1 k ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D1 cx i d f a1 k ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D1 regs3 mem3 md3) (ex_post B cx).
Definition dseg_D2 : Prop :=
  forall cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D2 cx i d f a1 p1 j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D2 regs3 mem3 md3) (ex_post B cx).
Definition dseg_D3 : Prop :=
  forall cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D3 cx i d f a1 p1 p2 m ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D3 regs3 mem3 md3) (ex_post B cx).
Definition dseg_D3c : Prop :=
  forall cx i d f a1 p1 p2 p3 ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D3c cx i d f a1 p1 p2 p3 ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D3c regs3 mem3 md3) (ex_post B cx).
Definition dseg_D4 : Prop :=
  forall cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D4 cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D4 regs3 mem3 md3) (ex_post B cx).
Definition dseg_D5 : Prop :=
  forall cx i d f name nl ns nl2 close v ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D5 cx i d f name nl ns nl2 close v ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D5 regs3 mem3 md3) (ex_post B cx).
Definition dseg_D6 : Prop :=
  forall cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from B cx i -> dat_D6 cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_D6 regs3 mem3 md3) (ex_post B cx).

(* ---- the scan's model at the exits (expected_m.scan_step) ---- *)
Lemma dd_scan_none : forall cx i d f, ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  MM.decl (cx_tb cx) i = MM.DNone -> ex_scan cx (S i) d (pred f).
Proof.
  intros cx i d f (Hi & Hd & Hf & Hu & Hr) Hlt Hdc. destruct f as [|f]; [lia|]. cbn [pred].
  split; [lia|]. split; [exact Hd|]. split; [lia|]. split; [exact Hu|].
  rewrite Hr, (expected_m.scan_step _ _ _ _ _ Hlt). unfold expected_m.sstep. rewrite Hdc. reflexivity.
Qed.

Lemma dd_scan_skip : forall cx i d f name nl ns nl2 close, ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close -> MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = false ->
  ex_scan cx (S close) d (pred f) /\ (i < S close)%nat.
Proof.
  intros cx i d f name nl ns nl2 close (Hi & Hd & Hf & Hu & Hr) Hlt Hdc Hm.
  pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
  destruct f as [|f]; [lia|]. cbn [pred].
  split; [|lia].
  split; [lia|]. split; [exact Hd|]. split; [lia|]. split; [exact Hu|].
  rewrite Hr, (expected_m.scan_step _ _ _ _ _ Hlt). unfold expected_m.sstep. rewrite Hdc, Hm. reflexivity.
Qed.

Lemma dd_res_cut : forall cx i d f, ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  MM.decl (cx_tb cx) i = MM.DCut -> cx_res cx = 0.
Proof.
  intros cx i d f (Hi & Hd & Hf & Hu & Hr) Hlt Hdc. destruct f as [|f]; [lia|].
  rewrite Hr, (expected_m.scan_step _ _ _ _ _ Hlt). unfold expected_m.sstep. rewrite Hdc. reflexivity.
Qed.

Lemma dd_res_full : forall cx i d f name nl ns nl2 close, ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close -> MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = true ->
  (16 < S d)%nat -> cx_res cx = 1.
Proof.
  intros cx i d f name nl ns nl2 close (Hi & Hd & Hf & Hu & Hr) Hlt Hdc Hm H16. destruct f as [|f]; [lia|].
  rewrite Hr, (expected_m.scan_step _ _ _ _ _ Hlt). unfold expected_m.sstep. rewrite Hdc, Hm.
  rewrite (proj2 (Nat.ltb_lt 16 (S d)) H16). reflexivity.
Qed.

(* ---- facts the entry gives every cut (B's frame: F = entry sp - 240) ---- *)
Lemma dd_bounds : forall cx, ex_base B cx ->
  cx_F cx mod 16 = 0 /\ alloc_ceiling + STK_expected - 240 <= cx_F cx /\ cx_F cx + 240 <= 2 ^ 47 /\
  4096 <= cx_t cx /\ cx_t cx + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling /\
  4096 <= cx_u cx /\ cx_u cx + Z.of_nat (length (cx_ub cx)) + 8 <= alloc_ceiling.
Proof.
  intros cx ((HPRE & _) & _ & _ & _ & Ct & Cu & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof Ct as (_ & Ht4 & Htc & _). pose proof Cu as (_ & Hu4 & Huc & _).
  unfold cx_F, cx_sp in *.
  split; [replace (spZ (cx_regs cx) - 240) with (spZ (cx_regs cx) + (-15) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hal16|].
  split; [lia|]. split; [lia|]. split; [exact Ht4|]. split; [exact Htc|]. split; [exact Hu4 | exact Huc].
Qed.

(* ---- memory facts across a step that changes memory only below the frame (a runtime callee's window) or in the
   decl's scratch slots [F + 0x20, F + 0x28) (local) and [F + 0x40, F + 0x48) (close) ---- *)
Lemma dd_val_kept : forall (W : world tfibsegs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x) ->
  val_mem tfibsegs (rdW W mem) a n v -> val_mem tfibsegs (rdW W mem') a n v.
Proof.
  intros W mem mem' a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) mem mem');
    [apply Hv; exact Hk|]. apply HA. lia.
Qed.

Definition dd_kept (cx : ecx) (W3 : world tfibsegs) (mem3 mem4 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) -> ~ (cx_F cx + 0x20 <= a < cx_F cx + 0x28) ->
  ~ (cx_F cx + 0x40 <= a < cx_F cx + 0x48) ->
  aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a.

Lemma dd_com_kept : forall cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  dd_kept cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  ex_com B cx ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4 HK Q2 Q3 Q4 Q25.
  pose proof (dd_bounds cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8464) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply HK; lia).
  split; [exact HJ4|]. split; [exact Hbl|].
  split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q25; exact R25|].
  split.
  { unfold ex_saved_ok, EX_SAVED in *.
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
    repeat (apply Forall_cons; [|]); try apply Forall_nil; cbn [fst snd] in *;
      (eapply dd_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia. }
  split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Ct)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Cu)|].
  split; [exact Kt | exact Ku].
Qed.

(* the scan's slots [F + 0x28, F + 0x88) survive a step that keeps them (F + 0x40 is scratch, not a slot) *)
Lemma dd_slots_kept : forall cx W3 mem3 mem4 d,
  ex_slots cx W3 mem3 d ->
  (forall a, cx_F cx + 0x28 <= a < cx_F cx + 0x88 -> ~ (cx_F cx + 0x40 <= a < cx_F cx + 0x48) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  ex_slots cx W3 mem4 d.
Proof.
  intros cx W3 mem3 mem4 d (S30 & S28 & S38 & S48 & S58 & S60 & S68 & S70 & S78 & S80) HK.
  unfold ex_slots.
  repeat split; (eapply dd_val_kept; [|eassumption]); intros x Hx; change (Z.of_nat 8) with 8 in Hx;
    apply HK; lia.
Qed.

(* the declared slot F + 0x30 rewritten (0x816d8): every other slot kept *)
Lemma dd_slots_d : forall cx W3 mem3 mem4 d d',
  ex_slots cx W3 mem3 d ->
  (forall a, cx_F cx + 0x28 <= a < cx_F cx + 0x88 -> ~ (cx_F cx + 0x30 <= a < cx_F cx + 0x38) ->
     ~ (cx_F cx + 0x40 <= a < cx_F cx + 0x48) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  val_mem tfibsegs (rdW W3 mem4) (cx_F cx + 0x30) 8 (Z.of_nat d') ->
  ex_slots cx W3 mem4 d'.
Proof.
  intros cx W3 mem3 mem4 d d' (S30 & S28 & S38 & S48 & S58 & S60 & S68 & S70 & S78 & S80) HK V30.
  unfold ex_slots. split; [exact V30|].
  repeat split; (eapply dd_val_kept; [|eassumption]); intros x Hx; change (Z.of_nat 8) with 8 in Hx;
    apply HK; lia.
Qed.

Lemma dd_com_cuts : forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_scan cx i d f.
Proof. intros cx i d f ly3 S3 W3 regs3 mem3 md3 (HB & HC & HS & _ & Hs & _). tauto. Qed.

(* a cut's common facts after a run that writes nothing and keeps the frame / global registers and s3, s11, s0 *)
Lemma dd_com_same : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 19 = w64 5 -> getr regs4 27 = w64 32 -> getr regs4 8 = w64 (2 ^ 64 - 1) ->
  dd_com cx i d f ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (HB & HC & HSL & _ & HSC & Hi) HJ4 AV
    Q2 Q3 Q4 Q25 R19 R27 R8.
  pose proof (dd_bounds cx HB) as (_ & HFlo & HFhi & _). pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8464) by reflexivity.
  split; [exact HB|].
  split; [exact (dd_com_kept cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4
                  (fun a Ha _ _ _ => AV a Ha) Q2 Q3 Q4 Q25)|].
  split; [apply (dd_slots_kept cx W3 mem3 mem4 d HSL); intros a Ha _; apply AV; lia|].
  split; [split; [exact R19 | split; [exact R27 | exact R8]]|].
  split; [exact HSC | exact Hi].
Qed.

(* the registers a run inside P, D1, D2, D3 keeps (no call yet): the frame / global ones, a6, a7, s7, and the
   constants s3 = 5, s11 = ' ', s0 = -1, t0 = ':', t1 = the mask *)
Definition dd_keepc (regs3 regs4 : bvmap 5 word) : Prop :=
  getr regs4 2 = getr regs3 2 /\ getr regs4 3 = getr regs3 3 /\ getr regs4 4 = getr regs3 4 /\
  getr regs4 25 = getr regs3 25 /\ getr regs4 16 = getr regs3 16 /\ getr regs4 17 = getr regs3 17 /\
  getr regs4 23 = getr regs3 23 /\
  getr regs4 19 = w64 5 /\ getr regs4 27 = w64 32 /\ getr regs4 8 = w64 (2 ^ 64 - 1) /\
  getr regs4 5 = w64 58 /\ getr regs4 6 = w64 EX_MASK1.

Lemma dd_keepc_com : forall cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 -> ex_cregs cx regs3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  dd_keepc regs3 regs4 ->
  dd_com cx i d f ly3 S3 W3 regs4 mem4 md4 /\ ex_cregs cx regs4 /\ getr regs4 23 = getr regs3 23.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC (R16 & R17 & _ & _) HJ4 AV
    (Q2 & Q3 & Q4 & Q25 & Q16 & Q17 & Q23 & R19 & R27 & R8 & R5 & R6).
  split; [exact (dd_com_same cx i d f ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HDC HJ4 AV Q2 Q3 Q4 Q25 R19 R27 R8)|].
  split; [|exact Q23].
  split; [rewrite Q16; exact R16|]. split; [rewrite Q17; exact R17|]. split; [exact R5 | exact R6].
Qed.

(* the exits into the shared block: a declaration that is DNone goes to EX_NEXT with j = i *)
Lemma dd_N_none : forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 -> ex_cregs cx regs3 -> getr regs3 23 = w64 (Z.of_nat i) ->
  MM.decl (cx_tb cx) i = MM.DNone -> dat_N cx i d (pred f) ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 (HB & HC & HSL & HSR & HSC & Hi) HCR R23 Hdn.
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HCR|].
  split; [exact (dd_scan_none cx i d f HSC Hi Hdn) | exact R23].
Qed.

(* a declaration that does not match goes to EX_JUMP with a1 = text + close *)
Lemma dd_J_skip : forall cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 -> ex_slots cx W3 mem3 d -> ex_sregs cx regs3 ->
  ex_cregs cx regs3 -> ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close -> MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = false ->
  getr regs3 11 = w64 (cx_t cx + Z.of_nat close) ->
  dat_J cx close d (pred f) ly3 S3 W3 regs3 mem3 md3 /\ (i <= close)%nat.
Proof.
  intros cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 HB HC HSL HSR HCR HSC Hi Hdc Hm R11.
  destruct (dd_scan_skip cx i d f name nl ns nl2 close HSC Hi Hdc Hm) as (HSC' & Hlt).
  split; [|lia].
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HCR|].
  split; [exact HSC' | exact R11].
Qed.
End c.

(* ---- the walk tactics shared by the decl files (FMW_plain.v fw_reg / pl_av / pl_mk / pl_g, as A's decl files copy
   them) ---- *)
Ltac dd_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac dd_g HS :=
  lazymatch goal with |- getr _ ?r = _ => dd_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac dd_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
Ltac dd_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
(* a run's frame writes only [lo, hi): memory kept outside it, composed with AVw (kept since the entry) *)
Ltac dd_avw W mem0 lo hi Usp :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    assert (AVn : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a)
      by (apply (fw_win tfibsegs _ _ _ _ _ lo hi HFr);
          lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end;
          repeat apply Forall_cons; try apply Forall_nil;
          cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val];
          first [left; lia | right; cbn [ew ewset Nat.eqb]; rewrite Usp; lia]);
    lazymatch goal with AV : forall a, _ -> _ -> aview _ _ m0 a = aview _ _ mem0 a |- _ =>
      let AV2 := fresh "AVw" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
        aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem0 a)
        by (intros a Ha Hn; rewrite (AVn a Ha Hn); exact (AV a Ha Hn));
      clear AV AVn; rename AV2 into AVw end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
(* the run's writes: the frame region (based at sp = F = entry sp - 240) writes only inside expected's stack *)
Ltac dd_awr Usp :=
  first
    [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end
    | lazymatch goal with |- awr_ok ?sg ?Bv ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok sg Bv E rs' stk sp0 fp b0 bc ly own) end ];
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -240);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Usp; unfold cx_F; lia | cbn; lia | cbn; lia |] ].
(* a register's value term: its atoms' values (the E-equations in context), then arithmetic modulo 2^64 *)
Ltac dd_val :=
  lazymatch goal with
  | |- sv_denot _ (SAlu ALU_ADD _ _) = _ => eapply dd_den_add; [dd_val | dd_val]
  | |- sv_denot _ (SAlu ALU_SUB _ _) = _ => eapply dd_den_sub; [dd_val | dd_val]
  | |- sv_denot _ (SMd M_MUL _ _) = _ => eapply dd_den_mul; [dd_val | dd_val]
  | |- sv_denot _ (SOff _ 0) = _ => eapply dd_den_off0; cbn [ew ewset Nat.eqb]; eassumption
  | |- sv_denot _ (SOff _ _) = _ => eapply dd_den_off; cbn [ew ewset Nat.eqb]; eassumption
  | |- sv_denot _ (SLit _) = _ => apply dd_den_lit
  end.
Ltac dd_modeq := apply Z_to_bv64_eq_mod;
  first [reflexivity | rewrite ?Z.add_0_r; reflexivity | f_equal; lia | Z.div_mod_to_equations; lia].
(* close `getr regs4 r = w64 v` (or = getr regs3 r) after dd_reg: the run's term for r over the entry's atoms *)
Ltac dd_rv EE :=
  lazymatch goal with
  | |- sv_denot _ (SOff ?n 0) = getr _ _ =>
      cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity
  | |- sv_denot _ _ = w64 _ => unfold w64; etransitivity; [dd_val | dd_modeq]
  | |- sv_denot _ _ = Z_to_bv 64 _ => etransitivity; [dd_val | dd_modeq]
  end.
Ltac dd_regs HS EE := lazymatch goal with |- getr _ ?r = _ => dd_reg HS r end; dd_rv EE.
Ltac dd_kp HS EE := unfold dd_keepc; repeat match goal with |- _ /\ _ => split end; dd_regs HS EE.
