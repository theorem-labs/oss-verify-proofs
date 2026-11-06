(* G4.ExDecl: ex_seg_P (FMW_ex_base.v) cut into sub-segments. From EX_P (0x81344, p = text + i + a1) the
   declaration body of expected (fuzz_manifest.c:145-170) runs three byte loops, strchr, strncmp and the program
   call plain. The walk is cut at the loop heads and after each call; every cut carries a semantic invariant
   (dat_D1 .. dat_D6 below), and every sub-segment file proves its dseg_* from the ones it jumps to:
     FMW_ex_decl_p.v   EX_P -> {EX_L (i + 1), D1 0}
     FMW_ex_decl_d1.v  D1 k -> {D1 (k + 1), D2 0}                 (the loop by induction)
     FMW_ex_decl_d2.v  D2 j -> {D2 (j + 1), EX_L (i + 1), D3 0}
     FMW_ex_decl_d3.v  D3 m -> {D3 (m + 1), EX_L (i + 1), D3c}
     FMW_ex_decl_d3c.v D3c  -> {D4}                               (strchr)
     FMW_ex_decl_d4.v  D4   -> {EX_R (a0 = 0), EX_L (close + 1), D5} (strncmp)
     FMW_ex_decl_d5.v  D5   -> {EX_L (close + 1), D6}             (plain, a program call)
     FMW_ex_decl_d6.v  D6   -> {EX_L (close + 1), EX_R (a0 = 1), EX_T}
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cut pcs inside ex_seg_P ---- *)
Definition EX_D1 : Z := 0x81380.   (* the spaces after the head word, fuzz_manifest.c:147-148 *)
Definition EX_D2 : Z := 0x813dc.   (* the name up to NUL, ':' or a space, :149 *)
Definition EX_D3 : Z := 0x81454.   (* the spaces after ':', :154 *)
Definition EX_D3c : Z := 0x81490.  (* '<' found: ns = p + 1, strchr (ns, '>') next, :156-159 *)
Definition EX_D4 : Z := 0x8149c.   (* after strchr (ns, '>'), :159 *)
Definition EX_D5 : Z := 0x814c0.   (* after strncmp (uri, ns, ns_len), :162 *)
Definition EX_D6 : Z := 0x8150c.   (* after plain (uri + ns_len), :162 *)

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

(* what every cut of ex_seg_P carries: expected's entry and common facts, the slots with declared = d, the scan's
   constant registers s6 = 6, s2 = 5, s0 = ' ' (s7 = text only at the cuts that reload it), the scan's model state
   at i *)
Definition dd_com (cx : ecx) (i d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\
  getr regs3 22 = w64 6 /\ getr regs3 18 = w64 5 /\ getr regs3 8 = w64 32 /\
  ex_scan cx i d f /\ (i < length (cx_tb cx))%nat.

(* D1 (0x81380): k spaces after p0 = i + a1 skipped, q = p0 + k: a0 = s4 = text + q, s7 = s11 = text + 2 + q,
   s10 = uri - text - 2 - q; s3 = i, s1 = '@', a5 = ':', a6 = the mask *)
Definition dat_D1 (cx : ecx) (i d f a1 k : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ dm_p0 cx i a1 /\
  (k <= MM.count_while MM.is_space (skipn (i + a1) (cx_tb cx)))%nat /\
  getr regs3 10 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) /\ getr regs3 20 = w64 (cx_t cx + Z.of_nat (i + a1 + k)) /\
  getr regs3 23 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k)) /\
  getr regs3 27 = w64 (cx_t cx + 2 + Z.of_nat (i + a1 + k)) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat (i + a1 + k)) /\
  getr regs3 19 = w64 (Z.of_nat i) /\ getr regs3 9 = w64 64 /\ getr regs3 15 = w64 58 /\
  getr regs3 16 = w64 EX_MASK1.

(* D2 (0x813dc): the name from p1 on, j bytes taken, a1 = the byte at p1 + j: a0 = s4 = text + p1, a4 = i, s5 = j,
   s8 = 1 + j, s3 = s1 = text + 1 + j, s7 = s11 = text + 2 + p1 + j, s10 = uri - text - 2 - p1 - j *)
Definition dat_D2 (cx : ecx) (i d f a1 p1 j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ dm_p1 cx i a1 p1 /\
  (j <= MM.count_while MM.name_ok (skipn p1 (cx_tb cx)))%nat /\
  getr regs3 11 = w64 (MM.byte_at (cx_tb cx) (p1 + j)) /\
  getr regs3 10 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 14 = w64 (Z.of_nat i) /\ getr regs3 21 = w64 (Z.of_nat j) /\ getr regs3 24 = w64 (1 + Z.of_nat j) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat j) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat j) /\
  getr regs3 23 = w64 (cx_t cx + 2 + Z.of_nat p1 + Z.of_nat j) /\
  getr regs3 27 = w64 (cx_t cx + 2 + Z.of_nat p1 + Z.of_nat j) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat p1 - Z.of_nat j) /\
  getr regs3 15 = w64 58 /\ getr regs3 16 = w64 EX_MASK1.

(* D3 (0x81454): ':' at p2, m spaces after it skipped: s4 = text + p1, a4 = i, s5 = p2 - p1, s8 = 1 + s5,
   s3 = s1 = text + 1 + s5, s7 = s11 = text + 2 + p2 + m, s10 = uri - text - 2 - p2 - m *)
Definition dat_D3 (cx : ecx) (i d f a1 p1 p2 m : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ dm_p2 cx i a1 p1 p2 /\
  (m <= MM.count_while MM.is_space (skipn (S p2) (cx_tb cx)))%nat /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 14 = w64 (Z.of_nat i) /\
  getr regs3 21 = w64 (Z.of_nat (p2 - p1)) /\ getr regs3 24 = w64 (1 + Z.of_nat (p2 - p1)) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\
  getr regs3 23 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat m) /\
  getr regs3 27 = w64 (cx_t cx + 2 + Z.of_nat p2 + Z.of_nat m) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - 2 - Z.of_nat p2 - Z.of_nat m) /\
  getr regs3 15 = w64 58 /\ getr regs3 16 = w64 EX_MASK1.

(* D3c (0x81490): the '<' at p3: s4 = text + p1, s5 = p2 - p1, s8 = 1 + s5, s3 = s1 = text + 1 + s5,
   s7 = s11 = text + p3 + 1 = ns, s10 = uri - text - p3 - 1 *)
Definition dat_D3c (cx : ecx) (i d f a1 p1 p2 p3 : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\ dm_p3 cx i a1 p1 p2 p3 /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 21 = w64 (Z.of_nat (p2 - p1)) /\ getr regs3 24 = w64 (1 + Z.of_nat (p2 - p1)) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat (p2 - p1)) /\
  getr regs3 23 = w64 (cx_t cx + Z.of_nat (S p3)) /\ getr regs3 27 = w64 (cx_t cx + Z.of_nat (S p3)) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat (S p3)).

(* D4 (0x8149c): strchr (ns, '>') answered r: the declaration is DCut (r = 0) or DFound name nl ns nl2 close
   (r = text + close); s4 = text + name, s5 = nl, s8 = 1 + nl, s3 = s1 = text + 1 + nl, s7 = s11 = text + ns,
   s10 = uri - text - ns *)
Definition dat_D4 (cx : ecx) (i d f name nl ns nl2 close : nat) (r : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  ((MM.decl (cx_tb cx) i = MM.DCut /\ r = 0) \/
   (MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ r = cx_t cx + Z.of_nat close)) /\
  getr regs3 10 = w64 r /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 24 = w64 (1 + Z.of_nat nl) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 23 = w64 (cx_t cx + Z.of_nat ns) /\ getr regs3 27 = w64 (cx_t cx + Z.of_nat ns) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat ns).

(* D5 (0x814c0): ns_len = nl2 < n, F+0x28 = close = text + close; strncmp (uri, ns, nl2) answered v *)
Definition dat_D5 (cx : ecx) (i d f name nl ns nl2 close : nat) (v : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ (nl2 < length (cx_ub cx))%nat /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat close) /\
  getr regs3 10 = w64 v /\ 0 <= v < 2 ^ 64 /\
  (v = 0 <-> firstn nl2 (skipn ns (cx_tb cx)) = firstn nl2 (cx_ub cx)) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 24 = w64 (1 + Z.of_nat nl) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 26 = w64 (cx_u cx - cx_t cx - Z.of_nat ns).

(* D6 (0x8150c): the namespace equals the uri's first nl2 bytes; plain (uri + nl2) answered; F+8 = local =
   uri + nl2, F+0x28 = text + close *)
Definition dat_D6 (cx : ecx) (i d f name nl ns nl2 close : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 /\
  MM.decl (cx_tb cx) i = MM.DFound name nl ns nl2 close /\ (nl2 < length (cx_ub cx))%nat /\
  firstn nl2 (skipn ns (cx_tb cx)) = firstn nl2 (cx_ub cx) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat close) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 8) 8 (cx_u cx + Z.of_nat nl2) /\
  getr regs3 10 = w64 (if MM.plain_name (skipn nl2 (cx_ub cx)) then 1 else 0) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 24 = w64 (1 + Z.of_nat nl) /\
  getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl).

(* ---- the sub-segment statements: every cut reaches expected's post ---- *)
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

(* ---- facts the entry gives every cut ---- *)
Lemma dd_bounds : forall cx, ex_base B cx ->
  cx_F cx mod 16 = 0 /\ alloc_ceiling + STK_expected - 208 <= cx_F cx /\ cx_F cx + 208 <= 2 ^ 47 /\
  4096 <= cx_t cx /\ cx_t cx + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling /\
  4096 <= cx_u cx /\ cx_u cx + Z.of_nat (length (cx_ub cx)) + 8 <= alloc_ceiling.
Proof.
  intros cx ((HPRE & _) & _ & _ & _ & Ct & Cu & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof Ct as (_ & Ht4 & Htc & _). pose proof Cu as (_ & Hu4 & Huc & _).
  unfold cx_F, cx_sp in *.
  split; [replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hal16|].
  split; [lia|]. split; [lia|]. split; [exact Ht4|]. split; [exact Htc|]. split; [exact Hu4 | exact Huc].
Qed.

(* ---- memory facts across a step that changes memory only below the frame (a runtime callee's window) or in the
   frame's scratch slots [F, F + 0x18) and [F + 0x28, F + 0x30) ---- *)
Lemma dd_val_kept : forall (W : world tfibsegs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x) ->
  val_mem tfibsegs (rdW W mem) a n v -> val_mem tfibsegs (rdW W mem') a n v.
Proof.
  intros W mem mem' a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) mem mem');
    [apply Hv; exact Hk|]. apply HA. lia.
Qed.

Definition dd_kept (cx : ecx) (W3 : world tfibsegs) (mem3 mem4 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) -> ~ (cx_F cx <= a < cx_F cx + 0x18) ->
  ~ (cx_F cx + 0x28 <= a < cx_F cx + 0x30) ->
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
  assert (FS : STK_expected = 8432) by reflexivity. assert (FR : STK_RT_STR = 8192) by reflexivity.
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

Lemma dd_slots_kept : forall cx W3 mem3 mem4 d,
  ex_base B cx -> ex_slots cx W3 mem3 d ->
  (forall a, cx_F cx + 0x18 <= a < cx_F cx + 0x68 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  ex_slots cx W3 mem4 d.
Proof.
  intros cx W3 mem3 mem4 d HB (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60) HK.
  unfold ex_slots.
  repeat split; (eapply dd_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia.
Qed.

(* the declared slot rewritten (0x81528): every other slot kept *)
Lemma dd_slots_d : forall cx W3 mem3 mem4 d d',
  ex_base B cx -> ex_slots cx W3 mem3 d ->
  (forall a, cx_F cx + 0x20 <= a < cx_F cx + 0x68 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  val_mem tfibsegs (rdW W3 mem4) (cx_F cx + 0x18) 8 (Z.of_nat d') ->
  ex_slots cx W3 mem4 d'.
Proof.
  intros cx W3 mem3 mem4 d d' HB (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60) HK V18.
  unfold ex_slots. split; [exact V18|].
  repeat split; (eapply dd_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia.
Qed.

Lemma dd_com_cuts : forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  dd_com cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  ex_base B cx /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_scan cx i d f.
Proof. intros cx i d f ly3 S3 W3 regs3 mem3 md3 (HB & HC & HS & _ & _ & _ & Hs & _). tauto. Qed.
End c.
