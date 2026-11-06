(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: loop 3 of image B's (fuzz_reply.asan-ubsan) walk of check_shape_ends (0x85770),
   the `while (want-- > 0)` loop of the g_gone = 0 path, from its head 0x8597c at first entry (W_cshe_epi.v cshe_l3_in)
   to the epilogue's entry 0x8592c (W_cshe_epi.v cshe_out_B).  A segment lemma for BCheckShapeEvent's
   pb_check_shape_ends (lib/B/W_check_shape_ends.v).  Structure ported from lib/A/W_cshe_l3.v (a working branch
   8a2058dadf4: l3_inv / l3_ab / l3_A1 / l3_A2 and the ends_run step lemmas, copied below with the prefix bl3) and, for the
   out-of-line list_drop, lib/B/W_check_no_loss.v (a working branch 5ef01234da3: cnl_drop's LDROP call, the
   journal splice and the block step).
   The B body (B_cshe.dis (sha256 ad90d15b451b; internal record) 0x8597c-0x85a0c) is not A's: B has no inline shadow checks here, keeps the line
   and its length in sp + 8 / sp (next_line's out cells), checks line + len with four UBSan traps (0x859a8 PTR_BLTU,
   0x859ac / 0x859b0 NONNULL, 0x859b4 PTR_DEC), CALLS list_drop at 0x85a00 (A inlines free + __asan_memmove), and its
   back-edge 0x85a0c `blt a0,s8` falls through to the unimp at 0x85a10 (DECW_FT).  Each abort arm (0x85a14) is refuted
   from cshe_spec's functional pre `gone = 0 -> ends_run ... <> None`, carried as the loop invariant's ends_run. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_traps W_shadow_pin W_cshe_epi.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel next_line_c.
(* The sink-instance guard, after every import (MERGE.md (sha256 0694aca87ccd; internal record) item 3) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side (CheckRep), lib/A/W_cshe_l3.v's *)
Lemma bl3_bz_inj : forall a b : byte, bz a = bz b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.
Lemma bl3_bzs_inj : forall a b : list byte, bzs a = bzs b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bl3_bz_inj; exact H1 | apply IH; exact H2].
Qed.
Lemma bl3_leqb : forall a b : list byte, RelayModel.list_eqb (bzs a) (bzs b) = true <-> a = b.
Proof.
intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec (bzs a) (bzs b)) as [E|E]; split; intros H.
- exact (bl3_bzs_inj a b E).
- reflexivity.
- discriminate.
- exfalso. apply E. rewrite H. reflexivity.
Qed.
Lemma bl3_split_nul : forall d l d', CheckRep.split_nul d = Some (l, d') ->
d = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l.
Proof.
induction d as [|b d IH]; intros l d' H; cbn [CheckRep.split_nul] in H; [discriminate|].
destruct (bv_unsigned b =? 0) eqn:Eb.
- injection H as <- <-. apply Z.eqb_eq in Eb. split; [|intros []].
  cbn. f_equal. apply bv_eq. rewrite Eb. reflexivity.
- destruct (CheckRep.split_nul d) as [[l0 r0]|] eqn:E; [|discriminate].
  injection H as <- <-. destruct (IH l0 r0 eq_refl) as [-> Hn]. split; [reflexivity|].
  intros [Hx | Hx]; [|exact (Hn Hx)]. subst b. rewrite Z.eqb_neq in Eb. apply Eb. reflexivity.
Qed.
Lemma bl3_split_nul_app : forall l d', ~ In (Z_to_bv 8 0) l -> CheckRep.split_nul (l ++ Z_to_bv 8 0 :: d') = Some (l, d').
Proof.
induction l as [|b l IH]; intros d' Hn; cbn [app CheckRep.split_nul].
- reflexivity.
- destruct (bv_unsigned b =? 0) eqn:Eb.
  + exfalso. apply Hn. left. apply bv_eq. apply Z.eqb_eq in Eb. rewrite Eb. reflexivity.
  + rewrite IH by (intros H; apply Hn; right; exact H). reflexivity.
Qed.
(* the first line of a NUL-terminated split is unique *)
Lemma bl3_nul_unique : forall (l1 l2 r1 r2 : list byte), l1 ++ Z_to_bv 8 0 :: r1 = l2 ++ Z_to_bv 8 0 :: r2 ->
~ In (Z_to_bv 8 0) l1 -> ~ In (Z_to_bv 8 0) l2 -> l1 = l2 /\ r1 = r2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] r1 r2 E H1 H2; cbn in E.
- injection E as E. split; [reflexivity | exact E].
- injection E as Ey _. exfalso. apply H2. left. symmetry. exact Ey.
- injection E as Ex _. exfalso. apply H1. left. exact Ex.
- injection E as -> E. destruct (IH l2 r1 r2 E) as [-> ->]; [intros H; apply H1; right; exact H | intros H; apply H2; right; exact H|].
  split; reflexivity.
Qed.
Lemma bl3_find_text : forall y rs i, CheckRep.find_text y rs = Some i ->
(i < length rs)%nat /\ snd (nth i rs (0, [])) = y /\ (forall k, (k < i)%nat -> snd (nth k rs (0, [])) <> y).
Proof.
intros y rs. induction rs as [|r rs IH]; intros i H; cbn [CheckRep.find_text] in H; [discriminate|].
destruct (RelayModel.list_eqb (bzs (snd r)) (bzs y)) eqn:E.
- injection H as <-. apply bl3_leqb in E. split; [cbn; lia|]. split; [exact E | intros k Hk; lia].
- destruct (CheckRep.find_text y rs) as [i0|] eqn:Ef; [|discriminate]. cbn in H. injection H as <-.
  destruct (IH i0 eq_refl) as (H1 & H2 & H3). split; [cbn; lia|]. split; [exact H2|].
  intros [|k] Hk; cbn [nth].
  + intros Hc. rewrite <- Hc in E. assert (Ht : RelayModel.list_eqb (bzs (snd r)) (bzs (snd r)) = true) by (apply bl3_leqb; reflexivity).
    rewrite Ht in E. discriminate.
  + apply H3. lia.
Qed.
(* the first match is unique *)
Lemma bl3_first_unique : forall (rs : list (Z * list byte)) y i j,
snd (nth i rs (0, [])) = y -> (forall k, (k < i)%nat -> snd (nth k rs (0, [])) <> y) ->
snd (nth j rs (0, [])) = y -> (forall k, (k < j)%nat -> snd (nth k rs (0, [])) <> y) -> i = j.
Proof.
intros rs y i j Hi Hi' Hj Hj'. destruct (Nat.lt_trichotomy i j) as [Hl | [He | Hl]]; [| exact He |].
- exfalso. exact (Hj' i Hl Hi).
- exfalso. exact (Hi' j Hl Hj).
Qed.
Definition bl3_ok (P l : list byte) : bool :=
Nat.leb 4 (length l) && RelayModel.list_eqb (bzs (skipn (length l - 4) l)) (bzs CheckRep.END4) && CheckRep.prefixb P l.
(* one step of ends_run, taken apart *)
Lemma bl3_ends_S : forall P rs d w rsF dsF cF, CheckRep.ends_run P rs d (S w) = Some (rsF, dsF, cF) ->
exists l d' i dsR cR, d = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ bl3_ok P l = true /\
CheckRep.find_text (firstn (length l - 4) l) rs = Some i /\
CheckRep.ends_run P (CheckRep.drop_nth i rs) d' w = Some (rsF, dsR, cR) /\
dsF = nth i rs (0, []) :: dsR /\ cF = Z.of_nat (length l) + 1 + cR.
Proof.
intros P rs d w rsF dsF cF H. cbn [CheckRep.ends_run] in H.
destruct (CheckRep.split_nul d) as [[l d']|] eqn:E1; [|discriminate].
destruct (Nat.leb 4 (length l) && RelayModel.list_eqb (bzs (skipn (length l - 4) l)) (bzs CheckRep.END4) &&
  CheckRep.prefixb P l) eqn:E2; [|discriminate].
destruct (CheckRep.find_text (firstn (length l - 4) l) rs) as [i|] eqn:E3; [|discriminate].
destruct (CheckRep.ends_run P (CheckRep.drop_nth i rs) d' w) as [[[x y] z]|] eqn:E4; [|discriminate].
injection H as <- <- <-. destruct (bl3_split_nul d l d' E1) as [Ed Hn].
exists l, d', i, y, z. repeat split; assumption.
Qed.
(* and put back together *)
Lemma bl3_ends_step : forall P rs l d' i w rsF dsR cR,
~ In (Z_to_bv 8 0) l -> bl3_ok P l = true ->
CheckRep.find_text (firstn (length l - 4) l) rs = Some i ->
CheckRep.ends_run P (CheckRep.drop_nth i rs) d' w = Some (rsF, dsR, cR) ->
CheckRep.ends_run P rs (l ++ Z_to_bv 8 0 :: d') (S w) = Some (rsF, nth i rs (0, []) :: dsR, Z.of_nat (length l) + 1 + cR).
Proof.
intros P rs l d' i w rsF dsR cR Hn Hok Hf Hr. cbn [CheckRep.ends_run]. rewrite (bl3_split_nul_app l d' Hn).
unfold bl3_ok in Hok. rewrite Hok, Hf, Hr. reflexivity.
Qed.
Lemma bl3_drop_len : forall (rs : list (Z * list byte)) i, (i < length rs)%nat ->
length (CheckRep.drop_nth i rs) = (length rs - 1)%nat.
Proof.
intros rs i Hi. unfold CheckRep.drop_nth. rewrite length_app, length_firstn, length_skipn. lia.
Qed.
Lemma bl3_ends_len : forall P w rs d, CheckRep.ends_run P rs d w <> None -> (w <= length rs)%nat.
Proof.
intros P w. induction w as [|w IH]; intros rs d H; [lia|].
destruct (CheckRep.ends_run P rs d (S w)) as [[[x y] z]|] eqn:E; [|exfalso; exact (H eq_refl)].
destruct (bl3_ends_S P rs d w x y z E) as (l & d' & i & dsR & cR & _ & _ & _ & Hf & Hr & _).
destruct (bl3_find_text _ _ _ Hf) as (Hi & _).
pose proof (IH (CheckRep.drop_nth i rs) d' ltac:(rewrite Hr; discriminate)) as Hl.
rewrite (bl3_drop_len rs i Hi) in Hl. lia.
Qed.
Lemma bl3_ends_O : forall P rs d rsF dsF cF, CheckRep.ends_run P rs d 0 = Some (rsF, dsF, cF) ->
rsF = rs /\ dsF = [] /\ cF = 0.
Proof. intros P rs d rsF dsF cF H. cbn in H. injection H as <- <- <-. auto. Qed.
Lemma bl3_drop_split : forall (A Bs : list (Z * list byte)) x,
CheckRep.drop_nth (length A) (A ++ x :: Bs) = A ++ Bs.
Proof. intros A. unfold CheckRep.drop_nth. induction A as [|a A IH]; intros Bs x; cbn; [reflexivity | f_equal; apply IH]. Qed.
Lemma bl3_nodup_drop : forall {Y : Type} (f : Z * list byte -> Y) (l : list (Z * list byte)) i,
NoDup (map f l) -> NoDup (map f (CheckRep.drop_nth i l)).
Proof.
intros Y f l i H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
- destruct (nth_split l (0, []) Hi) as (A & Bs & Hsp & HlA). rewrite Hsp in H |- *. rewrite <- HlA, bl3_drop_split.
  rewrite map_app in H |- *. cbn [map] in H. exact (NoDup_remove_1 _ _ _ H).
- unfold CheckRep.drop_nth. rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite app_nil_r. exact H.
Qed.
Lemma bl3_nth_line : forall (ob l d' : list byte) A k, skipn A ob = l ++ Z_to_bv 8 0 :: d' -> (k < length l)%nat ->
nth (A + k) ob (Z_to_bv 8 0) = nth k l (Z_to_bv 8 0).
Proof.
intros ob l d' A k E Hk. rewrite <- (firstn_skipn A ob) at 1.
assert (HA : length (firstn A ob) = A).
{ rewrite length_firstn. destruct (Nat.le_gt_cases A (length ob)) as [H|H]; [lia|].
  rewrite skipn_all2 in E by lia. destruct l; discriminate E. }
rewrite app_nth2 by lia. rewrite HA. replace (A + k - A)%nat with k by lia. rewrite E. apply app_nth1. exact Hk.
Qed.
Lemma bl3_nth_skipn : forall (l : list byte) m n, nth n (skipn m l) (Z_to_bv 8 0) = nth (m + n) l (Z_to_bv 8 0).
Proof. intros l m. revert l. induction m as [|m IH]; intros [|x l] n; cbn; try reflexivity. destruct n; reflexivity. apply IH. Qed.
Lemma bl3_skip_line : forall (ob l d' : list byte) A, skipn A ob = l ++ Z_to_bv 8 0 :: d' ->
skipn (A + length l + 1) ob = d'.
Proof.
intros ob l d' A E. replace (A + length l + 1)%nat with (S (length l) + A)%nat by lia.
rewrite <- skipn_skipn, E. clear E. induction l as [|x l IH]; [reflexivity|]. exact IH.
Qed.
Lemma bl3_incl_drop : forall (l : list (Z * list byte)) i, incl (CheckRep.drop_nth i l) l.
Proof.
intros l i x Hx. unfold CheckRep.drop_nth in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite <- (firstn_skipn i l). apply in_or_app. left. exact Hx.
- rewrite <- (firstn_skipn (S i) l). apply in_or_app. right. exact Hx.
Qed.

(* ------------------------------------------------------------------ the walk's Section, as W_cshe_epi.v's *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the cut points of one turn, as offsets of the listing (AF_fr_check_shape_ends = 0x342c, 0x85770) *)
Definition A_cl3_ab : Z := AF_fr_check_shape_ends + 0x25c.  (* 0x859cc, after bcmp of the line's end with " end" *)
Definition A_cl3_dr : Z := AF_fr_check_shape_ends + 0x294.  (* 0x85a04, list_drop's return *)

(* ------------------------------------------------------------------ the loop head 0x8597c *)
(* At the head (sp = sp0 - 112): s0 (x8) = PF, s1 (x9) = HA + 80 = the held list, s2 (x18) = AT, s3 (x19) = " end",
   s5 (x21) = 4, s6 (x22) = w the turns left, s7 (x23) = 5, a0 = w - 1.  s5 and s7 are pinned to their literals, so
   the length check 0x8599c `bltu s6,s5` and the trap 0x859b4 `bltu a0,s7` compare an atom with a literal.  The two
   extra atoms are the turn's line (32, its address in the stream) and its length (33): the model fixes both before
   next_line runs, and the cells region added after the call holds them. *)
Definition cl3_sr : list sv := sr_set (sr_set sr_atoms 21%bv (SLit 4)) 23%bv (SLit 5).
Definition cl3_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (22%nat, mkAF 1 (2 ^ 26) 0); (10%nat, mkAF 0 (2 ^ 26) 0);
(32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 4 (2 ^ 32) 0) ] [] [].
Definition ss_cl3 : sstate := mkSS A_csheB_l3 cl3_sr [] None cl3_facts.
(* no shadow check in this loop: no shadow entry, and the token engine's shadow base is never read *)
Definition cl3_Bx : sv := SLit SB.
(* next_line's two out cells in this frame, once it returned: sp + 0 the line's length (atom 33), sp + 8 its address
   (atom 32) *)
Definition cl3_cells : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition cl3_extra (line len : Z) : list word := map (Z_to_bv 64) [line; len].
(* the last head: s6 = 0, `blez s6` goes to the epilogue *)
Definition cl3_facts0 : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (22%nat, mkAF 0 0 0) ] [] [].
Definition ss_cl30 : sstate := mkSS A_csheB_l3 cl3_sr [] None cl3_facts0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma cl3_state : forall (W1 : world SEGS) regs mem SP w line len,
getr regs 2 = w64 SP -> getr regs 21 = w64 4 -> getr regs 23 = w64 5 ->
getr regs 22 = w64 w -> getr regs 10 = w64 (w - 1) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 1 <= w <= 2 ^ 26 ->
4096 <= line <= 140737479966720 -> 4 <= len <= 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cl3_extra line len))) ss_cl3
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_csheB_l3)) mem (seg_rom SEGS))) /\
sh_ok SEGS cl3_Bx [] (Eimg (Ereg regs (cl3_extra line len))) (mrestrict (w_H W1) mem).
Proof.
intros W1 regs mem SP w line len H2 H21 H23 H22 H10 HSP HSPa Hw Hl Hln.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs (cl3_extra line len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cl3_extra line len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E22 : ew E 22 = Z_to_bv 64 w) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E10 : ew E 10 = Z_to_bv 64 (w - 1)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 line) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (EX 1%nat ltac:(lia)).
split.
- rewrite restrict_mkst_fx. unfold ss_cl3. apply pa_entry_st_ok_full.
  + unfold cl3_sr.
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H23; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H21; reflexivity].
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [cl3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E22, E10, E32, E33, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- constructor.
Qed.

Lemma cl3_state0 : forall (W1 : world SEGS) regs mem SP,
getr regs 2 = w64 SP -> getr regs 21 = w64 4 -> getr regs 23 = w64 5 -> getr regs 22 = w64 0 ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_cl30
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_csheB_l3)) mem (seg_rom SEGS))) /\
sh_ok SEGS cl3_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W1) mem).
Proof.
intros W1 regs mem SP H2 H21 H23 H22 HSP HSPa.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs [])).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E22 : ew E 22 = Z_to_bv 64 0) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
split.
- rewrite restrict_mkst_fx. unfold ss_cl30. apply pa_entry_st_ok_full.
  + unfold cl3_sr.
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H23; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H21; reflexivity].
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [cl3_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E22, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- constructor.
Qed.

(* ------------------------------------------------------------------ 0x859cc, after bcmp *)
(* s4 (x20) = the line, s6 (x22) = its length, s8 (x24) = w the turns left after this one; next_line's two cells
   at sp + 0 / sp + 8 hold s6 / s4 *)
Definition cl3b_cells : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 22 0)); YP09.mkChunk 8 (CVal 8 (SOff 20 0))].
Definition cl3b_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (24%nat, mkAF 0 (2 ^ 26) 0);
(20%nat, mkAF 4096 140737479966720 0); (22%nat, mkAF 4 (2 ^ 32) 0) ] [] [].
Definition ss_cl3b : sstate := mkSS A_cl3_ab cl3_sr [ cl3b_cells ] None cl3b_facts.

Lemma cl3b_state : forall (W1 : world SEGS) regs mem SP w line len,
getr regs 2 = w64 SP -> getr regs 21 = w64 4 -> getr regs 23 = w64 5 ->
getr regs 24 = w64 w -> getr regs 22 = w64 len -> getr regs 20 = w64 line ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= w <= 2 ^ 26 ->
4096 <= line <= 140737479966720 -> 4 <= len <= 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W1) mem) SP 8 len -> val_mem SEGS (mrestrict (w_H W1) mem) (SP + 8) 8 line ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_cl3b
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_cl3_ab)) mem (seg_rom SEGS))) /\
sh_ok SEGS cl3_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W1) mem).
Proof.
intros W1 regs mem SP w line len H2 H21 H23 H24 H22 H20 HSP HSPa Hw Hl Hln M0 M8.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs [])).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E24 : ew E 24 = Z_to_bv 64 w) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E22 : ew E 22 = Z_to_bv 64 len) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E20 : ew E 20 = Z_to_bv 64 line) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (V2 : base_val E (Some 2%nat) = SP) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_cl3b. apply pa_entry_st_ok_full.
  + unfold cl3_sr.
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H23; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H21; reflexivity].
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cl3b_cells. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ SP 0 8 (SOff 22 0) len);
      [cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact M0.
    * apply (chunk_ok_val SEGS E _ SP 8 8 (SOff 20 0) line);
      [cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
  + apply pairwise_disjoint_of_extents. unfold cl3b_cells, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [cl3b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E24, E20, E22, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- constructor.
Qed.

(* ------------------------------------------------------------------ 0x85a04, list_drop's return *)
(* s8 (x24) = w the turns left after this one; the back-edge `addiw a0,s8,-1; mv s6,s8; blt a0,s8` reaches the head
   with s6 = w, a0 = w - 1 *)
Definition cl3d_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (24%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cl3d : sstate := mkSS A_cl3_dr cl3_sr [] None cl3d_facts.

Lemma cl3d_state : forall (W1 : world SEGS) regs mem SP w,
getr regs 2 = w64 SP -> getr regs 21 = w64 4 -> getr regs 23 = w64 5 -> getr regs 24 = w64 w ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= w <= 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_cl3d
(restrict (w_H W1) (mkst regs (Z_to_bv 64 (BASE + A_cl3_dr)) mem (seg_rom SEGS))) /\
sh_ok SEGS cl3_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W1) mem).
Proof.
intros W1 regs mem SP w H2 H21 H23 H24 HSP HSPa Hw.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs [])).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E24 : ew E 24 = Z_to_bv 64 w) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
split.
- rewrite restrict_mkst_fx. unfold ss_cl3d. apply pa_entry_st_ok_full.
  + unfold cl3_sr.
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H23; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H21; reflexivity].
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [cl3d_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E24, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
- constructor.
Qed.

Section c.
Variable B : asyms.
(* ARx conversion (route (b); A's lib/A/W_check_shape_ends.v Section c on a working branch 4f281bf9308): the
   generic allocator relation ARx with its laws, the placement PST, the room record RP; HP0 (every ghost list is []),
   IMGC (the image's cover) and BLKN (a block's size is >= 0) as W_check_no_loss.v's Section c takes them *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* The agreed Section hypotheses of the pieces (W_cshe_epi.v Section io's comment), by those names; LDROP in the form
   BCheckShapeEvent fixed at 2026-10-29 (B's pb_list_drop's Section form, a working branch
   436074f627e lib/B/W_list_drop.v:561-572): list_drop is taken at its own globals G' and lifted to G. *)
(* W_frame_x.v Section q's FRMF (the fake frames' alignment: the generic counterpart of YG0s.v frame_facts; at ARi0:
   W_frame_x.FRMF_AR) *)
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* the image is off the placement PST: the generic journal's image clause keeps a byte only outside PST *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop).
Hypothesis HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix).
Hypothesis HGR : gx_ok SEGS B cshe_ro_B.
Hypothesis HGRR : gx_rt B cshe_ro_B.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL A_lit_end5) 4 /\
  (0 < 4 -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL A_lit_end5) 4).
Hypothesis HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Let RUN := paj_run_x_x B PST ARx LAWS G HG.
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG.
Let BR := paj_branch (PI := PI).
(* ---- the walk at the empty ghost list (HP0: every ARx state's ghost list is []): AR0 / AJ0 / AJi0 / AFP0 are cgif's
   AR / journal / inner journal / afn_pre at Hp = [], and each kit lemma the AR walk cites is its _x twin at [] ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x SEGS B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation ajournal_gx_AR0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0 G0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_x SEGS B PST ARx G0 G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0 Hs G0 STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_x SEGS B PST ARx LAWS Hs G0 STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0 G0 XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_x SEGS B PST ARx G0 XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0 pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_x B PST ARx LAWS pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc k x y n o
     raw).
Local Notation range_addressable_of_block0 ly S W mem md :=
  (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation shadow_hull_vis_of_block0 ly S W mem md :=
  (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation sep_blocks0 ly S W mem md := (sep_blocks_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation sep_block_frame0 ly S W mem md := (sep_block_frame_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frm_img0 ly S W mem md := (frm_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation amem_range_of_block0 ly S W mem md := (amem_range_of_block_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation rom_pinned_view0 ly S W mem md := (rom_pinned_view_x SEGS B ARx LAWS ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_kit_x.blk_off_imgP_x's proof, at this file's off_img (lib/B/YCbq.v: IMG_TOP_B = 0x5fc000) *)
Lemma cshe_blk_off_img : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) -> off_img p (req_size n).
Proof.
  intros ly S W mem md p n HAR Hin. unfold off_img.
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n (BLKN ly S [] W mem md p n HAR Hin)) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* W_frame.v's frame_al64 / shadow_hull_vis_of_frame at AR0: W_frame_x's twins over FRMF *)
Lemma frame_al640 : forall ly S (W : world SEGS) mem md cid pos, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof. intros ly S W mem md cid pos HAR Hin. eapply frame_al64_x; eassumption. Qed.
Lemma shadow_hull_vis_of_frame0 : forall ly S (W : world SEGS) mem md cid pos d n,
  AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) d n.
Proof. intros ly S W mem md cid pos d n HAR Hin H1 H2 H3. eapply shadow_hull_vis_of_frame_x; eassumption. Qed.
(* W_frame_b.v frm_off_imgB (a fake frame lies off image B's own image [0x10000, 0x5fc000)) at AR0: its proof, with
   IMGC for the image's cover and FRMF for the frame's size *)
Lemma cshe_frm_off_img : forall ly S (W : world SEGS) mem md cid pos, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos HAR Hin.
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (FRMF ly S [] W mem md cid pos HAR Hin) as (_ & _ & F64 & _).
  destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max (frame_addr ly cid pos) 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max (frame_addr ly cid pos) 0x10000) HAR _)).
    right. left. exists cid, pos. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* a drop removes one block: the live counts do not grow *)
Lemma cl3_cnt_del : forall RP0 l1 l2 b, cnt_ok RP0 (l1 ++ b :: l2) -> cnt_ok RP0 (l1 ++ l2).
Proof.
intros RP0 l1 l2 b H. refine (cnt_ok_pk_mono RP0 _ _ _ _ _ H).
intros P0. pose proof (ReplyCnt.acnt_del_le P0 l1 l2 b). lia.
Qed.
(* MT_rk's free costs 1: the budget for n records is n *)
Lemma cl3_rk : forall n, Z.to_nat (Z.of_nat n * mo_free MT_rk) = n.
Proof. intros n. change (mo_free MT_rk) with 1. rewrite Z.mul_1_r. apply Nat2Z.id. Qed.
(* W_check_shape_event.v range_addressable_stack: the stack's shadow is zero (AR's zero-shadow law) *)
Lemma cl3_ra_stack : forall ly S W mem md a len,
AR0 ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S W mem md a len HAR Hlo Hhi Hlen x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly S [] W mem md x HAR ltac:(lia)).
Qed.
(* W_check_no_loss.v's cnl_blk / cnl_vec_len / cnl_rec_len / cnl_src_low / cnl_src_kept, copied: that file's
   lemmas live in its own Section, over its own hypotheses.  What they say: every byte the source's predicate
   reads is an application byte below the allocator's ceiling, so a run that only writes its own frame keeps
   the source - once its bytes keep their ASan view and nothing it had goes absent. *)
Lemma cl3_blk : forall ly S W mem md p n, AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ 1 <= req_size n /\ p + req_size n <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\ off_img p (req_size n) /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al0_blocks ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpr & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2]. pose proof asan_consts as (C1 & _).
pose proof (cshe_blk_off_img _ _ _ _ _ p n HAR Hin) as Hoff.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hoff|]. split; [exact Hia|]. exact Hpr.
Qed.
Lemma cl3_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma cl3_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cl3_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma cl3_src_low : forall ly1 S1 W1 mem1 md1 HA1 h1,
AR0 ly1 S1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x7fff8000 ->
forall rr, In rr (asrc_fp HA1 h1) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi.
pose proof asan_consts as (C1 & _).
assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
  0x10000 <= LA -> LA + 16 <= 0x7fff8000 ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros l LA Hl Hlo Hhi rr Hin a Ha.
  assert (HL : alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false) by exact Hl.
  destruct HL as [HA2 | HA2];
  (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
   unfold alist_fp in Hin; cbn [In] in Hin;
   destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; lia|];
   apply in_app_or in Hin as [Hin | Hin];
   [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|];
     destruct Hin as [<- | []];
     destruct Hv as [(Hc0 & _) | (Hc & Hvin & Hj & Hg)]; [apply Z.eqb_neq in Ec; lia|];
     destruct (cl3_blk ly1 S1 W1 mem1 md1 _ _ HAR Hvin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     unfold gfp in Ha; cbn [fst snd] in Ha; rewrite (cl3_vec_len l Hj) in Ha; lia
   | apply in_map_iff in Hin as (r & <- & Hr);
     rewrite Forall_forall in Hrec; destruct (Hrec r Hr) as (Hin2 & _);
     destruct (cl3_blk ly1 S1 W1 mem1 md1 _ _ HAR Hin2) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     cbn [fst snd gfp] in Ha; unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha; lia ]). }
intros rr Hin a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & Hpg & _ & Hexp & Hheld & _).
unfold asrc_fp in Hin. cbn [In] in Hin.
destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; unfold ASRC in Ha; lia|].
destruct Hin as [<- | Hin].
{ destruct (cl3_blk ly1 S1 W1 mem1 md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd gfp] in Ha. unfold bzs in Ha. rewrite length_map in Ha. unfold APARTIAL in *. lia. }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) ltac:(lia) ltac:(lia) rr Hin a Ha). }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) ltac:(lia) ltac:(lia) rr Hin a Ha). }
exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) ltac:(lia) ltac:(lia) rr Hin a Ha).
Qed.
Lemma cl3_alist_blks_in : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
Lemma cl3_src_blks : forall ly0 S0 W0 m0 HA0 h0, asrc_at B ly0 S0 W0 m0 HA0 h0 ->
forall b, In b (asrc_blks h0) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 HA0 h0 HS0 b Hb.
pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPd & _ & _ & _ & _ & _ & _ & _ & HPin & _ & _ & _ & HEx & HHl & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact HPin|].
apply in_app_or in Hb as [Hb | Hb]; [exact (cl3_alist_blks_in _ _ _ _ _ _ _ HPd b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
[exact (cl3_alist_blks_in _ _ _ _ _ _ _ HEx b Hb) | exact (cl3_alist_blks_in _ _ _ _ _ _ _ HHl b Hb)].
Qed.
(* an address stays writable when its presence is kept and the new world hides no more (W_list_drop.v
   writable_kept_w, copied) *)
Lemma cl3_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- rewrite (Hh _ EH') in Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* a value carried over a step that keeps its bytes (W_check_no_loss.v cnl_vm_keep, copied) *)
Lemma cl3_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
(* The source over one run of this walk: the view of every byte below the ceiling kept, nothing gone absent. *)
Lemma cl3_src_kept : forall ly S (W W' : world SEGS) mem mem' md HA h lo,
AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 0x10000 <= HA -> HA + 96 <= 0x7fff8000 ->
alloc_ceiling <= lo -> wle W W' ->
(forall a, 4096 <= a < lo -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
asrc_at B ly S W' mem' HA h.
Proof.
intros ly S W W' mem mem' md HA h lo HAR HS HAlo HAhi Hlo Hwle Hq Hp.
apply (asrc_at_kept B ly S W mem ly S W' mem' HA h HS).
- intros rr Hin a Ha.
  destruct (cl3_src_low ly S W mem md HA h HAR HS HAlo HAhi rr Hin a Ha) as [Hl1 Hl2].
  split; [apply Hq; lia | apply (cl3_writable_kept_w W W' mem mem' a); [apply Hp | exact Hwle]].
- intros b Hb. exact (cl3_src_blks ly S W mem HA h HS b Hb).
Qed.
Lemma cl3_set_held_id : forall h, CheckRep.set_held h (hs_held h) = h.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?]. reflexivity. Qed.

(* the source with its held list replaced: every other byte and block kept (lib/B/W_check_no_loss.v
   a working branch 5ef01234da3 nls_src_swap, over CheckRep.set_held) *)
Lemma cl3_src_swap : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA0 (h0 : hsrc) (H' : hlist),
asrc_at B ly1 S1 W1 m1 HA0 h0 ->
(forall a, HA0 <= a < HA0 + 80 -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (gfp (hs_partial h0) (bzs (hs_pjunk h0)) :: alist_fp (HA0 + 16) (hs_pending h0) ++ alist_fp (HA0 + 64) (hs_expected h0)) ->
(forall b, In b ((hs_partial h0, APARTIAL) :: alist_blks (hs_pending h0) ++ alist_blks (hs_expected h0)) -> In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 m2 (HA0 + 80) H' true ->
NoDup (hs_blocks (CheckRep.set_held h0 H')) ->
asrc_at B ly2 S2 W2 m2 HA0 (CheckRep.set_held h0 H').
Proof.
intros ly1 S1 W1 m1 ly2 S2 W2 m2 HA0 h0 H'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) HK HF HB HL HND.
assert (Hvm : forall a n v, HA0 <= a -> a + Z.of_nat n <= HA0 + 80 ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply HK; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 80) as [Hi8 | Hi8]; [apply (proj2 (HK (HA0 + i) ltac:(lia))); exact (H5 i Hi)|].
  pose proof HL as (_ & _ & _ & HW & _). replace (HA0 + i) with (HA0 + 80 + (i - 80)) by lia. apply HW. unfold ASRC in Hi. lia. }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H10
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 m1); [intros x Hx; apply (HF (gfp (hs_partial h0) (bzs (hs_pjunk h0))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H22
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb]|].
split; [exact HL | exact HND].
Qed.

(* the objects of cshe_ro_B are image bytes the allocator does not own, not errno: below the ceiling *)
Lemma cl3_ro_in : forall b n a, In (b, n) cshe_ro_B -> b <= a < b + n -> inG cshe_ro_B a.
Proof.
intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin|].
unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Lemma cl3_ro : forall b n a, In (b, n) cshe_ro_B -> b <= a < b + n ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
4096 <= a < alloc_ceiling.
Proof.
intros b n a Hin Ha. pose proof (cl3_ro_in b n a Hin Ha) as Hg.
destruct (HGR a Hg) as (Hi & Ho & _). destruct (HGRR a Hg) as (He & _).
pose proof (pa_img_range a Hi) as Hr. pose proof asan_consts as (C1 & _).
split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. lia.
Qed.
Lemma cl3_ro_gone : In (VAL A_g_gone, 1) cshe_ro_B.
Proof. cbv [cshe_ro_B]. left. reflexivity. Qed.
Lemma cl3_ro_nout : In (VAL A_g_nout, 8) cshe_ro_B.
Proof. cbv [cshe_ro_B]. right. left. reflexivity. Qed.
Lemma cl3_ro_out : In (VAL A_g_out, 8) cshe_ro_B.
Proof. cbv [cshe_ro_B]. right. right. left. reflexivity. Qed.
Lemma cl3_saved_kept : forall (W1 W2 : world SEGS) m1 m2 sp rs,
(forall a, sp - 96 <= a < sp -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
cshe_saved_B W1 m1 sp rs -> cshe_saved_B W2 m2 sp rs.
Proof.
intros W1 W2 m1 m2 sp rs HK (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
unfold cshe_saved_B.
repeat split; (apply (cl3_vm_keep W1 W2 m1 m2); [intros k Hk; apply HK; cbn in Hk; lia | assumption]).
Qed.
(* a run that wrote nothing keeps the view and presence (lib/B/W_check_no_loss.v nls_eqv_view) *)
Lemma cl3_eqv_view : forall (W1 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
(forall a, aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) /\ (forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a).
Proof.
intros W1 m m' Hq. split.
- intros a. apply aview_eq_of. apply Hq.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b. pose proof (Hq (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx.
  rewrite Hh in Hx. rewrite Hx. exact Hb.
Qed.

(* ------------------------------------------------------------------ the loop *)
Section loop.
(* the entry of check_shape_ends (cshe_spec's names), and what the loop keeps needing of it; the main lemma
   cshe_l3_B, below, discharges each from cshe_spec's premises *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 O OUT : Z) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past the call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_out_B B PST ARx G MT RP regs0 ly S W mem md XO AT HA A0 0 h P ob kr).
Local Notation WANT := (CheckRep.want_of P (hl_recs (hs_held h))).
Local Notation LIT := (VAL A_lit_end5).
Local Notation PLEN := (Z.of_nat (length P)).
Hypothesis HPRE : AFP0 CSHE_STK_B ly S W regs0 mem md ch.
Hypothesis HX0 : 0 <= XO.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HAT8 : AT mod 8 = 0.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 0x10000 <= HA.
Hypothesis HAhi : HA + ASRC <= 0x7fff8000.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HOlen : Z.of_nat (length ob) = O.
Hypothesis HO40 : O <= 2 ^ 40.
Hypothesis HO32 : 0 < O -> O < 2 ^ 32.
Hypothesis HOM : amem_range OUT (O + 8).
(* the stream's block is none of the held list's blocks (cshe_spec's `~ In OUT (hs_blocks h)`) *)
Hypothesis HOH : ob <> [] -> ~ In OUT (list_blocks (hs_held h)).
Hypothesis HA0 : 0 <= A0 <= O.
Hypothesis HROM0 : rom_view SEGS W mem.
(* the source g_s[j] (cshe_spec's HA = g_s + 96 j and HGS, HGR, HGRR): image bytes the allocator does not own, not
   errno, not read-only, apart from g_gone / g_nout / g_out, and inside g_s (cshe_ro_B's fourth object) *)
Hypothesis HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a.
Hypothesis HAgs : VAL (A_OBJ 19) <= HA /\ HA + ASRC <= VAL (A_OBJ 19) + 384.
(* the prefix P at PF, NUL-terminated, with its entry shadow facts, and where it lives (W3's ruling, a working branch
   fb87b19890f W_contract.v:1840-1841): a read-only literal with a const shadow (ashp), or a local in one of S's fake
   frames, whose bytes and shadow the journal's frame clause keeps *)
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
Hypothesis HPSV : shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1).
Hypothesis HPD : ((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1)) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
(* the held list's blocks at the entry are the entry's blocks (asrc_at's held alist_at) *)
Hypothesis HBLK : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S).
(* " end" (A_lit_end5), bcmp's second operand *)
Hypothesis HLG : garr8 SEGS (arm W mem) LIT (bzs END5).

(* What every state of the loop keeps, given the held list H1 now, the records ds dropped and the c bytes consumed. *)
Definition cl3_mem (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (mem1 : word -> option byte) (md1 : Model)
  (kk : Z) (H1 : hlist) (ds : list (Z * list byte)) : Prop :=
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_gone) 1 0 /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_nout) 8 O /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_out) 8 OUT /\
ob_at W1 mem1 OUT ob /\ (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
  Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved_B W1 mem1 sp0 regs0 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
(* the room round: one free's room (MT_rk's mo_free) per record still held, past the caller's kr; the live counts
   stay under the bounds (cshe_pk = ldrop_pk = 0: the drops only remove blocks) *)
rp_RM RP S1 (Z.to_nat (Z.of_nat (length (hl_recs H1)) * mo_free MT_rk) + kr) /\ cnt_ok RP (ablocks B ly1 S1).
(* the registers the loop keeps: the entry's sp - 112, gp, tp, s11, and its own s0 s1 s2 s3 s5 s7 *)
Definition cl3_regs (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\ getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 AT /\
getr regs1 19 = w64 LIT /\ getr regs1 21 = w64 4 /\ getr regs1 23 = w64 5.
(* the head 0x8597c, w turns left (lib/A/W_cshe_l3.v l3_inv; the plain proof's cse_inv) *)
Definition cl3_inv (w : nat) (ds : list (Z * list byte)) (c : Z) (W1 : world SEGS) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist),
cl3_mem ly1 S1 W1 mem1 md1 kk H1 ds /\
CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT = Some (rsF, ds ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\ val_mem SEGS (mrestrict (w_H W1) mem1) AT 8 (A0 + c) /\
cl3_regs regs1 /\ getr regs1 22 = w64 (Z.of_nat w) /\ getr regs1 10 = w64 (Z.of_nat w - 1).
(* 0x859cc, after bcmp: the line l at the stream's A0 + c is read (`at` moved past it), it passed the length and " end"
   checks, its stem is record i (find_text); s4 = the line, s6 = its length, s8 = w (lib/A/W_cshe_l3.v l3_ab) *)
Definition cl3_ab (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (d' : list byte),
cl3_mem ly1 S1 W2 mem2 md2 kk H1 ds /\
skipn (Z.to_nat (A0 + c)) ob = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ bl3_ok P l = true /\
CheckRep.find_text (firstn (length l - 4) l) (hl_recs H1) = Some i /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w <> None /\
(forall rsF dsR cR, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w = Some (rsF, dsR, cR) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, ds ++ nth i (hl_recs H1) (0, []) :: dsR, c + (Z.of_nat (length l) + 1 + cR))) /\
0 <= c /\ A0 + c + Z.of_nat (length l) + 1 <= O /\
val_mem SEGS (mrestrict (w_H W2) mem2) AT 8 (A0 + c + Z.of_nat (length l) + 1) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (sp0 - 112) 8 (Z.of_nat (length l)) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (sp0 - 112 + 8) 8 (OUT + (A0 + c)) /\
cl3_regs regs2 /\ getr regs2 24 = w64 (Z.of_nat w) /\ getr regs2 22 = w64 (Z.of_nat (length l)) /\
getr regs2 20 = w64 (OUT + (A0 + c)).
(* list_drop's entry 0x85b50 from 0x85a00: record i found and has the prefix; a0 = the held list, a1 = i, ra = 0x85a04 *)
Definition cl3_mid (w : nat) (ds : list (Z * list byte)) (c : Z) (i : nat) (W3 : world SEGS)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist),
cl3_mem ly1 S1 W3 mem3 md3 kk H1 ds /\
(i < length (hl_recs H1))%nat /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + c)) ob) w =
   Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, (ds ++ [nth i (hl_recs H1) (0, [])]) ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\ val_mem SEGS (mrestrict (w_H W3) mem3) AT 8 (A0 + c) /\
cl3_regs regs3 /\ getr regs3 24 = w64 (Z.of_nat w) /\
getr regs3 1 = w64 (BASE + A_cl3_dr) /\ getr regs3 10 = w64 (HA + 80) /\ getr regs3 11 = w64 (Z.of_nat i).
(* ---- P at PF: the only lemmas that read HPD (ROM literal or fake-frame local), HPB / HPN / HPV and the entry's
   shadow facts HPRA / HPSV.  cl3_pf_img: P lies below the allocator's ceiling (the image's read-only bytes, or a
   fake frame: YCbq.v frames_bounds), so it is off every frame of this walk and s0 = PF is a low chain value. *)
Lemma cl3_pf_img : 4096 <= PF /\ PF + PLEN + 8 <= alloc_ceiling.
Proof.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR0 & _).
destruct HPD as [(HPROM & _) | (cid & pos & Hin & Hfr)].
- pose proof (HPROM PF ltac:(lia)) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range PF ltac:(exists sg; split; [exact Hsg | exact Hra])).
  pose proof (HPROM (PF + PLEN + 7) ltac:(lia)) as (sg2 & Hsg2 & _ & Hra2).
  pose proof (pa_img_range (PF + PLEN + 7) ltac:(exists sg2; split; [exact Hsg2 | exact Hra2])). lia.
- assert (Hfb : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid))
  by (eapply (frames_bounds_x SEGS B ARx LAWS); [exact HAR0 | exact Hin]). destruct Hfb as (Hf1 & Hf2 & _).
  pose proof (Hfr PF ltac:(lia)) as Ha. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as Hb.
  unfold in_zr, frame_rng in Ha, Hb. cbn [fst snd] in Ha, Hb. lia.
Qed.
(* the frame case: a byte of one of S's fake frames, or of its shadow, keeps its entry view at every state the
   journal reaches (YCbq.v ajournal's frame clause: the frame is no block of the held list, FPc's, and no global) *)
Lemma cl3_frame_keep : forall cid pos ly2 S2 (W2 : world SEGS) m2 md2 kk2, In (cid, pos) (frames S) ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly2 S2 W2 m2 md2 kk2 ->
forall a, (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) mem a.
Proof.
intros cid pos ly2 S2 W2 m2 md2 kk2 Hin HJ a Ha.
pose proof HPRE as (HAR0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid))
  by (eapply (frames_bounds_x SEGS B ARx LAWS); [exact HAR0 | exact Hin]). destruct Hfb as (Hf1 & Hf2 & _).
assert (Hal : frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
  by (eapply frame_al640; [exact HAR0 | exact Hin]). destruct Hal as (Fa64 & Fb64 & Fb).
set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa. pose proof (Z.div_mod fb 64 ltac:(lia)) as Dfb.
pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa8. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as Mfa8.
pose proof (Z.div_mod fb 8 ltac:(lia)) as Dfb8. pose proof (Z.mod_pos_bound fb 8 ltac:(lia)) as Mfb8.
(* where a lies: the frame (below the ceiling, not the image) or its shadow (above the low memory) *)
assert (Hwhere : (fa <= a < fa + fb) \/ (SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + fb / 8)).
{ unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. fold fa fb in Ha. unfold shadow_addr in Ha. lia. }
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
apply ajournal_gx_inner_x in HJ. destruct HJ as (memS & HJi & HgS).
destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KFR & _).
rewrite (KFR cid pos a Hin Ha).
- apply HgS. rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ Hg) as (Hi & _ & _).
  pose proof (pa_img_range _ Hi) as HIR.
  destruct Hwhere as [Hw | Hw]; [|lia].
  eapply (frm_img_x SEGS B ARx LAWS); [exact HAR0 | exact Hin | exact Hw | exact Hi].
- intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ((b & n) & <- & Hb). cbn [fst snd] in Hra.
  pose proof (HBLK _ Hb) as Hb0.
  destruct (cl3_blk ly S W mem md b n HAR0 Hb0) as (_ & _ & _ & _ & _ & Bc & Bc2 & _ & Bapp & _).
  destruct Hwhere as [Hw | Hw].
  + assert (Hd : zdisjoint (b, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid))
      by (eapply (sep_block_frame_x SEGS B ARx LAWS); [exact HAR0 | exact Hb0 | exact Hin]).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold fa fb in Hd. lia.
  + unfold in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg, YG0f.ASAN_CEIL in Bapp.
    pose proof (Z.div_mod (fa + fb) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fa + fb) 8 ltac:(lia)). lia.
Qed.
(* cl3_pf_at: at any state the loop reaches (cl3_mem's rom_view with the views below the ceiling kept, and the
   journal from the entry), P's bytes and nul are the entry's, its bytes up to PF + PLEN + 8 are readable, and its
   shadow is addressable and visible *)
Lemma cl3_pf_at : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk H1 ds (W2 : world SEGS) m2 ly2 S2 md2 kk2,
cl3_mem ly1 S1 W1 mem1 md1 kk H1 ds ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) mem1 a) ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly2 S2 W2 m2 md2 kk2 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W2) m2 (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) /\
aview SEGS (w_H W2) m2 (PF + PLEN) = Some 0 /\
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W2) m2 a <> None) /\
range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF PF (PLEN + 1) /\
(0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W2) m2) PF (PLEN + 1)).
Proof.
intros ly1 S1 W1 mem1 md1 kk H1 ds W2 m2 ly2 S2 md2 kk2
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROM & _ & _) KL HJ2.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR0 & _).
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (KP : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) mem a).
{ destruct HPD as [(HPROM & _) | (cid & pos & Hin & Hfr)].
  - intros a Ha. pose proof (HPROM a Ha) as Hr. pose proof Hr as (sg & Hsg & _ & Hra).
    pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
    rewrite KL by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr).
  - intros a Ha. apply (cl3_frame_keep cid pos _ _ _ _ _ _ Hin HJ2). left. exact (Hfr a Ha). }
assert (HSH : range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF PF (PLEN + 1) /\
  (0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W2) m2) PF (PLEN + 1))).
{ destruct HPD as [(_ & HASH) | (cid & pos & Hin & Hfr)].
  - apply (HASH ly2 S2 [] W2 m2 md2). eapply ajournal_gx_AR_x. exact HJ2.
  - assert (Hal : frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
  by (eapply frame_al640; [exact HAR0 | exact Hin]). destruct Hal as (Fa64 & Fb64 & Fb).
    pose proof (Hfr PF ltac:(lia)) as HaP. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as HbP.
    unfold in_zr, frame_rng in HaP, HbP. cbn [fst snd] in HaP, HbP.
    set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa. pose proof (Z.div_mod fb 64 ltac:(lia)) as Dfb.
    pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa8. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as Mfa8.
    pose proof (Z.div_mod fb 8 ltac:(lia)) as Dfb8. pose proof (Z.mod_pos_bound fb 8 ltac:(lia)) as Mfb8.
    split.
    + intros x Hx. destruct (HPRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite (cl3_frame_keep cid pos _ _ _ _ _ _ Hin HJ2); [exact Hs|]. right.
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold fa fb.
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
    + intros _ s Hs. rewrite (cl3_frame_keep cid pos _ _ _ _ _ _ Hin HJ2); [exact (HPSV s Hs)|]. right.
      unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fb. unfold shadow_addr in Hs.
      replace (PF + (PLEN + 1) - 1) with (PF + PLEN) in Hs by lia.
      pose proof (Z.div_mod PF 8 ltac:(lia)). pose proof (Z.mod_pos_bound PF 8 ltac:(lia)).
      pose proof (Z.div_mod (PF + PLEN) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + PF / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + PF / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (PF + PLEN) / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (PF + PLEN) / 8) 8 ltac:(lia)).
      lia. }
destruct HSH as [HRA HHV].
split; [intros i Hi; rewrite KP by lia; exact (HPB i Hi)|].
split; [rewrite KP by lia; exact HPN|].
split; [intros a Ha; rewrite KP by lia; exact (HPV a Ha)|].
split; [exact HRA | exact HHV].
Qed.

(* cl3_mem across a step that changes nothing below the ceiling nor the frame's saved slots, and takes no presence *)
Lemma cl3_mem_step : forall ly1 S1 (W1 W2 : world SEGS) mem1 mem2 md1 md2 kk kk2 H1 ds,
cl3_mem ly1 S1 W1 mem1 md1 kk H1 ds ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk2 ->
wle W1 W2 ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) ->
cl3_mem ly1 S1 W2 mem2 md2 kk2 H1 ds.
Proof.
intros ly1 S1 W1 W2 mem1 mem2 md1 md2 kk kk2 H1 ds
  (HJ & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK & HROM & HSAV &
   HERR & HRMk & HCNk)
  HJ2 Hwle Klow Kstk Kpres.
pose proof asan_consts as (C1 & _).
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
split; [exact HJ2|].
split.
{ apply (cl3_src_kept ly1 S1 W1 W2 mem1 mem2 md1 HA (CheckRep.set_held h H1) alloc_ceiling HAR1 HSRC);
  [lia | unfold ASRC in HAhi; lia | lia | exact Hwle | exact Klow | exact Kpres]. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MG]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_gone ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MNO]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_nout ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MOUT]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_out ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ intros k Hk. destruct HOBK as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
  destruct (cl3_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (_ & H4096 & _ & Hle & _ & Hc & _).
  rewrite Klow by lia. exact (HOBt k Hk). }
split; [exact HOBK|]. split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite Klow by lia. exact (HROM a Hr). }
split; [exact (cl3_saved_kept W1 W2 mem1 mem2 sp0 regs0 Kstk HSAV)|].
split; [intros jj Hjj; pose proof (pal_env B TL) as (_ & EIMG & _); pose proof (pa_img_range _ (EIMG (as_errno B + jj) ltac:(lia)));
  rewrite Klow by lia; exact (HERR jj Hjj)|].
exact (conj HRMk HCNk).
Qed.
(* " end" (cshe_spec's garr8 premise), byte by byte *)
Lemma cl3_lit_bytes : forall k, 0 <= k < 4 ->
aview SEGS (w_H W) mem (LIT + k) = Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0))).
Proof.
intros k Hk. assert (Hk' : (Z.to_nat k < length (bzs END5))%nat) by (cbn; lia).
pose proof (garr8_mbyte SEGS (arm W mem) LIT _ (Z.to_nat k) HLG Hk') as Hm.
unfold aview. replace (LIT + k) with (LIT + Z.of_nat (Z.to_nat k)) by lia. unfold arm in Hm. rewrite Hm.
cbn [option_map]. f_equal.
assert (Hc : (Z.to_nat k = 0 \/ Z.to_nat k = 1 \/ Z.to_nat k = 2 \/ Z.to_nat k = 3)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.
(* " end\0" lies in the image's read-only bytes *)
Lemma cl3_lit_img : 0x10000 <= LIT /\ LIT + 5 <= 0x5fc000.
Proof.
pose proof (HEND5R LIT ltac:(lia)) as (sg & Hsg & _ & Hra).
pose proof (pa_img_range LIT ltac:(exists sg; split; [exact Hsg | exact Hra])).
pose proof (HEND5R (LIT + 4) ltac:(lia)) as (sg2 & Hsg2 & _ & Hra2).
pose proof (pa_img_range (LIT + 4) ltac:(exists sg2; split; [exact Hsg2 | exact Hra2])). lia.
Qed.
(* a run of this loop writes nothing: every region it seats has an empty write window *)
Ltac cl3_nowr :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg; lia|]);
destruct Hin.
Ltac cl3_awr :=
lazymatch goal with |- awr_ok_x _ ?l _ _ _ _ _ _ _ _ _ _ => let l' := eval vm_compute in l in change l with l' end;
repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|]);
apply awr_ok_x_nil.

(* the first part of a turn: next_line, the length check, the four traps on line + len and bcmp of " end", from the
   head 0x8597c to 0x859cc (lib/A/W_cshe_l3.v l3_A1) *)
Lemma cl3_A1 : forall w ds c W1 regs1 mem1 md1, cl3_inv (Datatypes.S w) ds c W1 regs1 mem1 md1 ->
(forall l i W2 regs2 mem2 md2, cl3_ab w ds c l i W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cl3_ab)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c W1 regs1 mem1 md1 HI HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & kk & H1 & HM & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R22 & R10).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
(* the model: this turn's line l, its record i *)
assert (Hex : exists rsF dsF cF,
  CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) = Some (rsF, dsF, cF)).
{ destruct (CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w)) as [[[x y] z]|];
  [exists x, y, z; reflexivity | exfalso; exact (HRUN eq_refl)]. }
destruct Hex as (rsF & dsF & cF & ER).
destruct (bl3_ends_S P _ _ w rsF dsF cF ER) as (l & d' & i & dsR & cR & Ed & Hnz & Hok & Hft & HrR & EdsF & EcF).
destruct (bl3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold bl3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply bl3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (HAl : A0 + c + Z.of_nat (length l) + 1 <= O) by lia.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (cl3_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & _ & Ole & _ & Oceil & _ & Ooff & Oapp & Opres).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) <= 2 ^ 26).
{ pose proof (bl3_ends_len P _ _ _ (ltac:(rewrite ER; discriminate) : CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) <> None)) as Hle.
  unfold hl_n in Hn26. lia. }
destruct (cl3_state W1 regs1 mem1 (sp0 - 112) (Z.of_nat (Datatypes.S w)) (OUT + (A0 + c)) (Z.of_nat (length l))
  R2 R21 R23 R22 R10 HSPb HSPa Hw1 HlnR Hlen32) as [HS SHOK].
remember (Eimg (Ereg regs1 (cl3_extra (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ0 SHOK Bspan AF_fr_next_line.
{ cbn [ss_mem ss_cl3]. apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cl3_extra (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = w64 PF) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 LIT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = w64 (Z.of_nat (Datatypes.S w))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E10 : ew E 10 = w64 (Z.of_nat (Datatypes.S w) - 1)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (OUT + (A0 + c))) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length l))) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ; rewrite Q2; exact Usp).
pose proof cl3_pf_img as HPimg.
(* the run to the call wrote nothing *)
assert (MQ0 : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x).
{ intros x. apply HFr. intros (rg & Hin & _). destruct Hin. }
destruct (cl3_eqv_view W1 mem1 (ms_mem ms) MQ0) as (AV0 & AP0).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HAR1m : AR0 ly1 S1 W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREn : AFP0 NL_STK ly1 S1 W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms) mdc kk
    (ms_regs ms) NL_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold NL_STK, NL_FRAME, ESTACK. lia.
  - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia. lia. }
assert (HO0 : 0 < O) by lia.
destruct (Z.mod_divide (sp0 - 112) 16 ltac:(lia)) as [Hd16 _]. destruct (Hd16 HSPa) as [q16 Hq16]. clear Hd16.
eapply SRr_bind.
{ apply (NL W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc [] (XO + 112) AT (sp0 - 112 + 8) (sp0 - 112)
    (A0 + c) O OUT ob HPREn).
  - lia.
  - rewrite Zplus_mod, HX16. reflexivity.
  - rewrite Usp1, Etop. lia.
  - rewrite Usp1. intros a Ha. apply HPRi. rewrite WS. lia.
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11, Usp. reflexivity.
  - rewrite Q12, E2. reflexivity.
  - exact HAT8.
  - replace (sp0 - 112 + 8) with ((2 * q16 + 1) * 8) by lia. apply Z_mod_mult.
  - replace (sp0 - 112) with ((2 * q16) * 8) by lia. apply Z_mod_mult.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - lia.
  - lia.
  - lia.
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MAT].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MNO].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MOUT].
  - exact HOlen.
  - intros k Hk. rewrite AV0. exact (HOBt k Hk).
  - lia.
  - intros _. split; [lia|]. split; [unfold amem_range in HOM; lia|]. split; [exact (HO32 HO0)|].
    intros a Ha. rewrite Usp1. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - intros _. split; [rewrite Ed; apply in_or_app; right; left; reflexivity|]. split; [exact HOM|].
    split; [apply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia]|].
    split; [apply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]|].
    intros a Hr. rewrite AV0. exact (HROM a Hr). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
subst W2.
destruct HARM as [(HAeq & _) | (ln & HAlt & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
assert (Hln : ln = l).
{ destruct Hfl as (rest & Hsk & Hnz'). rewrite Ed in Hsk. destruct (bl3_nul_unique l ln d' rest Hsk Hnz Hnz') as [-> _]. reflexivity. }
subst ln.
rewrite Usp1 in HJn, HFRn.
assert (HJc' : AJ0 G (XO + 112) (nl_cells AT (sp0 - 112 + 8) (sp0 - 112)) NL_STK (sp0 - 112) []
  ly1 S1 W1 (ms_mem ms) mdc [] ly1 S1 W1 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha) | exact HJn]. }
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W1 (ms_mem ms) mdc kk NL_STK (sp0 - 112) (XO + 112) (nl_cells AT (sp0 - 112 + 8) (sp0 - 112)) [] []
  ly1 S1 W1 mem2 md2 0 HJ0 HJc'
  ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
match type of HJ2 with ?t -> _ => assert (HOc : t) end.
{ intros a (rg & Hin & Hrg). cbn [nl_cells In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg.
  - right. exists (AT, AT + 8). split; [left; reflexivity | cbn; lia].
  - left. rewrite WS. lia.
  - left. rewrite WS. lia. }
specialize (HJ2 HOc HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))). clear HOc.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
pose proof HJn as (_ & _ & _ & HXOn).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F38 : ew Ea 38 = w64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 112) by (rewrite OLDa by lia; exact Usp).
apply (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 2%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0))])) in HS; [| reflexivity | | ].
2: { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
  cbn [base_val]. rewrite UspA. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 112) 0 8 (SOff 33 0) (Z.of_nat (length l)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vlen2.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 112) 8 8 (SOff 32 0) (OUT + (A0 + c)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vln2]. }
2: { cbn [all_disjoint ss_mem]. exact I. }
assert (HAR2 : AR0 ly1 S1 W1 mem2 md2) by exact (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem2 md2 kk HJ2).
assert (SHOK2 : sh_ok SEGS cl3_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
rewrite Q1.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
{ (* 0x85994 beqz a0: next_line returned 1, it found the line *)
  exfalso. rewrite branch_eq_U, (U_atom Ea 38 1 F38), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
assert (F32 : ew Ea 32 = Z_to_bv 64 (OUT + (A0 + c))) by (rewrite OLDa by lia; exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 (Z.of_nat (length l))) by (rewrite OLDa by lia; exact E33).
assert (U32 : U Ea (SOff 32 0) = OUT + (A0 + c)) by (apply U_atom; [exact F32 | lia]).
assert (U33 : U Ea (SOff 33 0) = Z.of_nat (length l)) by (apply U_atom; [exact F33 | lia]).
assert (Uadd : U Ea (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = OUT + (A0 + c) + Z.of_nat (length l))
  by (apply trap_U_add; [exact U32 | exact U33 | lia]).
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
{ (* 0x859a8 bltu a0,s4: the UBSan pointer-overflow trap on line + len, never taken *)
  rewrite (trap_ptr_bltu Ea (SOff 32 0) (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) _ _ U32 Uadd ltac:(lia)) in Hc.
  discriminate Hc. }
clear Hc.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
(* the runs since next_line wrote nothing *)
assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W1 mem2 (ms_mem ms2) MQ1) as (AV1 & AP1).
(* below the ceiling, nothing changed since the head *)
assert (KL1 : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite AV1, HFRn; [apply AV0 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
  intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (ROMW : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KL1 by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W1) (ms_mem ms2) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KL1 by lia. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
assert (HLITr : forall k, 0 <= k < 4 -> aview SEGS (w_H W1) (ms_mem ms2) (LIT + k) =
  Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0)))).
{ intros k Hk. rewrite ROMW by (apply HEND5R; lia). exact (cl3_lit_bytes k Hk). }
pose proof cl3_lit_img as HLR.
set (xb := OUT + (A0 + c) + Z.of_nat (length l) - 4).
assert (R10b : getr (ms_regs ms2) 10 = w64 xb).
{ rewrite T10, F32, F33. rewrite unsigned_lit_small by lia. rewrite YI08.alu64_add_lit. unfold w64, xb. f_equal. lia. }
assert (R11b : getr (ms_regs ms2) 11 = w64 LIT) by (rewrite T11, (OLDa 19%nat) by lia; exact E19).
assert (Usp2 : spZ (ms_regs ms2) = sp0 - 112) by (unfold spZ; rewrite T2; exact UspA).
assert (HAR3 : AR0 ly1 S1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy md2) mat2 md2))
  by exact (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ2).
eapply SRr_bind.
{ apply (aj_bcmp_gx_at0 (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CSHE_STK_B sp0 FPc
    ly S W mem md [] ly1 S1 _ kk xb LIT 4 (-112) (Z_to_bv 64 (BASE + 13956)) HG HX16 HJ2 R10b R11b T12).
  - lia.
  - unfold xb. lia.
  - unfold xb. lia.
  - lia.
  - lia.
  - rewrite Usp2. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite T3, (OLDa 3%nat), E3 by lia. exact Hgp0.
  - rewrite T4, (OLDa 4%nat), E4 by lia. exact Htp0.
  - exact T1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|rewrite Usp2; unfold ESTACK; unfold xb in Ha; lia].
    replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE by (unfold xb in Ha; lia). discriminate.
  - intros a Ha. split; [|rewrite Usp2; unfold ESTACK; lia].
    replace a with (LIT + (a - LIT)) by lia. rewrite HLITr by lia. discriminate.
  - intros a Ha. unfold xb in Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range in HOM |- *. unfold xb. lia.
  - unfold amem_range, kLowMemEnd. lia.
  - eapply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms2) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia].
  - intros _. eapply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms2) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia | lia].
  - exact (proj1 (HEND5S _ _ _ _ _ _ HAR3)).
  - exact (proj2 (HEND5S _ _ _ _ _ _ HAR3)). }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros k Hk. unfold xb. replace (OUT + (A0 + c) + Z.of_nat (length l) - 4 + k) with
    (OUT + (A0 + c) + (Z.of_nat (length l) - 4 + k)) by lia.
  rewrite HLINE by lia. rewrite HLITr by lia. do 2 f_equal. rewrite <- Hend, bl3_nth_skipn. f_equal. lia. }
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 50)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F54 : ew Eb 54 = w64 0) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv; exact Hv0).
clear HEb.
assert (SHOK3 : sh_ok SEGS cl3_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
assert (HAR4 : AR0 ly1 S1 W1 mem3 md3) by exact (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem3 md3 kk HJ3).
paj_run_tok_x RUNx HS HJ3 SHOK3 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BR HS SHOK3 Bspan.
{ (* 0x859c8 bnez a0: bcmp found the line's last four bytes equal to " end" *)
  exfalso. rewrite branch_ne_U, (U_atom Eb 54 0 F54), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan 13960. { cl3_awr. }
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdF := mdq) in * end.
assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W1 mem3 (ms_mem ms4) MQ2) as (AV2 & AP2).
assert (OLDba : forall m, (m < 34)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (22%bv : bv 5) N22.
prreg HS (20%bv : bv 5) N20.
(* above sp, only next_line's three cells changed since the head; below the ceiling nothing did *)
assert (KS : forall yy, sp0 - 112 <= yy < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms4) yy = aview SEGS (w_H W1) mem2 yy).
{ intros yy Hyy. rewrite AV2, Hfr3 by (unfold ESTACK; lia). apply AV1. }
assert (KL : forall yy, 4096 <= yy < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) yy = aview SEGS (w_H W1) mem1 yy).
{ intros yy Hyy. rewrite AV2, Hfr3 by (unfold ESTACK in *; pose proof WS; lia). apply KL1. exact Hyy. }
replace (BASE + 13960) with (BASE + A_cl3_ab) by (unfold A_cl3_ab, AF_fr_check_shape_ends; lia).
apply (HKont l i W1 (ms_regs ms4) (ms_mem ms4) mdF).
exists ly1, S1, kk, H1, d'.
split.
{ apply (cl3_mem_step ly1 S1 W1 W1 mem1 (ms_mem ms4) md1 mdF kk kk H1 ds HM HJ3 (wle_refl _ W1) KL).
  - intros yy Hyy. rewrite KS by lia. rewrite HXOn; [apply AV0 | lia |].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros yy Hp. apply AP2. apply Hpres3. apply AP1. apply HPn. apply AP0. exact Hp. }
split; [exact Ed|]. split; [exact Hnz|]. split; [exact Hok|]. split; [exact Hft|].
split; [rewrite HrR; discriminate|].
split.
{ intros rsF' dsR' cR' Hx. apply HREL. rewrite Ed. exact (bl3_ends_step P (hl_recs H1) l d' i w rsF' dsR' cR' Hnz Hok Hft Hx). }
split; [exact Hc0|]. split; [exact HAl|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; lia | exact Vat2]|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; cbn in Hyy; lia | exact Vlen2]|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; cbn in Hyy; lia | exact Vln2]|].
split.
{ unfold cl3_regs.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N27, OLDba by lia; exact E27|].
  split; [rewrite N8, OLDba by lia; exact E8|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N24, OLDba, E10 by lia; unfold w64; f_equal; lia|].
split; [rewrite N22, OLDba, E33 by lia; reflexivity|].
rewrite N20, OLDba, E32 by lia. reflexivity.
Qed.

(* the second part of a turn: list_find of the line's stem, has_prefix of the line, from 0x859cc to list_drop's
   entry from 0x85a00 (lib/A/W_cshe_l3.v l3_A2, to the call) *)
Lemma cl3_A2 : forall w ds c l i W2 regs2 mem2 md2, cl3_ab w ds c l i W2 regs2 mem2 md2 ->
(forall W3 regs3 mem3 md3, cl3_mid w ds (c + Z.of_nat (length l) + 1) i W3 regs3 mem3 md3 ->
  SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem3 (seg_rom SEGS)) md3) Post) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cl3_ab)) mem2 (seg_rom SEGS)) md2) Post.
Proof.
intros w ds c l i W2 regs2 mem2 md2 HAB HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAB as (ly1 & S1 & kk & H1 & d' & HM & Ed & Hnz & Hok & Hft & HRUN & HREL & Hc0 & HAl & MAT & M0 & M8 &
  HREGS & R24 & R22 & R20).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
destruct (bl3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold bl3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply bl3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk HJ0) as HAR1.
destruct (cl3_blk ly1 S1 W2 mem2 md2 OUT CO HAR1 HOin) as (O16 & O4096 & _ & Ole & _ & Oceil & _ & Ooff & Oapp & Opres).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (bl3_ends_len P _ _ d'); exact HRUN).
rewrite (bl3_drop_len _ _ Hi) in Hw26.
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 0 <= Z.of_nat w <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cl3b_state W2 regs2 mem2 (sp0 - 112) (Z.of_nat w) (OUT + (A0 + c)) (Z.of_nat (length l))
  R2 R21 R23 R24 R22 R20 HSPb HSPa Hw1 HlnR Hlen32 M0 M8) as [HS SHOK].
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs2 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = w64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = w64 PF) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 LIT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (OUT + (A0 + c))) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 (Z.of_nat (length l))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (Z.of_nat w)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
pose proof cl3_pf_img as HPimg.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ0 SHOK Bspan AF_fr_list_find. { cl3_awr. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ; rewrite Q2; exact Usp).
assert (MQ0 : forall x, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
{ intros x. apply HFr. cl3_nowr. }
destruct (cl3_eqv_view W2 mem2 (ms_mem ms) MQ0) as (AV0 & AP0).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HSRCr : asrc_at B ly1 S1 W2 (ms_mem ms) HA (CheckRep.set_held h H1)).
{ apply (cl3_src_kept ly1 S1 W2 W2 mem2 (ms_mem ms) md2 HA _ alloc_ceiling HAR1 HSRC);
  [lia | unfold ASRC in HAhi; lia | lia | apply wle_refl | intros a _; apply AV0 | exact AP0]. }
pose proof HSRCr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAHr & _).
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 _ _ kk HJ0)
  as (memS & HJi & HgS).
assert (HAR1m : AR0 ly1 S1 W2 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREf : AFP0 LFIND_STK ly1 S1 W2 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W2 (ms_mem ms) mdc kk
    (ms_regs ms) LFIND_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite WS. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia. lia. }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite AV0. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
set (sb := firstn (length l - 4) l).
assert (Hsb : length sb = (length l - 4)%nat) by (unfold sb; rewrite length_firstn; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W2 (ms_mem ms) mdc (HA + 64) 32 HAR1m Hzs) as HRA64.
eapply SRr_bind.
{ apply (LFIND W2 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc [] (HA + 80) H1 true (OUT + (A0 + c)) sb HPREf).
  - rewrite Q10, E9. reflexivity.
  - rewrite Q11, E20. reflexivity.
  - rewrite Q12, E22, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hsb. lia.
  - exact HAHr.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold kLowMemEnd. unfold ASRC in HAhi. lia.
  - eapply range_addressable_sub; [exact HRA64 | lia | lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. rewrite WS in Hslo. unfold ASRC in HAhi. lia.
  - lia.
  - rewrite Hsb. lia.
  - rewrite Hsb. lia.
  - intros k Hk. rewrite Hsb in Hk. rewrite HLINE by lia. do 2 f_equal. unfold sb. rewrite nth_firstn.
    destruct (Z.to_nat k <? length l - 4)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. rewrite WS in Hslo. lia.
  - rewrite Hsb. unfold amem_range in HOM |- *. lia.
  - rewrite Hsb. eapply (range_addressable_of_block0 ly1 S1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia].
  - rewrite Hsb. intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJf & HPf & HPRf & HFRf & HRES).
assert (HRESi : getr regs3 10 = w64 (Z.of_nat i)).
{ destruct HRES as [(j & (Hj1 & Hj2 & Hj3) & Hr10) | (Hnf & _)].
  - rewrite Hr10. do 2 f_equal. apply (bl3_first_unique (hl_recs H1) sb j i Hj2 Hj3 Hti Hfirst).
  - exfalso. exact (Hnf i Hi Hti). }
rewrite Usp1 in HJf, HFRf.
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W2 (ms_mem ms) mdc kk LFIND_STK (sp0 - 112) 0 [] [] [] ly1 S1 W2 mem3 md3 0 HJ0 HJf
  ltac:(rewrite WS; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 32%nat regs3 (mrestrict (w_H W2) mem3) HPf [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 32)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F36 : ew Ea 36 = w64 (Z.of_nat i)) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact HRESi).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 112) by (rewrite OLDa by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS cl3_Bx [] Ea (mrestrict (w_H W2) mem3)) by constructor.
rewrite Q1.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
{ (* 0x859dc bltz a0: list_find found the record, i >= 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit_small; lia).
  cbn [sv_denot] in Hc. rewrite F36, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. unfold w64 in Hc.
  rewrite bv_signed_small in Hc by (rewrite Hu; lia). rewrite Hu in Hc. change (bv_signed (Z_to_bv 64 0)) with 0 in Hc. lia. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 Bspan AF_fr_has_prefix. { cl3_awr. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (MQ1 : forall x, mrestrict (w_H W2) (ms_mem ms1) x = mrestrict (w_H W2) mem3 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W2 mem3 (ms_mem ms1) MQ1) as (AV1 & AP1).
assert (KL1 : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV1, HFRf by (try lia; rewrite WS in Hslo; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia). apply AV0. }
assert (KS1 : forall a, sp0 - 112 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV1, HFRf by (try lia; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia). apply AV0. }
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KL1 by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (HLINE2 : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KL1 by lia. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 112) by (unfold spZ; rewrite P2; exact UspA).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdh := mdq) in * end.
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 _ _ kk HJ2)
  as (memS2 & HJi2 & HgS2).
assert (HAR3 : AR0 ly1 S1 W2 (ms_mem ms1) mdh) by exact (proj1 HJi2).
assert (HPREh : AFP0 HP_STK ly1 S1 W2 (ms_regs ms1) (ms_mem ms1) mdh []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS2 md [] ly1 S1 W2 (ms_mem ms1) mdh kk
    (ms_regs ms1) HP_STK (- 112 - XO) [] HJi2).
  - rewrite Usp2. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - rewrite WS. unfold HP_STK, ESTACK. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
  - rewrite P3, OLDa, E3 by lia. exact Hgp0.
  - rewrite P4, OLDa, E4 by lia. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite P8, OLDa, E8 by lia. rewrite unsigned_lit_small by lia. lia. }
destruct (cl3_pf_at ly1 S1 W2 mem2 md2 kk H1 ds W2 (ms_mem ms1) ly1 S1 mdh kk HM KL1 HJ2) as (PB1 & PN1 & PV1 & HRAP & HHVP).
assert (SHVSUB : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n').
{ intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
  assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
eapply SRr_bind.
{ apply (HP W2 ly1 S1 [] (ms_regs ms1) (ms_mem ms1) mdh [] (OUT + (A0 + c)) (Z.of_nat (length l)) PF PLEN HPREh).
  - rewrite P10, OLDa, E20 by lia. reflexivity.
  - rewrite P11, OLDa, E22 by lia. reflexivity.
  - rewrite P12, OLDa, E8 by lia. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * exact (PB1 k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. exact PN1.
  - intros a Ha. apply PV1. lia.
  - unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact (HHVP ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). apply PV1. lia.
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE2 by lia. discriminate.
    + unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
    + unfold amem_range in HOM |- *. lia.
    + eapply (range_addressable_of_block0 ly1 S1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (SHVSUB _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) (HHVP ltac:(lia))). }
cbv beta. intros W4 c4 Hwle4 (regs4 & mem4 & md4 & -> & HJh & HPh & HPRh & HFRh & HRESh).
assert (Hpref : PLEN <= Z.of_nat (length l) /\ hp_prefix_of W2 (ms_mem ms1) (OUT + (A0 + c)) PF PLEN).
{ unfold CheckRep.prefixb in Hpre. apply andb_prop in Hpre as [Hp1 Hp2]. apply Nat.leb_le in Hp1. apply bl3_leqb in Hp2.
  split; [lia|]. intros k Hk. rewrite HLINE2 by lia. rewrite (PB1 k Hk).
  do 2 f_equal. rewrite <- Hp2. rewrite nth_firstn. destruct (Z.to_nat k <? length P)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia]. }
assert (Hr10h : getr regs4 10 = w64 1).
{ destruct HRESh as [(_ & _ & Hr) | (Hnp & _)]; [exact Hr | exfalso; exact (Hnp (proj1 Hpref) (proj2 Hpref))]. }
rewrite Usp2 in HJh, HFRh.
assert (HJc' : AJ0 G 0 [] HP_STK (sp0 - 112) [] ly1 S1 W2 (ms_mem ms1) mdh [] ly1 S1 W4 mem4 md4 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|]. apply ajournal_gx_nil_x. exact HJh. }
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W2 (ms_mem ms1) mdh kk HP_STK (sp0 - 112) 0 [] [] [] ly1 S1 W4 mem4 md4 0 HJ2 HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_r in HJ3.
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HPh [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 48 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 48)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F52 : ew Eb 52 = w64 1) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hr10h).
clear HEb.
assert (OLDba : forall m, (m < 32)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (SHOK3 : sh_ok SEGS cl3_Bx [] Eb (mrestrict (w_H W4) mem4)) by constructor.
rewrite P1.
paj_run_tok_x RUNx HS HJ3 SHOK3 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BR HS SHOK3 Bspan.
{ (* 0x859f4 beqz a0: has_prefix returned 1 *)
  exfalso. rewrite branch_eq_U, (U_atom Eb 52 1 F52), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan AF_fr_list_drop. { cl3_awr. }
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdD := mdq) in * end.
assert (MQ3 : forall x, mrestrict (w_H W4) (ms_mem ms3) x = mrestrict (w_H W4) mem4 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W4 mem4 (ms_mem ms3) MQ3) as (AV3 & AP3).
prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
prreg HS (27%bv : bv 5) N27. prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18.
prreg HS (19%bv : bv 5) N19. prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
apply (HKont W4 (ms_regs ms3) (ms_mem ms3) mdD).
exists ly1, S1, kk, H1.
split.
{ apply (cl3_mem_step ly1 S1 W2 W4 mem2 (ms_mem ms3) md2 mdD kk kk H1 ds HM HJ3 Hwle4).
  - intros a Ha. rewrite AV3, HFRh by (try lia; rewrite WS in Hslo; unfold HP_STK, ESTACK; lia). apply KL1. exact Ha.
  - intros a Ha. rewrite AV3, HFRh by (try lia; unfold HP_STK, ESTACK; lia). apply KS1. lia.
  - intros a Hp. apply AP3. apply HPRh. apply AP1. apply HPRf. apply AP0. exact Hp. }
split; [exact Hi|].
assert (Esk : skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob = d').
{ replace (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) with (Z.to_nat (A0 + c) + length l + 1)%nat by lia.
  exact (bl3_skip_line ob l d' (Z.to_nat (A0 + c)) Ed). }
rewrite Esk.
split; [exact HRUN|].
split.
{ intros rsF dsF cF Hx. rewrite (HREL rsF dsF cF Hx). rewrite <- app_assoc. cbn [app]. f_equal. f_equal. lia. }
split; [lia|]. split; [lia|].
split.
{ apply (cl3_vm_keep W2 W4 mem2 (ms_mem ms3)).
  - intros yy Hyy. rewrite AV3, HFRh by (try lia; unfold HP_STK, ESTACK; lia). apply KS1. lia.
  - replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + c + Z.of_nat (length l) + 1) by lia. exact MAT. }
split.
{ unfold cl3_regs.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N27, OLDba by lia; exact E27|].
  split; [rewrite N8, OLDba by lia; exact E8|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N24, OLDba by lia; exact E24|].
split; [rewrite N1; unfold w64, A_cl3_dr, AF_fr_check_shape_ends; f_equal; lia|].
split; [rewrite N10, OLDba by lia; exact E9|].
rewrite N11, OLDb by lia. exact F36.
Qed.

(* ---- helpers of the drop step (lib/B/W_check_no_loss.v a working branch 5ef01234da3, at any index) *)
Lemma cl3_set_held2 : forall h0 a b, CheckRep.set_held (CheckRep.set_held h0 a) b = CheckRep.set_held h0 b.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?] a b. reflexivity. Qed.
Lemma cl3_map_drop : forall {Y : Type} (f : Z * list byte -> Y) (rs : list (Z * list byte)) i, (i < length rs)%nat ->
Permutation (map f rs) (f (nth i rs (0, [])) :: map f (CheckRep.drop_nth i rs)).
Proof.
intros Y f rs i Hi. destruct (nth_split rs (0, []) Hi) as (A & Bs & Hsp & HlA).
assert (Hd : CheckRep.drop_nth i rs = A ++ Bs) by (rewrite Hsp, <- HlA; apply bl3_drop_split).
rewrite Hd. rewrite Hsp at 1. rewrite !map_app. cbn [map].
apply Permutation_sym, Permutation_middle.
Qed.
Lemma cl3_list_blks_drop : forall l i, (i < length (hl_recs l))%nat ->
Permutation (list_blks l) ((fst (nth i (hl_recs l) (0, [])), Z.of_nat (length (snd (nth i (hl_recs l) (0, [])))) + 1) ::
  list_blks (ldrop_list l i)).
Proof.
intros l i Hi. unfold list_blks, ldrop_list. cbn [hl_v hl_cap hl_recs].
change (firstn i (hl_recs l) ++ skipn (Datatypes.S i) (hl_recs l)) with (CheckRep.drop_nth i (hl_recs l)).
eapply Permutation_trans; [apply Permutation_app_head; exact (cl3_map_drop (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ i Hi)|].
apply Permutation_sym, Permutation_middle.
Qed.
Lemma cl3_blks_fst : forall l, map fst (list_blks l) = list_blocks l.
Proof.
intros l. unfold list_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.
Lemma cl3_perm_drop : forall (T0 : Type) (b1 b2 L : list T0) x, Permutation (b1 ++ x :: b2) (x :: L) -> Permutation (b1 ++ b2) L.
Proof. intros T0 b1 b2 L x H. apply (Permutation_cons_inv (a := x)). rewrite Permutation_middle. exact H. Qed.
Lemma cl3_rec_len : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
(* every byte a list's predicate reads is its head's or one of its blocks' *)
Lemma cl3_alist_fp_in : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr ->
LA <= a < LA + 16 \/ exists b, In b (list_blks l) /\ fst b <= a < fst b + snd b.
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & Hcap & Hv & _ & _ & _) rr Hin a Ha.
unfold alist_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Ha; exact Ha|]. right.
apply in_app_or in Hin as [Hin | Hin].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
  exists (hl_v l, AREC * hl_cap l). split; [unfold list_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  destruct Hv as [(Hc0 & _) | (_ & _ & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite (cl3_vec_len l Hj) in Ha. exact Ha.
- apply in_map_iff in Hin as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1).
  split; [unfold list_blks; apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr0|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite cl3_rec_len in Ha. exact Ha.
Qed.
Lemma cl3_nodup_disj : forall (T0 : Type) (l1 l2 : list T0) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros T0. induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hx|]. cbn [app] in H.
apply List.NoDup_cons_iff in H as [Hn H].
destruct Hx as [<- | Hx]; [apply Hn; apply in_or_app; right; exact Hy | exact (IH l2 x H Hx Hy)].
Qed.
(* a byte that stays present stays writable, across a world step *)
Lemma cl3_awr_kept : forall (Wa Wb : world SEGS) (ma mb : word -> option byte) a, wle Wa Wb ->
(apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
writable_at SEGS (arm Wa ma) a -> writable_at SEGS (arm Wb mb) a.
Proof. intros Wa Wb ma mb a Hw Hp Hwr. exact (cl3_writable_kept_w Wa Wb ma mb a Hp Hw Hwr). Qed.

(* the third part of a turn: list_drop(l, i) at 0x85a00 (LDROP at the held list's own globals, lifted to G), then the
   back-edge 0x85a04 .. 0x85a0c to the head (a working branch's lib/B/W_check_no_loss.v cnl_drop's form) *)
Lemma cl3_A3 : forall w ds c i W3 regs3 mem3 md3, cl3_mid w ds c i W3 regs3 mem3 md3 ->
(forall ds' W4 regs4 mem4 md4, cl3_inv w ds' c W4 regs4 mem4 md4 ->
  SRr SEGS W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + A_csheB_l3)) mem4 (seg_rom SEGS)) md4) Post) ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem3 (seg_rom SEGS)) md3) Post.
Proof.
intros w ds c i W3 regs3 mem3 md3 HMD HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HMD as (ly1 & S1 & kk & H1 & HM & Hi & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R24 & R1 & R10 & R11).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
pose proof (ajournal_gx_AR0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk HJ0) as HAR1.
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (Usp : spZ regs3 = sp0 - 112) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
pose proof cl3_pf_img as HPimg.
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (bl3_ends_len P _ _ _ HRUN)).
rewrite (bl3_drop_len _ _ Hi) in Hw26.
assert (HnH1 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
(* the source's lists, the held one in particular *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HAH1 & HNDB).
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HAH1, HNDB.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [unfold hl_n in HnleC; lia|].
destruct (cl3_blk ly1 S1 W3 mem3 md3 _ _ HAR1 HvinH) as (V16 & V4096 & _ & _ & _ & Vceil & _ & Voff & _ & Vpres).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
set (r := nth i (hl_recs H1) (0, [])) in *.
assert (Hrin : In r (hl_recs H1)) by (apply nth_In; exact Hi).
rewrite Forall_forall in HFallH. destruct (HFallH r Hrin) as (HinR & HgarR & HlinR & _).
destruct (cl3_blk ly1 S1 W3 mem3 md3 _ _ HAR1 HinR) as (R16 & R4096 & _ & Rle & _ & Rceil & _ & Roff & _ & Rpres).
(* list_drop's entry *)
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk HJ0)
  as (memS & HJi & HgS).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W3 regs3 mem3 md3 []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W3 mem3 md3 kk regs3
    LDROP_STK (- 112 - XO) [] HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite WS. unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cl3_dr, AF_fr_check_shape_ends; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold A_cl3_dr, AF_fr_check_shape_ends; lia).
    unfold A_cl3_dr, AF_fr_check_shape_ends. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* list_drop's globals: the held list's head only *)
set (G2 := [(HA + 80, 16)]).
assert (HG2G : forall a, inG G2 a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply HGa; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG2 : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G2 a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
assert (HG2s : forall a, inG G2 a -> VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; unfold ASRC in HAgs; lia | exfalso; exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G2 G HG2G HG) as HG2.
assert (HGRT2 : gx_rt B G2).
{ eapply gx_rt_sub; [|exact HGRR]. intros a Ha. apply (cl3_ro_in (VAL (A_OBJ 19)) 384 a); [cbv [cshe_ro_B]; do 3 right; left; reflexivity | exact (HG2s a Ha)]. }
assert (HROMS2 : forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G2 a).
{ intros a Hr. destruct (ROMNS a Hr) as (He & Hp). split; [exact Hp|]. split; [exact He|].
  intros Hg. destruct (HGS a (HG2s a Hg)) as (_ & Hnr & _). exact (Hnr Hr). }
assert (HMF : mo_free MT <= Z.of_nat (length (hl_recs H1)) * mo_free MT)
  by (pose proof (mo_free_nonneg MT ML); nia).
eapply SRr_bind.
{ refine (LDROP G2 HG2 HGRT2 HROMS2 W3 ly1 S1 [] regs3 mem3 md3 [] (HA + 80) H1 true i HPREd R10 R11 HAH1 Hi _ _ _ _ _ _ _
    (Z.to_nat (Z.of_nat (length (hl_recs (ldrop_list H1 i))) * mo_free MT_rk) + kr)%nat _ _ _).
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold AREC, hl_n. unfold hl_n in Hn26. lia.
  - destruct Hzs as (zr & Hzr & Hz8 & Hz1 & Hz2). exists zr. split; [exact Hzr|]. split; [exact Hz8|]. split; lia.
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia|].
    rewrite Usp. unfold LDROP_STK, LDROP_FRAME, ASTACK. rewrite WS in Hslo. unfold ASRC in HAhi. lia.
  - intros a Ha. rewrite Usp. rewrite HreqV in Vceil. unfold LDROP_STK, LDROP_FRAME, ASTACK. rewrite WS in Hslo. lia.
  - eapply (mo_ok_le MT ML); [exact HMOK | exact HMF].
  - (* the room round: record i's free is spent from the budget, the rest's stays *)
    rewrite cl3_rk. rewrite cl3_rk in HRMk. change (Z.to_nat (mo_free MT_rk)) with 1%nat.
    refine (RMM_of RP S1 _ _ _ HRMk). cbn [ldrop_list hl_recs].
    change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (bl3_drop_len _ _ Hi). lia.
  - (* list_drop's count premise (ldrop_pk = 0): the invariant's *)
    exact HCNk.
  - exact HROM. }
cbv beta. intros W5 c5 Hwle5 (ly2 & S2 & hpD & regs5 & mem5 & md5 & -> & HJd & HPd & HPKd & HERRd & HL2 & (b1 & b2 & Eb1 & Eb2) & HMLEd & HRMd).
hp0g HJd.
assert (HAR2 : AR0 ly2 S2 W5 mem5 md5) by (eapply ajournal_gx_AR_x; exact HJd).
pose proof HJd as HJd0. apply ajournal_gx_inner_x in HJd0. destruct HJd0 as (memS2 & HJdi & HgS2).
rewrite Usp in HJdi. destruct HJdi as (_ & HlyD & _ & _ & _ & HfrD & _ & _ & KF & KB & KI & _).
set (FPd := [(hl_v H1, hl_v H1 + AREC * hl_cap H1);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in *.
assert (Hcl : ~ YI16.sink_open_fp FPd) by (apply sink_closed_pos; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia).
assert (HAr : 0x10000 <= HA /\ HA + 96 <= 0x5fc000).
{ pose proof (pa_img_range HA (proj1 (HAimg HA ltac:(unfold ASRC; lia)))).
  pose proof (pa_img_range (HA + 95) (proj1 (HAimg (HA + 95) ltac:(unfold ASRC; lia)))). lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - LDROP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite KF by (rewrite ?Z.add_0_r; lia). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Hi' Ho He Hn. pose proof (pa_img_range a Hi') as Hr.
  rewrite KI; [|exact Hi' | exact Ho | exact He | exact (HPST a Hi') | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. exact Hn. }
assert (Kblk : forall p n i0, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ inFP FPd (p + i0) ->
  0 <= i0 < req_size n -> aview SEGS (w_H W5) mem5 (p + i0) = aview SEGS (w_H W3) mem3 (p + i0)).
{ intros p n i0 Hb1 Hb2 Hn Hi0. destruct (cl3_blk ly1 S1 W3 mem3 md3 p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i0 Hb1 Hb2 Hi0 Hn). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. unfold off_img in Hoff. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W3 mem3) a -> writable_at SEGS (arm W5 mem5) a).
{ intros a Hi' Ho He Hw. apply (cl3_awr_kept W3 W5 mem3 mem5 a Hwle5); [|exact Hw]. intros Hp. exact (HPKd a Hi' Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W5 mem5) a).
{ intros p n a Hb Ha. destruct (cl3_blk ly2 S2 W5 mem5 md5 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
set (rb := (fst r, Z.of_nat (length (snd r)) + 1)) in *.
assert (Hlive : forall b, In b (ablocks B ly1 S1) -> b <> rb -> In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Eb2. rewrite Eb1 in Hb. apply in_app_or in Hb as [Hb | [<- | Hb]];
  [apply in_or_app; left; exact Hb | exfalso; exact (Hne eq_refl) | apply in_or_app; right; exact Hb]. }
(* the held list's addresses: its vector and r's text are none of the other lists' blocks *)
assert (HrbH : In (fst rb) (list_blocks H1)).
{ unfold list_blocks. apply in_or_app. right. change (fst rb) with (fst r). apply (in_map fst). exact Hrin. }
assert (HvH : In (hl_v H1) (list_blocks H1)).
{ unfold list_blocks. destruct (hl_cap H1 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity. }
set (Oth := (hs_partial h, APARTIAL) :: list_blks (hs_pending h) ++ list_blks (hs_expected h)).
assert (HNDl : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1)).
{ apply NoDup_ListNoDup in HNDB. rewrite <- !app_assoc. exact HNDB. }
assert (HOthA : forall b, In b Oth -> ~ In (fst b) (list_blocks H1)).
{ intros b Hb. apply (cl3_nodup_disj _ _ _ (fst b) HNDl).
  unfold Oth in Hb. destruct Hb as [<- | Hb]; [apply in_or_app; right; left; reflexivity|].
  apply in_app_or in Hb as [Hb | Hb].
  - apply in_or_app. left. rewrite <- cl3_blks_fst. apply (in_map fst). exact Hb.
  - apply in_or_app. right. right. rewrite <- cl3_blks_fst. apply (in_map fst). exact Hb. }
assert (HOth1 : forall b, In b Oth -> In b (ablocks B ly1 S1)).
{ intros b Hb. unfold Oth in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (cl3_alist_blks_in _ _ _ _ _ _ _ Hpend b Hb) | exact (cl3_alist_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
assert (HOth2 : forall b, In b Oth -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Hlive b (HOth1 b Hb)). intros E'. apply (HOthA b Hb). rewrite E'. exact HrbH. }
(* a byte of a block other than the vector and r's text is outside list_drop's footprint *)
assert (KAb : forall b a, In b (ablocks B ly1 S1) -> In b (ablocks B ly2 S2) ->
  fst b <> hl_v H1 -> fst b <> fst rb -> fst b <= a < fst b + snd b -> abyte_kept W3 mem3 W5 mem5 a).
{ intros (p & n) a Hb1 Hb2 Hnv Hnr Ha. cbn [fst snd] in Hnv, Hnr, Ha.
  destruct (cl3_blk ly1 S1 W3 mem3 md3 p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr' & _).
  replace a with (p + (a - p)) by lia.
  split; [|intros _; apply (Pblk p n); [exact Hb2 | lia]].
  apply (Kblk p n); [exact Hb1 | exact Hb2 | | lia].
  intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
  - pose proof (sep_blocks0 ly1 S1 W3 mem3 md3 _ _ p n HAR1 HvinH Hb1 ltac:(intros E'; injection E' as E1 _; lia)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
  - pose proof (sep_blocks0 ly1 S1 W3 mem3 md3 _ _ p n HAR1 HinR Hb1 ltac:(intros E'; injection E' as E1 _; unfold rb in Hnr; cbn [fst] in Hnr; lia)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KOth : forall b a, In b Oth -> fst b <= a < fst b + snd b -> abyte_kept W3 mem3 W5 mem5 a).
{ intros b a Hb Ha. apply (KAb b a (HOth1 b Hb) (HOth2 b Hb)); [| | exact Ha].
  - intros E'. apply (HOthA b Hb). rewrite E'. exact HvH.
  - intros E'. apply (HOthA b Hb). rewrite E'. exact HrbH. }
(* the source's own bytes outside the held head *)
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W3 mem3 W5 mem5 a).
{ intros a Ha. destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hi' & Ho & He & _).
  split; [apply Kimg; [exact Hi' | exact Ho | exact He | lia] | apply Pimg; assumption]. }
(* the journal: list_drop's inside this one *)
assert (HrbH0 : In rb (list_blks H0)).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). apply HINC. exact Hrin. }
assert (HvbH0 : In (hl_v H1, AREC * hl_cap H1) (list_blks H0)).
{ unfold list_blks. rewrite HV, HC in *. destruct (hl_cap H0 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|].
  apply in_or_app. left. left. reflexivity. }
assert (HFPd : forall a, inFP FPd a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). left. cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha.
  - split; [|exists (hl_v H1), (AREC * hl_cap H1); split; [exact HvinH | rewrite HreqV; exact Ha]].
    exists (hl_v H1, hl_v H1 + req_size (AREC * hl_cap H1)). split; [|cbn [fst snd]; rewrite HreqV; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v H1, AREC * hl_cap H1)). exact HvbH0.
  - split; [|exists (fst r), (Z.of_nat (length (snd r)) + 1); split; [exact HinR | exact Ha]].
    exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ rb). exact HrbH0. }
pose proof (ajournal_gx_G_mono0 G2 G 0 [] LDROP_STK (spZ regs3) FPd ly1 S1 W3 mem3 md3 [] ly2 S2 W5 mem5 md5 1
  HG2G HJd) as HJd'. rewrite Usp in HJd'.
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk
  LDROP_STK (sp0 - 112) 0 [] FPd [] ly2 S2 W5 mem5 md5 1 HJ0 HJd'
  ltac:(rewrite WS; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPd) as HJ2.
cbn [app] in HJ2.
(* the held list without record i, and the source around it *)
assert (HND2 : NoDup (hs_blocks (CheckRep.set_held (CheckRep.set_held h H1) (ldrop_list H1 i)))).
{ rewrite cl3_set_held2. apply NoDup_ListNoDup. unfold hs_blocks. cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held].
  assert (HPb : Permutation (list_blocks H1) (fst rb :: list_blocks (ldrop_list H1 i))).
  { rewrite <- !cl3_blks_fst.
    change (fst rb :: map fst (list_blks (ldrop_list H1 i))) with (map fst (rb :: list_blks (ldrop_list H1 i))).
    apply Permutation_map. exact (cl3_list_blks_drop H1 i Hi). }
  assert (HP2 : Permutation ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1)
    (fst rb :: (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks (ldrop_list H1 i))).
  { eapply Permutation_trans; [apply Permutation_app_head; exact HPb|]. apply Permutation_sym, Permutation_middle. }
  pose proof (Permutation_NoDup HP2 HNDl) as Hx. apply List.NoDup_cons_iff in Hx as [_ Hx].
  rewrite <- !app_assoc in Hx. exact Hx. }
assert (HSRC2 : asrc_at B ly2 S2 W5 mem5 HA (CheckRep.set_held h (ldrop_list H1 i))).
{ rewrite <- (cl3_set_held2 h H1 (ldrop_list H1 i)).
  apply (cl3_src_swap ly1 S1 W3 mem3 ly2 S2 W5 mem5 HA (CheckRep.set_held h H1) (ldrop_list H1 i) HSRC KHd); [| | exact HL2 | exact HND2].
  - intros rr Hrr a Ha. cbn [CheckRep.set_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KOth (hs_partial h, APARTIAL)); [left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (cl3_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KOth b); [unfold Oth; right; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (cl3_alist_fp_in _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KOth b); [unfold Oth; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. apply HOth2. exact Hb. }
assert (HOUTn : ob <> [] -> OUT <> hl_v H1 /\ OUT <> fst rb).
{ intros Hne. pose proof (HOH Hne) as Hn. split.
  - intros E'. apply Hn. rewrite E'. unfold list_blocks. rewrite HV, HC in *.
    destruct (hl_cap H0 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity.
  - intros E'. apply Hn. rewrite E'. unfold list_blocks. apply in_or_app. right. change (fst rb) with (fst r).
    apply (in_map fst). apply HINC. exact Hrin. }
assert (HM2 : cl3_mem ly2 S2 W5 mem5 md5 (kk + 1) (ldrop_list H1 i) (ds ++ [r])).
{ split; [exact HJ2|].
  split; [exact HSRC2|].
  split; [exact HV|]. split; [exact HC|].
  split.
  { unfold CheckRep.texts in HND |- *. cbn [ldrop_list hl_recs].
    change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    exact (bl3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND). }
  split; [intros x Hx; apply HINC; exact (bl3_incl_drop (hl_recs H1) i x Hx)|].
  split; [cbn [ldrop_list hl_recs]; change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1));
    rewrite (bl3_drop_len _ _ Hi), length_app; cbn [length]; lia|].
  assert (KG : forall b n x, In (b, n) cshe_ro_B -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
    aview SEGS (w_H W5) mem5 x = aview SEGS (w_H W3) mem3 x).
  { intros b n x Hin Hx Hn. destruct (cl3_ro b n x Hin Hx) as (Hi' & Ho & He & _). apply Kimg; assumption. }
  assert (HG3 : forall x, HA + 80 <= x < HA + 96 -> ~ (VAL A_g_gone <= x < VAL A_g_gone + 1) /\
    ~ (VAL A_g_nout <= x < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= x < VAL A_g_out + 8)).
  { intros x Hx. assert (Hs : VAL (A_OBJ 19) <= x < VAL (A_OBJ 19) + 384) by (unfold ASRC in HAgs; lia).
    destruct (HGS x Hs) as (_ & _ & Hg1 & Hg2 & Hg3). auto. }
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_gone); [lia | intros Hc; apply (proj1 (HG3 x Hc)); lia] | exact MG]|].
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_nout); [lia | intros Hc; apply (proj1 (proj2 (HG3 x Hc))); lia] | exact MNO]|].
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_out); [lia | intros Hc; apply (proj2 (proj2 (HG3 x Hc))); lia] | exact MOUT]|].
  split.
  { intros k Hk. destruct HOBK as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
    assert (Hne : ob <> []) by (intros E0; rewrite E0 in Hk; cbn in Hk; lia).
    destruct (HOUTn Hne) as (Hn1 & Hn2).
    assert (HO2 : In (OUT, CO) (ablocks B ly2 S2)) by (apply (Hlive _ HOin); intros E'; apply Hn2; rewrite <- E'; reflexivity).
    destruct (cl3_blk ly1 S1 W3 mem3 md3 OUT CO HAR1 HOin) as (_ & _ & _ & Hle & _).
    rewrite (proj1 (KAb (OUT, CO) (OUT + k) HOin HO2 Hn1 Hn2 ltac:(cbn [fst snd]; lia))). exact (HOBt k Hk). }
  split.
  { destruct HOBK as [E0 | (CO & HCO & HOin)]; [left; exact E0|].
    destruct (Nat.eq_dec (length ob) 0) as [Hl0 | Hl0]; [left; apply length_zero_iff_nil; exact Hl0|].
    assert (Hne : ob <> []) by (intros E0; rewrite E0 in Hl0; apply Hl0; reflexivity).
    destruct (HOUTn Hne) as (Hn1 & Hn2). right. exists CO. split; [exact HCO|].
    apply (Hlive _ HOin). intros E'. apply Hn2. rewrite <- E'. reflexivity. }
  split.
  { intros rest HQ0. rewrite map_app, <- app_assoc in HQ0. cbn [map app] in HQ0.
    pose proof (HPERM (rb :: rest) HQ0) as HP1. rewrite Eb2. rewrite Eb1 in HP1. exact (cl3_perm_drop _ b1 b2 rest _ HP1). }
  split; [rewrite HfrD; exact HFRS|].
  split.
  { eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLEd)|].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
    rewrite Z.mul_add_distr_r, Z.mul_1_l. lia. }
  split.
  { apply (mo_ok_step MT ML S1 S2 (mo_free MT)); [|exact HMLEd].
    eapply (mo_ok_le MT ML); [exact HMOK|].
    cbn [ldrop_list hl_recs]. change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (bl3_drop_len _ _ Hi). rewrite Nat2Z.inj_sub by lia. cbn [Z.of_nat Pos.of_succ_nat].
    rewrite Z.mul_sub_distr_r, Z.mul_1_l. lia. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as (He & Hpinn).
    assert (Hd : forall r0, {in_zr a r0} + {~ in_zr a r0}).
    { intros r0. unfold in_zr. destruct (Z_le_gt_dec (fst r0) a); destruct (Z_lt_ge_dec a (fst r0 + snd r0));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno].
    - exact (rom_pinned_view0 ly2 S2 W5 mem5 md5 a HAR2 (Hpinn Hown)).
    - assert (Hi' : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; [exact Hsg | exact Hra]).
      rewrite (Kimg a Hi' Hno He); [exact (HROM a Hr)|].
      intros Hc. destruct (HGS a ltac:(unfold ASRC in HAgs; lia)) as (_ & Hnr & _). exact (Hnr Hr). }
  split.
  { apply (cl3_saved_kept W3 W5 mem3 mem5 sp0 regs0); [|exact HSAV].
    intros a Ha. apply Kstk; [rewrite WS in Hslo; lia | unfold LDROP_STK, LDROP_FRAME, ASTACK; lia]. }
  split; [intros jj Hjj; rewrite HERRd by lia; exact (HERR jj Hjj)|].
  (* the room round: list_drop's post room is the rest's budget; the counts fell by record i's block *)
  split; [exact HRMd|]. rewrite Eb2. rewrite Eb1 in HCNk. exact (cl3_cnt_del RP _ _ _ HCNk). }
(* ---- 0x85a04: the back-edge *)
assert (P2 : getr regs5 2 = getr regs3 2) by (apply (HPd 2); unfold acallee_saved; lia).
assert (P3 : getr regs5 3 = getr regs3 3) by (apply (HPd 3); unfold acallee_saved; lia).
assert (P4 : getr regs5 4 = getr regs3 4) by (apply (HPd 4); unfold acallee_saved; lia).
assert (P8 : getr regs5 8 = getr regs3 8) by (apply (HPd 8); unfold acallee_saved; lia).
assert (P9 : getr regs5 9 = getr regs3 9) by (apply (HPd 9); unfold acallee_saved; lia).
assert (P18 : getr regs5 18 = getr regs3 18) by (apply (HPd 18); unfold acallee_saved; lia).
assert (P19 : getr regs5 19 = getr regs3 19) by (apply (HPd 19); unfold acallee_saved; lia).
assert (P21 : getr regs5 21 = getr regs3 21) by (apply (HPd 21); unfold acallee_saved; lia).
assert (P23 : getr regs5 23 = getr regs3 23) by (apply (HPd 23); unfold acallee_saved; lia).
assert (P24 : getr regs5 24 = getr regs3 24) by (apply (HPd 24); unfold acallee_saved; lia).
assert (P27 : getr regs5 27 = getr regs3 27) by (apply (HPd 27); unfold acallee_saved; lia).
rewrite R1.
assert (Hwr : 0 <= Z.of_nat w <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cl3d_state W5 regs5 mem5 (sp0 - 112) (Z.of_nat w) (eq_trans P2 R2) (eq_trans P21 R21) (eq_trans P23 R23)
  (eq_trans P24 R24) HSPb HSPa Hwr) as [HS SHOK].
remember (Eimg (Ereg regs5 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs5 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ2 SHOK Bspan A_csheB_l3. { cl3_awr. }
assert (E24 : ew E 24 = w64 (Z.of_nat w)) by (rewrite (EEo 24%nat 24%bv eq_refl), P24; exact R24).
psrr_branch_tok RUNx BR HS SHOK Bspan.
2: { (* 0x85a0c blt a0,s8: a0 = w - 1 < s8 = w (w <= 2 ^ 26), so the fall-through to the unimp at 0x85a10
        (DECW_FT; W_traps.v trap_seat is this fact as a seat condition) never runs *)
  exfalso. rewrite trap_br_lt, !S_SOff in Hc. rewrite E24 in Hc. unfold w64 in Hc.
  rewrite unsigned_lit_small in Hc by lia.
  rewrite !bv_swrap_small in Hc by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  apply Z.ltb_ge in Hc. lia. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ2 SHOK Bspan A_csheB_l3. { cl3_awr. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (22%bv : bv 5) N22. prreg HS (10%bv : bv 5) N10.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?m) _ (ms_mem ?m) _; cfg_model := ?mdq |} _ =>
  assert (MQ : forall x, mrestrict (w_H W5) (ms_mem m) x = mrestrict (w_H W5) mem5 x);
  [intros x; repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
     rewrite (Hf x) by cl3_nowr end; reflexivity|];
  destruct (cl3_eqv_view W5 mem5 (ms_mem m) MQ) as (AVE & APE);
  replace (BASE + 13880) with (BASE + A_csheB_l3) by (unfold A_csheB_l3, AF_fr_check_shape_ends; lia);
  apply (HKont (ds ++ [r]) W5 (ms_regs m) (ms_mem m) mdq)
end.
exists ly2, S2, (kk + 1), (ldrop_list H1 i).
assert (Edr : hl_recs (ldrop_list H1 i) = CheckRep.drop_nth i (hl_recs H1)) by reflexivity.
split.
{ eapply (cl3_mem_step ly2 S2 W5 W5 mem5 _ md5 _ (kk + 1) (kk + 1) (ldrop_list H1 i) (ds ++ [r]) HM2 HJ2 (wle_refl _ W5)).
  - intros a _. apply AVE.
  - intros a _. apply AVE.
  - exact APE. }
rewrite Edr.
split; [exact HRUN|].
split; [exact HREL|].
split; [exact Hc0|]. split; [exact HcO|].
split.
{ apply (cl3_vm_keep W3 W5 mem3 _); [|exact MAT]. intros x Hx. rewrite AVE.
  apply Kstk; [rewrite WS in Hslo; lia | unfold LDROP_STK, LDROP_FRAME, ASTACK; lia]. }
split.
{ unfold cl3_regs.
  split; [rewrite N2, (EEo 2%nat 2%bv eq_refl), P2; exact R2|].
  split; [rewrite N3, (EEo 3%nat 3%bv eq_refl), P3; exact R3|].
  split; [rewrite N4, (EEo 4%nat 4%bv eq_refl), P4; exact R4|].
  split; [rewrite N27, (EEo 27%nat 27%bv eq_refl), P27; exact R27|].
  split; [rewrite N8, (EEo 8%nat 8%bv eq_refl), P8; exact R8|].
  split; [rewrite N9, (EEo 9%nat 9%bv eq_refl), P9; exact R9|].
  split; [rewrite N18, (EEo 18%nat 18%bv eq_refl), P18; exact R18|].
  split; [rewrite N19, (EEo 19%nat 19%bv eq_refl), P19; exact R19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N22; exact E24|].
rewrite N10, E24. unfold w64 at 1. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* the last head: no turn left (s6 = 0), 0x8597c `blez s6` goes to the epilogue 0x8592c, where cshe_out_B's want
   disjunct is the invariant's ends_run at w = 0 *)
Lemma cl3_base : forall ds c W1 regs1 mem1 md1, cl3_inv 0 ds c W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros ds c W1 regs1 mem1 md1 HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & kk & H1 & HM & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R22 & R10).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
destruct (cl3_state0 W1 regs1 mem1 (sp0 - 112) R2 R21 R23 R22 HSPb HSPa) as [HS SHOK].
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
pose proof HM as (HJ0 & _).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ0 SHOK Bspan A_csheB_ret. { cl3_awr. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?m) ?pc (ms_mem ?m) _; cfg_model := ?mdq |} _ =>
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem m) x = mrestrict (w_H W1) mem1 x);
  [intros x; repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
     rewrite (Hf x) by cl3_nowr end; reflexivity|];
  destruct (cl3_eqv_view W1 mem1 (ms_mem m) MQ) as (AVE & APE);
  pose proof (cl3_mem_step ly1 S1 W1 W1 mem1 (ms_mem m) md1 mdq kk kk H1 ds HM HJ0 (wle_refl _ W1)
    ltac:(intros a _; apply AVE) ltac:(intros a _; apply AVE) APE) as HM';
  apply SRr_ret; exists ly1, S1, (ms_regs m), (ms_mem m), mdq, kk, H1, ds, c
end.
destruct HM' as (HJ' & HSRC' & HV' & HC' & HND' & HINC' & HLEN' & MG' & MNO' & MOUT' & HOBt' & HOBK' & HPERM' & HFRS' &
  HMLE' & HMOK' & HROM' & HSAV' & HERR' & HRM' & HCN').
split; [reflexivity|].
split; [exact HJ'|].
split; [rewrite N2, (EEo 2%nat 2%bv eq_refl); exact R2|].
split; [rewrite N3, (EEo 3%nat 3%bv eq_refl); exact R3|].
split; [rewrite N4, (EEo 4%nat 4%bv eq_refl); exact R4|].
split; [rewrite N27, (EEo 27%nat 27%bv eq_refl); exact R27|].
split; [exact HSAV'|].
split; [exact HSRC'|].
split; [exact HV'|]. split; [exact HC'|]. split; [exact HND'|].
split.
{ right. split; [reflexivity|].
  specialize (HREL (hl_recs H1) [] 0 eq_refl). rewrite app_nil_r, Z.add_0_r in HREL. exact HREL. }
split; [exact Hc0|].
split; [apply (cl3_vm_keep W1 W1 mem1 _); [intros x _; apply AVE | exact MAT]|].
split; [exact MG'|].
split; [exact HPERM'|].
split; [exact HFRS'|].
split.
{ eapply (mo_le_mono MT ML); [exact HMLE'|]. pose proof (mo_free_nonneg MT ML) as Hf0.
  unfold hl_n. apply Z.mul_le_mono_nonneg_r; lia. }
split; [exact HERR'|].
(* the room round: the records left keep their free's room unspent; past them, the caller's kr *)
rewrite cl3_rk in HRM'. exact (RMM_of RP S1 kr _ (Nat.le_add_l _ _) HRM').
Qed.

(* the loop, by induction on the turns left: each turn is cl3_A1 ; cl3_A2 ; cl3_A3 back to the head *)
Lemma cl3_loop : forall w ds c W1 regs1 mem1 md1, cl3_inv w ds c W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction w as [|w IH]; intros ds c W1 regs1 mem1 md1 HI.
- exact (cl3_base ds c W1 regs1 mem1 md1 HI).
- apply (cl3_A1 w ds c W1 regs1 mem1 md1 HI). intros l i W2 regs2 mem2 md2 HAB.
  apply (cl3_A2 w ds c l i W2 regs2 mem2 md2 HAB). intros W3 regs3 mem3 md3 HMD.
  apply (cl3_A3 w ds (c + Z.of_nat (length l) + 1) i W3 regs3 mem3 md3 HMD). intros ds' W4 regs4 mem4 md4 HI4.
  exact (IH ds' _ W4 regs4 mem4 md4 HI4).
Qed.
End loop.

(* ------------------------------------------------------------------ the piece: loop 3, cshe_l3_in -> cshe_out_B *)
(* Its premises are cshe_spec's (W3's text at a working branch fb87b19890f W_contract.v Section w3e, with P a ROM
   literal OR a fake-frame local; CSHE_STK read as CSHE_STK_B, g_s as B's A_OBJ 19, `let H := hs_held h` and
   `let PLEN := Z.of_nat (length P)` expanded, `cshe_cost H` unfolded), only those loop 3 uses, in cshe_spec's
   order. *)
Lemma cshe_l3_B : forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob,
AFP0 CSHE_STK_B ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\
   forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob)
  (CheckRep.want_of P (hl_recs (hs_held h))) <> None) ->
mo_ok MT S (hl_n (hs_held h) * mo_free MT) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l3_in B PST ARx G regs ly S W mem md XO AT HA PF gone h P W1 c1 ->
SRr SEGS W1 c1 (cshe_out_B B PST ARx G MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr).
Proof.
intros W ly S regs mem md ch XO AT HA j PF h P A0 gone O OUT ob
  HPRE HX0 HX16 HXtop HSRC HA8 HA4096 HAk HGa Hzs HAj Hj4 HND Hn26 HAT8 HATl HATh MAT0 HPz HPl HPF0 HPFh HPB HPN HPV
  HPM1 HPM8 HPRA HPSV HPD HLG HROM0 MG0 MNO0 MOUT0 HOBt HOlen HO40 HO32 HOM HOBK HA0 HFUN HMOK kr HRM0 HCN0 W1 c1 HIN.
destruct HIN as (regs1 & mem1 & md1 & -> & HJ1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23 & R22 & R10 &
  HSAV1 & KV & KP & Hg0).
subst gone.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
(* the source g_s[j] *)
assert (HAgs : VAL (A_OBJ 19) <= HA /\ HA + ASRC <= VAL (A_OBJ 19) + 384) by (unfold ASRC in *; lia).
assert (Hgs_in : In (VAL (A_OBJ 19), 384) cshe_ro_B) by (cbv [cshe_ro_B]; do 3 right; left; reflexivity).
assert (HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a).
{ intros a Ha. destruct (cl3_ro _ _ a Hgs_in ltac:(lia)) as (Hi & Ho & He & _).
  destruct (HGS a ltac:(lia)) as (_ & Hnr & _). auto. }
assert (HAr : 0x10000 <= HA /\ HA + ASRC <= 0x5fc000).
{ pose proof (pa_img_range HA (proj1 (HAimg HA ltac:(unfold ASRC; lia)))).
  pose proof (pa_img_range (HA + ASRC - 1) (proj1 (HAimg (HA + ASRC - 1) ltac:(unfold ASRC; lia)))). lia. }
(* the journal's world step and the views below the frame *)
pose proof HJ1 as HJ1i. apply ajournal_gx_inner_x in HJ1i. destruct HJ1i as (memS & HJi & _).
pose proof HJi as (HAR1 & _ & _ & Hwle1 & _).
assert (KL : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KV; lia).
assert (KR : forall a, 4096 <= a < 0x5fc000 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KL; lia).
assert (HOH : ob <> [] -> ~ In OUT (list_blocks (hs_held h))).
{ intros Hne Hin. destruct HOBK as [E0 | (CO & _ & _ & Hn)]; [exact (Hne E0)|]. apply Hn.
  unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
assert (HOBK' : ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S))
  by (destruct HOBK as [E0 | (CO & H1 & H2 & _)]; [left; exact E0 | right; exists CO; split; assumption]).
assert (HINV : cl3_inv regs ly S W mem md XO AT HA PF A0 O OUT h P ob kr (CheckRep.want_of P (hl_recs (hs_held h))) [] 0
  W1 regs1 mem1 md1).
{ exists ly, S, 0, (hs_held h).
  split.
  { split; [exact HJ1|].
    split; [rewrite cl3_set_held_id; apply (cl3_src_kept ly S W W1 mem mem1 md HA h alloc_ceiling HAR0 HSRC);
      [lia | unfold ASRC in HAr; lia | lia | exact Hwle1 | exact KL | exact KP]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|]. split; [apply incl_refl|].
    split; [cbn [length]; lia|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_gone ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MG0]|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_nout ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MNO0]|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_out ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MOUT0]|].
    split.
    { intros k Hk. destruct HOBK' as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
      destruct (cl3_blk ly S W mem md OUT CO HAR0 HOin) as (_ & H4096 & _ & Hle & _ & Hc & _).
      rewrite KL by lia. exact (HOBt k Hk). }
    split; [exact HOBK'|].
    split; [intros rest HQ0; exact HQ0|].
    split; [reflexivity|].
    split; [exact (mo_le_refl MT ML S)|].
    split; [unfold hl_n in HMOK; exact HMOK|].
    split.
    { intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
      rewrite KR by lia. exact (HROM0 a Hr). }
    split; [exact HSAV1|].
    split; [intros jj Hjj; pose proof (pal_env B TL) as (_ & EIMG & _);
      pose proof (pa_img_range _ (EIMG (as_errno B + jj) ltac:(lia))); apply KR; lia|].
    (* the room round: cshe_cost MT_rk is one free per record, the loop's budget at the held list; the counts are the
       entry's (cshe_pk = 0) *)
    split; [|exact HCN0]. unfold cshe_cost, hl_n in HRM0. exact HRM0. }
  rewrite Z.add_0_r.
  split; [exact (HFUN eq_refl)|].
  split; [intros rsF dsF cF E; rewrite E; reflexivity|].
  split; [lia|]. split; [lia|].
  split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn in Hx; apply KV; [lia | rewrite WS; lia] | exact MAT0]|].
  split; [unfold cl3_regs; repeat split; assumption|].
  split; assumption. }
assert (HBLK : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S)).
{ pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
  intros b Hb. exact (cl3_alist_blks_in _ _ _ _ _ _ _ HAH0 b Hb). }
eapply cl3_loop with (regs0 := regs) (ly := ly) (S := S) (W := W) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT)
  (HA := HA) (PF := PF) (A0 := A0) (O := O) (OUT := OUT) (h := h) (P := P) (ob := ob) (kr := kr).
all: try eassumption.
all: try (unfold ASRC in *; lia).
all: try (intros a Ha; exact (proj1 (HPV a Ha))).
Qed.
Print Assumptions cshe_l3_B.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): loop 3 at a world relation R, for W_check_shape_ends.v pb_check_shape_ends_xR.
   cshe_l3_B_xR is cshe_l3_B with cshe_l3_in -> cshe_l3_in_xR, SRr SEGS -> SRrG SEGS R and cshe_out_B -> cshe_out_B_xR
   (W_cshe_epi.v Section wR).  Each <name>_xR below is the strict <name> with the journal ajournal_gx_x SEGS B PST ARx
   -> ajournal_gx_xR SEGS B PST ARx R (AJ0R, at the empty ghost list as AJ0); the runs are paj_run_x_xG /
   paj_run_to_x_xG (W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR), the branch paj_branch_xR, the binds SRrG_bind.
   next_line, list_find, has_prefix and bcmp stay at their strict contracts: lifted by SRr_SRrG (WLE_R), bcmp through
   W_sites_x.v aj_bcmp_gx_at_xR, and their journals by cl3_jR.  list_drop is LDROP_R (W_contract_xR_g3.v
   ldrop_spec_xR).  A step at R may hide more than wle allows, so writability across a step comes from presence alone
   (cl3_writable_kept_pR) and cl3_src_kept_xR / cl3_mem_step_xR / cl3_awr_kept_xR take no world premise.  The strict
   texts above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis LDROP_R : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_xR B PST ARx R MT RP G' (BASE + AF_fr_list_drop).
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* the walk at the empty ghost list over the R journal: the R twins of AJ0 / AJi0 and of the kit notations above *)
Local Notation AJ0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR SEGS B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation ajournal_gx_AR0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_xR SEGS B PST ARx (R := R) G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0R G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_xR SEGS B PST ARx (R := R) G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0R G0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_xR SEGS B PST ARx (R := R) G0 G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0R Hs G0 STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hs R_trans G0 STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0R G0 XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_xR SEGS B PST ARx R_refl G0 XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0R STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_atR SEGS B PST ARx (R := R) STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0R pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc k
     x y n o raw).
(* a strict callee's journal is one at R (W_journal_x.v ajournal_gx_xR_mono, WLE_R) *)
Lemma cl3_jR {G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k} :
ajournal_gx_x SEGS B PST ARx G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k ->
ajournal_gx_xR SEGS B PST ARx R G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k.
Proof.
intros HJ. exact (ajournal_gx_xR_mono SEGS B PST ARx (@wle SEGS) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* writability across a step that keeps presence, at any world relation: where the byte is hidden or absent its
   writability is the segment's (lib/A/W_cshe_l2w.v l2_writable_kept_pR, copied) *)
Lemma cl3_writable_kept_pR : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EHb.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
- destruct (m' (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
  destruct (w_H W (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
(* cl3_src_kept with writability from presence alone: no world premise *)
Lemma cl3_src_kept_xR : forall ly S (W W' : world SEGS) mem mem' md HA h lo,
AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 0x10000 <= HA -> HA + 96 <= 0x7fff8000 ->
alloc_ceiling <= lo ->
(forall a, 4096 <= a < lo -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
asrc_at B ly S W' mem' HA h.
Proof.
intros ly S W W' mem mem' md HA h lo HAR HS HAlo HAhi Hlo Hq Hp.
apply (asrc_at_kept B ly S W mem ly S W' mem' HA h HS).
- intros rr Hin a Ha.
  destruct (cl3_src_low ly S W mem md HA h HAR HS HAlo HAhi rr Hin a Ha) as [Hl1 Hl2].
  split; [apply Hq; lia | exact (cl3_writable_kept_pR W W' mem mem' a (Hp a))].
- intros b Hb. exact (cl3_src_blks ly S W mem HA h HS b Hb).
Qed.
(* cl3_awr_kept with no world premise *)
Lemma cl3_awr_kept_xR : forall (Wa Wb : world SEGS) (ma mb : word -> option byte) a,
(apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
writable_at SEGS (arm Wa ma) a -> writable_at SEGS (arm Wb mb) a.
Proof. intros Wa Wb ma mb a Hp Hwr. exact (cl3_writable_kept_pR Wa Wb ma mb a Hp Hwr). Qed.

(* ------------------------------------------------------------------ the loop at R *)
(* Section loop's variables, notations and hypotheses, verbatim, with Post at cshe_out_B_xR .. R .. *)
Section loopR.
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 O OUT : Z) (h : hsrc) (P ob : list byte).
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_out_B_xR B PST ARx G R MT RP regs0 ly S W mem md XO AT HA A0 0 h P ob kr).
Local Notation WANT := (CheckRep.want_of P (hl_recs (hs_held h))).
Local Notation LIT := (VAL A_lit_end5).
Local Notation PLEN := (Z.of_nat (length P)).
Hypothesis HPRE : AFP0 CSHE_STK_B ly S W regs0 mem md ch.
Hypothesis HX0 : 0 <= XO.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HAT8 : AT mod 8 = 0.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 0x10000 <= HA.
Hypothesis HAhi : HA + ASRC <= 0x7fff8000.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HOlen : Z.of_nat (length ob) = O.
Hypothesis HO40 : O <= 2 ^ 40.
Hypothesis HO32 : 0 < O -> O < 2 ^ 32.
Hypothesis HOM : amem_range OUT (O + 8).
Hypothesis HOH : ob <> [] -> ~ In OUT (list_blocks (hs_held h)).
Hypothesis HA0 : 0 <= A0 <= O.
Hypothesis HROM0 : rom_view SEGS W mem.
Hypothesis HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a.
Hypothesis HAgs : VAL (A_OBJ 19) <= HA /\ HA + ASRC <= VAL (A_OBJ 19) + 384.
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
Hypothesis HPSV : shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1).
Hypothesis HPD : ((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1)) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
Hypothesis HBLK : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S).
Hypothesis HLG : garr8 SEGS (arm W mem) LIT (bzs END5).

(* cl3_mem at R *)
Definition cl3_mem_xR (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (mem1 : word -> option byte) (md1 : Model)
  (kk : Z) (H1 : hlist) (ds : list (Z * list byte)) : Prop :=
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_gone) 1 0 /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_nout) 8 O /\
val_mem SEGS (mrestrict (w_H W1) mem1) (VAL A_g_out) 8 OUT /\
ob_at W1 mem1 OUT ob /\ (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
  Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rom_view SEGS W1 mem1 /\ cshe_saved_B W1 mem1 sp0 regs0 /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
rp_RM RP S1 (Z.to_nat (Z.of_nat (length (hl_recs H1)) * mo_free MT_rk) + kr) /\ cnt_ok RP (ablocks B ly1 S1).
(* cl3_regs, restated inside Section loopR *)
Definition cl3_regs_xR (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 27 = getr regs0 27 /\ getr regs1 8 = w64 PF /\ getr regs1 9 = w64 (HA + 80) /\ getr regs1 18 = w64 AT /\
getr regs1 19 = w64 LIT /\ getr regs1 21 = w64 4 /\ getr regs1 23 = w64 5.
(* cl3_inv at R *)
Definition cl3_inv_xR (w : nat) (ds : list (Z * list byte)) (c : Z) (W1 : world SEGS) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist),
cl3_mem_xR ly1 S1 W1 mem1 md1 kk H1 ds /\
CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT = Some (rsF, ds ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\ val_mem SEGS (mrestrict (w_H W1) mem1) AT 8 (A0 + c) /\
cl3_regs_xR regs1 /\ getr regs1 22 = w64 (Z.of_nat w) /\ getr regs1 10 = w64 (Z.of_nat w - 1).
(* cl3_ab at R *)
Definition cl3_ab_xR (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (d' : list byte),
cl3_mem_xR ly1 S1 W2 mem2 md2 kk H1 ds /\
skipn (Z.to_nat (A0 + c)) ob = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ bl3_ok P l = true /\
CheckRep.find_text (firstn (length l - 4) l) (hl_recs H1) = Some i /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w <> None /\
(forall rsF dsR cR, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w = Some (rsF, dsR, cR) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, ds ++ nth i (hl_recs H1) (0, []) :: dsR, c + (Z.of_nat (length l) + 1 + cR))) /\
0 <= c /\ A0 + c + Z.of_nat (length l) + 1 <= O /\
val_mem SEGS (mrestrict (w_H W2) mem2) AT 8 (A0 + c + Z.of_nat (length l) + 1) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (sp0 - 112) 8 (Z.of_nat (length l)) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (sp0 - 112 + 8) 8 (OUT + (A0 + c)) /\
cl3_regs_xR regs2 /\ getr regs2 24 = w64 (Z.of_nat w) /\ getr regs2 22 = w64 (Z.of_nat (length l)) /\
getr regs2 20 = w64 (OUT + (A0 + c)).
(* cl3_mid at R *)
Definition cl3_mid_xR (w : nat) (ds : list (Z * list byte)) (c : Z) (i : nat) (W3 : world SEGS)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist),
cl3_mem_xR ly1 S1 W3 mem3 md3 kk H1 ds /\
(i < length (hl_recs H1))%nat /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + c)) ob) w =
   Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, (ds ++ [nth i (hl_recs H1) (0, [])]) ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\ val_mem SEGS (mrestrict (w_H W3) mem3) AT 8 (A0 + c) /\
cl3_regs_xR regs3 /\ getr regs3 24 = w64 (Z.of_nat w) /\
getr regs3 1 = w64 (BASE + A_cl3_dr) /\ getr regs3 10 = w64 (HA + 80) /\ getr regs3 11 = w64 (Z.of_nat i).
(* cl3_pf_img, restated inside Section loopR *)
Lemma cl3_pf_img_xR : 4096 <= PF /\ PF + PLEN + 8 <= alloc_ceiling.
Proof.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR0 & _).
destruct HPD as [(HPROM & _) | (cid & pos & Hin & Hfr)].
- pose proof (HPROM PF ltac:(lia)) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range PF ltac:(exists sg; split; [exact Hsg | exact Hra])).
  pose proof (HPROM (PF + PLEN + 7) ltac:(lia)) as (sg2 & Hsg2 & _ & Hra2).
  pose proof (pa_img_range (PF + PLEN + 7) ltac:(exists sg2; split; [exact Hsg2 | exact Hra2])). lia.
- assert (Hfb : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid))
  by (eapply (frames_bounds_x SEGS B ARx LAWS); [exact HAR0 | exact Hin]). destruct Hfb as (Hf1 & Hf2 & _).
  pose proof (Hfr PF ltac:(lia)) as Ha. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as Hb.
  unfold in_zr, frame_rng in Ha, Hb. cbn [fst snd] in Ha, Hb. lia.
Qed.
(* cl3_frame_keep at R *)
Lemma cl3_frame_keep_xR : forall cid pos ly2 S2 (W2 : world SEGS) m2 md2 kk2, In (cid, pos) (frames S) ->
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly2 S2 W2 m2 md2 kk2 ->
forall a, (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) mem a.
Proof.
intros cid pos ly2 S2 W2 m2 md2 kk2 Hin HJ a Ha.
pose proof HPRE as (HAR0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid))
  by (eapply (frames_bounds_x SEGS B ARx LAWS); [exact HAR0 | exact Hin]). destruct Hfb as (Hf1 & Hf2 & _).
assert (Hal : frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
  by (eapply frame_al640; [exact HAR0 | exact Hin]). destruct Hal as (Fa64 & Fb64 & Fb).
set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa. pose proof (Z.div_mod fb 64 ltac:(lia)) as Dfb.
pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa8. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as Mfa8.
pose proof (Z.div_mod fb 8 ltac:(lia)) as Dfb8. pose proof (Z.mod_pos_bound fb 8 ltac:(lia)) as Mfb8.
assert (Hwhere : (fa <= a < fa + fb) \/ (SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + fb / 8)).
{ unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. fold fa fb in Ha. unfold shadow_addr in Ha. lia. }
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
apply ajournal_gx_inner_xR in HJ. destruct HJ as (memS & HJi & HgS).
destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KFR & _).
rewrite (KFR cid pos a Hin Ha).
- apply HgS. rewrite unsigned_lit_small by lia. intros Hg. destruct (HG _ Hg) as (Hi & _ & _).
  pose proof (pa_img_range _ Hi) as HIR.
  destruct Hwhere as [Hw | Hw]; [|lia].
  eapply (frm_img_x SEGS B ARx LAWS); [exact HAR0 | exact Hin | exact Hw | exact Hi].
- intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ((b & n) & <- & Hb). cbn [fst snd] in Hra.
  pose proof (HBLK _ Hb) as Hb0.
  destruct (cl3_blk ly S W mem md b n HAR0 Hb0) as (_ & _ & _ & _ & _ & Bc & Bc2 & _ & Bapp & _).
  destruct Hwhere as [Hw | Hw].
  + assert (Hd : zdisjoint (b, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid))
      by (eapply (sep_block_frame_x SEGS B ARx LAWS); [exact HAR0 | exact Hb0 | exact Hin]).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold fa fb in Hd. lia.
  + unfold in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg, YG0f.ASAN_CEIL in Bapp.
    pose proof (Z.div_mod (fa + fb) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fa + fb) 8 ltac:(lia)). lia.
Qed.
(* cl3_pf_at at R *)
Lemma cl3_pf_at_xR : forall ly1 S1 (W1 : world SEGS) mem1 md1 kk H1 ds (W2 : world SEGS) m2 ly2 S2 md2 kk2,
cl3_mem_xR ly1 S1 W1 mem1 md1 kk H1 ds ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) mem1 a) ->
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly2 S2 W2 m2 md2 kk2 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W2) m2 (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) /\
aview SEGS (w_H W2) m2 (PF + PLEN) = Some 0 /\
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W2) m2 a <> None) /\
range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF PF (PLEN + 1) /\
(0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W2) m2) PF (PLEN + 1)).
Proof.
intros ly1 S1 W1 mem1 md1 kk H1 ds W2 m2 ly2 S2 md2 kk2
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROM & _ & _) KL HJ2.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAR0 & _).
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (KP : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) mem a).
{ destruct HPD as [(HPROM & _) | (cid & pos & Hin & Hfr)].
  - intros a Ha. pose proof (HPROM a Ha) as Hr. pose proof Hr as (sg & Hsg & _ & Hra).
    pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
    rewrite KL by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr).
  - intros a Ha. apply (cl3_frame_keep_xR cid pos _ _ _ _ _ _ Hin HJ2). left. exact (Hfr a Ha). }
assert (HSH : range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF PF (PLEN + 1) /\
  (0 < PLEN + 1 -> shadow_hull_vis (aview SEGS (w_H W2) m2) PF (PLEN + 1))).
{ destruct HPD as [(_ & HASH) | (cid & pos & Hin & Hfr)].
  - apply (HASH ly2 S2 [] W2 m2 md2). eapply ajournal_gx_AR_xR. exact HJ2.
  - assert (Hal : frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
  by (eapply frame_al640; [exact HAR0 | exact Hin]). destruct Hal as (Fa64 & Fb64 & Fb).
    pose proof (Hfr PF ltac:(lia)) as HaP. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as HbP.
    unfold in_zr, frame_rng in HaP, HbP. cbn [fst snd] in HaP, HbP.
    set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa. pose proof (Z.div_mod fb 64 ltac:(lia)) as Dfb.
    pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa8. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as Mfa8.
    pose proof (Z.div_mod fb 8 ltac:(lia)) as Dfb8. pose proof (Z.mod_pos_bound fb 8 ltac:(lia)) as Mfb8.
    split.
    + intros x Hx. destruct (HPRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite (cl3_frame_keep_xR cid pos _ _ _ _ _ _ Hin HJ2); [exact Hs|]. right.
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold fa fb.
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
    + intros _ s Hs. rewrite (cl3_frame_keep_xR cid pos _ _ _ _ _ _ Hin HJ2); [exact (HPSV s Hs)|]. right.
      unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fb. unfold shadow_addr in Hs.
      replace (PF + (PLEN + 1) - 1) with (PF + PLEN) in Hs by lia.
      pose proof (Z.div_mod PF 8 ltac:(lia)). pose proof (Z.mod_pos_bound PF 8 ltac:(lia)).
      pose proof (Z.div_mod (PF + PLEN) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + PF / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + PF / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (PF + PLEN) / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (PF + PLEN) / 8) 8 ltac:(lia)).
      lia. }
destruct HSH as [HRA HHV].
split; [intros i Hi; rewrite KP by lia; exact (HPB i Hi)|].
split; [rewrite KP by lia; exact HPN|].
split; [intros a Ha; rewrite KP by lia; exact (HPV a Ha)|].
split; [exact HRA | exact HHV].
Qed.

(* cl3_mem_step at R *)
Lemma cl3_mem_step_xR : forall ly1 S1 (W1 W2 : world SEGS) mem1 mem2 md1 md2 kk kk2 H1 ds,
cl3_mem_xR ly1 S1 W1 mem1 md1 kk H1 ds ->
AJ0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk2 ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
(forall a, apresent (w_H W1) mem1 a -> apresent (w_H W2) mem2 a) ->
cl3_mem_xR ly1 S1 W2 mem2 md2 kk2 H1 ds.
Proof.
intros ly1 S1 W1 W2 mem1 mem2 md1 md2 kk kk2 H1 ds
  (HJ & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK & HROM & HSAV &
   HERR & HRMk & HCNk)
  HJ2 Klow Kstk Kpres.
pose proof asan_consts as (C1 & _).
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ) as HAR1.
split; [exact HJ2|].
split.
{ apply (cl3_src_kept_xR ly1 S1 W1 W2 mem1 mem2 md1 HA (CheckRep.set_held h H1) alloc_ceiling HAR1 HSRC);
  [lia | unfold ASRC in HAhi; lia | lia | exact Klow | exact Kpres]. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MG]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_gone ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MNO]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_nout ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ apply (cl3_vm_keep W1 W2 mem1 mem2); [|exact MOUT]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  destruct (cl3_ro _ _ x cl3_ro_out ltac:(lia)) as (_ & _ & _ & Hl). apply Klow. exact Hl. }
split.
{ intros k Hk. destruct HOBK as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
  destruct (cl3_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (_ & H4096 & _ & Hle & _ & Hc & _).
  rewrite Klow by lia. exact (HOBt k Hk). }
split; [exact HOBK|]. split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite Klow by lia. exact (HROM a Hr). }
split; [exact (cl3_saved_kept W1 W2 mem1 mem2 sp0 regs0 Kstk HSAV)|].
split; [intros jj Hjj; pose proof (pal_env B TL) as (_ & EIMG & _); pose proof (pa_img_range _ (EIMG (as_errno B + jj) ltac:(lia)));
  rewrite Klow by lia; exact (HERR jj Hjj)|].
exact (conj HRMk HCNk).
Qed.
(* cl3_lit_bytes, restated inside Section loopR *)
Lemma cl3_lit_bytes_xR : forall k, 0 <= k < 4 ->
aview SEGS (w_H W) mem (LIT + k) = Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0))).
Proof.
intros k Hk. assert (Hk' : (Z.to_nat k < length (bzs END5))%nat) by (cbn; lia).
pose proof (garr8_mbyte SEGS (arm W mem) LIT _ (Z.to_nat k) HLG Hk') as Hm.
unfold aview. replace (LIT + k) with (LIT + Z.of_nat (Z.to_nat k)) by lia. unfold arm in Hm. rewrite Hm.
cbn [option_map]. f_equal.
assert (Hc : (Z.to_nat k = 0 \/ Z.to_nat k = 1 \/ Z.to_nat k = 2 \/ Z.to_nat k = 3)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.
(* cl3_lit_img, restated inside Section loopR *)
Lemma cl3_lit_img_xR : 0x10000 <= LIT /\ LIT + 5 <= 0x5fc000.
Proof.
pose proof (HEND5R LIT ltac:(lia)) as (sg & Hsg & _ & Hra).
pose proof (pa_img_range LIT ltac:(exists sg; split; [exact Hsg | exact Hra])).
pose proof (HEND5R (LIT + 4) ltac:(lia)) as (sg2 & Hsg2 & _ & Hra2).
pose proof (pa_img_range (LIT + 4) ltac:(exists sg2; split; [exact Hsg2 | exact Hra2])). lia.
Qed.
(* Section loop's tactics cl3_nowr / cl3_awr *)
Ltac cl3_nowr :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg; lia|]);
destruct Hin.
Ltac cl3_awr :=
lazymatch goal with |- awr_ok_x _ ?l _ _ _ _ _ _ _ _ _ _ => let l' := eval vm_compute in l in change l with l' end;
repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|]);
apply awr_ok_x_nil.

(* cl3_A1 at R *)
Lemma cl3_A1_xR : forall w ds c W1 regs1 mem1 md1, cl3_inv_xR (Datatypes.S w) ds c W1 regs1 mem1 md1 ->
(forall l i W2 regs2 mem2 md2, cl3_ab_xR w ds c l i W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cl3_ab)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c W1 regs1 mem1 md1 HI HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & kk & H1 & HM & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R22 & R10).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
assert (Hex : exists rsF dsF cF,
  CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) = Some (rsF, dsF, cF)).
{ destruct (CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w)) as [[[x y] z]|];
  [exists x, y, z; reflexivity | exfalso; exact (HRUN eq_refl)]. }
destruct Hex as (rsF & dsF & cF & ER).
destruct (bl3_ends_S P _ _ w rsF dsF cF ER) as (l & d' & i & dsR & cR & Ed & Hnz & Hok & Hft & HrR & EdsF & EcF).
destruct (bl3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold bl3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply bl3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (HAl : A0 + c + Z.of_nat (length l) + 1 <= O) by lia.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (cl3_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & _ & Ole & _ & Oceil & _ & Ooff & Oapp & Opres).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) <= 2 ^ 26).
{ pose proof (bl3_ends_len P _ _ _ (ltac:(rewrite ER; discriminate) : CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) <> None)) as Hle.
  unfold hl_n in Hn26. lia. }
destruct (cl3_state W1 regs1 mem1 (sp0 - 112) (Z.of_nat (Datatypes.S w)) (OUT + (A0 + c)) (Z.of_nat (length l))
  R2 R21 R23 R22 R10 HSPb HSPa Hw1 HlnR Hlen32) as [HS SHOK].
remember (Eimg (Ereg regs1 (cl3_extra (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ0 SHOK Bspan AF_fr_next_line.
{ cbn [ss_mem ss_cl3]. apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cl3_extra (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = w64 PF) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 LIT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = w64 (Z.of_nat (Datatypes.S w))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E10 : ew E 10 = w64 (Z.of_nat (Datatypes.S w) - 1)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (OUT + (A0 + c))) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length l))) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ; rewrite Q2; exact Usp).
pose proof cl3_pf_img_xR as HPimg.
assert (MQ0 : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x).
{ intros x. apply HFr. intros (rg & Hin & _). destruct Hin. }
destruct (cl3_eqv_view W1 mem1 (ms_mem ms) MQ0) as (AV0 & AP0).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HAR1m : AR0 ly1 S1 W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREn : AFP0 NL_STK ly1 S1 W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms) mdc kk
    (ms_regs ms) NL_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold NL_STK, NL_FRAME, ESTACK. lia.
  - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia. lia. }
assert (HO0 : 0 < O) by lia.
destruct (Z.mod_divide (sp0 - 112) 16 ltac:(lia)) as [Hd16 _]. destruct (Hd16 HSPa) as [q16 Hq16]. clear Hd16.
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R). apply (NL W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc [] (XO + 112) AT (sp0 - 112 + 8) (sp0 - 112)
    (A0 + c) O OUT ob HPREn).
  - lia.
  - rewrite Zplus_mod, HX16. reflexivity.
  - rewrite Usp1, Etop. lia.
  - rewrite Usp1. intros a Ha. apply HPRi. rewrite WS. lia.
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11, Usp. reflexivity.
  - rewrite Q12, E2. reflexivity.
  - exact HAT8.
  - replace (sp0 - 112 + 8) with ((2 * q16 + 1) * 8) by lia. apply Z_mod_mult.
  - replace (sp0 - 112) with ((2 * q16) * 8) by lia. apply Z_mod_mult.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - lia.
  - lia.
  - lia.
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_ra_stack ly1 S1 W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MAT].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MNO].
  - apply (cl3_vm_keep W1 W1 mem1 (ms_mem ms)); [intros x _; apply AV0 | exact MOUT].
  - exact HOlen.
  - intros k Hk. rewrite AV0. exact (HOBt k Hk).
  - lia.
  - intros _. split; [lia|]. split; [unfold amem_range in HOM; lia|]. split; [exact (HO32 HO0)|].
    intros a Ha. rewrite Usp1. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - intros _. split; [rewrite Ed; apply in_or_app; right; left; reflexivity|]. split; [exact HOM|].
    split; [apply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia]|].
    split; [apply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]|].
    intros a Hr. rewrite AV0. exact (HROM a Hr). }
cbv beta. intros W2 c2 HR2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
subst W2.
destruct HARM as [(HAeq & _) | (ln & HAlt & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
assert (Hln : ln = l).
{ destruct Hfl as (rest & Hsk & Hnz'). rewrite Ed in Hsk. destruct (bl3_nul_unique l ln d' rest Hsk Hnz Hnz') as [-> _]. reflexivity. }
subst ln.
rewrite Usp1 in HJn, HFRn.
assert (HJc' : AJ0 G (XO + 112) (nl_cells AT (sp0 - 112 + 8) (sp0 - 112)) NL_STK (sp0 - 112) []
  ly1 S1 W1 (ms_mem ms) mdc [] ly1 S1 W1 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha) | exact HJn]. }
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W1 (ms_mem ms) mdc kk NL_STK (sp0 - 112) (XO + 112) (nl_cells AT (sp0 - 112 + 8) (sp0 - 112)) [] []
  ly1 S1 W1 mem2 md2 0 HJ0 (cl3_jR HJc')
  ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
match type of HJ2 with ?t -> _ => assert (HOc : t) end.
{ intros a (rg & Hin & Hrg). cbn [nl_cells In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg.
  - right. exists (AT, AT + 8). split; [left; reflexivity | cbn; lia].
  - left. rewrite WS. lia.
  - left. rewrite WS. lia. }
specialize (HJ2 HOc HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))). clear HOc.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
pose proof HJn as (_ & _ & _ & HXOn).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F38 : ew Ea 38 = w64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 112) by (rewrite OLDa by lia; exact Usp).
apply (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 2%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0))])) in HS; [| reflexivity | | ].
2: { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
  cbn [base_val]. rewrite UspA. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 112) 0 8 (SOff 33 0) (Z.of_nat (length l)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vlen2.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 112) 8 8 (SOff 32 0) (OUT + (A0 + c)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vln2]. }
2: { cbn [all_disjoint ss_mem]. exact I. }
assert (HAR2 : AR0 ly1 S1 W1 mem2 md2) by exact (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem2 md2 kk HJ2).
assert (SHOK2 : sh_ok SEGS cl3_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
rewrite Q1.
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_tok_xR RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BRR HS SHOK2 Bspan.
{ (* 0x85994 beqz a0: next_line returned 1, it found the line *)
  exfalso. rewrite branch_eq_U, (U_atom Ea 38 1 F38), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_tok_xR RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
assert (F32 : ew Ea 32 = Z_to_bv 64 (OUT + (A0 + c))) by (rewrite OLDa by lia; exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 (Z.of_nat (length l))) by (rewrite OLDa by lia; exact E33).
assert (U32 : U Ea (SOff 32 0) = OUT + (A0 + c)) by (apply U_atom; [exact F32 | lia]).
assert (U33 : U Ea (SOff 33 0) = Z.of_nat (length l)) by (apply U_atom; [exact F33 | lia]).
assert (Uadd : U Ea (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = OUT + (A0 + c) + Z.of_nat (length l))
  by (apply trap_U_add; [exact U32 | exact U33 | lia]).
psrr_branch_tok RUNx BRR HS SHOK2 Bspan.
{ (* 0x859a8 bltu a0,s4: the UBSan pointer-overflow trap on line + len, never taken *)
  rewrite (trap_ptr_bltu Ea (SOff 32 0) (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) _ _ U32 Uadd ltac:(lia)) in Hc.
  discriminate Hc. }
clear Hc.
paj_run_tok_xR RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W1 mem2 (ms_mem ms2) MQ1) as (AV1 & AP1).
assert (KL1 : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite AV1, HFRn; [apply AV0 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
  intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (ROMW : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KL1 by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W1) (ms_mem ms2) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KL1 by lia. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
assert (HLITr : forall k, 0 <= k < 4 -> aview SEGS (w_H W1) (ms_mem ms2) (LIT + k) =
  Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0)))).
{ intros k Hk. rewrite ROMW by (apply HEND5R; lia). exact (cl3_lit_bytes_xR k Hk). }
pose proof cl3_lit_img_xR as HLR.
set (xb := OUT + (A0 + c) + Z.of_nat (length l) - 4).
assert (R10b : getr (ms_regs ms2) 10 = w64 xb).
{ rewrite T10, F32, F33. rewrite unsigned_lit_small by lia. rewrite YI08.alu64_add_lit. unfold w64, xb. f_equal. lia. }
assert (R11b : getr (ms_regs ms2) 11 = w64 LIT) by (rewrite T11, (OLDa 19%nat) by lia; exact E19).
assert (Usp2 : spZ (ms_regs ms2) = sp0 - 112) by (unfold spZ; rewrite T2; exact UspA).
assert (HAR3 : AR0 ly1 S1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy md2) mat2 md2))
  by exact (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 _ _ kk HJ2).
eapply (SRrG_bind SEGS R R_trans).
{ apply (aj_bcmp_gx_at0R (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CSHE_STK_B sp0 FPc
    ly S W mem md [] ly1 S1 _ kk xb LIT 4 (-112) (Z_to_bv 64 (BASE + 13956)) HG HX16 HJ2 R10b R11b T12).
  - lia.
  - unfold xb. lia.
  - unfold xb. lia.
  - lia.
  - lia.
  - rewrite Usp2. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite T3, (OLDa 3%nat), E3 by lia. exact Hgp0.
  - rewrite T4, (OLDa 4%nat), E4 by lia. exact Htp0.
  - exact T1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|rewrite Usp2; unfold ESTACK; unfold xb in Ha; lia].
    replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE by (unfold xb in Ha; lia). discriminate.
  - intros a Ha. split; [|rewrite Usp2; unfold ESTACK; lia].
    replace a with (LIT + (a - LIT)) by lia. rewrite HLITr by lia. discriminate.
  - intros a Ha. unfold xb in Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range in HOM |- *. unfold xb. lia.
  - unfold amem_range, kLowMemEnd. lia.
  - eapply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms2) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia].
  - intros _. eapply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms2) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia | lia].
  - exact (proj1 (HEND5S _ _ _ _ _ _ HAR3)).
  - exact (proj2 (HEND5S _ _ _ _ _ _ HAR3)). }
cbv beta. intros W3 c3 HR3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros k Hk. unfold xb. replace (OUT + (A0 + c) + Z.of_nat (length l) - 4 + k) with
    (OUT + (A0 + c) + (Z.of_nat (length l) - 4 + k)) by lia.
  rewrite HLINE by lia. rewrite HLITr by lia. do 2 f_equal. rewrite <- Hend, bl3_nth_skipn. f_equal. lia. }
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 50)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F54 : ew Eb 54 = w64 0) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv; exact Hv0).
clear HEb.
assert (SHOK3 : sh_ok SEGS cl3_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
assert (HAR4 : AR0 ly1 S1 W1 mem3 md3) by exact (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W1 mem3 md3 kk HJ3).
paj_run_tok_xR RUNx HS HJ3 SHOK3 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BRR HS SHOK3 Bspan.
{ (* 0x859c8 bnez a0: bcmp found the line's last four bytes equal to " end" *)
  exfalso. rewrite branch_ne_U, (U_atom Eb 54 0 F54), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_xR RUNTOx HS HJ3 SHOK3 Bspan 13960. { cl3_awr. }
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdF := mdq) in * end.
assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W1 mem3 (ms_mem ms4) MQ2) as (AV2 & AP2).
assert (OLDba : forall m, (m < 34)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (22%bv : bv 5) N22.
prreg HS (20%bv : bv 5) N20.
assert (KS : forall yy, sp0 - 112 <= yy < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms4) yy = aview SEGS (w_H W1) mem2 yy).
{ intros yy Hyy. rewrite AV2, Hfr3 by (unfold ESTACK; lia). apply AV1. }
assert (KL : forall yy, 4096 <= yy < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) yy = aview SEGS (w_H W1) mem1 yy).
{ intros yy Hyy. rewrite AV2, Hfr3 by (unfold ESTACK in *; pose proof WS; lia). apply KL1. exact Hyy. }
replace (BASE + 13960) with (BASE + A_cl3_ab) by (unfold A_cl3_ab, AF_fr_check_shape_ends; lia).
apply (HKont l i W1 (ms_regs ms4) (ms_mem ms4) mdF).
exists ly1, S1, kk, H1, d'.
split.
{ apply (cl3_mem_step_xR ly1 S1 W1 W1 mem1 (ms_mem ms4) md1 mdF kk kk H1 ds HM HJ3 KL).
  - intros yy Hyy. rewrite KS by lia. rewrite HXOn; [apply AV0 | lia |].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros yy Hp. apply AP2. apply Hpres3. apply AP1. apply HPn. apply AP0. exact Hp. }
split; [exact Ed|]. split; [exact Hnz|]. split; [exact Hok|]. split; [exact Hft|].
split; [rewrite HrR; discriminate|].
split.
{ intros rsF' dsR' cR' Hx. apply HREL. rewrite Ed. exact (bl3_ends_step P (hl_recs H1) l d' i w rsF' dsR' cR' Hnz Hok Hft Hx). }
split; [exact Hc0|]. split; [exact HAl|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; lia | exact Vat2]|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; cbn in Hyy; lia | exact Vlen2]|].
split; [apply (cl3_vm_keep W1 W1 mem2 (ms_mem ms4)); [intros yy Hyy; apply KS; cbn in Hyy; lia | exact Vln2]|].
split.
{ unfold cl3_regs_xR.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N27, OLDba by lia; exact E27|].
  split; [rewrite N8, OLDba by lia; exact E8|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N24, OLDba, E10 by lia; unfold w64; f_equal; lia|].
split; [rewrite N22, OLDba, E33 by lia; reflexivity|].
rewrite N20, OLDba, E32 by lia. reflexivity.
Qed.

(* cl3_A2 at R *)
Lemma cl3_A2_xR : forall w ds c l i W2 regs2 mem2 md2, cl3_ab_xR w ds c l i W2 regs2 mem2 md2 ->
(forall W3 regs3 mem3 md3, cl3_mid_xR w ds (c + Z.of_nat (length l) + 1) i W3 regs3 mem3 md3 ->
  SRrG SEGS R W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem3 (seg_rom SEGS)) md3) Post) ->
SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cl3_ab)) mem2 (seg_rom SEGS)) md2) Post.
Proof.
intros w ds c l i W2 regs2 mem2 md2 HAB HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAB as (ly1 & S1 & kk & H1 & d' & HM & Ed & Hnz & Hok & Hft & HRUN & HREL & Hc0 & HAl & MAT & M0 & M8 &
  HREGS & R24 & R22 & R20).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
destruct (bl3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold bl3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply bl3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 mem2 md2 kk HJ0) as HAR1.
destruct (cl3_blk ly1 S1 W2 mem2 md2 OUT CO HAR1 HOin) as (O16 & O4096 & _ & Ole & _ & Oceil & _ & Ooff & Oapp & Opres).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (bl3_ends_len P _ _ d'); exact HRUN).
rewrite (bl3_drop_len _ _ Hi) in Hw26.
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 0 <= Z.of_nat w <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cl3b_state W2 regs2 mem2 (sp0 - 112) (Z.of_nat w) (OUT + (A0 + c)) (Z.of_nat (length l))
  R2 R21 R23 R24 R22 R20 HSPb HSPa Hw1 HlnR Hlen32 M0 M8) as [HS SHOK].
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs2 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = w64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = w64 PF) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 AT) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 LIT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (OUT + (A0 + c))) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 (Z.of_nat (length l))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (Z.of_nat w)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
pose proof cl3_pf_img_xR as HPimg.
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ0 SHOK Bspan AF_fr_list_find. { cl3_awr. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ; rewrite Q2; exact Usp).
assert (MQ0 : forall x, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
{ intros x. apply HFr. cl3_nowr. }
destruct (cl3_eqv_view W2 mem2 (ms_mem ms) MQ0) as (AV0 & AP0).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HSRCr : asrc_at B ly1 S1 W2 (ms_mem ms) HA (CheckRep.set_held h H1)).
{ apply (cl3_src_kept_xR ly1 S1 W2 W2 mem2 (ms_mem ms) md2 HA _ alloc_ceiling HAR1 HSRC);
  [lia | unfold ASRC in HAhi; lia | lia | intros a _; apply AV0 | exact AP0]. }
pose proof HSRCr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAHr & _).
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 _ _ kk HJ0)
  as (memS & HJi & HgS).
assert (HAR1m : AR0 ly1 S1 W2 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREf : AFP0 LFIND_STK ly1 S1 W2 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W2 (ms_mem ms) mdc kk
    (ms_regs ms) LFIND_STK (- 112 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite WS. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia. lia. }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite AV0. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
set (sb := firstn (length l - 4) l).
assert (Hsb : length sb = (length l - 4)%nat) by (unfold sb; rewrite length_firstn; lia).
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 [] W2 (ms_mem ms) mdc (HA + 64) 32 HAR1m Hzs) as HRA64.
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R). apply (LFIND W2 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdc [] (HA + 80) H1 true (OUT + (A0 + c)) sb HPREf).
  - rewrite Q10, E9. reflexivity.
  - rewrite Q11, E20. reflexivity.
  - rewrite Q12, E22, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hsb. lia.
  - exact HAHr.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold kLowMemEnd. unfold ASRC in HAhi. lia.
  - eapply range_addressable_sub; [exact HRA64 | lia | lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. rewrite WS in Hslo. unfold ASRC in HAhi. lia.
  - lia.
  - rewrite Hsb. lia.
  - rewrite Hsb. lia.
  - intros k Hk. rewrite Hsb in Hk. rewrite HLINE by lia. do 2 f_equal. unfold sb. rewrite nth_firstn.
    destruct (Z.to_nat k <? length l - 4)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. rewrite WS in Hslo. lia.
  - rewrite Hsb. unfold amem_range in HOM |- *. lia.
  - rewrite Hsb. eapply (range_addressable_of_block0 ly1 S1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia].
  - rewrite Hsb. intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]. }
cbv beta. intros W3 c3 HR3 (-> & regs3 & mem3 & md3 & -> & HJf & HPf & HPRf & HFRf & HRES).
assert (HRESi : getr regs3 10 = w64 (Z.of_nat i)).
{ destruct HRES as [(j & (Hj1 & Hj2 & Hj3) & Hr10) | (Hnf & _)].
  - rewrite Hr10. do 2 f_equal. apply (bl3_first_unique (hl_recs H1) sb j i Hj2 Hj3 Hti Hfirst).
  - exfalso. exact (Hnf i Hi Hti). }
rewrite Usp1 in HJf, HFRf.
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W2 (ms_mem ms) mdc kk LFIND_STK (sp0 - 112) 0 [] [] [] ly1 S1 W2 mem3 md3 0 HJ0 (cl3_jR HJf)
  ltac:(rewrite WS; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 32%nat regs3 (mrestrict (w_H W2) mem3) HPf [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 32)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F36 : ew Ea 36 = w64 (Z.of_nat i)) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact HRESi).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 112) by (rewrite OLDa by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS cl3_Bx [] Ea (mrestrict (w_H W2) mem3)) by constructor.
rewrite Q1.
paj_run_tok_xR RUNx HS HJ2 SHOK2 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BRR HS SHOK2 Bspan.
{ (* 0x859dc bltz a0: list_find found the record, i >= 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit_small; lia).
  cbn [sv_denot] in Hc. rewrite F36, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. unfold w64 in Hc.
  rewrite bv_signed_small in Hc by (rewrite Hu; lia). rewrite Hu in Hc. change (bv_signed (Z_to_bv 64 0)) with 0 in Hc. lia. }
clear Hc.
paj_run_to_tok_xR RUNTOx HS HJ2 SHOK2 Bspan AF_fr_has_prefix. { cl3_awr. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (MQ1 : forall x, mrestrict (w_H W2) (ms_mem ms1) x = mrestrict (w_H W2) mem3 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W2 mem3 (ms_mem ms1) MQ1) as (AV1 & AP1).
assert (KL1 : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV1, HFRf by (try lia; rewrite WS in Hslo; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia). apply AV0. }
assert (KS1 : forall a, sp0 - 112 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV1, HFRf by (try lia; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia). apply AV0. }
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KL1 by lia. rewrite (HROM a Hr). symmetry. exact (HROM0 a Hr). }
assert (HLINE2 : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KL1 by lia. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia.
  rewrite (HOBt (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (bl3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 112) by (unfold spZ; rewrite P2; exact UspA).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdh := mdq) in * end.
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W2 _ _ kk HJ2)
  as (memS2 & HJi2 & HgS2).
assert (HAR3 : AR0 ly1 S1 W2 (ms_mem ms1) mdh) by exact (proj1 HJi2).
assert (HPREh : AFP0 HP_STK ly1 S1 W2 (ms_regs ms1) (ms_mem ms1) mdh []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS2 md [] ly1 S1 W2 (ms_mem ms1) mdh kk
    (ms_regs ms1) HP_STK (- 112 - XO) [] HJi2).
  - rewrite Usp2. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - rewrite WS. unfold HP_STK, ESTACK. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
  - rewrite P3, OLDa, E3 by lia. exact Hgp0.
  - rewrite P4, OLDa, E4 by lia. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite P8, OLDa, E8 by lia. rewrite unsigned_lit_small by lia. lia. }
destruct (cl3_pf_at_xR ly1 S1 W2 mem2 md2 kk H1 ds W2 (ms_mem ms1) ly1 S1 mdh kk HM KL1 HJ2) as (PB1 & PN1 & PV1 & HRAP & HHVP).
assert (SHVSUB : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n').
{ intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
  assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R). apply (HP W2 ly1 S1 [] (ms_regs ms1) (ms_mem ms1) mdh [] (OUT + (A0 + c)) (Z.of_nat (length l)) PF PLEN HPREh).
  - rewrite P10, OLDa, E20 by lia. reflexivity.
  - rewrite P11, OLDa, E22 by lia. reflexivity.
  - rewrite P12, OLDa, E8 by lia. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * exact (PB1 k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. exact PN1.
  - intros a Ha. apply PV1. lia.
  - unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact (HHVP ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). apply PV1. lia.
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE2 by lia. discriminate.
    + unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
    + unfold amem_range in HOM |- *. lia.
    + eapply (range_addressable_of_block0 ly1 S1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block0 ly1 S1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (SHVSUB _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) (HHVP ltac:(lia))). }
cbv beta. intros W4 c4 HR4 (regs4 & mem4 & md4 & -> & HJh & HPh & HPRh & HFRh & HRESh).
assert (Hpref : PLEN <= Z.of_nat (length l) /\ hp_prefix_of W2 (ms_mem ms1) (OUT + (A0 + c)) PF PLEN).
{ unfold CheckRep.prefixb in Hpre. apply andb_prop in Hpre as [Hp1 Hp2]. apply Nat.leb_le in Hp1. apply bl3_leqb in Hp2.
  split; [lia|]. intros k Hk. rewrite HLINE2 by lia. rewrite (PB1 k Hk).
  do 2 f_equal. rewrite <- Hp2. rewrite nth_firstn. destruct (Z.to_nat k <? length P)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia]. }
assert (Hr10h : getr regs4 10 = w64 1).
{ destruct HRESh as [(_ & _ & Hr) | (Hnp & _)]; [exact Hr | exfalso; exact (Hnp (proj1 Hpref) (proj2 Hpref))]. }
rewrite Usp2 in HJh, HFRh.
assert (HJc' : AJ0 G 0 [] HP_STK (sp0 - 112) [] ly1 S1 W2 (ms_mem ms1) mdh [] ly1 S1 W4 mem4 md4 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|]. apply ajournal_gx_nil_x. exact HJh. }
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md []
  ly1 S1 W2 (ms_mem ms1) mdh kk HP_STK (sp0 - 112) 0 [] [] [] ly1 S1 W4 mem4 md4 0 HJ2 (cl3_jR HJc')
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_r in HJ3.
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HPh [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 48 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 48)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F52 : ew Eb 52 = w64 1) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hr10h).
clear HEb.
assert (OLDba : forall m, (m < 32)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (SHOK3 : sh_ok SEGS cl3_Bx [] Eb (mrestrict (w_H W4) mem4)) by constructor.
rewrite P1.
paj_run_tok_xR RUNx HS HJ3 SHOK3 Bspan. { cl3_awr. }
psrr_branch_tok RUNx BRR HS SHOK3 Bspan.
{ (* 0x859f4 beqz a0: has_prefix returned 1 *)
  exfalso. rewrite branch_eq_U, (U_atom Eb 52 1 F52), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_xR RUNTOx HS HJ3 SHOK3 Bspan AF_fr_list_drop. { cl3_awr. }
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdD := mdq) in * end.
assert (MQ3 : forall x, mrestrict (w_H W4) (ms_mem ms3) x = mrestrict (w_H W4) mem4 x).
{ intros x.
  repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
    rewrite (Hf x) by cl3_nowr end.
  reflexivity. }
destruct (cl3_eqv_view W4 mem4 (ms_mem ms3) MQ3) as (AV3 & AP3).
prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
prreg HS (27%bv : bv 5) N27. prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18.
prreg HS (19%bv : bv 5) N19. prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
apply (HKont W4 (ms_regs ms3) (ms_mem ms3) mdD).
exists ly1, S1, kk, H1.
split.
{ apply (cl3_mem_step_xR ly1 S1 W2 W4 mem2 (ms_mem ms3) md2 mdD kk kk H1 ds HM HJ3).
  - intros a Ha. rewrite AV3, HFRh by (try lia; rewrite WS in Hslo; unfold HP_STK, ESTACK; lia). apply KL1. exact Ha.
  - intros a Ha. rewrite AV3, HFRh by (try lia; unfold HP_STK, ESTACK; lia). apply KS1. lia.
  - intros a Hp. apply AP3. apply HPRh. apply AP1. apply HPRf. apply AP0. exact Hp. }
split; [exact Hi|].
assert (Esk : skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob = d').
{ replace (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) with (Z.to_nat (A0 + c) + length l + 1)%nat by lia.
  exact (bl3_skip_line ob l d' (Z.to_nat (A0 + c)) Ed). }
rewrite Esk.
split; [exact HRUN|].
split.
{ intros rsF dsF cF Hx. rewrite (HREL rsF dsF cF Hx). rewrite <- app_assoc. cbn [app]. f_equal. f_equal. lia. }
split; [lia|]. split; [lia|].
split.
{ apply (cl3_vm_keep W2 W4 mem2 (ms_mem ms3)).
  - intros yy Hyy. rewrite AV3, HFRh by (try lia; unfold HP_STK, ESTACK; lia). apply KS1. lia.
  - replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + c + Z.of_nat (length l) + 1) by lia. exact MAT. }
split.
{ unfold cl3_regs_xR.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N27, OLDba by lia; exact E27|].
  split; [rewrite N8, OLDba by lia; exact E8|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N24, OLDba by lia; exact E24|].
split; [rewrite N1; unfold w64, A_cl3_dr, AF_fr_check_shape_ends; f_equal; lia|].
split; [rewrite N10, OLDba by lia; exact E9|].
rewrite N11, OLDb by lia. exact F36.
Qed.

(* cl3_set_held2, restated inside Section loopR *)
Lemma cl3_set_held2_xR : forall h0 a b, CheckRep.set_held (CheckRep.set_held h0 a) b = CheckRep.set_held h0 b.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?] a b. reflexivity. Qed.
(* cl3_map_drop, restated inside Section loopR *)
Lemma cl3_map_drop_xR : forall {Y : Type} (f : Z * list byte -> Y) (rs : list (Z * list byte)) i, (i < length rs)%nat ->
Permutation (map f rs) (f (nth i rs (0, [])) :: map f (CheckRep.drop_nth i rs)).
Proof.
intros Y f rs i Hi. destruct (nth_split rs (0, []) Hi) as (A & Bs & Hsp & HlA).
assert (Hd : CheckRep.drop_nth i rs = A ++ Bs) by (rewrite Hsp, <- HlA; apply bl3_drop_split).
rewrite Hd. rewrite Hsp at 1. rewrite !map_app. cbn [map].
apply Permutation_sym, Permutation_middle.
Qed.
(* cl3_list_blks_drop, restated inside Section loopR *)
Lemma cl3_list_blks_drop_xR : forall l i, (i < length (hl_recs l))%nat ->
Permutation (list_blks l) ((fst (nth i (hl_recs l) (0, [])), Z.of_nat (length (snd (nth i (hl_recs l) (0, [])))) + 1) ::
  list_blks (ldrop_list l i)).
Proof.
intros l i Hi. unfold list_blks, ldrop_list. cbn [hl_v hl_cap hl_recs].
change (firstn i (hl_recs l) ++ skipn (Datatypes.S i) (hl_recs l)) with (CheckRep.drop_nth i (hl_recs l)).
eapply Permutation_trans; [apply Permutation_app_head; exact (cl3_map_drop_xR (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ i Hi)|].
apply Permutation_sym, Permutation_middle.
Qed.
(* cl3_blks_fst, restated inside Section loopR *)
Lemma cl3_blks_fst_xR : forall l, map fst (list_blks l) = list_blocks l.
Proof.
intros l. unfold list_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.
(* cl3_perm_drop, restated inside Section loopR *)
Lemma cl3_perm_drop_xR : forall (T0 : Type) (b1 b2 L : list T0) x, Permutation (b1 ++ x :: b2) (x :: L) -> Permutation (b1 ++ b2) L.
Proof. intros T0 b1 b2 L x H. apply (Permutation_cons_inv (a := x)). rewrite Permutation_middle. exact H. Qed.
(* cl3_rec_len, restated inside Section loopR *)
Lemma cl3_rec_len_xR : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
(* cl3_alist_fp_in, restated inside Section loopR *)
Lemma cl3_alist_fp_in_xR : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr ->
LA <= a < LA + 16 \/ exists b, In b (list_blks l) /\ fst b <= a < fst b + snd b.
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & Hcap & Hv & _ & _ & _) rr Hin a Ha.
unfold alist_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Ha; exact Ha|]. right.
apply in_app_or in Hin as [Hin | Hin].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
  exists (hl_v l, AREC * hl_cap l). split; [unfold list_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  destruct Hv as [(Hc0 & _) | (_ & _ & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite (cl3_vec_len l Hj) in Ha. exact Ha.
- apply in_map_iff in Hin as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1).
  split; [unfold list_blks; apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr0|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite cl3_rec_len_xR in Ha. exact Ha.
Qed.
(* cl3_nodup_disj, restated inside Section loopR *)
Lemma cl3_nodup_disj_xR : forall (T0 : Type) (l1 l2 : list T0) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros T0. induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hx|]. cbn [app] in H.
apply List.NoDup_cons_iff in H as [Hn H].
destruct Hx as [<- | Hx]; [apply Hn; apply in_or_app; right; exact Hy | exact (IH l2 x H Hx Hy)].
Qed.
(* cl3_A3 at R *)
Lemma cl3_A3_xR : forall w ds c i W3 regs3 mem3 md3, cl3_mid_xR w ds c i W3 regs3 mem3 md3 ->
(forall ds' W4 regs4 mem4 md4, cl3_inv_xR w ds' c W4 regs4 mem4 md4 ->
  SRrG SEGS R W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + A_csheB_l3)) mem4 (seg_rom SEGS)) md4) Post) ->
SRrG SEGS R W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem3 (seg_rom SEGS)) md3) Post.
Proof.
intros w ds c i W3 regs3 mem3 md3 HMD HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HMD as (ly1 & S1 & kk & H1 & HM & Hi & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R24 & R1 & R10 & R11).
pose proof HM as (HJ0 & HSRC & HV & HC & HND & HINC & HLEN & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK &
  HROM & HSAV & HERR & HRMk & HCNk).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
pose proof (ajournal_gx_AR0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk HJ0) as HAR1.
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (Usp : spZ regs3 = sp0 - 112) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
pose proof cl3_pf_img_xR as HPimg.
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (bl3_ends_len P _ _ _ HRUN)).
rewrite (bl3_drop_len _ _ Hi) in Hw26.
assert (HnH1 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HAH1 & HNDB).
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HAH1, HNDB.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [unfold hl_n in HnleC; lia|].
destruct (cl3_blk ly1 S1 W3 mem3 md3 _ _ HAR1 HvinH) as (V16 & V4096 & _ & _ & _ & Vceil & _ & Voff & _ & Vpres).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
set (r := nth i (hl_recs H1) (0, [])) in *.
assert (Hrin : In r (hl_recs H1)) by (apply nth_In; exact Hi).
rewrite Forall_forall in HFallH. destruct (HFallH r Hrin) as (HinR & HgarR & HlinR & _).
destruct (cl3_blk ly1 S1 W3 mem3 md3 _ _ HAR1 HinR) as (R16 & R4096 & _ & Rle & _ & Rceil & _ & Roff & _ & Rpres).
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CSHE_STK_B sp0 FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk HJ0)
  as (memS & HJi & HgS).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W3 regs3 mem3 md3 []).
{ eapply (afn_pre_at0R (CSHE_STK_B + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W3 mem3 md3 kk regs3
    LDROP_STK (- 112 - XO) [] HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite WS. unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cl3_dr, AF_fr_check_shape_ends; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold A_cl3_dr, AF_fr_check_shape_ends; lia).
    unfold A_cl3_dr, AF_fr_check_shape_ends. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
set (G2 := [(HA + 80, 16)]).
assert (HG2G : forall a, inG G2 a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply HGa; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG2 : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G2 a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
assert (HG2s : forall a, inG G2 a -> VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; unfold ASRC in HAgs; lia | exfalso; exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G2 G HG2G HG) as HG2.
assert (HGRT2 : gx_rt B G2).
{ eapply gx_rt_sub; [|exact HGRR]. intros a Ha. apply (cl3_ro_in (VAL (A_OBJ 19)) 384 a); [cbv [cshe_ro_B]; do 3 right; left; reflexivity | exact (HG2s a Ha)]. }
assert (HROMS2 : forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G2 a).
{ intros a Hr. destruct (ROMNS a Hr) as (He & Hp). split; [exact Hp|]. split; [exact He|].
  intros Hg. destruct (HGS a (HG2s a Hg)) as (_ & Hnr & _). exact (Hnr Hr). }
assert (HMF : mo_free MT <= Z.of_nat (length (hl_recs H1)) * mo_free MT)
  by (pose proof (mo_free_nonneg MT ML); nia).
eapply (SRrG_bind SEGS R R_trans).
{ refine (LDROP_R G2 HG2 HGRT2 HROMS2 W3 ly1 S1 [] regs3 mem3 md3 [] (HA + 80) H1 true i HPREd R10 R11 HAH1 Hi _ _ _ _ _ _ _
    (Z.to_nat (Z.of_nat (length (hl_recs (ldrop_list H1 i))) * mo_free MT_rk) + kr)%nat _ _ _).
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold AREC, hl_n. unfold hl_n in Hn26. lia.
  - destruct Hzs as (zr & Hzr & Hz8 & Hz1 & Hz2). exists zr. split; [exact Hzr|]. split; [exact Hz8|]. split; lia.
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia|].
    rewrite Usp. unfold LDROP_STK, LDROP_FRAME, ASTACK. rewrite WS in Hslo. unfold ASRC in HAhi. lia.
  - intros a Ha. rewrite Usp. rewrite HreqV in Vceil. unfold LDROP_STK, LDROP_FRAME, ASTACK. rewrite WS in Hslo. lia.
  - eapply (mo_ok_le MT ML); [exact HMOK | exact HMF].
  - (* the room round: record i's free is spent from the budget, the rest's stays *)
    rewrite cl3_rk. rewrite cl3_rk in HRMk. change (Z.to_nat (mo_free MT_rk)) with 1%nat.
    refine (RMM_of RP S1 _ _ _ HRMk). cbn [ldrop_list hl_recs].
    change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (bl3_drop_len _ _ Hi). lia.
  - (* list_drop's count premise (ldrop_pk = 0): the invariant's *)
    exact HCNk.
  - exact HROM. }
cbv beta. intros W5 c5 HR5 (ly2 & S2 & hpD & regs5 & mem5 & md5 & -> & HJd & HPd & HPKd & HERRd & HL2 & (b1 & b2 & Eb1 & Eb2) & HMLEd & HRMd).
hp0gR HJd.
assert (HAR2 : AR0 ly2 S2 W5 mem5 md5) by (eapply ajournal_gx_AR_xR; exact HJd).
pose proof HJd as HJd0. apply ajournal_gx_inner_xR in HJd0. destruct HJd0 as (memS2 & HJdi & HgS2).
rewrite Usp in HJdi. destruct HJdi as (_ & HlyD & _ & _ & _ & HfrD & _ & _ & KF & KB & KI & _).
set (FPd := [(hl_v H1, hl_v H1 + AREC * hl_cap H1);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in *.
assert (Hcl : ~ YI16.sink_open_fp FPd) by (apply sink_closed_pos; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia).
assert (HAr : 0x10000 <= HA /\ HA + 96 <= 0x5fc000).
{ pose proof (pa_img_range HA (proj1 (HAimg HA ltac:(unfold ASRC; lia)))).
  pose proof (pa_img_range (HA + 95) (proj1 (HAimg (HA + 95) ltac:(unfold ASRC; lia)))). lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - LDROP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite KF by (rewrite ?Z.add_0_r; lia). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Hi' Ho He Hn. pose proof (pa_img_range a Hi') as Hr.
  rewrite KI; [|exact Hi' | exact Ho | exact He | exact (HPST a Hi') | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. exact Hn. }
assert (Kblk : forall p n i0, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ inFP FPd (p + i0) ->
  0 <= i0 < req_size n -> aview SEGS (w_H W5) mem5 (p + i0) = aview SEGS (w_H W3) mem3 (p + i0)).
{ intros p n i0 Hb1 Hb2 Hn Hi0. destruct (cl3_blk ly1 S1 W3 mem3 md3 p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i0 Hb1 Hb2 Hi0 Hn). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. unfold off_img in Hoff. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W3 mem3) a -> writable_at SEGS (arm W5 mem5) a).
{ intros a Hi' Ho He Hw. apply (cl3_awr_kept_xR W3 W5 mem3 mem5 a); [|exact Hw]. intros Hp. exact (HPKd a Hi' Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W5 mem5) a).
{ intros p n a Hb Ha. destruct (cl3_blk ly2 S2 W5 mem5 md5 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
set (rb := (fst r, Z.of_nat (length (snd r)) + 1)) in *.
assert (Hlive : forall b, In b (ablocks B ly1 S1) -> b <> rb -> In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Eb2. rewrite Eb1 in Hb. apply in_app_or in Hb as [Hb | [<- | Hb]];
  [apply in_or_app; left; exact Hb | exfalso; exact (Hne eq_refl) | apply in_or_app; right; exact Hb]. }
assert (HrbH : In (fst rb) (list_blocks H1)).
{ unfold list_blocks. apply in_or_app. right. change (fst rb) with (fst r). apply (in_map fst). exact Hrin. }
assert (HvH : In (hl_v H1) (list_blocks H1)).
{ unfold list_blocks. destruct (hl_cap H1 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity. }
set (Oth := (hs_partial h, APARTIAL) :: list_blks (hs_pending h) ++ list_blks (hs_expected h)).
assert (HNDl : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1)).
{ apply NoDup_ListNoDup in HNDB. rewrite <- !app_assoc. exact HNDB. }
assert (HOthA : forall b, In b Oth -> ~ In (fst b) (list_blocks H1)).
{ intros b Hb. apply (cl3_nodup_disj_xR _ _ _ (fst b) HNDl).
  unfold Oth in Hb. destruct Hb as [<- | Hb]; [apply in_or_app; right; left; reflexivity|].
  apply in_app_or in Hb as [Hb | Hb].
  - apply in_or_app. left. rewrite <- cl3_blks_fst_xR. apply (in_map fst). exact Hb.
  - apply in_or_app. right. right. rewrite <- cl3_blks_fst_xR. apply (in_map fst). exact Hb. }
assert (HOth1 : forall b, In b Oth -> In b (ablocks B ly1 S1)).
{ intros b Hb. unfold Oth in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (cl3_alist_blks_in _ _ _ _ _ _ _ Hpend b Hb) | exact (cl3_alist_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
assert (HOth2 : forall b, In b Oth -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Hlive b (HOth1 b Hb)). intros E'. apply (HOthA b Hb). rewrite E'. exact HrbH. }
assert (KAb : forall b a, In b (ablocks B ly1 S1) -> In b (ablocks B ly2 S2) ->
  fst b <> hl_v H1 -> fst b <> fst rb -> fst b <= a < fst b + snd b -> abyte_kept W3 mem3 W5 mem5 a).
{ intros (p & n) a Hb1 Hb2 Hnv Hnr Ha. cbn [fst snd] in Hnv, Hnr, Ha.
  destruct (cl3_blk ly1 S1 W3 mem3 md3 p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr' & _).
  replace a with (p + (a - p)) by lia.
  split; [|intros _; apply (Pblk p n); [exact Hb2 | lia]].
  apply (Kblk p n); [exact Hb1 | exact Hb2 | | lia].
  intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
  - pose proof (sep_blocks0 ly1 S1 W3 mem3 md3 _ _ p n HAR1 HvinH Hb1 ltac:(intros E'; injection E' as E1 _; lia)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
  - pose proof (sep_blocks0 ly1 S1 W3 mem3 md3 _ _ p n HAR1 HinR Hb1 ltac:(intros E'; injection E' as E1 _; unfold rb in Hnr; cbn [fst] in Hnr; lia)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KOth : forall b a, In b Oth -> fst b <= a < fst b + snd b -> abyte_kept W3 mem3 W5 mem5 a).
{ intros b a Hb Ha. apply (KAb b a (HOth1 b Hb) (HOth2 b Hb)); [| | exact Ha].
  - intros E'. apply (HOthA b Hb). rewrite E'. exact HvH.
  - intros E'. apply (HOthA b Hb). rewrite E'. exact HrbH. }
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W3 mem3 W5 mem5 a).
{ intros a Ha. destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hi' & Ho & He & _).
  split; [apply Kimg; [exact Hi' | exact Ho | exact He | lia] | apply Pimg; assumption]. }
assert (HrbH0 : In rb (list_blks H0)).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). apply HINC. exact Hrin. }
assert (HvbH0 : In (hl_v H1, AREC * hl_cap H1) (list_blks H0)).
{ unfold list_blks. rewrite HV, HC in *. destruct (hl_cap H0 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|].
  apply in_or_app. left. left. reflexivity. }
assert (HFPd : forall a, inFP FPd a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). left. cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha.
  - split; [|exists (hl_v H1), (AREC * hl_cap H1); split; [exact HvinH | rewrite HreqV; exact Ha]].
    exists (hl_v H1, hl_v H1 + req_size (AREC * hl_cap H1)). split; [|cbn [fst snd]; rewrite HreqV; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v H1, AREC * hl_cap H1)). exact HvbH0.
  - split; [|exists (fst r), (Z.of_nat (length (snd r)) + 1); split; [exact HinR | exact Ha]].
    exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ rb). exact HrbH0. }
pose proof (ajournal_gx_G_mono0R G2 G 0 [] LDROP_STK (spZ regs3) FPd ly1 S1 W3 mem3 md3 [] ly2 S2 W5 mem5 md5 1
  HG2G HJd) as HJd'. rewrite Usp in HJd'.
pose proof (ajournal_gx_sub0R Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W3 mem3 md3 kk
  LDROP_STK (sp0 - 112) 0 [] FPd [] ly2 S2 W5 mem5 md5 1 HJ0 HJd'
  ltac:(rewrite WS; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPd) as HJ2.
cbn [app] in HJ2.
assert (HND2 : NoDup (hs_blocks (CheckRep.set_held (CheckRep.set_held h H1) (ldrop_list H1 i)))).
{ rewrite cl3_set_held2_xR. apply NoDup_ListNoDup. unfold hs_blocks. cbn [CheckRep.set_held hs_pending hs_partial hs_expected hs_held].
  assert (HPb : Permutation (list_blocks H1) (fst rb :: list_blocks (ldrop_list H1 i))).
  { rewrite <- !cl3_blks_fst_xR.
    change (fst rb :: map fst (list_blks (ldrop_list H1 i))) with (map fst (rb :: list_blks (ldrop_list H1 i))).
    apply Permutation_map. exact (cl3_list_blks_drop_xR H1 i Hi). }
  assert (HP2 : Permutation ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H1)
    (fst rb :: (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks (ldrop_list H1 i))).
  { eapply Permutation_trans; [apply Permutation_app_head; exact HPb|]. apply Permutation_sym, Permutation_middle. }
  pose proof (Permutation_NoDup HP2 HNDl) as Hx. apply List.NoDup_cons_iff in Hx as [_ Hx].
  rewrite <- !app_assoc in Hx. exact Hx. }
assert (HSRC2 : asrc_at B ly2 S2 W5 mem5 HA (CheckRep.set_held h (ldrop_list H1 i))).
{ rewrite <- (cl3_set_held2_xR h H1 (ldrop_list H1 i)).
  apply (cl3_src_swap ly1 S1 W3 mem3 ly2 S2 W5 mem5 HA (CheckRep.set_held h H1) (ldrop_list H1 i) HSRC KHd); [| | exact HL2 | exact HND2].
  - intros rr Hrr a Ha. cbn [CheckRep.set_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KOth (hs_partial h, APARTIAL)); [left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (cl3_alist_fp_in_xR _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KOth b); [unfold Oth; right; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (cl3_alist_fp_in_xR _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KOth b); [unfold Oth; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. apply HOth2. exact Hb. }
assert (HOUTn : ob <> [] -> OUT <> hl_v H1 /\ OUT <> fst rb).
{ intros Hne. pose proof (HOH Hne) as Hn. split.
  - intros E'. apply Hn. rewrite E'. unfold list_blocks. rewrite HV, HC in *.
    destruct (hl_cap H0 =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity.
  - intros E'. apply Hn. rewrite E'. unfold list_blocks. apply in_or_app. right. change (fst rb) with (fst r).
    apply (in_map fst). apply HINC. exact Hrin. }
assert (HM2 : cl3_mem_xR ly2 S2 W5 mem5 md5 (kk + 1) (ldrop_list H1 i) (ds ++ [r])).
{ split; [exact HJ2|].
  split; [exact HSRC2|].
  split; [exact HV|]. split; [exact HC|].
  split.
  { unfold CheckRep.texts in HND |- *. cbn [ldrop_list hl_recs].
    change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    exact (bl3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND). }
  split; [intros x Hx; apply HINC; exact (bl3_incl_drop (hl_recs H1) i x Hx)|].
  split; [cbn [ldrop_list hl_recs]; change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1));
    rewrite (bl3_drop_len _ _ Hi), length_app; cbn [length]; lia|].
  assert (KG : forall b n x, In (b, n) cshe_ro_B -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
    aview SEGS (w_H W5) mem5 x = aview SEGS (w_H W3) mem3 x).
  { intros b n x Hin Hx Hn. destruct (cl3_ro b n x Hin Hx) as (Hi' & Ho & He & _). apply Kimg; assumption. }
  assert (HG3 : forall x, HA + 80 <= x < HA + 96 -> ~ (VAL A_g_gone <= x < VAL A_g_gone + 1) /\
    ~ (VAL A_g_nout <= x < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= x < VAL A_g_out + 8)).
  { intros x Hx. assert (Hs : VAL (A_OBJ 19) <= x < VAL (A_OBJ 19) + 384) by (unfold ASRC in HAgs; lia).
    destruct (HGS x Hs) as (_ & _ & Hg1 & Hg2 & Hg3). auto. }
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_gone); [lia | intros Hc; apply (proj1 (HG3 x Hc)); lia] | exact MG]|].
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_nout); [lia | intros Hc; apply (proj1 (proj2 (HG3 x Hc))); lia] | exact MNO]|].
  split; [apply (cl3_vm_keep W3 W5 mem3 mem5); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    apply (KG _ _ x cl3_ro_out); [lia | intros Hc; apply (proj2 (proj2 (HG3 x Hc))); lia] | exact MOUT]|].
  split.
  { intros k Hk. destruct HOBK as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
    assert (Hne : ob <> []) by (intros E0; rewrite E0 in Hk; cbn in Hk; lia).
    destruct (HOUTn Hne) as (Hn1 & Hn2).
    assert (HO2 : In (OUT, CO) (ablocks B ly2 S2)) by (apply (Hlive _ HOin); intros E'; apply Hn2; rewrite <- E'; reflexivity).
    destruct (cl3_blk ly1 S1 W3 mem3 md3 OUT CO HAR1 HOin) as (_ & _ & _ & Hle & _).
    rewrite (proj1 (KAb (OUT, CO) (OUT + k) HOin HO2 Hn1 Hn2 ltac:(cbn [fst snd]; lia))). exact (HOBt k Hk). }
  split.
  { destruct HOBK as [E0 | (CO & HCO & HOin)]; [left; exact E0|].
    destruct (Nat.eq_dec (length ob) 0) as [Hl0 | Hl0]; [left; apply length_zero_iff_nil; exact Hl0|].
    assert (Hne : ob <> []) by (intros E0; rewrite E0 in Hl0; apply Hl0; reflexivity).
    destruct (HOUTn Hne) as (Hn1 & Hn2). right. exists CO. split; [exact HCO|].
    apply (Hlive _ HOin). intros E'. apply Hn2. rewrite <- E'. reflexivity. }
  split.
  { intros rest HQ0. rewrite map_app, <- app_assoc in HQ0. cbn [map app] in HQ0.
    pose proof (HPERM (rb :: rest) HQ0) as HP1. rewrite Eb2. rewrite Eb1 in HP1. exact (cl3_perm_drop_xR _ b1 b2 rest _ HP1). }
  split; [rewrite HfrD; exact HFRS|].
  split.
  { eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLEd)|].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
    rewrite Z.mul_add_distr_r, Z.mul_1_l. lia. }
  split.
  { apply (mo_ok_step MT ML S1 S2 (mo_free MT)); [|exact HMLEd].
    eapply (mo_ok_le MT ML); [exact HMOK|].
    cbn [ldrop_list hl_recs]. change (firstn i (hl_recs H1) ++ skipn (Datatypes.S i) (hl_recs H1)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (bl3_drop_len _ _ Hi). rewrite Nat2Z.inj_sub by lia. cbn [Z.of_nat Pos.of_succ_nat].
    rewrite Z.mul_sub_distr_r, Z.mul_1_l. lia. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as (He & Hpinn).
    assert (Hd : forall r0, {in_zr a r0} + {~ in_zr a r0}).
    { intros r0. unfold in_zr. destruct (Z_le_gt_dec (fst r0) a); destruct (Z_lt_ge_dec a (fst r0 + snd r0));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hno].
    - exact (rom_pinned_view0 ly2 S2 W5 mem5 md5 a HAR2 (Hpinn Hown)).
    - assert (Hi' : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; [exact Hsg | exact Hra]).
      rewrite (Kimg a Hi' Hno He); [exact (HROM a Hr)|].
      intros Hc. destruct (HGS a ltac:(unfold ASRC in HAgs; lia)) as (_ & Hnr & _). exact (Hnr Hr). }
  split.
  { apply (cl3_saved_kept W3 W5 mem3 mem5 sp0 regs0); [|exact HSAV].
    intros a Ha. apply Kstk; [rewrite WS in Hslo; lia | unfold LDROP_STK, LDROP_FRAME, ASTACK; lia]. }
  split; [intros jj Hjj; rewrite HERRd by lia; exact (HERR jj Hjj)|].
  split; [exact HRMd|]. rewrite Eb2. rewrite Eb1 in HCNk. exact (cl3_cnt_del RP _ _ _ HCNk). }
assert (P2 : getr regs5 2 = getr regs3 2) by (apply (HPd 2); unfold acallee_saved; lia).
assert (P3 : getr regs5 3 = getr regs3 3) by (apply (HPd 3); unfold acallee_saved; lia).
assert (P4 : getr regs5 4 = getr regs3 4) by (apply (HPd 4); unfold acallee_saved; lia).
assert (P8 : getr regs5 8 = getr regs3 8) by (apply (HPd 8); unfold acallee_saved; lia).
assert (P9 : getr regs5 9 = getr regs3 9) by (apply (HPd 9); unfold acallee_saved; lia).
assert (P18 : getr regs5 18 = getr regs3 18) by (apply (HPd 18); unfold acallee_saved; lia).
assert (P19 : getr regs5 19 = getr regs3 19) by (apply (HPd 19); unfold acallee_saved; lia).
assert (P21 : getr regs5 21 = getr regs3 21) by (apply (HPd 21); unfold acallee_saved; lia).
assert (P23 : getr regs5 23 = getr regs3 23) by (apply (HPd 23); unfold acallee_saved; lia).
assert (P24 : getr regs5 24 = getr regs3 24) by (apply (HPd 24); unfold acallee_saved; lia).
assert (P27 : getr regs5 27 = getr regs3 27) by (apply (HPd 27); unfold acallee_saved; lia).
rewrite R1.
assert (Hwr : 0 <= Z.of_nat w <= 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cl3d_state W5 regs5 mem5 (sp0 - 112) (Z.of_nat w) (eq_trans P2 R2) (eq_trans P21 R21) (eq_trans P23 R23)
  (eq_trans P24 R24) HSPb HSPa Hwr) as [HS SHOK].
remember (Eimg (Ereg regs5 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs5 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ2 SHOK Bspan A_csheB_l3. { cl3_awr. }
assert (E24 : ew E 24 = w64 (Z.of_nat w)) by (rewrite (EEo 24%nat 24%bv eq_refl), P24; exact R24).
psrr_branch_tok RUNx BRR HS SHOK Bspan.
2: { (* 0x85a0c blt a0,s8: a0 = w - 1 < s8 = w (w <= 2 ^ 26), so the fall-through to the unimp at 0x85a10
        (DECW_FT; W_traps.v trap_seat is this fact as a seat condition) never runs *)
  exfalso. rewrite trap_br_lt, !S_SOff in Hc. rewrite E24 in Hc. unfold w64 in Hc.
  rewrite unsigned_lit_small in Hc by lia.
  rewrite !bv_swrap_small in Hc by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  apply Z.ltb_ge in Hc. lia. }
clear Hc.
paj_run_to_tok_xR RUNTOx HS HJ2 SHOK Bspan A_csheB_l3. { cl3_awr. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (21%bv : bv 5) N21. prreg HS (23%bv : bv 5) N23. prreg HS (22%bv : bv 5) N22. prreg HS (10%bv : bv 5) N10.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst (ms_regs ?m) _ (ms_mem ?m) _; cfg_model := ?mdq |} _ =>
  assert (MQ : forall x, mrestrict (w_H W5) (ms_mem m) x = mrestrict (w_H W5) mem5 x);
  [intros x; repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
     rewrite (Hf x) by cl3_nowr end; reflexivity|];
  destruct (cl3_eqv_view W5 mem5 (ms_mem m) MQ) as (AVE & APE);
  replace (BASE + 13880) with (BASE + A_csheB_l3) by (unfold A_csheB_l3, AF_fr_check_shape_ends; lia);
  apply (HKont (ds ++ [r]) W5 (ms_regs m) (ms_mem m) mdq)
end.
exists ly2, S2, (kk + 1), (ldrop_list H1 i).
assert (Edr : hl_recs (ldrop_list H1 i) = CheckRep.drop_nth i (hl_recs H1)) by reflexivity.
split.
{ eapply (cl3_mem_step_xR ly2 S2 W5 W5 mem5 _ md5 _ (kk + 1) (kk + 1) (ldrop_list H1 i) (ds ++ [r]) HM2 HJ2).
  - intros a _. apply AVE.
  - intros a _. apply AVE.
  - exact APE. }
rewrite Edr.
split; [exact HRUN|].
split; [exact HREL|].
split; [exact Hc0|]. split; [exact HcO|].
split.
{ apply (cl3_vm_keep W3 W5 mem3 _); [|exact MAT]. intros x Hx. rewrite AVE.
  apply Kstk; [rewrite WS in Hslo; lia | unfold LDROP_STK, LDROP_FRAME, ASTACK; lia]. }
split.
{ unfold cl3_regs_xR.
  split; [rewrite N2, (EEo 2%nat 2%bv eq_refl), P2; exact R2|].
  split; [rewrite N3, (EEo 3%nat 3%bv eq_refl), P3; exact R3|].
  split; [rewrite N4, (EEo 4%nat 4%bv eq_refl), P4; exact R4|].
  split; [rewrite N27, (EEo 27%nat 27%bv eq_refl), P27; exact R27|].
  split; [rewrite N8, (EEo 8%nat 8%bv eq_refl), P8; exact R8|].
  split; [rewrite N9, (EEo 9%nat 9%bv eq_refl), P9; exact R9|].
  split; [rewrite N18, (EEo 18%nat 18%bv eq_refl), P18; exact R18|].
  split; [rewrite N19, (EEo 19%nat 19%bv eq_refl), P19; exact R19|].
  split; [rewrite N21; reflexivity | rewrite N23; reflexivity]. }
split; [rewrite N22; exact E24|].
rewrite N10, E24. unfold w64 at 1. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* cl3_base at R *)
Lemma cl3_base_xR : forall ds c W1 regs1 mem1 md1, cl3_inv_xR 0 ds c W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros ds c W1 regs1 mem1 md1 HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & kk & H1 & HM & HRUN & HREL & Hc0 & HcO & MAT & HREGS & R22 & R10).
pose proof HREGS as (R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 112 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
destruct (cl3_state0 W1 regs1 mem1 (sp0 - 112) R2 R21 R23 R22 HSPb HSPa) as [HS SHOK].
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
pose proof HM as (HJ0 & _).
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_to_tok_xR RUNTOx HS HJ0 SHOK Bspan A_csheB_ret. { cl3_awr. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (27%bv : bv 5) N27.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst (ms_regs ?m) ?pc (ms_mem ?m) _; cfg_model := ?mdq |} _ =>
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem m) x = mrestrict (w_H W1) mem1 x);
  [intros x; repeat match goal with Hf : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- mrestrict _ ?m1 x = _ =>
     rewrite (Hf x) by cl3_nowr end; reflexivity|];
  destruct (cl3_eqv_view W1 mem1 (ms_mem m) MQ) as (AVE & APE);
  pose proof (cl3_mem_step_xR ly1 S1 W1 W1 mem1 (ms_mem m) md1 mdq kk kk H1 ds HM HJ0
    ltac:(intros a _; apply AVE) ltac:(intros a _; apply AVE) APE) as HM';
  apply (SRrG_ret SEGS R R_refl); exists ly1, S1, (ms_regs m), (ms_mem m), mdq, kk, H1, ds, c
end.
destruct HM' as (HJ' & HSRC' & HV' & HC' & HND' & HINC' & HLEN' & MG' & MNO' & MOUT' & HOBt' & HOBK' & HPERM' & HFRS' &
  HMLE' & HMOK' & HROM' & HSAV' & HERR' & HRM' & HCN').
split; [reflexivity|].
split; [exact HJ'|].
split; [rewrite N2, (EEo 2%nat 2%bv eq_refl); exact R2|].
split; [rewrite N3, (EEo 3%nat 3%bv eq_refl); exact R3|].
split; [rewrite N4, (EEo 4%nat 4%bv eq_refl); exact R4|].
split; [rewrite N27, (EEo 27%nat 27%bv eq_refl); exact R27|].
split; [exact HSAV'|].
split; [exact HSRC'|].
split; [exact HV'|]. split; [exact HC'|]. split; [exact HND'|].
split.
{ right. split; [reflexivity|].
  specialize (HREL (hl_recs H1) [] 0 eq_refl). rewrite app_nil_r, Z.add_0_r in HREL. exact HREL. }
split; [exact Hc0|].
split; [apply (cl3_vm_keep W1 W1 mem1 _); [intros x _; apply AVE | exact MAT]|].
split; [exact MG'|].
split; [exact HPERM'|].
split; [exact HFRS'|].
split.
{ eapply (mo_le_mono MT ML); [exact HMLE'|]. pose proof (mo_free_nonneg MT ML) as Hf0.
  unfold hl_n. apply Z.mul_le_mono_nonneg_r; lia. }
split; [exact HERR'|].
rewrite cl3_rk in HRM'. exact (RMM_of RP S1 kr _ (Nat.le_add_l _ _) HRM').
Qed.

(* cl3_loop at R *)
Lemma cl3_loop_xR : forall w ds c W1 regs1 mem1 md1, cl3_inv_xR w ds c W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_csheB_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction w as [|w IH]; intros ds c W1 regs1 mem1 md1 HI.
- exact (cl3_base_xR ds c W1 regs1 mem1 md1 HI).
- apply (cl3_A1_xR w ds c W1 regs1 mem1 md1 HI). intros l i W2 regs2 mem2 md2 HAB.
  apply (cl3_A2_xR w ds c l i W2 regs2 mem2 md2 HAB). intros W3 regs3 mem3 md3 HMD.
  apply (cl3_A3_xR w ds (c + Z.of_nat (length l) + 1) i W3 regs3 mem3 md3 HMD). intros ds' W4 regs4 mem4 md4 HI4.
  exact (IH ds' _ W4 regs4 mem4 md4 HI4).
Qed.
End loopR.

(* cshe_l3_B at R *)
Lemma cshe_l3_B_xR : forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob,
AFP0 CSHE_STK_B ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\
   forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob)
  (CheckRep.want_of P (hl_recs (hs_held h))) <> None) ->
mo_ok MT S (hl_n (hs_held h) * mo_free MT) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) -> cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
forall W1 c1, cshe_l3_in_xR B PST ARx G R regs ly S W mem md XO AT HA PF gone h P W1 c1 ->
SRrG SEGS R W1 c1 (cshe_out_B_xR B PST ARx G R MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr).
Proof.
intros W ly S regs mem md ch XO AT HA j PF h P A0 gone O OUT ob
  HPRE HX0 HX16 HXtop HSRC HA8 HA4096 HAk HGa Hzs HAj Hj4 HND Hn26 HAT8 HATl HATh MAT0 HPz HPl HPF0 HPFh HPB HPN HPV
  HPM1 HPM8 HPRA HPSV HPD HLG HROM0 MG0 MNO0 MOUT0 HOBt HOlen HO40 HO32 HOM HOBK HA0 HFUN HMOK kr HRM0 HCN0 W1 c1 HIN.
destruct HIN as (regs1 & mem1 & md1 & -> & HJ1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R21 & R23 & R22 & R10 &
  HSAV1 & KV & KP & Hg0).
subst gone.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HAgs : VAL (A_OBJ 19) <= HA /\ HA + ASRC <= VAL (A_OBJ 19) + 384) by (unfold ASRC in *; lia).
assert (Hgs_in : In (VAL (A_OBJ 19), 384) cshe_ro_B) by (cbv [cshe_ro_B]; do 3 right; left; reflexivity).
assert (HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a).
{ intros a Ha. destruct (cl3_ro _ _ a Hgs_in ltac:(lia)) as (Hi & Ho & He & _).
  destruct (HGS a ltac:(lia)) as (_ & Hnr & _). auto. }
assert (HAr : 0x10000 <= HA /\ HA + ASRC <= 0x5fc000).
{ pose proof (pa_img_range HA (proj1 (HAimg HA ltac:(unfold ASRC; lia)))).
  pose proof (pa_img_range (HA + ASRC - 1) (proj1 (HAimg (HA + ASRC - 1) ltac:(unfold ASRC; lia)))). lia. }
pose proof HJ1 as HJ1i. apply ajournal_gx_inner_xR in HJ1i. destruct HJ1i as (memS & HJi & _).
pose proof HJi as (HAR1 & _).
assert (KL : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KV; lia).
assert (KR : forall a, 4096 <= a < 0x5fc000 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KL; lia).
assert (HOH : ob <> [] -> ~ In OUT (list_blocks (hs_held h))).
{ intros Hne Hin. destruct HOBK as [E0 | (CO & _ & _ & Hn)]; [exact (Hne E0)|]. apply Hn.
  unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
assert (HOBK' : ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S))
  by (destruct HOBK as [E0 | (CO & H1 & H2 & _)]; [left; exact E0 | right; exists CO; split; assumption]).
assert (HINV : cl3_inv_xR regs ly S W mem md XO AT HA PF A0 O OUT h P ob kr (CheckRep.want_of P (hl_recs (hs_held h))) [] 0
  W1 regs1 mem1 md1).
{ exists ly, S, 0, (hs_held h).
  split.
  { split; [exact HJ1|].
    split; [rewrite cl3_set_held_id; apply (cl3_src_kept_xR ly S W W1 mem mem1 md HA h alloc_ceiling HAR0 HSRC);
      [lia | unfold ASRC in HAr; lia | lia | exact KL | exact KP]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|]. split; [apply incl_refl|].
    split; [cbn [length]; lia|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_gone ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MG0]|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_nout ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MNO0]|].
    split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
      destruct (cl3_ro _ _ x cl3_ro_out ltac:(lia)) as (_ & _ & _ & Hl); apply KL; exact Hl | exact MOUT0]|].
    split.
    { intros k Hk. destruct HOBK' as [E0 | (CO & HCO & HOin)]; [rewrite E0 in Hk; cbn in Hk; lia|].
      destruct (cl3_blk ly S W mem md OUT CO HAR0 HOin) as (_ & H4096 & _ & Hle & _ & Hc & _).
      rewrite KL by lia. exact (HOBt k Hk). }
    split; [exact HOBK'|].
    split; [intros rest HQ0; exact HQ0|].
    split; [reflexivity|].
    split; [exact (mo_le_refl MT ML S)|].
    split; [unfold hl_n in HMOK; exact HMOK|].
    split.
    { intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
      rewrite KR by lia. exact (HROM0 a Hr). }
    split; [exact HSAV1|].
    split; [intros jj Hjj; pose proof (pal_env B TL) as (_ & EIMG & _);
      pose proof (pa_img_range _ (EIMG (as_errno B + jj) ltac:(lia))); apply KR; lia|].
    split; [|exact HCN0]. unfold cshe_cost, hl_n in HRM0. exact HRM0. }
  rewrite Z.add_0_r.
  split; [exact (HFUN eq_refl)|].
  split; [intros rsF dsF cF E; rewrite E; reflexivity|].
  split; [lia|]. split; [lia|].
  split; [apply (cl3_vm_keep W W1 mem mem1); [intros x Hx; cbn in Hx; apply KV; [lia | rewrite WS; lia] | exact MAT0]|].
  split; [unfold cl3_regs_xR; repeat split; assumption|].
  split; assumption. }
assert (HBLK : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S)).
{ pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH0 & _).
  intros b Hb. exact (cl3_alist_blks_in _ _ _ _ _ _ _ HAH0 b Hb). }
eapply cl3_loop_xR with (regs0 := regs) (ly := ly) (S := S) (W := W) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT)
  (HA := HA) (PF := PF) (A0 := A0) (O := O) (OUT := OUT) (h := h) (P := P) (ob := ob) (kr := kr).
all: try eassumption.
all: try (unfold ASRC in *; lia).
all: try (intros a Ha; exact (proj1 (HPV a Ha))).
Qed.
End wR.

End c.
End b.
End a.
