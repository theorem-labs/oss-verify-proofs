(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: loop 3 of the ASan walk of fuzz_reply's check_shape_ends (0x853b0), the
   `while (want-- > 0)` loop from its head 0x8559c to the epilogue 0x85690, over W_check_shape_ends.v's interface
   (cshe_post, cshe_spec, the Section hypotheses).  A segment lemma for W3's pb_check_shape_ends.
   THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): over any allocator relation ARx with its laws,
   in W_check_shape_ends.v's generic Section header (XCshe's): cshe_l3_top_x concludes W_contract_x.cshe_post_x.
   W_cshe_top.v re-derives the AR theorem at ARi0. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_has_prefix.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side (CheckRep) *)
Lemma l3_bz_inj : forall a b : byte, bz a = bz b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.
Lemma l3_bzs_inj : forall a b : list byte, bzs a = bzs b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply l3_bz_inj; exact H1 | apply IH; exact H2].
Qed.
Lemma l3_leqb : forall a b : list byte, RelayModel.list_eqb (bzs a) (bzs b) = true <-> a = b.
Proof.
intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec (bzs a) (bzs b)) as [E|E]; split; intros H.
- exact (l3_bzs_inj a b E).
- reflexivity.
- discriminate.
- exfalso. apply E. rewrite H. reflexivity.
Qed.
Lemma l3_split_nul : forall d l d', CheckRep.split_nul d = Some (l, d') ->
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
Lemma l3_split_nul_app : forall l d', ~ In (Z_to_bv 8 0) l -> CheckRep.split_nul (l ++ Z_to_bv 8 0 :: d') = Some (l, d').
Proof.
induction l as [|b l IH]; intros d' Hn; cbn [app CheckRep.split_nul].
- reflexivity.
- destruct (bv_unsigned b =? 0) eqn:Eb.
  + exfalso. apply Hn. left. apply bv_eq. apply Z.eqb_eq in Eb. rewrite Eb. reflexivity.
  + rewrite IH by (intros H; apply Hn; right; exact H). reflexivity.
Qed.
(* the first line of a NUL-terminated split is unique *)
Lemma l3_nul_unique : forall (l1 l2 r1 r2 : list byte), l1 ++ Z_to_bv 8 0 :: r1 = l2 ++ Z_to_bv 8 0 :: r2 ->
~ In (Z_to_bv 8 0) l1 -> ~ In (Z_to_bv 8 0) l2 -> l1 = l2 /\ r1 = r2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] r1 r2 E H1 H2; cbn in E.
- injection E as E. split; [reflexivity | exact E].
- injection E as Ey _. exfalso. apply H2. left. symmetry. exact Ey.
- injection E as Ex _. exfalso. apply H1. left. exact Ex.
- injection E as -> E. destruct (IH l2 r1 r2 E) as [-> ->]; [intros H; apply H1; right; exact H | intros H; apply H2; right; exact H|].
  split; reflexivity.
Qed.
Lemma l3_find_text : forall y rs i, CheckRep.find_text y rs = Some i ->
(i < length rs)%nat /\ snd (nth i rs (0, [])) = y /\ (forall k, (k < i)%nat -> snd (nth k rs (0, [])) <> y).
Proof.
intros y rs. induction rs as [|r rs IH]; intros i H; cbn [CheckRep.find_text] in H; [discriminate|].
destruct (RelayModel.list_eqb (bzs (snd r)) (bzs y)) eqn:E.
- injection H as <-. apply l3_leqb in E. split; [cbn; lia|]. split; [exact E | intros k Hk; lia].
- destruct (CheckRep.find_text y rs) as [i0|] eqn:Ef; [|discriminate]. cbn in H. injection H as <-.
  destruct (IH i0 eq_refl) as (H1 & H2 & H3). split; [cbn; lia|]. split; [exact H2|].
  intros [|k] Hk; cbn [nth].
  + intros Hc. rewrite <- Hc in E. assert (Ht : RelayModel.list_eqb (bzs (snd r)) (bzs (snd r)) = true) by (apply l3_leqb; reflexivity).
    rewrite Ht in E. discriminate.
  + apply H3. lia.
Qed.
(* the first match is unique *)
Lemma l3_first_unique : forall (rs : list (Z * list byte)) y i j,
snd (nth i rs (0, [])) = y -> (forall k, (k < i)%nat -> snd (nth k rs (0, [])) <> y) ->
snd (nth j rs (0, [])) = y -> (forall k, (k < j)%nat -> snd (nth k rs (0, [])) <> y) -> i = j.
Proof.
intros rs y i j Hi Hi' Hj Hj'. destruct (Nat.lt_trichotomy i j) as [Hl | [He | Hl]]; [| exact He |].
- exfalso. exact (Hj' i Hl Hi).
- exfalso. exact (Hi' j Hl Hj).
Qed.
Definition l3_ok (P l : list byte) : bool :=
Nat.leb 4 (length l) && RelayModel.list_eqb (bzs (skipn (length l - 4) l)) (bzs CheckRep.END4) && CheckRep.prefixb P l.
(* one step of ends_run, taken apart *)
Lemma l3_ends_S : forall P rs d w rsF dsF cF, CheckRep.ends_run P rs d (S w) = Some (rsF, dsF, cF) ->
exists l d' i dsR cR, d = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ l3_ok P l = true /\
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
injection H as <- <- <-. destruct (l3_split_nul d l d' E1) as [Ed Hn].
exists l, d', i, y, z. repeat split; assumption.
Qed.
(* and put back together *)
Lemma l3_ends_step : forall P rs l d' i w rsF dsR cR,
~ In (Z_to_bv 8 0) l -> l3_ok P l = true ->
CheckRep.find_text (firstn (length l - 4) l) rs = Some i ->
CheckRep.ends_run P (CheckRep.drop_nth i rs) d' w = Some (rsF, dsR, cR) ->
CheckRep.ends_run P rs (l ++ Z_to_bv 8 0 :: d') (S w) = Some (rsF, nth i rs (0, []) :: dsR, Z.of_nat (length l) + 1 + cR).
Proof.
intros P rs l d' i w rsF dsR cR Hn Hok Hf Hr. cbn [CheckRep.ends_run]. rewrite (l3_split_nul_app l d' Hn).
unfold l3_ok in Hok. rewrite Hok, Hf, Hr. reflexivity.
Qed.
Lemma l3_drop_len : forall (rs : list (Z * list byte)) i, (i < length rs)%nat ->
length (CheckRep.drop_nth i rs) = (length rs - 1)%nat.
Proof.
intros rs i Hi. unfold CheckRep.drop_nth. rewrite length_app, length_firstn, length_skipn. lia.
Qed.
Lemma l3_ends_len : forall P w rs d, CheckRep.ends_run P rs d w <> None -> (w <= length rs)%nat.
Proof.
intros P w. induction w as [|w IH]; intros rs d H; [lia|].
destruct (CheckRep.ends_run P rs d (S w)) as [[[x y] z]|] eqn:E; [|exfalso; exact (H eq_refl)].
destruct (l3_ends_S P rs d w x y z E) as (l & d' & i & dsR & cR & _ & _ & _ & Hf & Hr & _).
destruct (l3_find_text _ _ _ Hf) as (Hi & _).
pose proof (IH (CheckRep.drop_nth i rs) d' ltac:(rewrite Hr; discriminate)) as Hl.
rewrite (l3_drop_len rs i Hi) in Hl. lia.
Qed.
Lemma l3_ends_O : forall P rs d rsF dsF cF, CheckRep.ends_run P rs d 0 = Some (rsF, dsF, cF) ->
rsF = rs /\ dsF = [] /\ cF = 0.
Proof. intros P rs d rsF dsF cF H. cbn in H. injection H as <- <- <-. auto. Qed.
Lemma l3_drop_split : forall (A Bs : list (Z * list byte)) x,
CheckRep.drop_nth (length A) (A ++ x :: Bs) = A ++ Bs.
Proof. intros A. unfold CheckRep.drop_nth. induction A as [|a A IH]; intros Bs x; cbn; [reflexivity | f_equal; apply IH]. Qed.
Lemma l3_nodup_drop : forall {Y : Type} (f : Z * list byte -> Y) (l : list (Z * list byte)) i,
NoDup (map f l) -> NoDup (map f (CheckRep.drop_nth i l)).
Proof.
intros Y f l i H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
- destruct (nth_split l (0, []) Hi) as (A & Bs & Hsp & HlA). rewrite Hsp in H |- *. rewrite <- HlA, l3_drop_split.
  rewrite map_app in H |- *. cbn [map] in H. exact (NoDup_remove_1 _ _ _ H).
- unfold CheckRep.drop_nth. rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite app_nil_r. exact H.
Qed.
Lemma l3_nth_line : forall (ob l d' : list byte) A k, skipn A ob = l ++ Z_to_bv 8 0 :: d' -> (k < length l)%nat ->
nth (A + k) ob (Z_to_bv 8 0) = nth k l (Z_to_bv 8 0).
Proof.
intros ob l d' A k E Hk. rewrite <- (firstn_skipn A ob) at 1.
assert (HA : length (firstn A ob) = A).
{ rewrite length_firstn. destruct (Nat.le_gt_cases A (length ob)) as [H|H]; [lia|].
  rewrite skipn_all2 in E by lia. destruct l; discriminate E. }
rewrite app_nth2 by lia. rewrite HA. replace (A + k - A)%nat with k by lia. rewrite E. apply app_nth1. exact Hk.
Qed.
Lemma l3_nth_skipn : forall (l : list byte) m n, nth n (skipn m l) (Z_to_bv 8 0) = nth (m + n) l (Z_to_bv 8 0).
Proof. intros l m. revert l. induction m as [|m IH]; intros [|x l] n; cbn; try reflexivity. destruct n; reflexivity. apply IH. Qed.
Lemma l3_skip_line : forall (ob l d' : list byte) A, skipn A ob = l ++ Z_to_bv 8 0 :: d' ->
skipn (A + length l + 1) ob = d'.
Proof.
intros ob l d' A E. replace (A + length l + 1)%nat with (S (length l) + A)%nat by lia.
rewrite <- skipn_skipn, E. clear E. induction l as [|x l IH]; [reflexivity|]. exact IH.
Qed.
Lemma l3_incl_drop : forall (l : list (Z * list byte)) i, incl (CheckRep.drop_nth i l) l.
Proof.
intros l i x Hx. unfold CheckRep.drop_nth in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite <- (firstn_skipn i l). apply in_or_app. left. exact Hx.
- rewrite <- (firstn_skipn (S i) l). apply in_or_app. right. exact Hx.
Qed.

(* A run writes only inside its regions' write windows; here the only one is l->n, [HA + 88, HA + 92) (the region
   based at atom 18 = HA + 80, window [8, 12)).  U18: the env's value of atom 18. *)
Ltac l3_wkeep HFr U18 :=
lazymatch type of HFr with frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) =>
  apply (aview_kept_out Ev rs H m0 m1 HFr); [lia|];
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U18 in Hrg; lia|]);
  destruct Hin
end.

Ltac prreg_raw HS r Hr :=
lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* W1's lib/A/W_list_drop.v ld_count_eq: the memmove's byte count ((n + ~i) << 4) as the walk's addw / slli leave it *)
Lemma l3_count_eq : forall nn ii, 0 <= ii -> ii + 1 <= nn -> nn < 2 ^ 30 ->
alu64 ALU_SLL (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 nn))
  (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1)))))) (Z_to_bv 64 4)
= Z_to_bv 64 (16 * (nn - ii - 1)).
Proof.
intros nn ii H0 H1 H2.
assert (RX : bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1))) = 2 ^ 64 - 1 - ii).
{ rewrite YO0c.alu64_xori_m1. rewrite unsigned_lit_small by lia. apply not64_eq. lia. }
assert (RL : bv_unsigned (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1)))) = 2 ^ 32 - 1 - ii).
{ rewrite YO0c.low32_unsigned, RX. unfold lo32.
  replace (2 ^ 64 - 1 - ii) with ((2 ^ 32 - 1 - ii) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (RN : bv_unsigned (low32 (Z_to_bv 64 nn)) = nn).
{ rewrite YO0c.low32_unsigned, unsigned_lit_small by lia. unfold lo32. apply Z.mod_small. lia. }
assert (RA : bv_unsigned (alu32 ALU_ADD (low32 (Z_to_bv 64 nn))
  (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1))))) = nn - ii - 1).
{ rewrite YO0c.alu32_add_unsigned, RN, RL.
  replace (nn + (2 ^ 32 - 1 - ii)) with ((nn - ii - 1) + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
apply bv_eq. rewrite YO0c.alu64_sll, YO0c.sext64_alu32, RA.
rewrite sx32_small by lia. rewrite (unsigned_lit_small 4) by lia.
replace (4 mod 64) with 4 by reflexivity.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. lia.
Qed.

Lemma l3_set_held_id : forall h, CheckRep.set_held h (hs_held h) = h.
Proof. intros h. destruct h. reflexivity. Qed.

(* ------------------------------------------------------------------ the walk's Section, as W_check_shape_ends.v's *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the second state of a turn: 0x85614, a0 = &l->v[j] (j the line's record, from list_find) *)
Definition A_cshe_l3s : Z := AF_fr_check_shape_ends + 0x264.

(* ------------------------------------------------------------------ the loop head 0x8559c *)
(* At the head (sp = sp0 - 144): s0 (x8) = HA + 88 = &l->n, s1 (x9) = PF, s2 (x18) = HA + 80 = l (the held list),
   s3 (x19) = AT, s4 (x20) = .str.4 " end", s8 (x24) = 4, s9 (x25) = SB, s10 (x26) = SB + (HA + 80) / 8 (the shadow
   byte of l->v), s11 (x27) = w + 1 (w the turns left, >= 1); 16(sp) holds SB + (HA + 88) / 8 (the shadow byte of
   l->n).  s0 is pinned to s2 + 8 and s10 / 16(sp) to the shadow form the token engine reads (match_x), so the
   three shadow checks of l->v and l->n are covered by the one shadow entry of s2's 16 bytes. *)
Definition cshe_l3_shn : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0).
Definition cshe_l3_shv : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0).
Definition cshe_l3_fr : YP09.region := YP09.mkRegion (Some 2%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 cshe_l3_shn)].
Definition cshe_l3_hd : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 8 12
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition cshe_l3_sr : list sv :=
sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 18 8)) 24%bv (SLit 4)) 26%bv cshe_l3_shv.
(* atoms 32 the vector v, 33 the count n, 34 the line's address, 35 its length (next_line's two out cells) *)
Definition cshe_l3_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 (2 ^ 26) 0); (34%nat, mkAF 4096 140737479966720 0);
(35%nat, mkAF 4 (2 ^ 32) 0); (27%nat, mkAF 2 (2 ^ 26) 0) ] [] [].
Definition ss_cshe_l3 : sstate := mkSS A_cshe_l3 cshe_l3_sr [ cshe_l3_fr; cshe_l3_hd ] None cshe_l3_facts.
Definition cshe_l3_SH : list shent := [ mkSHE 18 0 16 ].
Definition cshe_l3_extra (v n line len : Z) : list word := map (Z_to_bv 64) [v; n; line; len].
(* next_line's two out cells in this frame, once it returned: 24(sp) the line's length, 32(sp) its address *)
Definition cshe_l3_cells : YP09.region := YP09.mkRegion (Some 2%nat) 24 40 0 0
[YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0))].

Lemma l3_U_sh : forall E m c x, ew E m = Z_to_bv 64 x -> ew E 25 = Z_to_bv 64 SB -> 0 <= x < 2 ^ 47 -> x + c < 2 ^ 47 -> 0 <= x + c ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 25 0)) = (x + c) / 8 + SB.
Proof.
intros E m c x Hm H25 Hx Hc Hc0.
rewrite !U_SAlu, (U_atom_off E m x c Hm) by lia. rewrite (U_atom E 25 SB H25) by (unfold SB; lia). rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
assert (D : 0 <= (x + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. unfold SB. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma cshe_l3_state : forall (W : world SEGS) regs mem SP HA v n line len w,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) -> getr regs 24 = w64 4 ->
getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) -> getr regs 27 = w64 (w + 1) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
4096 <= line <= 140737479966720 -> 4 <= len <= 2 ^ 32 -> 1 <= w < 2 ^ 26 ->
val_mem SEGS (arm W mem) (SP + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n -> awr W mem (HA + 88) 4 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_l3_extra v n line len))) ss_cshe_l3
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l3)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 cshe_l3_SH (Eimg (Ereg regs (cshe_l3_extra v n line len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n line len w H2 H8 H18 H24 H25 H26 H27 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn Hl Hln Hw
M16 Mv Mn Hwn HRA.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HD88 : 0 <= (HA + 88) / 8 <= HA + 88) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (cshe_l3_extra v n line len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cshe_l3_extra v n line len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E27 : ew E 27 = Z_to_bv 64 (w + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 line) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (VB : forall m x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> base_val E (Some m) = x).
{ intros m x Hm Hx. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hx. }
assert (V2 : base_val E (Some 2%nat) = SP) by (apply VB; [exact E2 | lia]).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (apply VB; [exact E18 | lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_cshe_l3. apply pa_entry_st_ok_full.
  + unfold cshe_l3_sr.
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, cshe_l3_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l3_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H24; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cshe_l3_fr, cshe_l3_hd.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ SP 16 8 cshe_l3_shn ((HA + 88) / 8 + SB));
      [| unfold SB; zside | zside | exact M16].
      unfold cshe_l3_shn. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))))
        with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))).
      rewrite (l3_U_sh E 18 8 (HA + 80) E18 E25) by lia.
      replace (HA + 80 + 8) with (HA + 88) by lia. rewrite unsigned_lit_small; [reflexivity|].
      unfold SB. lia.
    * rewrite V18. split; [lia|]. split; [lia|]. split.
      { intros o Ho. unfold awr, arm in Hwn. replace (HA + 80 + o) with (HA + 88 + (o - 8)) by lia. exact (Hwn (o - 8) ltac:(lia)). }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
  + apply pairwise_disjoint_of_extents. unfold cshe_l3_fr, cshe_l3_hd, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V2, V18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cshe_l3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E27, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* the state at 0x855d0, after bcmp returned 0 (the length check and the " end" compare passed): s6 (x22) = len, s7
   (x23) = the line's address, a0 = 0, next_line's two cells in the frame; else as at the head *)

(* the state at 0x85614 (a0 = EA = &l->v[i], s5 (x21) = i): the record's text pointer v[i].s at EA (atom 34), its
   16 bytes under a second shadow entry *)
Definition cshe_l3_slot : YP09.region := YP09.mkRegion (Some 10%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition cshe_l3s_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 (2 ^ 26) 0); (34%nat, mkAF 4096 140737479966720 0);
(10%nat, mkAF 4096 140737479966720 4); (21%nat, mkAF 0 (2 ^ 26) 0); (27%nat, mkAF 2 (2 ^ 26) 0) ] [] [].
Definition ss_cshe_l3s : sstate := mkSS A_cshe_l3s cshe_l3_sr [ cshe_l3_fr; cshe_l3_hd; cshe_l3_slot ] None cshe_l3s_facts.
Definition cshe_l3s_SH : list shent := [ mkSHE 18 0 16; mkSHE 10 0 16 ].

Lemma cshe_l3s_state : forall (W : world SEGS) regs mem SP HA v n line len w EA ii,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) -> getr regs 24 = w64 4 ->
getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) -> getr regs 27 = w64 (w + 1) ->
getr regs 10 = w64 EA -> getr regs 21 = w64 ii -> 4096 <= EA -> EA + 16 <= 140737479966720 -> EA mod 16 = 0 -> 0 <= ii < 2 ^ 26 ->
EA + 16 <= SP -> (HA + 96 <= EA \/ EA + 16 <= HA + 80) -> (EA + 16 <= 0x7fff8000 \/ 0x10007fff8000 <= EA) ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
4096 <= line <= 140737479966720 -> 4 <= len <= 2 ^ 32 -> 1 <= w < 2 ^ 26 ->
val_mem SEGS (arm W mem) (SP + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n -> awr W mem (HA + 88) 4 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
val_mem SEGS (arm W mem) EA 8 line -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF EA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_l3_extra v n line len))) ss_cshe_l3s
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l3s)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 cshe_l3s_SH (Eimg (Ereg regs (cshe_l3_extra v n line len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n line len w EA ii H2 H8 H18 H24 H25 H26 H27 H10 H21 HElo HEhi HE16 Hii HESP HEHA HEapp HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn Hl Hln Hw
M16 Mv Mn Hwn HRA MEA HRAE.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HD88 : 0 <= (HA + 88) / 8 <= HA + 88) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (cshe_l3_extra v n line len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cshe_l3_extra v n line len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E27 : ew E 27 = Z_to_bv 64 (w + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 line) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (VB : forall m x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> base_val E (Some m) = x).
{ intros m x Hm Hx. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hx. }
assert (V2 : base_val E (Some 2%nat) = SP) by (apply VB; [exact E2 | lia]).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (apply VB; [exact E18 | lia]).
assert (E10 : ew E 10 = Z_to_bv 64 EA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E21 : ew E 21 = Z_to_bv 64 ii) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (V10 : base_val E (Some 10%nat) = EA) by (apply VB; [exact E10 | lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_cshe_l3s. apply pa_entry_st_ok_full.
  + unfold cshe_l3_sr.
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, cshe_l3_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l3_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H24; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cshe_l3_fr, cshe_l3_hd, cshe_l3_slot.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ SP 16 8 cshe_l3_shn ((HA + 88) / 8 + SB));
      [| unfold SB; zside | zside | exact M16].
      unfold cshe_l3_shn. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))))
        with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))).
      rewrite (l3_U_sh E 18 8 (HA + 80) E18 E25) by lia.
      replace (HA + 80 + 8) with (HA + 88) by lia. rewrite unsigned_lit_small; [reflexivity|].
      unfold SB. lia.
    * rewrite V18. split; [lia|]. split; [lia|]. split.
      { intros o Ho. unfold awr, arm in Hwn. replace (HA + 80 + o) with (HA + 88 + (o - 8)) by lia. exact (Hwn (o - 8) ltac:(lia)). }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
    * rewrite V10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ EA 0 8 (SOff 34 0) line);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact MEA.
  + apply pairwise_disjoint_of_extents. unfold cshe_l3_fr, cshe_l3_hd, cshe_l3_slot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V2, V18, V10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; destruct HEHA; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cshe_l3s_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E27, E32, E33, E34, E10, E21, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cshe_l3s_SH. constructor; [|constructor; [|constructor]].
  + eapply shent_ok_of_range.
    * exact HRA.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. lia.
  + eapply shent_ok_of_range.
    * exact HRAE.
    * unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom E 10 EA E10) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. destruct HEapp; lia.
Qed.

Definition A_cshe_l3b : Z := AF_fr_check_shape_ends + 0x220.
Definition cshe_l3b_cells : YP09.region := YP09.mkRegion (Some 2%nat) 24 40 0 0
[YP09.mkChunk 24 (CVal 8 (SOff 22 0)); YP09.mkChunk 32 (CVal 8 (SOff 23 0))].
Definition cshe_l3b_sr : list sv := sr_set cshe_l3_sr 10%bv (SLit 0).
Definition cshe_l3b_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF 4096 0x7fff8000 3); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 (2 ^ 26) 0); (23%nat, mkAF 4096 140737479966720 0);
(22%nat, mkAF 4 (2 ^ 32) 0); (27%nat, mkAF 2 (2 ^ 26) 0) ] [] [].
Definition ss_cshe_l3b : sstate := mkSS A_cshe_l3b cshe_l3b_sr [ cshe_l3b_cells; cshe_l3_fr; cshe_l3_hd ] None cshe_l3b_facts.

Lemma cshe_l3b_state : forall (W : world SEGS) regs mem SP HA v n line len w,
getr regs 2 = w64 SP -> getr regs 8 = w64 (HA + 88) -> getr regs 18 = w64 (HA + 80) -> getr regs 24 = w64 4 ->
getr regs 25 = w64 SB -> getr regs 26 = w64 ((HA + 80) / 8 + SB) -> getr regs 27 = w64 (w + 1) ->
getr regs 10 = w64 0 -> getr regs 22 = w64 len -> getr regs 23 = w64 line ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> HA mod 8 = 0 -> 4096 <= HA -> HA + 96 <= 0x7fff8000 ->
4096 <= v <= 140737479966720 -> v mod 16 = 0 -> 1 <= n <= 2 ^ 26 ->
4096 <= line <= 140737479966720 -> 4 <= len <= 2 ^ 32 -> 1 <= w < 2 ^ 26 ->
val_mem SEGS (arm W mem) (SP + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W mem) (HA + 80) 8 v -> val_mem SEGS (arm W mem) (HA + 88) 4 n -> awr W mem (HA + 88) 4 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (HA + 80) 16 ->
val_mem SEGS (arm W mem) (SP + 24) 8 len -> val_mem SEGS (arm W mem) (SP + 32) 8 line ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_l3_extra v n line len))) ss_cshe_l3b
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l3b)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx1 cshe_l3_SH (Eimg (Ereg regs (cshe_l3_extra v n line len))) (mrestrict (w_H W) mem).
Proof.
intros W regs mem SP HA v n line len w H2 H8 H18 H24 H25 H26 H27 H10 H22 H23 HSP HSPa HA8 HAlo HAhi Hv Hv16 Hn Hl Hln Hw
M16 Mv Mn Hwn HRA M24 M32.
pose proof pa_B_ok as HBASE.
assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HD88 : 0 <= (HA + 88) / 8 <= HA + 88) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := Eimg (Ereg regs (cshe_l3_extra v n line len))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cshe_l3_extra v n line len) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 SP) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E18 : ew E 18 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E27 : ew E 27 = Z_to_bv 64 (w + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 v) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 line) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat ltac:(lia)).
assert (E22 : ew E 22 = Z_to_bv 64 len) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 line) by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (VB : forall m x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> base_val E (Some m) = x).
{ intros m x Hm Hx. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hx. }
assert (V2 : base_val E (Some 2%nat) = SP) by (apply VB; [exact E2 | lia]).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (apply VB; [exact E18 | lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_cshe_l3b. apply pa_entry_st_ok_full.
  + unfold cshe_l3b_sr, cshe_l3_sr.
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H10; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H26. unfold w64, cshe_l3_shv. apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
           with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
         rewrite (l3_U_sh E 18 0 (HA + 80) E18 E25) by lia. rewrite Z.add_0_r.
         apply unsigned_lit_small. unfold SB. lia. }
    apply regs_ok_pin; [| intros X; discriminate X | rewrite H24; reflexivity].
    apply regs_ok_pin; [| intros X; discriminate X |].
    2: { rewrite H8. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SOff 18 8))) with (U E (SOff 18 8)).
         rewrite (U_atom_off E 18 (HA + 80) 8 E18) by lia. replace (HA + 80 + 8) with (HA + 88) by lia.
         apply unsigned_lit_small. lia. }
    subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cshe_l3b_cells, cshe_l3_fr, cshe_l3_hd.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ SP 24 8 (SOff 22 0) len);
         [cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M24].
      -- apply (chunk_ok_val SEGS E _ SP 32 8 (SOff 23 0) line);
         [cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M32].
    * rewrite V2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ SP 16 8 cshe_l3_shn ((HA + 88) / 8 + SB));
      [| unfold SB; zside | zside | exact M16].
      unfold cshe_l3_shn. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))))
        with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 25 0))).
      rewrite (l3_U_sh E 18 8 (HA + 80) E18 E25) by lia.
      replace (HA + 80 + 8) with (HA + 88) by lia. rewrite unsigned_lit_small; [reflexivity|].
      unfold SB. lia.
    * rewrite V18. split; [lia|]. split; [lia|]. split.
      { intros o Ho. unfold awr, arm in Hwn. replace (HA + 80 + o) with (HA + 88 + (o - 8)) by lia. exact (Hwn (o - 8) ltac:(lia)). }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 0 8 (SOff 32 0) v);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ (HA + 80) 8 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (HA + 80 + 8) with (HA + 88) by lia. exact Mn.
  + apply pairwise_disjoint_of_extents. unfold cshe_l3b_cells, cshe_l3_fr, cshe_l3_hd, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V2, V18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cshe_l3b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E18, E25, E27, E32, E33, E22, E23, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H808 : (HA + 80) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold Bx1. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom E 18 (HA + 80) E18) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): W_check_shape_ends.v's room record *)
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
(* the Section hypotheses of W_check_shape_ends.v's generic Section c, verbatim *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* loop 3's free(v[i].s) (0x85628, return address 0x8562c): its call context is the singleton [ra] (s0 = HA + 88 is
   no stack address, so chain_pre's chain is empty) *)
Hypothesis HCTX_cshe_l3 : In [BASE + AF_fr_check_shape_ends + 0x27c] CTX_AFREE.
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG.
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* the stack's shadow is zero: the laws' per-byte zero-shadow field of the real stack (YCbqG.v alx_zshadow_byte) *)
Lemma l3_ra_stack : forall ly S {hp : list Z} W mem md a len,
ARx ly S hp W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S hp W mem md a len HAR Hlo Hhi Hlen x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly S hp W mem md x HAR ltac:(lia)).
Qed.

(* the bytes asrc_at reads (its own 96 bytes, and its lists' blocks) carry it to a later memory *)
Lemma l3_text_recs_length : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma l3_list_kept : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 LA l lines,
alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly1 S1)).
Proof.
intros ly1 S1 W1 W2 m1 m2 LA l lines HL KH KB. destruct HL as (_ & _ & _ & _ & (Hn & Hc) & Hv & _ & _ & HF).
rewrite Forall_forall in HF. split.
- intros rr Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
  apply in_app_or in Hr as [Hr | Hr].
  + destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    destruct Hv as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
    apply (KB _ _ a Hin). unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, l3_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
    change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hj. unfold req_size, AREC in *.
    destruct (16 * hl_cap l =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
  + apply in_map_iff in Hr as (x & <- & Hx). destruct (HF x Hx) as (Hin & _).
    apply (KB _ _ a Hin). unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha.
    unfold req_size. destruct (Z.of_nat (length (snd x)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia.
- intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  + destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct Hv as [(Hc0 & _) | (_ & Hin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hin].
  + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (HF x Hx)).
Qed.
Lemma l3_src_kept : forall ly1 S1 (W1 W2 : world SEGS) m1 m2 HA1 h1,
asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 W1 W2 m1 m2 HA1 h1 HS KH KB.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpl & _ & _ & HE & HH & _).
destruct (l3_list_kept _ _ _ _ _ _ (HA1 + 16) _ _ HP ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K1 B1].
destruct (l3_list_kept _ _ _ _ _ _ (HA1 + 64) _ _ HE ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K2 B2].
destruct (l3_list_kept _ _ _ _ _ _ (HA1 + 80) _ _ HH ltac:(intros a Ha; apply KH; unfold ASRC; lia) KB) as [K3 B3].
apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W2 m2 HA1 h1 HS).
- intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  + apply KH. exact Ha.
  + apply (KB _ _ a Hpin). unfold gfp, bzs in Ha. rewrite length_map in Ha. cbn [fst snd] in Ha.
    unfold req_size, APARTIAL in *. cbn. lia.
  + apply in_app_or in Hr as [Hr|Hr]; [exact (K1 r Hr a Ha)|].
    apply in_app_or in Hr as [Hr|Hr]; [exact (K2 r Hr a Ha) | exact (K3 r Hr a Ha)].
- intros b Hb. unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb|Hb]; [exact (B1 b Hb)|].
  apply in_app_or in Hb as [Hb|Hb]; [exact (B2 b Hb) | exact (B3 b Hb)].
Qed.
Lemma l3_saved_kept : forall (W1 W2 : world SEGS) m1 m2 sp rs,
(forall a, sp - 104 <= a < sp -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
cshe_saved W1 m1 sp rs -> cshe_saved W2 m2 sp rs.
Proof.
intros W1 W2 m1 m2 sp rs HK HS. unfold cshe_saved in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; (apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [intros k Hk; apply HK; cbn in Hk; lia | assumption]).
Qed.

(* W1's lib/A/W_list_drop.v helpers (a working branch 5bc6dd7b8b5), copied *)
Lemma l3_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m' ) a.
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
Lemma l3_aview_of_val_mem2 : forall H H' (m m' : word -> option byte) a n v k,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H' m' (a + k) = aview SEGS H m (a + k).
Proof.
intros H H' m m' a n v k H1 H2 Hk. unfold aview.
rewrite (val_mem_agree SEGS _ _ a n v H1 H2 k Hk). reflexivity.
Qed.
(* one step of the turn keeps the source: every byte of it but l->n's four by view, l->n by its value *)
Lemma l3_src_step : forall ly1 S1 {hp1 : list Z} md1 (W1 W2 : world SEGS) m1 m2 HA1 h1 lo hi,
ARx ly1 S1 hp1 W1 m1 md1 -> asrc_at B ly1 S1 W1 m1 HA1 h1 ->
(forall a, HA1 <= a < HA1 + ASRC -> in_img SEGS a) -> alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (HA1 + 88 <= a < HA1 + 92) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall k, 0 <= k < 4 -> aview SEGS (w_H W2) m2 (HA1 + 88 + k) = aview SEGS (w_H W1) m1 (HA1 + 88 + k)) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> wle W1 W2 ->
asrc_at B ly1 S1 W2 m2 HA1 h1.
Proof.
intros ly1 S1 hp1 md1 W1 W2 m1 m2 HA1 h1 lo hi HAR HS Himg Hlo HK HK4 Hp Hw.
pose proof (asan_consts) as (C1 & _).
apply (l3_src_kept ly1 S1 W1 W2 m1 m2 HA1 h1 HS).
- intros a Ha. split; [|intros Hwr; exact (l3_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  pose proof (pa_img_range a (Himg a Ha)) as HI.
  destruct (Z_lt_le_dec a (HA1 + 88)) as [H1 | H1]; [apply HK; lia|].
  destruct (Z_lt_le_dec a (HA1 + 92)) as [H2 | H2]; [|apply HK; lia].
  replace a with (HA1 + 88 + (a - (HA1 + 88))) by lia. apply HK4. lia.
- intros b n a Hin Ha. split; [|intros Hwr; exact (l3_writable_kept_w W1 W2 m1 m2 a (Hp a) Hw Hwr)].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 m1 md1 b n HAR Hin) as (_ & B4096 & Bceil & _).
  apply HK; [lia | lia |]. intros Hc. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 m1 md1 b n a HAR Hin Ha). apply Himg. unfold ASRC. lia.
Qed.


Lemma l3_sll4 : forall z, 0 <= z < 2 ^ 59 -> alu64 ALU_SLL (Z_to_bv 64 z) (Z_to_bv 64 4) = Z_to_bv 64 (16 * z).
Proof.
intros z Hz. apply bv_eq. rewrite YO0c.alu64_sll.
rewrite (unsigned_lit_small 4) by lia. rewrite (unsigned_lit_small z) by lia.
replace (4 mod 64) with 4 by reflexivity.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma l3_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma l3_amem_of_app : forall lo len a m, in_app lo len -> lo <= a -> 0 <= m -> a + m <= lo + len -> amem_range a m.
Proof.
intros lo len a m (H1 & H2) Ha Hm Hb. pose proof alloc_ceiling_val as AC.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H2. lia.
Qed.
Lemma l3_shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* W3's lib/A/W_check_no_loss.v helpers (cnl_free_gx, cnl_rec_fields, cnl_garr8_val_mem8; W1's free and record-cell
   lemmas there), copied *)
(* the room round: a free keeps the live counts under their bounds (one block fewer, ReplyCnt.acnt_del_le), as
   W_list_free.v lf_cnt_del; and a budget restated by an equation *)
Lemma l3_cnt_del : forall RP0 l1 (x : Z * Z) l2, cnt_ok RP0 (l1 ++ x :: l2) -> cnt_ok RP0 (l1 ++ l2).
Proof.
intros RP0 l1 x l2 H. unfold cnt_ok in *.
apply (cnt_ok_pk_mono RP0 (fun _ => 0%nat) (fun _ => 0%nat) (l1 ++ x :: l2) (l1 ++ l2)); [|exact H].
intros P0. cbv beta. rewrite !Nat.add_0_r. apply ReplyCnt.acnt_del_le.
Qed.
Lemma l3_rm_cast : forall RP0 S0 (m m' : nat), rp_RM RP0 S0 m -> m = m' -> rp_RM RP0 S0 m'.
Proof. intros RP0 S0 m m' H <-. exact H. Qed.
Lemma l3_free_gx : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch -> In (raZ regsT :: spine ch) CTX_AFREE ->
(* the room round: the rule's room (one free) and the live counts at the call *)
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall i, 0 <= i < req_size nb -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (pa <= a < pa + req_size nb) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb o raw ch kr
HJ HX Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (Hal' : (o - XO1) mod 16 = 0) by (rewrite Zminus_mod, Hal, HX; reflexivity).
eapply SRr_mono.
{ exact (AFREE W regsT memT (STK + XO1) (sp0 + XO1) FP ly S hp W0 memS md own lyc Sc hpc mdc k pa nb (o - XO1) raw ch kr
  HJi Hin Ha0 ltac:(lia) Hal' ltac:(lia) ltac:(lia)
  (* the stack room below the call (a Theorem Labs lane's ACALL_PREFIX), from the journal's astk_ok *)
  (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o - XO1) regsT HJi ltac:(lia) ltac:(lia))
  Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Herr & Hpr).
replace (sp0 + XO1 + (o - XO1) - ASTACK) with (sp0 + o - ASTACK) in HK by lia.
replace (sp0 + XO1 + (o - XO1)) with (sp0 + o) in HK by lia.
exists ly2, S2, hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK |
  split; [exact Hle | split; [exact HRM2 | split; [exact Herr | exact Hpr]]]]]]]].
apply (ajournal_gx_pack_x SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply (proj1 HK); lia.
Qed.
Lemma l3_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma l3_rec_fields : forall ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64) /\
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) 8
  (Z.of_nat (length (snd (nth j (HarnessRep.hl_recs l) (0, [])))) mod 2 ^ 64).
Proof.
intros ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, l3_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply l3_garr8_val_mem8 in H1. apply l3_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|]. replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.

Lemma l3_lb : forall (l : hlist), 0 < hl_cap l -> list_blocks l = hl_v l :: map fst (hl_recs l).
Proof. intros l Hc. unfold list_blocks. destruct (hl_cap l =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.
Lemma l3_req_ge : forall n, 0 <= n -> n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia. Qed.
(* W3's cnl_list_kept (W_check_no_loss.v): the bytes a list's predicate reads are kept when its head is and each of
   its blocks (all satisfying Pb) is *)
Lemma l3_list_kept_P : forall ly1 S1 {hp1 : list Z} (W1 W2 : world SEGS) m1 md1 m2 LA l lines (Pb : Z -> Prop),
ARx ly1 S1 hp1 W1 m1 md1 -> alist_at B ly1 S1 W1 m1 LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W1 m1 W2 m2 a) ->
(forall b n a, In (b, n) (ablocks B ly1 S1) -> Pb b -> b <= a < b + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
(forall b, In b (list_blocks l) -> Pb b) ->
akept W1 m1 W2 m2 (alist_fp LA l).
Proof.
intros ly1 S1 hp1 W1 W2 m1 md1 m2 LA l lines Pb HAR HL KH KB HP rr Hr a Ha.
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [apply KH; exact Ha|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
  destruct HL as (_ & _ & _ & _ & (Hn & Hcap) & [(Hc & _) | (Hc & Hin & Hj & _)] & _); [apply Z.eqb_neq in Ec; lia|].
  pose proof (l3_req_ge (AREC * hl_cap l) ltac:(unfold AREC; lia)) as Hrq.
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. rewrite Ec. left. reflexivity.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, l3_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul in Ha.
    change (Z.of_nat 16) with 16 in Ha. unfold hl_n in Hn, Hj. unfold AREC in *. lia.
- apply in_map_iff in Hr as (x & <- & Hx).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF x Hx) as (Hin & _).
  pose proof (l3_req_ge (Z.of_nat (length (snd x)) + 1) ltac:(lia)) as Hrq.
  apply (KB _ _ a Hin).
  + apply HP. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hx.
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha. lia.
Qed.
(* W3's cnl_src_set (W_check_no_loss.v), for the held list: the source with its held list replaced *)
Lemma l3_src_held : forall ly1 S1 (W1 : world SEGS) mem1 ly2 S2 (W2 : world SEGS) mem2 HA1 h1 l l',
asrc_at B ly1 S1 W1 mem1 HA1 (CheckRep.set_held h1 l) ->
(forall x, HA1 <= x < HA1 + 80 -> abyte_kept W1 mem1 W2 mem2 x) ->
akept W1 mem1 W2 mem2 (gfp (hs_partial h1) (bzs (hs_pjunk h1)) ::
  alist_fp (HA1 + 16) (hs_pending h1) ++ alist_fp (HA1 + 64) (hs_expected h1)) ->
(forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks (hs_expected h1)) ->
  In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 mem2 (HA1 + 80) l' true ->
NoDup (hs_blocks (CheckRep.set_held h1 l')) ->
asrc_at B ly2 S2 W2 mem2 HA1 (CheckRep.set_held h1 l').
Proof.
intros ly1 S1 W1 mem1 ly2 S2 W2 mem2 HA1 h1 l l'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) KH HK HB HE ND.
assert (Hvm : forall a n v, HA1 <= a -> a + Z.of_nat n <= HA1 + 80 ->
  val_mem SEGS (arm W1 mem1) a n v -> val_mem SEGS (arm W2 mem2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 mem1); [intros x Hx; apply KH; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. unfold ASRC in Hi.
  destruct (Z_lt_le_dec i 80) as [Hi1 | Hi1]; [apply (proj2 (KH (HA1 + i) ltac:(lia))); exact (H5 i ltac:(unfold ASRC; lia))|].
  destruct HE as (_ & _ & _ & Hw & _). replace (HA1 + i) with (HA1 + 80 + (i - 80)) by lia. exact (Hw (i - 80) ltac:(lia)). }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 mem1); [exact H10
  | eapply akept_sub; [exact HK | intros rr Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 mem1); [intros x Hx; apply (HK (gfp (hs_partial h1) (bzs (hs_pjunk h1))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [apply (alist_at_kept B ly1 S1 W1 mem1); [exact H22
  | eapply akept_sub; [exact HK | intros rr Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb]|].
split; [exact HE|].
exact ND.
Qed.

(* ------------------------------------------------------------------ the loop *)
Section loop.
(* the entry of check_shape_ends (cshe_spec's names), and what the loop keeps needing of it *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 O OUT : Z) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past this call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_post_x B PST ARx MT RP G regs0 ly S hp W mem md XO AT HA h P A0 0 ob kr).
Local Notation WANT := (CheckRep.want_of P (hl_recs (hs_held h))).
Local Notation LIT := (VAL A_lit_end5).
Local Notation PLEN := (Z.of_nat (length P)).
Hypothesis HPRE : afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs0 mem md ch.
Hypothesis HX0 : 0 <= XO.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HAT8 : AT mod 8 = 0.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HOlen : Z.of_nat (length ob) = O.
Hypothesis HO40 : O <= 2 ^ 40.
Hypothesis HO32 : 0 < O -> O < 2 ^ 32.
Hypothesis HOM : amem_range OUT (O + 8).
Hypothesis HOB : ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h).
Hypothesis HA0 : 0 <= A0 <= O.
Hypothesis HROM0 : rom_view SEGS W mem.
(* the source g_s[j]: image bytes the allocator does not own, not errno, not read-only (cshe_spec's cshe_home for
   them, at its image clause; the stack and fake-frame clauses do not hold of g_s) *)
Hypothesis HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a.
(* and apart from the three other globals the loop keeps: g_gone, g_nout, g_out (objects of cshe_ro) *)
Hypothesis HAg : forall a, HA <= a < HA + ASRC -> ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\
  ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= a < VAL A_g_out + 8).
(* the prefix P at PF (cshe_spec's PF facts): a read-only literal (.str.2, 0x20ee0, at the remove arm and the exit) or
   a local of one of the entry's fake frames (prefix[48], at the gone arm); HPHOME is cshe_spec's premise for it *)
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPHOME : (forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
(* P's shadow at the entry (cshe_spec's premise) and the entry's source (its held blocks are the walk's free
   footprint): what W_check_shape_ends.v's cshe_P_at carries P's facts along the journal with *)
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.
(* .str.4 " end" (A_lit_end5), the bcmp operand: its bytes (cshe_spec's garr8 premise); read-only by HEND5R *)
Hypothesis HLG : garr8 SEGS (arm W mem) LIT (bzs END5).

Lemma l3_lit_bytes : forall k, 0 <= k < 4 ->
aview SEGS (w_H W) mem (LIT + k) = Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0))).
Proof.
intros k Hk. assert (Hk' : (Z.to_nat k < length (bzs END5))%nat) by (cbn; lia).
pose proof (garr8_mbyte SEGS (arm W mem) LIT _ (Z.to_nat k) HLG Hk') as Hm.
unfold aview. replace (LIT + k) with (LIT + Z.of_nat (Z.to_nat k)) by lia. unfold arm in Hm. rewrite Hm.
cbn [option_map]. f_equal.
assert (Hc : (Z.to_nat k = 0 \/ Z.to_nat k = 1 \/ Z.to_nat k = 2 \/ Z.to_nat k = 3)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.
(* errno's four bytes are image bytes (the runtime's api_env), none of them a byte of g_s[j] *)
Lemma l3_errno_img : forall q, 0 <= q < 4 -> in_img SEGS (as_errno B + q).
Proof. intros q Hq. pose proof (pal_env B TL) as (_ & HeImg & _). apply HeImg. lia. Qed.
Lemma l3_errno_off : forall q, 0 <= q < 4 -> ~ (HA <= as_errno B + q < HA + ASRC).
Proof. intros q Hq Hc. destruct (HAimg (as_errno B + q) Hc) as (_ & _ & He & _). lia. Qed.
(* errno's view is the entry's (cshe_post's conjunct) *)
Definition l3_err (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j).

(* the invariant at the head, w turns left (the plain proof's cse_inv, old ASan proof 23f70bc959c
   lib/A/Prog/check_shape_ends.v:503-521, over this walk's journal) *)
Definition l3_regs (regs1 : bvmap 5 word) (w : nat) : Prop :=
getr regs1 2 = w64 (sp0 - 144) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 8 = w64 (HA + 88) /\ getr regs1 9 = w64 PF /\ getr regs1 18 = w64 (HA + 80) /\ getr regs1 19 = w64 AT /\
getr regs1 20 = w64 LIT /\ getr regs1 24 = w64 4 /\ getr regs1 25 = w64 SB /\
getr regs1 26 = w64 ((HA + 80) / 8 + SB) /\ getr regs1 27 = w64 (Z.of_nat w + 1).
Definition l3_inv (w : nat) (ds : list (Z * list byte)) (c : Z) (W1 : world SEGS) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist),
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT = Some (rsF, ds ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\
val_mem SEGS (arm W1 mem1) AT 8 (A0 + c) /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W1 mem1) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W1 mem1) (VAL A_g_out) 8 OUT /\
ob_at W1 mem1 OUT ob /\ (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
(* the room round: one free per record left past the caller's kr, and the live counts, which only fall *)
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W1 mem1 /\ cshe_saved W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
l3_regs regs1 w /\ l3_err W1 mem1.

(* the second state of a turn, 0x85614 (after has_prefix, a0 = &l->v[i]): the line l is read (the cell `at` moved past it),
   its record i found; nothing of the allocator changed yet *)
Definition l3_mid (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist),
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk /\
asrc_at B ly1 S1 W2 mem2 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
(i < length (hl_recs H1))%nat /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1))
   (skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, (ds ++ [nth i (hl_recs H1) (0, [])]) ++ dsF, (c + Z.of_nat (length l) + 1) + cF)) /\
0 <= c /\ A0 + (c + Z.of_nat (length l) + 1) <= O /\
val_mem SEGS (arm W2 mem2) AT 8 (A0 + (c + Z.of_nat (length l) + 1)) /\ val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W2 mem2) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W2 mem2) (VAL A_g_out) 8 OUT /\
ob_at W2 mem2 OUT ob /\ (exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W2 mem2 /\ cshe_saved W2 mem2 sp0 regs0 /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
l3_regs regs2 (Datatypes.S w) /\ getr regs2 21 = w64 (Z.of_nat i) /\ getr regs2 10 = w64 (hl_v H1 + 16 * Z.of_nat i) /\
l3_err W2 mem2.

(* the state at 0x855d0 (after bcmp): the line l at the stream's A0 + c is read, `at` moved past it, its stem
   found at record i (the model's find_text), the line passed the length and " end" checks *)
Definition l3_ab (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (d' : list byte),
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk /\
asrc_at B ly1 S1 W2 mem2 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
skipn (Z.to_nat (A0 + c)) ob = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ l3_ok P l = true /\
CheckRep.find_text (firstn (length l - 4) l) (hl_recs H1) = Some i /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w <> None /\
(forall rsF dsR cR, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w = Some (rsF, dsR, cR) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, ds ++ nth i (hl_recs H1) (0, []) :: dsR, c + (Z.of_nat (length l) + 1 + cR))) /\
0 <= c /\ A0 + c + Z.of_nat (length l) + 1 <= O /\
val_mem SEGS (arm W2 mem2) AT 8 (A0 + c + Z.of_nat (length l) + 1) /\ val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W2 mem2) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W2 mem2) (VAL A_g_out) 8 OUT /\
ob_at W2 mem2 OUT ob /\ (exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W2 mem2 /\ cshe_saved W2 mem2 sp0 regs0 /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 24) 8 (Z.of_nat (length l)) /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 32) 8 (OUT + (A0 + c)) /\
l3_regs regs2 (Datatypes.S w) /\ getr regs2 10 = w64 0 /\ getr regs2 22 = w64 (Z.of_nat (length l)) /\
getr regs2 23 = w64 (OUT + (A0 + c)) /\ l3_err W2 mem2.

(* the first part of a turn: next_line, the length check and bcmp of " end", from the head to 0x855d0 *)
Lemma l3_A1 : forall w ds c W1 regs1 mem1 md1, l3_inv (Datatypes.S w) ds c W1 regs1 mem1 md1 ->
(forall l i W2 regs2 mem2 md2, l3_ab w ds c l i W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3b)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c W1 regs1 mem1 md1 HI HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & hp1 & kk & H1 & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & HRUN & HREL & Hc0 & HcO & MAT & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & HREGS & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
(* the model: this turn's line l, its record i *)
assert (Hex : exists rsF dsF cF,
  CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) = Some (rsF, dsF, cF)).
{ destruct (CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w)) as [[[x y] z]|];
  [exists x, y, z; reflexivity | exfalso; exact (HRUN eq_refl)]. }
destruct Hex as (rsF & dsF & cF & ER).
destruct (l3_ends_S P _ _ w rsF dsF cF ER) as (l & d' & i & dsR & cR & Ed & Hnz & Hok & Hft & HrR & EdsF & EcF).
destruct (l3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold l3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply l3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (HAl : A0 + c + Z.of_nat (length l) + 1 <= O) by lia.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (Hw26 : (Datatypes.S w <= length (hl_recs H1))%nat) by (apply (l3_ends_len P _ _ (skipn (Z.to_nat (A0 + c)) ob)); rewrite ER; discriminate).
assert (HN0 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cshe_l3_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l)) (Z.of_nat (Datatypes.S w))
  R2 R8 R18 R24 R25 R26 R27 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' HlnR Hlen32 Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
assert (V18 : base_val E (Some 18%nat) = HA + 80).
{ cbn [base_val]. rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl), R18.
  apply unsigned_lit_small. unfold ASRC, kLowMemEnd in HAhi. lia. }
paj_run_to_tok_x RUNTOx HS HJ0 SHOK Bspan AF_fr_next_line.
{ cbv [ss_mem ss_cshe_l3 cshe_l3_fr cshe_l3_hd].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (OUT + (A0 + c))) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length l))) by exact (EX 3%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
(* the run to the call wrote nothing but l->n's window, which it did not store to either *)
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. apply (aview_kept_out E (ss_mem ss_cshe_l3) (w_H W1) mem1 (ms_mem ms) HFr a Ha).
  intros (rg & Hin & Hrg). cbn [ss_mem ss_cshe_l3 In] in Hin. unfold cshe_l3_fr, cshe_l3_hd in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg; [lia|]. rewrite V18 in Hrg. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREn : afn_pre_x SEGS B ARx NL_STK ly1 S1 hp1 W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_at SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 (ms_mem ms) mdc kk
    (ms_regs ms) NL_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold NL_STK, NL_FRAME, ESTACK. lia.
  - unfold NL_STK, NL_FRAME, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
assert (HO0 : 0 < O) by lia.
assert (HOw : forall a, OUT <= a < OUT + CO -> ~ (sp0 - CSHE_STK <= a < sp0 + XO)) by (intros a Ha; lia).
destruct (Z.mod_divide (sp0 - 144) 16 ltac:(lia)) as [Hd16 _]. destruct (Hd16 HSPa) as [q16 Hq16]. clear Hd16.
eapply SRr_bind.
{ apply (NL W1 ly1 S1 hp1 (ms_regs ms) (ms_mem ms) mdc [] (XO + 144) AT (sp0 - 144 + 32) (sp0 - 144 + 24)
    (A0 + c) O OUT ob HPREn).
  - lia.
  - rewrite Zplus_mod, HX16. reflexivity.
  - rewrite Usp1, Etop. lia.
  - rewrite Usp1. intros a Ha. apply HPRi. rewrite WS. lia.
  - rewrite Q10, E19. reflexivity.
  - rewrite Q11, Usp. reflexivity.
  - rewrite Q12, Usp. reflexivity.
  - exact HAT8.
  - replace (sp0 - 144 + 32) with ((2 * q16 + 4) * 8) by lia. apply Z_mod_mult.
  - replace (sp0 - 144 + 24) with ((2 * q16 + 3) * 8) by lia. apply Z_mod_mult.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - lia.
  - lia.
  - lia.
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [intros k Hk; apply KEEPr; lia | exact MAT].
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact MNO].
    intros k Hk. pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
    apply KEEPr; [lia|]. intros Hc. destruct (HAg (VAL A_g_nout + k) ltac:(unfold ASRC; lia)) as (_ & Hn & _). apply Hn. lia.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact MOUT].
    intros k Hk. pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
    apply KEEPr; [lia|]. intros Hc. destruct (HAg (VAL A_g_out + k) ltac:(unfold ASRC; lia)) as (_ & _ & Hn). apply Hn. lia.
  - exact HOlen.
  - intros k Hk. rewrite KEEPr; [exact (HOBt k Hk) | lia |].
    intros Hc. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))).
  - lia.
  - intros _. split; [lia|]. split; [lia|]. split; [exact (HO32 HO0)|]. intros a Ha. rewrite Usp1. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - intros _. split; [rewrite Ed; apply in_or_app; right; left; reflexivity|]. split; [exact HOM|].
    split; [apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia]|].
    split; [apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]|].
    intros a Hr. rewrite KEEPr; [exact (HROM a Hr) | |].
    + destruct Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
    + intros Hc. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
subst W2.
destruct HARM as [(HAeq & _) | (ln & HAlt & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
assert (Hln : ln = l).
{ destruct Hfl as (rest & Hsk & Hnz'). rewrite Ed in Hsk. destruct (l3_nul_unique l ln d' rest Hsk Hnz Hnz') as [-> _]. reflexivity. }
subst ln.
rewrite Usp1 in HJn, HFRn.
assert (HJc' : ajournal_gx_x SEGS B PST ARx G (XO + 144) (nl_cells AT (sp0 - 144 + 32) (sp0 - 144 + 24)) NL_STK (sp0 - 144) []
  ly1 S1 hp1 W1 (ms_mem ms) mdc [] ly1 S1 hp1 W1 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha) | exact HJn]. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W1 (ms_mem ms) mdc kk NL_STK (sp0 - 144) (XO + 144) (nl_cells AT (sp0 - 144 + 32) (sp0 - 144 + 24)) [] []
  ly1 S1 hp1 W1 mem2 md2 0 HJ0 HJc'
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
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HXOn; [lia|].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRn; [lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W1) (ms_mem ms) mem2 a); [intros Hp; exact (HPn a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; rewrite OLDa by lia; exact U18).
apply (st_ok_pi_add_region Ea _ _ cshe_l3_cells) in HS; [| reflexivity | | ].
2: { unfold region_ok, cshe_l3_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
  cbn [base_val]. rewrite UspA. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 144) 24 8 (SOff 35 0) (Z.of_nat (length l)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vlen2].
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 144) 32 8 (SOff 34 0) (OUT + (A0 + c)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vln2]. }
2: { apply all_disjoint_of_extents. unfold cshe_l3_cells, extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem]. rewrite V18a. cbn [base_val]. rewrite UspA.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. lia. }
assert (HAR2 : ARx ly1 S1 hp1 W1 mem2 md2) by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem2 md2 kk HJ2).
assert (F25 : ew Ea 25 = w64 SB) by (rewrite OLDa by lia; exact E25).
assert (F18 : ew Ea 18 = w64 (HA + 80)) by (rewrite OLDa by lia; exact E18).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite Q1.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. unfold cshe_l3_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
{ (* next_line returned 0: it found the line *)
  exfalso. rewrite branch_eq_U, (U_atom Ea 40 1 F40), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. unfold cshe_l3_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* the two runs since next_line wrote nothing but l->n's window *)
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha Hno.
  lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ =>
    rewrite (aview_kept_out _ _ _ _ _ Hf a Ha) end.
  - lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end.
  - intros (rg & Hin & Hrg).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U18a in Hrg; lia|]).
    destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
set (xb := OUT + (A0 + c) + Z.of_nat (length l) - 4).
assert (R10b : getr (ms_regs ms1) 10 = w64 xb).
{ rewrite T10, (OLDa 34%nat), (OLDa 35%nat) by lia. rewrite E34, E35. rewrite unsigned_lit_small by lia.
  rewrite YI08.alu64_add_lit. unfold w64, xb. f_equal. lia. }
assert (R11b : getr (ms_regs ms1) 11 = w64 LIT) by (rewrite T11, (OLDa 20%nat) by lia; exact E20).
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 144) by (unfold spZ; rewrite T2; exact UspA).
(* the rom view and the stream, carried to the call *)
assert (ROMK1 : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  assert (Hno : ~ (HA + 88 <= a < HA + 92)) by (intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr)).
  rewrite KEEP1 by lia. rewrite HFRn; [ | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
  - apply KEEPr; lia.
  - intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (HROM1 : rom_view SEGS W1 (ms_mem ms1)) by (intros a Hr; rewrite ROMK1 by exact Hr; exact (HROM a Hr)).
assert (ROMW : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W) mem a)
  by (intros a Hr; rewrite (HROM1 a Hr); symmetry; exact (HROM0 a Hr)).
assert (OBK1 : ob_at W1 (ms_mem ms1) OUT ob).
{ intros k Hk. rewrite KEEP1; [exact (Hob2 k Hk) | lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
assert (HAR3 : ARx ly1 S1 hp1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2))
  by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ2).
pose proof (pa_obj_img 31 ltac:(lia)) as HLR. change (A_OBJ 31) with A_lit_end5 in HLR.
assert (HLITr : forall k, 0 <= k < 4 -> aview SEGS (w_H W1) (ms_mem ms1) (LIT + k) =
  Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0)))).
{ intros k Hk. rewrite ROMW by (apply HEND5R; lia). exact (l3_lit_bytes k Hk). }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W1) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (OBK1 (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
eapply SRr_bind.
{ apply (aj_bcmp_gx_at_x B PST ARx LAWS (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms1) (ms_mem ms1) CSHE_STK sp0 FPc
    ly S hp W mem md [] ly1 S1 hp1 _ kk xb LIT 4 (-144) (Z_to_bv 64 (BASE + 13028)) HG HX16 HJ2 R10b R11b T12).
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
  - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia].
  - intros _. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia | lia].
  - exact (proj1 (HEND5S ly1 S1 hp1 W1 (ms_mem ms1) _ HAR3)).
  - intros Hp4. exact (proj2 (HEND5S ly1 S1 hp1 W1 (ms_mem ms1) _ HAR3) Hp4). }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros k Hk. unfold xb. replace (OUT + (A0 + c) + Z.of_nat (length l) - 4 + k) with
    (OUT + (A0 + c) + (Z.of_nat (length l) - 4 + k)) by lia.
  rewrite HLINE by lia. rewrite HLITr by lia. do 2 f_equal. rewrite <- Hend, l3_nth_skipn. f_equal. lia. }
(* what the turn kept so far, from the head's memory mem1: every byte outside this function's stack window and
   l->n, and presence *)
assert (KEEPc3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK <= a < sp0 + XO) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hw Hn. rewrite Hfr3; [| exact Ha | rewrite WS in Hw; unfold ESTACK; lia].
  rewrite KEEP1 by assumption. rewrite HFRn; [ | exact Ha | rewrite WS in Hw; unfold NL_STK, NL_FRAME, ESTACK; lia |].
  - apply KEEPr; assumption.
  - intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (PRES3 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem3 a).
{ intros a Hp. apply Hpres3.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPn. apply (apresent_grows _ _ _ _ HG0). exact Hp. }
assert (ROMK3 : forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite Hfr3; [exact (ROMW a Hr) | lia | unfold ESTACK; lia]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W1) (ms_mem ms1) mem3 a); [intros Hp; exact (Hpres3 a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F56 : ew Eb 56 = w64 0) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv; exact Hv0).
clear HEb.
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
(* ---- 0x855d0: the state l3_ab *)
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
prreg HS (25%bv : bv 5) N25. prreg HS (27%bv : bv 5) N27.
prreg_raw HS (26%bv : bv 5) N26.
(* l->n's value is still n (the region based at s2, chunk 8) *)
pose proof (st_ok_pi_region_nth Eb _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg2 U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnH3.
assert (FRK3 : forall a, sp0 - 144 <= a < sp0 + XO -> ~ (sp0 - 144 + 24 <= a < sp0 - 144 + 40) -> ~ (AT <= a < AT + 8) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hc1 Hc2. rewrite Hfr3 by (unfold ESTACK; lia). rewrite KEEP1 by lia. rewrite HXOn by
    (try lia; intros (rg & Hin & Hrg); cbn [nl_cells In] in Hin; destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia).
  apply KEEPr; lia. }
assert (CK3 : forall a, sp0 - 144 <= a < sp0 + XO -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha. rewrite Hfr3 by (unfold ESTACK; lia). apply KEEP1; lia. }
replace (BASE + 13028) with (BASE + A_cshe_l3b) by (unfold A_cshe_l3b, AF_fr_check_shape_ends; lia).
apply (HKont l i W1 regs3 mem3 md3).
exists ly1, S1, hp1, kk, H1, d'.
split; [exact HJ3|].
split.
{ apply (l3_src_step ly1 S1 md1 W1 W1 mem1 mem3 HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha Hw Hn. apply KEEPc3; assumption.
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W1) (w_H W1) mem1 mem3 (HA + 80 + 8) 4 (hl_n H1) k MnH MnH3). cbn. lia.
  - exact PRES3.
  - apply wle_refl. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split; [exact Ed|]. split; [exact Hnz|]. split; [exact Hok|]. split; [exact Hft|].
split; [rewrite HrR; discriminate|].
split.
{ intros rsF' dsR' cR' Hx. apply HREL. rewrite Ed. exact (l3_ends_step P (hl_recs H1) l d' i w rsF' dsR' cR' Hnz Hok Hft Hx). }
split; [exact Hc0|]. split; [exact HAl|].
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [intros k Hk'; apply CK3; cbn in Hk'; lia|].
  replace (A0 + c + Z.of_nat (length l) + 1) with (A0 + c + Z.of_nat (length l) + 1) by lia. exact Vat2. }
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
pose proof (proj1 (HGR (VAL A_g_gone) ltac:(unfold inG, cshe_ro; apply Exists_exists; exists (VAL A_g_gone, 1); split; [left; reflexivity | unfold in_zr; cbn; lia]))) as Igg.
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MG].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_gone + k) ltac:(unfold ASRC; lia)) as (Hn1x & _). apply Hn1x. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MNO].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_nout + k) ltac:(unfold ASRC; lia)) as (_ & Hn1x & _). apply Hn1x. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MOUT].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_out + k) ltac:(unfold ASRC; lia)) as (_ & _ & Hn1x). apply Hn1x. lia. }
split.
{ intros k Hk'. rewrite KEEPc3; [exact (HOBt k Hk') | lia | rewrite WS; lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
split; [exists CO; split; [exact HCO | exact HOin]|].
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split; [exact HRMr|]. split; [exact HCNTr|].
split; [intros a Hr; rewrite (ROMK3 a Hr); exact (HROM0 a Hr)|].
split.
{ apply (l3_saved_kept W1 W1 mem1 mem3 sp0 regs0); [|exact HSAV].
  intros a Ha. apply FRK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact M16]. intros k Hk'. cbn in Hk'. apply FRK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [|exact Vlen2]. intros k Hk'. cbn in Hk'. apply CK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [|exact Vln2]. intros k Hk'. cbn in Hk'. apply CK3; lia. }
split.
{ unfold l3_regs.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split; [|rewrite N27, OLDba by lia; exact E27].
  rewrite N26. unfold w64, cshe_l3_shv. apply bv_eq.
  change (bv_unsigned (sv_denot Eb (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
    with (U Eb (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
  rewrite (l3_U_sh Eb 18 0 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | exact E25 | lia]).
  rewrite Z.add_0_r. assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite unsigned_lit_small; [reflexivity | unfold SB; lia]. }
split; [rewrite N10, F56; reflexivity|].
split; [rewrite N22, OLDba by lia; exact E35|].
split; [rewrite N23, OLDba by lia; exact E34|].
intros q Hq. pose proof (pa_img_range _ (l3_errno_img q Hq)) as HeR.
rewrite KEEPc3; [exact (HERR q Hq) | lia | rewrite WS; lia | intros Hc; apply (l3_errno_off q Hq); unfold ASRC; lia].
Qed.

(* the second part of a turn: list_find of the line's stem, has_prefix of the line, the shadow check of l->v and
   a0 = &l->v[i], from 0x855d0 to 0x85614 *)
Lemma l3_A2 : forall w ds c l i W2 regs2 mem2 md2, l3_ab w ds c l i W2 regs2 mem2 md2 ->
(forall W3 regs3 mem3 md3, l3_mid w ds c l i W3 regs3 mem3 md3 ->
  SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + A_cshe_l3s)) mem3 (seg_rom SEGS)) md3) Post) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3b)) mem2 (seg_rom SEGS)) md2) Post.
Proof.
intros w ds c l i W2 regs2 mem2 md2 HAB HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAB as (ly1 & S1 & hp1 & kk & H1 & d' & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & Ed & Hnz & Hok & Hft & HRUN & HREL &
  Hc0 & HAl & MAT & MG & MNO & MOUT & HOBt & (CO & HCO & HOin) & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & M24 & M32 &
  HREGS & R10 & R22 & R23 & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
destruct (l3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold l3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply l3_leqb in Hend.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W2 mem2 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W2 mem2 md2 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (l3_ends_len P _ _ d'); exact HRUN).
rewrite (l3_drop_len _ _ Hi) in Hw26.
assert (HN0 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 mem2 md2 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cshe_l3b_state W2 regs2 mem2 (sp0 - 144) HA (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l)) (Z.of_nat (Datatypes.S w))
  R2 R8 R18 R24 R25 R26 R27 R10 R22 R23 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' HlnR Hlen32 Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) M24 M32) as [HS SHOK].
remember (Eimg (Ereg regs2 (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs2 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 (Z.of_nat (length l))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (OUT + (A0 + c))) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
paj_run_to_tok_x RUNTOx HS HJ0 SHOK Bspan AF_fr_list_find.
{ cbv [ss_mem ss_cshe_l3b cshe_l3b_cells cshe_l3_fr cshe_l3_hd].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms)) |- _ => l3_wkeep Hf U18 end. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
(* l->n is still n *)
pose proof (st_ok_pi_region_nth E _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region E _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg2 U18 ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as MnHr.
assert (PRESr : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
assert (HSRCr : asrc_at B ly1 S1 W2 (ms_mem ms) HA (CheckRep.set_held h H1)).
{ apply (l3_src_step ly1 S1 md2 W2 W2 mem2 (ms_mem ms) HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha _ Hn. apply KEEPr; assumption.
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W2) (w_H W2) mem2 (ms_mem ms) (HA + 80 + 8) 4 (hl_n H1) k MnH MnHr). cbn. lia.
  - exact PRESr.
  - apply wle_refl. }
pose proof HSRCr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAHr & _).
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
assert (HAR1m : ARx ly1 S1 hp1 W2 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREf : afn_pre_x SEGS B ARx LFIND_STK ly1 S1 hp1 W2 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_at SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W2 (ms_mem ms) mdc kk
    (ms_regs ms) LFIND_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KEEPr; cycle 1; [lia | |].
  - intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + (A0 + c) + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + (A0 + c) + k) ltac:(unfold ASRC; lia))).
  - replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (HOBt (A0 + c + k)) by lia.
    do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
    apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
set (sb := firstn (length l - 4) l).
assert (Hsb : length sb = (length l - 4)%nat) by (unfold sb; rewrite length_firstn; lia).
eapply SRr_bind.
{ apply (LFIND W2 ly1 S1 hp1 (ms_regs ms) (ms_mem ms) mdc [] (HA + 80) H1 true (OUT + (A0 + c)) sb HPREf).
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11, E23. reflexivity.
  - rewrite Q12, E22, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hsb. lia.
  - exact HAHr.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold kLowMemEnd. lia.
  - eapply range_addressable_sub; [exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 (ms_mem ms) mdc (HA + 64) 32 HAR1m Hzs) | lia | lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - lia.
  - rewrite Hsb. lia.
  - rewrite Hsb. lia.
  - intros k Hk. rewrite Hsb in Hk. rewrite HLINE by lia. do 2 f_equal. unfold sb. rewrite nth_firstn.
    destruct (Z.to_nat k <? length l - 4)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite Hsb. unfold amem_range in HOM |- *. lia.
  - rewrite Hsb. eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia].
  - rewrite Hsb. intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJf & HPf & HPRf & HFRf & HRES).
assert (HRESi : getr regs3 10 = w64 (Z.of_nat i)).
{ destruct HRES as [(j & (Hj1 & Hj2 & Hj3) & Hr10) | (Hnf & _)].
  - rewrite Hr10. do 2 f_equal. apply (l3_first_unique (hl_recs H1) sb j i Hj2 Hj3 Hti Hfirst).
  - exfalso. exact (Hnf i Hi Hti). }
rewrite Usp1 in HJf, HFRf.
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W2 (ms_mem ms) mdc kk LFIND_STK (sp0 - 144) 0 [] [] [] ly1 S1 hp1 W2 mem3 md3 0 HJ0 HJf
  ltac:(rewrite WS; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs3 (mrestrict (w_H W2) mem3) HPf [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3b_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W2) (ms_mem ms) mem3 a); [intros Hp; exact (HPRf a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 (Z.of_nat i)) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact HRESi).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (HAR2 : ARx ly1 S1 hp1 W2 mem3 md3) by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem3 md3 kk HJ2).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 mem3 md3 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB) by (rewrite ?OLDa by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80)) by (rewrite ?OLDa by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite Q1.
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BR HS SHOK2 Bspan.
{ (* bltz: list_find found the record, i >= 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit_small; lia).
  cbn [sv_denot] in Hc. rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. unfold w64 in Hc.
  rewrite bv_signed_small in Hc by (rewrite Hu; lia). rewrite Hu in Hc. change (bv_signed (Z_to_bv 64 0)) with 0 in Hc. lia. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ2 SHOK2 Bspan AF_fr_has_prefix.
{ cbn [ss_mem add_cond]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 144) by (unfold spZ; rewrite P2; exact UspA).
(* what list_find and the runs kept of mem2 *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hn.
  transitivity (aview SEGS (w_H W2) (ms_mem ms0) a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => l3_wkeep Hf U18a end. }
  transitivity (aview SEGS (w_H W2) mem3 a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end. }
  rewrite HFRf by assumption. apply KEEPr; assumption. }
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KEEP2; [rewrite (HROM a Hr); symmetry; exact (HROM0 a Hr) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
assert (HLINE2 : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KEEP2; cycle 1; [lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia | |].
  - intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + (A0 + c) + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + (A0 + c) + k) ltac:(unfold ASRC; lia))).
  - replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (HOBt (A0 + c + k)) by lia.
    do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
    apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
(* the stack's bounds, for P's distance from has_prefix's scratch below *)
pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & Hceil0 & Hslo0 & _) & _).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdh := mdq) in * end.
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 _ _ kk HJ2)
  as (memS2 & HJi2 & HgS2).
assert (HAR3 : ARx ly1 S1 hp1 W2 (ms_mem ms1) mdh) by exact (proj1 HJi2).
assert (HPREh : afn_pre_x SEGS B ARx HP_STK ly1 S1 hp1 W2 (ms_regs ms1) (ms_mem ms1) mdh []).
{ eapply (afn_pre_x_at SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS2 md [] ly1 S1 hp1 W2 (ms_mem ms1) mdh kk
    (ms_regs ms1) HP_STK (- 144 - XO) [] HJi2).
  - rewrite Usp2. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
  - rewrite P3, OLDa, E3 by lia. exact Hgp0.
  - rewrite P4, OLDa, E4 by lia. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite P8, U18a. rewrite unsigned_lit_small by lia. lia. }
(* P's bytes, shadow and bound at the call, in both homes (W_check_shape_ends.v cshe_P_at) *)
destruct (cshe_P_at_x B PST ARx G LAWS FRMF HG XO [(AT, AT + 8)] CSHE_STK sp0 ly S hp W mem md HA h PF PLEN (proj1 HPRE) HSRC0
  ltac:(lia) HPRA HPHOME ly1 S1 hp1 W2 (ms_mem ms1) mdh kk HJ2 ROMK) as (PK & HRAP & HHVP & PLOW).
eapply SRr_bind.
{ apply (W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP W2 ly1 S1 hp1 (ms_regs ms1) (ms_mem ms1) mdh []
    (OUT + (A0 + c)) (Z.of_nat (length l)) PF PLEN HPREh).
  - rewrite P10, OLDa, E23 by lia. reflexivity.
  - rewrite P11, OLDa, E22 by lia. reflexivity.
  - rewrite P12, OLDa, E9 by lia. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * rewrite PK by lia. exact (HPB k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. rewrite PK by lia. exact HPN.
  - intros a Ha. rewrite PK by lia. apply HPV. lia.
  - unfold hp_off. rewrite Usp2. intros a Ha. pose proof (PLOW a ltac:(lia)).
    unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact HHVP.
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia. apply HPV. lia.
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE2 by lia. discriminate.
    + unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
    + unfold amem_range in HOM |- *. lia.
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l3_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) HHVP). }
cbv beta. intros W4 c4 Hwle4 (regs4 & mem4 & md4 & -> & HJh & HPh & HPRh & HFRh & HRESh).
assert (Hpref : PLEN <= Z.of_nat (length l) /\ hp_prefix_of W2 (ms_mem ms1) (OUT + (A0 + c)) PF PLEN).
{ unfold CheckRep.prefixb in Hpre. apply andb_prop in Hpre as [Hp1 Hp2]. apply Nat.leb_le in Hp1. apply l3_leqb in Hp2.
  split; [lia|]. intros k Hk. rewrite HLINE2 by lia. rewrite PK by lia. rewrite (HPB k Hk).
  do 2 f_equal. rewrite <- Hp2. rewrite nth_firstn. destruct (Z.to_nat k <? length P)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia]. }
assert (Hr10h : getr regs4 10 = w64 1).
{ destruct HRESh as [(_ & _ & Hr) | (Hnp & _)]; [exact Hr | exfalso; exact (Hnp (proj1 Hpref) (proj2 Hpref))]. }
rewrite Usp2 in HJh, HFRh.
assert (HJc' : ajournal_gx_x SEGS B PST ARx G 0 [] HP_STK (sp0 - 144) [] ly1 S1 hp1 W2 (ms_mem ms1) mdh [] ly1 S1 hp1 W4 mem4 md4 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|]. apply ajournal_gx_nil_x. exact HJh. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W2 (ms_mem ms1) mdh kk HP_STK (sp0 - 144) 0 [] [] [] ly1 S1 hp1 W4 mem4 md4 0 HJ2 HJc'
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_r in HJ3.
jafter_call_keep_pi HS 52%nat regs4 (mrestrict (w_H W4) mem4) HPh [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3b_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha Hw. apply (l3_writable_kept_w W2 W4 (ms_mem ms1) mem4 a); [intros Hp; exact (HPRh a Hp) | exact Hwle4 | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F56 : ew Eb 56 = w64 1) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hr10h).
clear HEb.
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (HAR4 : ARx ly1 S1 hp1 W4 mem4 md4) by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W4 mem4 md4 kk HJ3).
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (SHOK3 : sh_ok SEGS Bx1 cshe_l3_SH Eb (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W4 mem4 md4 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB) by (rewrite ?OLDba by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite P1.
paj_run_tok_x RUNx HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNx BR HS SHOK3 Bspan.
{ exfalso. rewrite branch_eq_U, (U_atom Eb 56 1 F56), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan A_cshe_l3s.
{ cbn [ss_mem add_cond]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* ---- 0x85614: the state l3_mid *)
assert (KEEPall : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W4) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hn.
  transitivity (aview SEGS (w_H W4) (ms_mem ms2) a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem ms3)) |- _ => l3_wkeep Hf U18b end. }
  transitivity (aview SEGS (w_H W4) mem4 a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem4) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
  rewrite HFRh by (try exact Ha; unfold HP_STK, LFIND_STK, LFIND_FRAME, ESTACK in *; lia). apply KEEP2; assumption. }
assert (PRESall : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W4) (ms_mem ms3) a).
{ intros a Hp.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem ms3)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem4) (mrestrict _ (ms_mem ms2)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPRh.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPRf. exact (apresent_grows _ _ _ _ HG0 Hp). }
pose proof (st_ok_pi_region_nth Eb _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg3. cbn [ms_mem restrict] in HRg3.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg3 U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnH4.
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20. prreg HS (21%bv : bv 5) N21. prreg HS (24%bv : bv 5) N24.
prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
replace (BASE + 13096) with (BASE + A_cshe_l3s) by (unfold A_cshe_l3s, AF_fr_check_shape_ends; lia).
apply (HKont W4 (ms_regs ms3) (ms_mem ms3) _).
exists ly1, S1, hp1, kk, H1.
split; [exact HJ3|].
split.
{ apply (l3_src_step ly1 S1 md2 W2 W4 mem2 (ms_mem ms3) HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha Hw Hn. apply KEEPall; [exact Ha | rewrite WS in Hw; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia | exact Hn].
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W2) (w_H W4) mem2 (ms_mem ms3) (HA + 80 + 8) 4 (hl_n H1) k MnH MnH4). cbn. lia.
  - exact PRESall.
  - exact Hwle4. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split; [exact Hi|].
assert (Esk : skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob = d').
{ replace (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) with (Z.to_nat (A0 + c) + length l + 1)%nat by lia.
  exact (l3_skip_line ob l d' (Z.to_nat (A0 + c)) Ed). }
rewrite Esk.
split; [exact HRUN|].
split.
{ intros rsF dsF cF Hx. rewrite (HREL rsF dsF cF Hx). rewrite <- app_assoc. cbn [app]. f_equal. f_equal. lia. }
split; [lia|]. split; [lia|].
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
assert (KV : forall x n v, 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
  (forall a, x <= a < x + Z.of_nat n -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) /\ ~ (HA + 88 <= a < HA + 92)) ->
  val_mem SEGS (arm W2 mem2) x n v -> val_mem SEGS (arm W4 (ms_mem ms3)) x n v).
{ intros x n v Hx0 Hx1 Hx2 Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W4) mem2 (ms_mem ms3)); [|exact Hv].
  intros k Hk. destruct (Hx2 (x + k) ltac:(lia)) as [Hw Hn]. apply KEEPall; [lia | exact Hw | exact Hn]. }
split.
{ replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + c + Z.of_nat (length l) + 1) by lia.
  apply KV; [lia | lia | intros a Ha; split; lia | exact MAT]. }
split.
{ apply KV; [lia | lia | | exact MG]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (Hn1x & _). apply Hn1x. lia. }
split.
{ apply KV; [lia | lia | | exact MNO]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & Hn1x & _). apply Hn1x. lia. }
split.
{ apply KV; [lia | lia | | exact MOUT]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & _ & Hn1x). apply Hn1x. lia. }
split.
{ intros k Hk'. rewrite KEEPall; [exact (HOBt k Hk') | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
split; [exists CO; split; [exact HCO | exact HOin]|].
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split; [exact HRMr|]. split; [exact HCNTr|].
split.
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KEEPall; [exact (HROM a Hr) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
split.
{ apply (l3_saved_kept W2 W4 mem2 (ms_mem ms3) sp0 regs0); [|exact HSAV].
  intros a Ha. apply KEEPall; lia. }
split.
{ apply KV; [lia | lia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; lia | exact M16]. }
split.
{ unfold l3_regs.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split; [|rewrite N27, OLDba by lia; exact E27].
  rewrite N26, (OLDba 18%nat), (OLDba 25%nat) by lia. rewrite E18, E25. unfold w64.
  rewrite l3_srl3 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
split.
{ rewrite N21. rewrite OLDb by lia. exact F40. }
rewrite N10, (OLDba 32%nat) by lia. rewrite E32. rewrite OLDb by lia. rewrite F40. unfold w64.
assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
split; [rewrite l3_sll4 by lia; rewrite YI08.alu64_add_lit; f_equal; lia|].
intros q Hq. pose proof (pa_img_range _ (l3_errno_img q Hq)) as HeR.
rewrite KEEPall; [exact (HERR q Hq) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
intros Hc; apply (l3_errno_off q Hq); unfold ASRC; lia.
Qed.

(* the third part of a turn: the inlined list_drop (free(v[i].s), __asan_memmove of the records above, n - 1),
   s11 - 1 and the back-edge: to the head when turns are left, else to the epilogue and the post *)
Lemma l3_B : forall w ds c l i W1 regs1 mem1 md1, l3_mid w ds c l i W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2 ds' c', (1 <= w)%nat -> l3_inv w ds' c' W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3)) mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3s)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c l i W1 regs1 mem1 md1 HM HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HM as (ly1 & S1 & hp1 & kk & H1 & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & Hi & HRUN & HREL & Hc1 & HcO &
  MAT & MG & MNO & MOUT & HOBt & (CO & HCO & HOin) & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & HREGS & R21 & R10 & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (QA : ASTACK = 16384) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hi26 : Z.of_nat i < hl_n H1) by (unfold hl_n; lia).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by exact (l3_ends_len P _ _ _ HRUN).
rewrite (l3_drop_len _ _ Hi) in Hw26.
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
(* the record i: its block, and its text pointer in the vector's slot *)
set (r := nth i (hl_recs H1) (0, [])).
assert (HinR : In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly1 S1)).
{ rewrite Forall_forall in HFallH. exact (proj1 (HFallH r (nth_In _ _ Hi))). }
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HinR) as (R16 & R4096 & Rceil & Rapp & Rpres & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
destruct (l3_rec_fields ly1 S1 W1 mem1 (HA + 80) H1 true i HAH1 Hi) as (Ms0 & _).
fold r in Ms0. rewrite Z.mod_small in Ms0 by lia.
set (EA := hl_v H1 + 16 * Z.of_nat i).
assert (HEAlo : 4096 <= EA) by (unfold EA; lia).
assert (HEAhi : EA + 16 <= hl_v H1 + AREC * hl_cap H1) by (unfold EA, AREC, hl_n in *; lia).
assert (HEA16 : EA mod 16 = 0).
{ unfold EA. rewrite Zplus_mod, V16. replace (16 * Z.of_nat i) with (Z.of_nat i * 16) by lia. rewrite Z_mod_mult. reflexivity. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
destruct (cshe_l3s_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) (fst r) 4 (Z.of_nat (Datatypes.S w)) EA (Z.of_nat i)
  R2 R8 R18 R24 R25 R26 R27 R10 R21 HEAlo ltac:(unfold AREC in HEAhi; rewrite HreqV in Vceil; unfold AREC in Vceil; lia) HEA16
  ltac:(unfold hl_n in Hn26; lia) ltac:(unfold AREC in HEAhi; rewrite HreqV in Vceil; unfold AREC in Vceil; rewrite WS in Hslo; lia)
  ltac:(destruct (Z_lt_le_dec EA (HA + 96)) as [Hx|Hx]; [right|left; exact Hx];
        destruct (Z_lt_le_dec (EA + 16) (HA + 81)) as [Hy|Hy]; [lia|];
        exfalso; apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (Z.max EA (HA + 80)) HAR1 HvinH
          ltac:(rewrite HreqV; unfold AREC in *; lia));
        exact (proj1 (HAimg (Z.max EA (HA + 80)) ltac:(unfold ASRC; lia))))
  ltac:(rewrite HreqV in Vapp; unfold in_app, kLowShadowBeg, kHighMemBeg, AREC in Vapp |- *; unfold AREC in HEAhi; lia) HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' ltac:(rewrite HreqR in Rceil; lia) ltac:(lia) Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])
  Ms0
  ltac:(eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1));
        [exact HAR1 | exact HvinH | lia | rewrite HreqV; unfold AREC in *; lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (cshe_l3_extra (hl_v H1) (hl_n H1) (fst r) 4))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (fst r) 4) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = w64 EA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
(* ---- 0x85614 .. 0x85628: the shadow checks of v[i] and l->v, a0 = v[i].s, jal free ---- *)
paj_run_tok_x RUNx HS HJ0 SHOK Bspan.
{ cbv [ss_mem ss_cshe_l3s cshe_l3_fr cshe_l3_hd cshe_l3_slot].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem1) (mrestrict _ (ms_mem ms)) |- _ => l3_wkeep Hf U18 end. }
assert (Usp1 : spZ (ms_regs ms) = sp0 + -144) by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) mdc) by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ0).
(* ---- free(v[i].s) ---- *)
eapply SRr_bind.
{ apply (l3_free_gx XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 mdc kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-144) (Z_to_bv 64 (BASE + 13120)) [] (length (hl_recs (ldrop_list H1 i)) + kr)
    HJ0 HX16 HinR).
  - rewrite Q10, E34. reflexivity.
  - exact Usp1.
  - reflexivity.
  - lia.
  - rewrite WS, QA. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 88) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp1. rewrite WS in Hslo. lia.
    + unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_shape_ends + 0x27c); [exact HCTX_cshe_l3|].
    unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. unfold AF_fr_check_shape_ends. lia.
  - (* the free's room: one record fewer is left past it *)
    apply (l3_rm_cast RP S1 _ _ HRMr). change (hl_recs (ldrop_list H1 i)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (l3_drop_len _ _ Hi). lia.
  - exact HCNTr.
  - intros _ k Hk. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). apply HINC. apply nth_In. exact Hi.
  - pose proof (mo_free_nonneg MT ML) as Hf0.
    apply (mok_station MT S1 S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) 0 (mo_free MT) ML HMOK
      (mo_le_refl MT ML S1) Hf0). unfold hl_n in Hn1. nia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle & HRM2 & HEf & Hpres2).
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hia Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hia Ho He)|].
  apply (Hpres2 a Hia).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 hp1 W1 (ms_mem ms) _ a HAR1m Hia) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 Hia) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 (ms_mem ms) _ (fst r) _ a HAR1m HinR Hr Hia). }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); rewrite ?WS, ?QA in *; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    exact (proj1 (IMGK a Hia Ho He)).
  - intros a Ha Hw. destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    apply (l3_writable_kept_w W1 W2 (ms_mem ms) mem2 a); [exact (proj2 (IMGK a Hia Ho He)) | exact Hwle2 | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB) by (rewrite ?OLDa by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80)) by (rewrite ?OLDa by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
paj_run_tok_x RUNx HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (F21 : ew Ea 21 = w64 (Z.of_nat i)) by (rewrite OLDa by lia; exact E21).
assert (F32 : ew Ea 32 = Z_to_bv 64 (hl_v H1)) by (rewrite OLDa by lia; exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 (hl_n H1)) by (rewrite OLDa by lia; exact E33).
assert (Uspm : spZ (ms_regs ms0) = sp0 - 144)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2; exact UspA).
assert (R10m : getr (ms_regs ms0) 10 = w64 EA).
{ rewrite P10, F21, F32. unfold w64. rewrite l3_sll4 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
assert (R11m : getr (ms_regs ms0) 11 = w64 (EA + 16)).
{ rewrite P11, F21, F32. unfold w64. rewrite l3_sll4 by lia. rewrite !YI08.alu64_add_lit. f_equal; lia. }
assert (R12m : getr (ms_regs ms0) 12 = w64 (AREC * (hl_n H1 - Z.of_nat i - 1))).
{ rewrite P12, F21, F33. unfold w64. rewrite l3_count_eq by lia. unfold AREC. f_equal; lia. }
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; apply nth_In; exact Hi).
assert (Hvin2 : In (hl_v H1, AREC * hl_cap H1) (ablocks B ly2 S2)).
{ pose proof HvinH as Hv1. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hv1.
  apply in_app_or in Hv1 as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply VNE. first [exact Ex | exact (eq_sym Ex)]. }
assert (HAR3 : ARx ly2 S2 hp2 W2 (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2))
  by exact (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 _ _ (kk + 1) HJ2).
destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (V16' & V4096' & Vceil' & Vapp' & Vpres' & _).
rewrite HreqV in Vceil', Vapp', Vpres'.
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a Hr; destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; [exact Hsg | exact Hra]).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
  rewrite KEEPr; [exact (HROM a Hrom) | lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom). }
assert (ROM2 : rom_view SEGS W2 mem2) by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (KEEPm : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end. }
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
  rewrite KEEPm; [exact (ROM2 a Hrom) | lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom). }
assert (Ecap : (hl_cap H0 =? 0) = false) by (apply Z.eqb_neq; rewrite <- HC; lia).
assert (HvFP : forall a, hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1 -> inFP FPc a).
{ intros a Ha. exists (hl_v H0, hl_v H0 + req_size (AREC * hl_cap H0)).
  split; [|cbn [fst snd]; rewrite <- HV, <- HC, HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v H0, AREC * hl_cap H0)).
  unfold list_blks. rewrite Ecap. apply in_or_app. left. left. reflexivity. }
assert (HEAeq : EA = hl_v H1 + 16 * Z.of_nat i) by reflexivity. clearbody EA.
assert (HnC : hl_n H1 <= hl_cap H1) by lia.
(* ---- the memmove of the records above i, 0x85660 ---- *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) _
  W2 (ms_regs ms0) (ms_mem ms0) CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 _ (kk + 1)
  (- 144) (Z_to_bv 64 (BASE + 13176)) HG HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite WS. unfold ESTACK. lia.
- rewrite P3, OLDa, E3 by lia. exact Hgp0.
- rewrite P4, OLDa, E4 by lia. exact Htp0.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec EA a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (EA + AREC * (hl_n H1 - Z.of_nat i - 1))) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact (proj1 (HG a HGb))].
- intros a Ha HnG. split; [|unfold AREC in *; lia].
  right. left. split; [apply HvFP; unfold AREC in *; lia|].
  exists (hl_v H1), (AREC * hl_cap H1). split; [exact Hvin2 | rewrite HreqV; unfold AREC in *; lia].
- intros HPRE2 HSC.
  assert (MNIMG : forall a, EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1) -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2).
    rewrite HreqV. unfold AREC in *. lia. }
  apply (AMOVE ly2 S2 hp2 W2 (ms_regs ms0) (ms_mem ms0) _
    EA (EA + 16) (AREC * (hl_n H1 - Z.of_nat i - 1)) HPRE2 R10m R11m R12m).
  + unfold AREC in *; lia.
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres' a ltac:(unfold AREC in *; lia))).
    * exact (proj2 (Vpres' a ltac:(unfold AREC in *; lia))).
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres' a ltac:(unfold AREC in *; lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split; (apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia).
  + exact MNIMG. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 mem3 md3 (kk + 1) HJ3) as HAR4.
assert (MOFF : forall a, in_img SEGS a -> ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1))).
{ intros a Hia Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact Hia]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold AREC, ESTACK in *; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & _).
    pose proof (pa_img_range a Hia). apply Hfr3; [lia | exact (MOFF a Hia) | unfold ESTACK; lia].
  - intros a Ha Hw. apply (l3_writable_kept_w W2 W2 (ms_mem ms0) mem3 a); [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (SHOK3 : sh_ok SEGS Bx1 cshe_l3_SH Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB) by (rewrite ?OLDba by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
paj_run_tok_x RUNx HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* ---- 0x85678, the back-edge: first what the turn kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
pose proof alloc_ceiling_val as ACV.
assert (HSPc : alloc_ceiling + 16528 <= sp0) by (rewrite WS in Hslo; lia).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms1) _ (kk + 1) HJ3) as HARF.
assert (KEEPf : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms1)) |- _ => l3_wkeep Hf U18b end. }
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) -> ~ (sp0 - 144 - ESTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn Hd Hs. rewrite (KEEPf a Ha Hn). rewrite (Hfr3 a Ha Hd ltac:(lia)). exact (KEEPm a Ha Hn). }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hia Ho He Hn. pose proof (pa_img_range a Hia) as Har.
  rewrite (KALL a ltac:(lia) Hn (MOFF a Hia) ltac:(unfold ESTACK; lia)).
  rewrite (proj1 (proj2 (proj2 HK)) a Hia Ho He). apply KEEPr; [lia | exact Hn]. }
assert (KBLK : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <= a < pb + req_size nb ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros pb nb a Hin Ha Hnr Hnm.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 pb nb HAR1 Hin) as (_ & Hp4096 & Hpc & _ & _ & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (intros Hc; apply Hni; exact (proj1 (HAimg a ltac:(unfold ASRC; lia)))).
  rewrite (KALL a ltac:(lia) Hnw Hnm ltac:(unfold ESTACK; lia)).
  replace a with (pb + (a - pb)) by lia.
  rewrite (proj1 (proj2 HK) pb nb (a - pb) Hin ltac:(lia) ltac:(cbv beta; lia)).
  replace (pb + (a - pb)) with a by lia. apply KEEPr; [lia | exact Hnw]. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs.
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (unfold ASRC, kLowMemEnd in HAhi; lia).
  rewrite (KALL a ltac:(lia) Hnw ltac:(unfold AREC in *; lia) ltac:(rewrite QA in Hs; unfold ESTACK; lia)).
  rewrite (proj1 HK a Ha ltac:(lia)). apply KEEPr; [lia | exact Hnw]. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (fst r)
  (Z.of_nat (length (snd r)) + 1) HAR1 HvinH HinR ltac:(intros Heq; injection Heq as Heq _; exact (VNE Heq))) as DJ.
unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
assert (KMOV : forall k, 0 <= k < AREC * (hl_n H1 - 1 - Z.of_nat i) ->
  aview SEGS (w_H W2) (ms_mem ms1) (hl_v H1 + AREC * Z.of_nat i + k) =
  aview SEGS (w_H W1) mem1 (hl_v H1 + AREC * Z.of_nat i + AREC + k)).
{ intros k Hk. unfold AREC in *.
  assert (Hni1 : ~ in_img SEGS (EA + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (16 * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hni2 : ~ in_img SEGS (EA + 16 + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (16 * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hnw1 : ~ (HA + 88 <= EA + k < HA + 92))
    by (intros Hc; apply Hni1; exact (proj1 (HAimg (EA + k) ltac:(unfold ASRC; lia)))).
  assert (Hnw2 : ~ (HA + 88 <= EA + 16 + k < HA + 92))
    by (intros Hc; apply Hni2; exact (proj1 (HAimg (EA + 16 + k) ltac:(unfold ASRC; lia)))).
  replace (hl_v H1 + 16 * Z.of_nat i + k) with (EA + k) by lia.
  replace (hl_v H1 + 16 * Z.of_nat i + 16 + k) with (EA + 16 + k) by lia.
  rewrite (KEEPf (EA + k) ltac:(lia) Hnw1).
  rewrite (Hmov k ltac:(lia)).
  rewrite (KEEPm (EA + 16 + k) ltac:(lia) Hnw2).
  replace (EA + 16 + k) with (hl_v H1 + (16 * Z.of_nat i + 16 + k)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v H1) (16 * hl_cap H1) (16 * Z.of_nat i + 16 + k) HvinH ltac:(rewrite HreqV; lia)
    ltac:(cbv beta; lia)).
  replace (hl_v H1 + (16 * Z.of_nat i + 16 + k)) with (EA + 16 + k) by lia.
  apply KEEPr; [lia | exact Hnw2]. }
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hia Ho He Hp.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem3) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply Hpres3.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply (proj2 (IMGK a Hia Ho He)).
  lazymatch goal with Hg : mem_grows (mrestrict _ mem1) (mrestrict _ (ms_mem ms)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  exact Hp. }
assert (BLK2 : forall pb nb, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> In (pb, nb) (ablocks B ly2 S2)).
{ intros pb nb Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply Hne2. first [exact Ex | exact (eq_sym Ex)]. }
assert (KOFF : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> pb <= a < pb + req_size nb ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1))).
{ intros pb nb a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HinR
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. lia. }
assert (KOFV : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> hl_v H1 -> pb <= a < pb + req_size nb ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1))).
{ intros pb nb a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb (hl_v H1) (AREC * hl_cap H1) HAR1 Hin HvinH
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. unfold AREC in *. lia. }
assert (KBK : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> pb <> hl_v H1 -> pb <= a < pb + req_size nb ->
  abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros pb nb a Hin Hp1 Hp2 Ha. split.
  - exact (KBLK pb nb a Hin Ha (KOFF pb nb a Hin Hp1 Ha) (KOFV pb nb a Hin Hp2 Ha)).
  - intros Hw. destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms1) _ pb nb HARF (BLK2 pb nb Hin Hp1)) as (_ & _ & _ & _ & Hpr & _).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpr a Ha))). }
assert (KHD : forall a, HA <= a < HA + ASRC -> ~ (HA + 88 <= a < HA + 92) -> abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros a Ha Hw. destruct (HAimg a Ha) as (Hia & Ho & He & _). split.
  - exact (KIMG a Hia Ho He Hw).
  - intros Hwr. apply (l3_writable_kept_w W1 W2 mem1 (ms_mem ms1) a); [intros Hp; exact (KPRES a Hia Ho He Hp) | exact Hwle2 | exact Hwr]. }
(* l->n after the store: n - 1 *)
pose proof (st_ok_pi_region_nth Eb _ _ 1
  (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
  HS ltac:(vm_compute; reflexivity)) as HRgF. cbn [ms_mem restrict] in HRgF.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgF U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnF.
(* the record i's place in the list, and the list without it *)
destruct (nth_split (hl_recs H1) (0, []) Hi) as (RA & RB & Hsp & HlA).
fold r in Hsp.
assert (Hdrop : CheckRep.drop_nth i (hl_recs H1) = RA ++ RB) by (rewrite Hsp, <- HlA; apply l3_drop_split).
assert (Hldr : hl_recs (ldrop_list H1 i) = RA ++ RB) by exact Hdrop.
assert (Hrnot : ~ In (fst r) (map fst (RA ++ RB))).
{ pose proof HNDvH as ND1. apply NoDup_ListNoDup in ND1. rewrite Hsp, map_app in ND1. cbn [map] in ND1.
  rewrite map_app. exact (List.NoDup_remove_2 _ _ _ ND1). }
assert (HinRA : forall x, In x (RA ++ RB) -> In x (hl_recs H1)).
{ intros x Hx. rewrite Hsp. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HE2 : alist_at B ly2 S2 W2 (ms_mem ms1) (HA + 80) (ldrop_list H1 i) true).
{ apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) (HA + 80) H1 true i HAH1 Hi).
  - exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(unfold ASRC; lia) ltac:(lia))).
  - intros k Hk. destruct (HAimg (HA + 80 + k) ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    apply (l3_writable_kept_w W1 W2 mem1 (ms_mem ms1) (HA + 80 + k)); [intros Hp; exact (KPRES _ Hia Ho He Hp) | exact Hwle2 | exact (MwH k Hk)].
  - exact MnF.
  - intros k Hk. exact (KMOV k Hk).
  - intros a Ha.
    assert (Ha2 : hl_v H1 <= a < hl_v H1 + req_size (AREC * hl_cap H1)) by (rewrite HreqV; unfold AREC in *; lia).
    exact (KBLK (hl_v H1) (AREC * hl_cap H1) a HvinH Ha2 (KOFF (hl_v H1) (AREC * hl_cap H1) a HvinH VNE Ha2)
      ltac:(unfold AREC in *; lia)).
  - intros r' Hr' a Ha. rewrite Hldr in Hr'.
    assert (Hin' : In (fst r', Z.of_nat (length (snd r')) + 1) (ablocks B ly1 S1)).
    { rewrite Forall_forall in HFallH. exact (proj1 (HFallH r' (HinRA r' Hr'))). }
    assert (Hne1 : fst r' <> fst r) by (intros Heq; apply Hrnot; rewrite <- Heq; apply in_map; exact Hr').
    assert (Hne2 : fst r' <> hl_v H1) by (intros Heq; apply HninH; rewrite <- Heq; apply in_map; exact (HinRA r' Hr')).
    exact (proj1 (KBK _ _ a Hin' Hne1 Hne2 ltac:(pose proof (l3_req_ge (Z.of_nat (length (snd r')) + 1) ltac:(lia)); lia))). }
(* ---- the source with the shorter held list ---- *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & HED & _ & _).
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected] in HPD, HPIN, HPJLEN, HED.
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (NDB : NoDup (hs_blocks (CheckRep.set_held h H1)))
  by (pose proof HSRC as HSRCx; repeat (destruct HSRCx as [_ HSRCx]); exact HSRCx).
apply NoDup_ListNoDup in NDB.
change (hs_blocks (CheckRep.set_held h H1)) with
  (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks H1) in NDB.
rewrite (l3_lb H1 Hcpos), Hsp, map_app in NDB. cbn [map] in NDB.
assert (ND1 : ~ In (fst r) (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
  hl_v H1 :: map fst RA ++ map fst RB)).
{ assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
    hl_v H1 :: map fst RA) ++ fst r :: map fst RB)) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_2 in Hx. rewrite <- !app_assoc in Hx. exact Hx. }
assert (ND2 : ~ In (hl_v H1) (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h))).
{ assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++
    hl_v H1 :: (map fst RA ++ fst r :: map fst RB))) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_2 in Hx. intros Hc. apply Hx. apply in_or_app. left. exact Hc. }
assert (NDnew : NoDup (hs_blocks (CheckRep.set_held h (ldrop_list H1 i)))).
{ apply NoDup_ListNoDup.
  change (hs_blocks (CheckRep.set_held h (ldrop_list H1 i))) with
    (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (ldrop_list H1 i)).
  rewrite (l3_lb (ldrop_list H1 i) Hcpos), Hldr, map_app.
  assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
    hl_v H1 :: map fst RA) ++ fst r :: map fst RB)) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_1 in Hx. rewrite <- !app_assoc in Hx. exact Hx. }
assert (SFP : akept W1 mem1 W2 (ms_mem ms1)
  (gfp (hs_partial h) (bzs (hs_pjunk h)) :: alist_fp (HA + 16) (hs_pending h) ++ alist_fp (HA + 64) (hs_expected h))).
{ intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    apply (KBK (hs_partial h) APARTIAL a HPIN).
    + intros Hc. apply ND1. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
    + intros Hc. apply ND2. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
    + rewrite HreqP. lia.
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (l3_list_kept_P ly1 S1 W1 W2 mem1 md1 (ms_mem ms1) (HA + 16) (hs_pending h) false
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HPD).
      * intros x Hx. apply KHD; [unfold ASRC; lia | lia].
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. split; intros Hc; [apply ND1 | apply ND2]; rewrite <- Hc; rewrite !in_app_iff; cbn [In]; tauto.
    + apply (l3_list_kept_P ly1 S1 W1 W2 mem1 md1 (ms_mem ms1) (HA + 64) (hs_expected h) true
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HED).
      * intros x Hx. apply KHD; [unfold ASRC; lia | lia].
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. split; intros Hc; [apply ND1 | apply ND2]; rewrite <- Hc; rewrite !in_app_iff; cbn [In]; tauto. }
assert (ABLK : forall (lst : hlist) LA lines, alist_at B ly1 S1 W1 mem1 LA lst lines ->
  forall b, In b (alist_blks lst) -> In b (ablocks B ly1 S1)).
{ intros lst LA lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  - destruct (hl_cap lst =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
  - apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HFa).
    rewrite Forall_forall in HFa. exact (proj1 (HFa x Hx)). }
assert (ABF : forall (lst : hlist) b, In b (alist_blks lst) -> In (fst b) (list_blocks lst)).
{ intros lst b Hb. unfold alist_blks, list_blocks in Hb |- *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
  - left. destruct (hl_cap lst =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst]. left. reflexivity.
  - right. apply in_map_iff in Hb as (x & <- & Hx). cbn [fst]. apply in_map. exact Hx. }
assert (SBLK : forall b, In b ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h)) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb. cbn [In] in Hb. destruct Hb as [<- | Hb].
  - apply (BLK2 _ _ HPIN). intros Hc. apply ND1. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [pb nb].
    + apply (BLK2 pb nb (ABLK _ _ _ HPD _ Hb)). intros Hc. apply ND1. rewrite <- Hc. pose proof (ABF _ _ Hb) as Hb'.
      cbn [fst] in Hb'. rewrite !in_app_iff. cbn [In]. tauto.
    + apply (BLK2 pb nb (ABLK _ _ _ HED _ Hb)). intros Hc. apply ND1. rewrite <- Hc. pose proof (ABF _ _ Hb) as Hb'.
      cbn [fst] in Hb'. rewrite !in_app_iff. cbn [In]. tauto. }
assert (SRC2 : asrc_at B ly2 S2 W2 (ms_mem ms1) HA (CheckRep.set_held h (ldrop_list H1 i))).
{ apply (l3_src_held ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) HA h H1 (ldrop_list H1 i) HSRC).
  - intros x Hx. apply KHD; [unfold ASRC; lia | lia].
  - exact SFP.
  - exact SBLK.
  - exact HE2.
  - exact NDnew. }
(* ---- the stream's block, the globals, the frame ---- *)
assert (HO0 : 0 < O) by lia.
assert (HOUTnb : ~ In OUT (hs_blocks h)).
{ destruct HOB as [E0 | (CO0 & _ & _ & Hni)]; [rewrite E0 in HOlen; cbn in HOlen; lia | exact Hni]. }
assert (HOr : OUT <> fst r).
{ intros Heq. apply HOUTnb. rewrite Heq.
  assert (Hm : In (fst r) (list_blocks (hs_held h)))
    by (unfold list_blocks; apply in_or_app; right; apply in_map; apply HINC; apply nth_In; exact Hi).
  unfold hs_blocks. rewrite !in_app_iff. tauto. }
assert (HOv : OUT <> hl_v H1).
{ intros Heq. apply HOUTnb. rewrite Heq, HV.
  assert (Hm : In (hl_v H0) (list_blocks (hs_held h))) by (unfold list_blocks; rewrite Ecap; left; reflexivity).
  unfold hs_blocks. rewrite !in_app_iff. tauto. }
assert (OBF : ob_at W2 (ms_mem ms1) OUT ob).
{ intros k Hk. pose proof (l3_req_ge CO ltac:(lia)) as HqC.
  rewrite (proj1 (KBK OUT CO (OUT + k) HOin HOr HOv ltac:(lia))). exact (HOBt k Hk). }
assert (KG : forall a, inG cshe_ro a -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hg Hn. destruct (HGR a Hg) as (Hia & Ho & _). destruct (HGRR a Hg) as (He & _). exact (KIMG a Hia Ho He Hn). }
assert (GG : forall a, VAL A_g_gone <= a < VAL A_g_gone + 1 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (Hx & _). apply Hx. lia. }
assert (GN : forall a, VAL A_g_nout <= a < VAL A_g_nout + 8 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_nout, 8). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & Hx & _). apply Hx. lia. }
assert (GO : forall a, VAL A_g_out <= a < VAL A_g_out + 8 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_out, 8). split; [right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & _ & Hx). apply Hx. lia. }
assert (MGF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_gone) 1 0).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MG].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GG (VAL A_g_gone + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MNOF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_nout) 8 O).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MNO].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GN (VAL A_g_nout + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MOUTF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_out) 8 OUT).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MOUT].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GO (VAL A_g_out + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MATF : val_mem SEGS (arm W2 (ms_mem ms1)) AT 8 (A0 + (c + Z.of_nat (length l) + 1))).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MAT].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. apply KHI; [lia | rewrite QA; lia]. }
assert (SAVF : cshe_saved W2 (ms_mem ms1) sp0 regs0).
{ apply (l3_saved_kept W1 W2 mem1 (ms_mem ms1) sp0 regs0); [|exact HSAV]. intros a Ha. apply KHI; [lia | rewrite QA; lia]. }
assert (M16F : val_mem SEGS (arm W2 (ms_mem ms1)) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact M16].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. apply KHI; [lia | rewrite QA; lia]. }
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hia. pose proof (pa_img_range a Hia) as Har.
  assert (Hn : ~ (HA + 88 <= a < HA + 92))
    by (intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom)).
  rewrite (KEEPf a ltac:(lia) Hn). rewrite (Hfr3 a ltac:(lia) (MOFF a Hia) ltac:(unfold ESTACK; lia)). exact (ROMK a Hrom). }
(* ---- the allocator's side and the model's ---- *)
assert (PERMF : forall rest, Permutation (ablocks B ly S) (cshe_ds_blks (ds ++ [r]) ++ rest) ->
  Permutation (ablocks B ly2 S2) rest).
{ intros rest Hpm.
  assert (Hpm1 : Permutation (ablocks B ly S) (cshe_ds_blks ds ++ (fst r, Z.of_nat (length (snd r)) + 1) :: rest)).
  { unfold cshe_ds_blks in Hpm |- *. rewrite map_app in Hpm. cbn [map] in Hpm. rewrite <- app_assoc in Hpm. exact Hpm. }
  pose proof (HPERM _ Hpm1) as Hp1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hp1.
  exact (Permutation_app_inv l1 l2 [] rest _ Hp1). }
assert (FRSF : frames S2 = frames S) by (rewrite Hfrs2; exact HFRS).
pose proof (mo_free_nonneg MT ML) as Hf0.
assert (MLEF : mo_le MT S S2 (Z.of_nat (length (ds ++ [r])) * mo_free MT)).
{ replace (Z.of_nat (length (ds ++ [r])) * mo_free MT) with (Z.of_nat (length ds) * mo_free MT + mo_free MT)
    by (rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat]; ring).
  exact (mle_station MT S S1 S2 _ _ ML HMLE Hle). }
assert (HLD : (length (hl_recs (ldrop_list H1 i)) + 1 = length (hl_recs H1))%nat).
{ change (hl_recs (ldrop_list H1 i)) with (CheckRep.drop_nth i (hl_recs H1)). rewrite (l3_drop_len _ _ Hi). lia. }
assert (MOKF : mo_ok MT S2 (Z.of_nat (length (hl_recs (ldrop_list H1 i))) * mo_free MT)).
{ assert (HLD' : Z.of_nat (length (hl_recs H1)) = Z.of_nat (length (hl_recs (ldrop_list H1 i))) + 1) by (rewrite <- HLD; lia).
  apply (mok_station MT S1 S2 (Z.of_nat (length (hl_recs H1)) * mo_free MT) (mo_free MT) _ ML HMOK Hle);
    [apply Z.mul_nonneg_nonneg; lia | rewrite HLD'; lia]. }
(* the room round: the free's post room, and the live counts one block fewer *)
assert (CNTF : cnt_ok RP (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HCNTr. exact (l3_cnt_del RP l1 _ l2 HCNTr). }
assert (ERRF : l3_err W2 (ms_mem ms1)).
{ intros q Hq. pose proof (l3_errno_img q Hq) as Hie. pose proof (pa_img_range _ Hie) as Har.
  assert (Hw : ~ (HA + 88 <= as_errno B + q < HA + 92)) by (intros Hc; apply (l3_errno_off q Hq); unfold ASRC; lia).
  rewrite (KALL (as_errno B + q) ltac:(lia) Hw (MOFF _ Hie) ltac:(unfold ESTACK; lia)).
  rewrite (HEf q Hq). rewrite (KEEPr (as_errno B + q) ltac:(lia) Hw). exact (HERR q Hq). }
(* ---- the memory facts, carried to a later memory that kept every byte but l->n and wrote n - 1 there ---- *)
assert (TRANS : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) (ms_mem ms1) a) ->
  val_mem SEGS (arm W2 m') (HA + 80 + 8) 4 (hl_n H1 - 1) ->
  (forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) m' a) ->
  asrc_at B ly2 S2 W2 m' HA (CheckRep.set_held h (ldrop_list H1 i)) /\
  val_mem SEGS (arm W2 m') AT 8 (A0 + (c + Z.of_nat (length l) + 1)) /\
  val_mem SEGS (arm W2 m') (VAL A_g_gone) 1 0 /\ val_mem SEGS (arm W2 m') (VAL A_g_nout) 8 O /\
  val_mem SEGS (arm W2 m') (VAL A_g_out) 8 OUT /\ ob_at W2 m' OUT ob /\ rom_view SEGS W2 m' /\
  cshe_saved W2 m' sp0 regs0 /\ val_mem SEGS (arm W2 m') (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\ l3_err W2 m').
{ intros m' Hk Hn' Hp'.
  assert (VK : forall x n v, (forall a, x <= a < x + Z.of_nat n -> 0 <= a < 2 ^ 64 /\ ~ (HA + 88 <= a < HA + 92)) ->
    val_mem SEGS (arm W2 (ms_mem ms1)) x n v -> val_mem SEGS (arm W2 m') x n v).
  { intros x n v Hx Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms1) m'); [|exact Hv].
    intros k Hk'. destruct (Hx (x + k) ltac:(lia)) as [Hb Hn]. exact (Hk _ Hb Hn). }
  assert (GB : forall a, inG cshe_ro a -> 0 <= a < 2 ^ 64)
    by (intros a Hg; pose proof (pa_img_range a (proj1 (HGR a Hg))); lia).
  split.
  { apply (l3_src_step ly2 S2 _ W2 W2 (ms_mem ms1) m' HA (CheckRep.set_held h (ldrop_list H1 i)) alloc_ceiling alloc_ceiling HARF SRC2).
    - intros a Ha. exact (proj1 (HAimg a Ha)).
    - lia.
    - intros a Ha _ Hn. exact (Hk a Ha Hn).
    - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
      exact (l3_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) m' (HA + 80 + 8) 4 (hl_n H1 - 1) k MnF Hn' ltac:(cbn; lia)).
    - exact Hp'.
    - apply wle_refl. }
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; lia | exact MATF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GG a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MGF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GN a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MNOF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GO a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MOUTF]|].
  split.
  { intros k Hk'. pose proof (l3_req_ge CO ltac:(lia)) as HqC.
    assert (Hni : ~ in_img SEGS (OUT + k)) by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO); [exact HAR1 | exact HOin | lia]).
    rewrite (Hk (OUT + k) ltac:(lia) ltac:(intros Hc; apply Hni; exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))))).
    exact (OBF k Hk'). }
  split.
  { intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
    rewrite (Hk a ltac:(lia) ltac:(intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom))).
    exact (ROMF a Hrom). }
  split.
  { apply (l3_saved_kept W2 W2 (ms_mem ms1) m' sp0 regs0); [|exact SAVF]. intros a Ha. apply Hk; [lia|].
    unfold ASRC, kLowMemEnd in HAhi. lia. }
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; [lia | unfold ASRC, kLowMemEnd in HAhi; lia] | exact M16F]|].
  intros q Hq. pose proof (pa_img_range _ (l3_errno_img q Hq)) as HeR.
  rewrite (Hk (as_errno B + q) ltac:(lia) ltac:(intros Hc; apply (l3_errno_off q Hq); unfold ASRC; lia)). exact (ERRF q Hq). }
assert (F27 : ew Eb 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite OLDba by lia; exact E27).
psrr_branch_tok RUNx BR HS SHOK3 Bspan.
{ (* taken: s11 - 1 > 1, back to the head *)
  rewrite branch_ltu_U, (U_atom_off Eb 27 (Z.of_nat (Datatypes.S w) + 1) (-1) F27), U_lit in Hc by lia.
  apply Z.ltb_lt in Hc.
  destruct w as [|w']; [exfalso; lia|].
  paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan A_cshe_l3.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  pmkst HS.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
  prreg HS (20%bv : bv 5) N20. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26.
  prreg HS (27%bv : bv 5) N27.
  assert (KEEPj : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
  pose proof (st_ok_pi_region_nth Eb _ _ 1
    (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
    HS ltac:(vm_compute; reflexivity)) as HRgJ. cbn [ms_mem restrict] in HRgJ.
  pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgJ U18b ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)) as MnJ.
  assert (PRESj : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a).
  { intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
      exact (apresent_grows _ _ _ a Hg Hp) end. }
  destruct (TRANS (ms_mem ms2) KEEPj MnJ PRESj) as (SRCj & MATj & MGj & MNOj & MOUTj & OBj & ROMj & SAVj & M16j & ERRj).
  replace (BASE + 12976) with (BASE + A_cshe_l3) by (unfold A_cshe_l3, AF_fr_check_shape_ends; lia).
  apply (HKont W2 (ms_regs ms2) (ms_mem ms2) _ (ds ++ [r]) (c + Z.of_nat (length l) + 1)); [lia|].
  exists ly2, S2, hp2, (kk + 1), (ldrop_list H1 i).
  split; [exact HJ3|].
  split; [exact SRCj|].
  split; [exact HV|]. split; [exact HC|].
  split; [exact (l3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND)|].
  split; [intros x Hx; apply HINC; exact (l3_incl_drop (hl_recs H1) i x Hx)|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [exact HRUN|].
  split; [exact HREL|].
  split; [lia|]. split; [exact HcO|].
  split; [exact MATj|]. split; [exact MGj|]. split; [exact MNOj|]. split; [exact MOUTj|].
  split; [exact OBj|].
  split; [right; exists CO; split; [exact HCO | exact (BLK2 OUT CO HOin HOr)]|].
  split; [exact PERMF|]. split; [exact FRSF|]. split; [exact MLEF|]. split; [exact MOKF|].
  split; [exact HRM2|]. split; [exact CNTF|].
  split; [exact ROMj|]. split; [exact SAVj|]. split; [exact M16j|].
  split; [|exact ERRj].
  unfold l3_regs.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split.
  { rewrite N26, (OLDba 18%nat), (OLDba 25%nat) by lia. rewrite E18, E25. unfold w64.
    rewrite l3_srl3 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
  rewrite N27, F27. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia. }
rewrite branch_ltu_U, (U_atom_off Eb 27 (Z.of_nat (Datatypes.S w) + 1) (-1) F27), U_lit in Hc by lia.
apply Z.ltb_ge in Hc.
destruct w as [|w']; [|exfalso; lia].
(* ---- the last turn: on to the epilogue 0x85690 ---- *)
paj_run_to_tok_x RUNTOx HS HJ3 SHOK3 Bspan A_cshe_ret.
{ cbn [ss_mem add_cond].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
assert (KEEPj : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
pose proof (st_ok_pi_region_nth Eb _ _ 1
  (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
  HS ltac:(vm_compute; reflexivity)) as HRgJ. cbn [ms_mem restrict] in HRgJ.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgJ U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnJ.
assert (PRESj : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
destruct (TRANS (ms_mem ms2) KEEPj MnJ PRESj) as (_ & _ & _ & _ & _ & _ & _ & SAVj & _ & _).
replace (BASE + 13220) with (BASE + A_cshe_ret) by (unfold A_cshe_ret, AF_fr_check_shape_ends; lia).
apply (cshe_epi_x B PST ARx G LAWS HG W ly S hp mem md XO [(AT, AT + 8)] FPc ly2 S2 hp2 W2 regs0 (ms_regs ms2) (ms_mem ms2) _ (kk + 1) Post HJ3 Hra0 Hal16).
- rewrite WS. lia.
- lia.
- rewrite N2, OLDba by lia. exact E2.
- rewrite N3, OLDba by lia. exact E3.
- rewrite N4, OLDba by lia. exact E4.
- exact SAVj.
- intros regs' mem' md' Hpr Hk' Hp' HJ'.
  assert (KEEPe : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) (ms_mem ms1) a)
    by (intros a Ha Hn; rewrite (Hk' a Ha); exact (KEEPj a Ha Hn)).
  assert (MnE : val_mem SEGS (arm W2 mem') (HA + 80 + 8) 4 (hl_n H1 - 1)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms2) mem'); [|exact MnJ].
    intros k Hk. apply Hk'. unfold ASRC, kLowMemEnd in HAhi. lia. }
  destruct (TRANS mem' KEEPe MnE ltac:(intros a Hp; exact (Hp' a (PRESj a Hp))))
    as (SRCe & MATe & MGe & _ & _ & _ & _ & _ & _ & ERRe).
  exists ly2, S2, hp2, regs', mem', md', (kk + 1), (ldrop_list H1 i), (ds ++ [r]), (c + Z.of_nat (length l) + 1).
  split; [reflexivity|].
  split; [exact HJ'|].
  split; [exact Hpr|].
  split; [exact ERRe|].
  split; [exact SRCe|].
  split; [exact HV|]. split; [exact HC|].
  split; [exact (l3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND)|].
  split.
  { right. split; [reflexivity|].
    rewrite (HREL (CheckRep.drop_nth i (hl_recs H1)) [] 0 eq_refl). rewrite app_nil_r, Z.add_0_r. reflexivity. }
  split; [lia|].
  split; [replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + (c + Z.of_nat (length l) + 1)) by lia; exact MATe|].
  split; [exact MGe|].
  split; [exact PERMF|]. split; [exact FRSF|].
  split; [|exact (RMM_of RP S2 kr (length (hl_recs (ldrop_list H1 i)) + kr) ltac:(lia) HRM2)].
  apply (mle_weaken MT S S2 _ _ ML MLEF). unfold cshe_cost, hl_n.
  assert (Hl : Z.of_nat (length (ds ++ [r])) <= Z.of_nat (length (hl_recs H0))) by (rewrite length_app; cbn [length]; lia).
  apply Z.mul_le_mono_nonneg_r; [exact Hf0 | exact Hl].
Qed.
(* the loop, by induction on the turns left: each turn is l3_A1 (to 0x855d0), l3_A2 (to 0x85614), l3_B (the drop and
   the back-edge); the last turn ends in the epilogue and cshe_post *)
Lemma l3_loop : forall n ds c W1 regs1 mem1 md1, l3_inv (Datatypes.S n) ds c W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof using All.
induction n as [|n IH]; intros ds c W1 regs1 mem1 md1 HI;
  apply (l3_A1 _ ds c W1 regs1 mem1 md1 HI); intros l i W2 regs2 mem2 md2 HAB;
  apply (l3_A2 _ ds c l i W2 regs2 mem2 md2 HAB); intros W3 regs3 mem3 md3 HM;
  apply (l3_B _ ds c l i W3 regs3 mem3 md3 HM); intros W4 regs4 mem4 md4 ds' c' Hw HI'.
- lia.
- exact (IH ds' c' W4 regs4 mem4 md4 HI').
Qed.
End loop.

(* ------------------------------------------------------------------ the top lemma: W_cshe_top.v's Hypothesis L3 *)
(* Its type was W_cshe_top.v's L3 (a working branch 7035864229a) verbatim; since fb87b19890f its two P premises
   (in_rom on P's bytes, ashp of its shadow) are cshe_spec's one disjunctive P-home premise, at the same position.
   cshe_spec's premises, the branch (g_gone = 0, want > 0) and the state cshe_gone_l3 leaves at the loop head: what the
   composition supplies at the head is exactly these premises; of them the loop reads the journal (index 0, from the
   entry), asrc_at, rom_view and cshe_saved at (W1, mem1), the cells *at = A0, g_gone = 0 and sp + 16 =
   (&held.n) / 8 + SB, the frame-clause keep (for g_nout, g_out and the stream), and x2 x3 x4 x8 x9 x18 x19 x20 x24 x25
   x26 x27 (x27 = want + 1); P's home is carried to the has_prefix call by W_check_shape_ends.v's cshe_P_at. *)
Lemma cshe_l3_top_x : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob
  (W1 : world SEGS) hp1 regs1 mem1 md1 s5v,
let H := hs_held h in
let PLEN := Z.of_nat (length P) in
let want := Z.of_nat (CheckRep.want_of P (hl_recs H)) in
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA <= a < HA + ASRC -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall a, HA <= a < HA + ASRC -> cshe_home B ly S a) ->
NoDup (CheckRep.texts H) ->
hl_n H < 2 ^ 26 ->
(forall a, hl_v H <= a < hl_v H + AREC * hl_cap H -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs H) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF AT 8 ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> PLEN + 1 < 2 ^ 32 -> 0 < PF -> PF + PLEN + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + PLEN) = Some 0 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (PLEN + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
mo_ok MT S (cshe_cost MT H) ->
(* the branch *)
gone = 0 -> 0 < want -> 0 < hl_n H ->
(* the state at loop 3's head 0x8559c *)
wle W W1 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp1 W1 mem1 md1 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) ->
(forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W1) mem1 a) ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 (spZ regs) regs ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 8) 8 3 ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
(* s5 (x21) still holds loop 1's s5v; 0x8557c computed want = a0 + s5 with 0 <= a0 <= 2 (cshe_tst_ok) *)
0 <= s5v < 2 ^ 26 -> 0 <= want - s5v <= 2 ->
getr regs1 2 = w64 (spZ regs - 144) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 10 = w64 want ->
getr regs1 18 = w64 (HA + 80) -> getr regs1 19 = w64 AT -> getr regs1 20 = w64 (VAL A_lit_end5) ->
getr regs1 21 = w64 s5v -> getr regs1 22 = w64 0 -> getr regs1 23 = w64 (SB + (hl_v H + AREC * hl_n H) / 8) ->
getr regs1 24 = w64 4 -> getr regs1 25 = w64 SB -> getr regs1 26 = w64 ((HA + 80) / 8 + SB) ->
getr regs1 27 = w64 (want + 1) ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
forall kr : nat, rp_RM RP S (length (hl_recs H) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1)
  (cshe_post_x B PST ARx MT RP G regs ly S hp W mem md XO AT HA h P A0 gone ob kr).
Proof.
cbv zeta.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob W1 hp1 regs1 mem1 md1 s5v
  HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HAoff HAhome HND HnH
  HVoff HRoff HAT8 HATlo HAThi HATra MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1
  HPhome HE5 HROM Mg Rg MO MOUT HOB HOlen HO40 HO32 HOmr HOblk HA0 HFN HMO
  Hgone Hwant Hn0 Hwle HJ1 HK1 HP1 HPf1 HSRC1 HROM1 HSAV1 M8 M16 MAT1 MG1 HERR1 Hs5 Hs5w
  R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 kr HRM0 HCNT0.
subst gone.
assert (EWx : exists w', CheckRep.want_of P (hl_recs (hs_held h)) = Datatypes.S w').
{ destruct (CheckRep.want_of P (hl_recs (hs_held h))) as [|w']; [cbn in Hwant; lia | exists w'; reflexivity]. }
destruct EWx as (w' & EW).
assert (HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a).
{ intros a Ha.
  assert (Hg : inG cshe_ro a).
  { unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384).
    split; [right; right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; unfold ASRC in *; lia]. }
  destruct (HGR a Hg) as (Hi & Ho & _). destruct (HGRR a Hg) as (He & _).
  destruct (HGS a ltac:(unfold ASRC in *; lia)) as (_ & Hr & _).
  split; [exact Hi|]. split; [exact Ho|]. split; [exact He | exact Hr]. }
assert (HAg : forall a, HA <= a < HA + ASRC -> ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\
  ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= a < VAL A_g_out + 8)).
{ intros a Ha. destruct (HGS a ltac:(unfold ASRC in *; lia)) as (_ & _ & G1 & G2 & G3).
  split; [exact G1|]. split; [exact G2 | exact G3]. }
assert (HPV : forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None)
  by (intros a Ha; exact (proj1 (HPvis a Ha))).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as ACV.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (KW : forall a, in_img SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Hi. pose proof (pa_img_range a Hi). apply HK1; [lia | rewrite WS in *; lia]. }
apply (l3_loop regs ly S hp W mem md ch XO AT HA PF A0 O OUT h P ob kr HPRE HXO0 HXO16 HXtop HAT8 HATlo HAThi Hal8 Hlo HAhiK
  HGin Hzs HnH HOlen HO40 HO32 HOmr HOblk HA0 HROM HAimg HAg HPnz HP32 HPF0 HPFk HPhome HPby HPnul HPV HPmr1 HPmr8
  HPra1 HSRC HE5
  w' [] 0 W1 regs1 mem1 md1).
unfold l3_inv, l3_regs.
exists ly, S, hp1, 0, (hs_held h).
split; [exact HJ1|].
split; [rewrite l3_set_held_id; exact HSRC1|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|].
split; [apply incl_refl|].
split; [cbn [length]; lia|].
split; [rewrite Z.add_0_r, <- EW; exact (HFN eq_refl)|].
split; [intros rsF dsF cF Hx; rewrite Z.add_0_r, <- EW in Hx; rewrite Hx; reflexivity|].
split; [lia|]. split; [lia|].
split; [rewrite Z.add_0_r; exact MAT1|].
split; [exact MG1|].
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) mem mem1); [|exact MO]. intros k Hk. apply KW.
  destruct (HGR (VAL A_g_nout + k)) as (Hi & _); [|exact Hi].
  unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_nout, 8).
  split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) mem mem1); [|exact MOUT]. intros k Hk. apply KW.
  destruct (HGR (VAL A_g_out + k)) as (Hi & _); [|exact Hi].
  unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_out, 8).
  split; [right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk; lia]. }
split.
{ destruct HOblk as [E0 | (CO & HCO & HOin & _)].
  - subst ob. intros k Hk. cbn [length Z.of_nat] in Hk. lia.
  - intros k Hk. destruct (alx_blocks _ _ _ LAWS ly S hp W mem md OUT CO HAR0 HOin) as (_ & O4 & Oc & _).
    pose proof (l3_req_ge CO ltac:(lia)).
    rewrite (HK1 (OUT + k) ltac:(lia) ltac:(rewrite WS in *; lia)). exact (HOB k Hk). }
split; [destruct HOblk as [E0 | (CO & HCO & HOin & _)]; [left; exact E0 | right; exists CO; split; assumption]|].
split; [intros rest Hp; exact Hp|].
split; [reflexivity|].
split; [exact (mo_le_refl MT ML S)|].
split; [exact HMO|].
split; [exact HRM0|]. split; [exact HCNT0|].
split; [exact HROM1|]. split; [exact HSAV1|]. split; [exact M16|].
split; [|exact HERR1].
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R24|]. split; [exact R25|].
split; [exact R26|].
rewrite EW in R27. exact R27.
Qed.
(* ------------------------------------------------------------------ route R: loop 3 at a world relation R *)
(* RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, added beside the strict texts above (each kept byte-identical): cshe_l3_top_xR is cshe_l3_top_x
   with the journal ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R, SRr SEGS -> SRrG SEGS R,
   cshe_post_x -> cshe_post_xR (W_contract_xR_g6.v) and the head premise wle W W1 -> R W W1: W_cshe_top.v's Section
   hypothesis L3R.  Section loopR is Section loop's header verbatim but for Post, and its texts are loop's with the runs
   paj_run_x_xG / paj_run_to_x_xG (paj_run_tok_xR / paj_run_to_tok_xR), the branch paj_branch_xR, the binds SRrG_bind,
   and the steps: next_line, list_find and has_prefix stay strict, lifted by l3_lift_wle (which keeps their wle) and
   their journals by l3_jR; bcmp (l3_bcmp_gx_at_xR) and memmove (aj_gx_entry_at_xR) through the entry's R form; free
   through the R rule (l3_free_gxR: its RO premise from ARx at the call state, RO_ARx); P's facts
   (l3_P_at_xR) and the epilogue (l3_epi_m_xR / l3_epi_xR) are W_check_shape_ends.v's cshe_P_at_x / cshe_epi_m_x /
   cshe_epi_x over the R journal, their proofs the same.  After free the continuation has R, not wle: the bytes whose
   writability it carries are image bytes (g_s[j]), never hidden (hidden_not_img), so presence carries it
   (l3_writable_kept_img). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* W_check_shape_ends.v's cshe_v64, copied: a saved register's value is a 64-bit number *)
Ltac l3_v64 w :=
let H := fresh "Hbr" in pose proof (bv_unsigned_in_range 64 w) as H;
change (bv_modulus 64) with (2 ^ 64) in H; zside.

(* a strict step at R, its wle kept for the continuation (the strict callees next_line, list_find, has_prefix) *)
Lemma l3_lift_wle : forall W c (Q : world SEGS -> config -> Prop), SRr SEGS W c Q ->
SRrG SEGS R W c (fun W' c' => wle W W' /\ Q W' c').
Proof.
intros W c Q H. apply (SRr_SRrG SEGS R WLE_R). eapply SRr_mono; [exact H|].
intros W' c' Hw HQ. exact (conj Hw HQ).
Qed.
(* a strict callee's journal is one at R (ajournal_gx_xR_mono, WLE_R) *)
Lemma l3_jR {G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k} :
ajournal_gx_x SEGS B PST ARx G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k ->
ajournal_gx_xR SEGS B PST ARx R G0 XO1 OUT1 STK sp1 FP ly0 S0 Hp0 W0 mem0 md0 own ly1 S1 Hp1 W1 mem1 md1 k.
Proof.
intros HJ. exact (ajournal_gx_xR_mono SEGS B PST ARx (@wle SEGS) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* l3_writable_kept_w for an image byte, with no world premise: an image byte is hidden in no world *)
Lemma l3_writable_kept_img : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m' ) a.
Proof.
intros W W' m m' a Hi Hp Hw.
assert (Hi' : in_img SEGS (bv_unsigned (Z_to_bv 64 a)))
  by (pose proof (pa_img_range a Hi); rewrite unsigned_lit_small by lia; exact Hi).
unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- rewrite (hidden_not_img SEGS W' _ Hi') in EH'. discriminate EH'.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + rewrite (hidden_not_img SEGS W _ Hi') in EH. discriminate EH.
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* :841 l3_free_gx at R *)
Lemma l3_free_gxR : forall XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb (o : Z) raw ch
  (kr : nat),
ajournal_gx_xR SEGS B PST ARx R G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own lyc Sc hpc W memT mdc k -> XO1 mod 16 = 0 ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch -> In (raZ regsT :: spine ch) CTX_AFREE ->
(* the room round: the rule's room (one free) and the live counts at the call *)
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall i, 0 <= i < req_size nb -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (pa <= a < pa + req_size nb) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros XO1 OUT1 W regsT memT STK sp0 FP ly S hp W0 mem md own lyc Sc hpc mdc k pa nb o raw ch kr
HJ HX Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hch Hctx HRM HCNT Hfp Hmo.
(* the call memory's RO, from ARx at the call state (W_list_drop.v aj_free_gx_xR) *)
pose proof HJ as HAR. apply ajournal_gx_AR_xR in HAR.
pose proof (RO_ARx _ _ _ _ _ _ HAR) as HRO.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (Hal' : (o - XO1) mod 16 = 0) by (rewrite Zminus_mod, Hal, HX; reflexivity).
eapply (SRrG_mono SEGS R).
{ exact (AFREE_R W regsT memT (STK + XO1) (sp0 + XO1) FP ly S hp W0 memS md own lyc Sc hpc mdc k pa nb (o - XO1) raw ch kr
  HJi Hin Ha0 ltac:(lia) Hal' ltac:(lia) ltac:(lia)
  (* the stack room below the call (a Theorem Labs lane's ACALL_PREFIX), from the journal's astk_ok *)
  (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o - XO1) regsT HJi ltac:(lia) ltac:(lia))
  Hgp Htp Hra Hraw Hch HRO Hctx HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 HR2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Herr & Hpr).
replace (sp0 + XO1 + (o - XO1) - ASTACK) with (sp0 + o - ASTACK) in HK by lia.
replace (sp0 + XO1 + (o - XO1)) with (sp0 + o) in HK by lia.
exists ly2, S2, hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK |
  split; [exact Hle | split; [exact HRM2 | split; [exact Herr | exact Hpr]]]]]]]].
apply (ajournal_gx_pack_xR SEGS B PST ARx G XO1 OUT1 STK sp0 FP ly S hp W0 mem md own ly2 S2 hp2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply (proj1 HK); lia.
Qed.
(* W_sites_x.v:795 aj_bcmp_gx_at_x at R, through aj_gx_entry_at_xR (the bcmp contract stays strict) *)
Lemma l3_bcmp_gx_at_xR : forall pc, abcmp_realizes_x SEGS B ARx pc ->
forall G XO OUT W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x n -> src_ok SEGS W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
 (v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc ABC G1 XO OUT W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
HG1 HX16 HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
eapply (SRrG_mono SEGS R).
{ apply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G1 XO OUT (2 * ESTACK) pc (fun _ => False)
    (fun regs' _ => exists v, getr regs' 10 = v /\
      (v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)))
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw HG1 HX16 HJ Hsp Hal Hneg
    ltac:(unfold ESTACK; lia) Hbud Hgp Htp Hra Hraw).
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE [Hlo Hpres]. eapply SRr_mono.
    { exact (ABC lyc Sc Hpc W regsT memT mdc x y n HPRE Hlo Hpres Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
        ltac:(rewrite Hsp; exact Hbx) ltac:(rewrite Hsp; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [exists v; split; [exact Hres | exact Hcmp]|].
    split; [intros a Ha _ Hs; exact (Hfr a Ha Hs) | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (v & Hres & Hcmp) & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hres|]. split; [exact Hcmp|].
split; [intros a Ha Hs; exact (Hfr a Ha (fun H => H) Hs) | exact Hpres2].
Qed.
(* W_check_shape_ends.v:3254 cshe_P_at_x over the R journal *)
Lemma l3_P_at_xR : forall XO OUT STK sp0 ly S hp W mem md HA h PF PLEN,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= PLEN ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
forall ly1 S1 hp1 W1 mem1 md1 kk,
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 (blk_FP (list_blks (hs_held h))) ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk ->
(forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1) /\
(forall a, PF <= a < PF + PLEN + 8 -> 4096 <= a < alloc_ceiling).
Proof.
intros XO OUT STK sp0 ly S hp W mem md HA h PF PLEN HAR0 HSRC HPL HRA HOME ly1 S1 hp1 W1 mem1 md1 kk HJ ROMK.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HOME as [(HR & HS) | (cid & pos & Hin & Hfr)].
- (* a read-only literal *)
  destruct (HS ly1 S1 hp1 W1 mem1 md1 HAR1) as [HRAP HHVP].
  split; [intros a Ha; exact (ROMK a (HR a Ha))|].
  split; [exact HRAP|]. split; [exact (HHVP ltac:(lia))|].
  intros a Ha. destruct (HR a Ha) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
- (* a local of one of the entry's fake frames *)
  assert (HBS : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S)).
  { intros b Hb. apply (cshe_src_blks B ly S W mem HA h HSRC b). unfold asrc_blks.
    right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ)
    as (memS & HJi & Hag).
  pose proof HJi as (_ & Hlay & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S hp W mem md cid pos HAR0 Hin) as (Hf0 & Hfc & _).
  destruct (W_frame_x.frame_al64_x SEGS ARx FRMF ly S hp W mem md cid pos HAR0 Hin) as (Hal & Hbal & _).
  assert (HPin : frame_addr ly cid pos <= PF /\ PF + PLEN + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
  { pose proof (Hfr PF ltac:(lia)) as H1. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as H2.
    unfold in_zr, frame_rng in H1, H2. cbn [fst snd] in H1, H2. lia. }
  (* no frame byte and no shadow byte of the frame is in the free footprint, nor in G *)
  assert (NFP : forall x, inFP (blk_FP (list_blks (hs_held h))) x ->
    x < frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly S hp W mem md p k cid pos HAR0 (HBS _ Hpk) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (NFPs : forall x, inFP (blk_FP (list_blks (hs_held h))) x -> x < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p k HAR0 (HBS _ Hpk)) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
  split.
  { intros a Ha. rewrite (F4 cid pos a Hin).
    - apply Hag. rewrite unsigned_lit_small by lia. intros Hg.
      exact (frm_img_x SEGS B ARx LAWS ly S hp W mem md cid pos a HAR0 Hin ltac:(lia) (proj1 (HG a Hg))).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - intros HF. pose proof (NFP a HF). lia. }
  split.
  { apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1));
      [|exact HRA].
    intros x Hx.
    pose proof (cshe_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) x Hal Hbal ltac:(lia)) as Hsx.
    unfold shadow_addr in Hsx. unfold shadow_of_addr.
    assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite (F4 cid pos _ Hin).
    - apply Hag. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). intros Hg.
      pose proof (pa_img_range _ (proj1 (HG _ Hg))). unfold SHADOW_OFF in *. lia.
    - right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
    - intros HF. pose proof (NFPs _ HF). lia. }
  split.
  { assert (EF : frame_addr ly1 cid pos = frame_addr ly cid pos).
    { destruct Hlay as (_ & _ & _ & _ & _ & HF & _). unfold frame_addr. rewrite HF. reflexivity. }
    apply (W_frame_x.shadow_hull_vis_of_frame_x SEGS B ARx LAWS FRMF ly1 S1 hp1 W1 mem1 md1 cid pos PF (PLEN + 1) HAR1);
      [rewrite Hfrs; exact Hin | rewrite EF; lia | rewrite EF; lia | lia]. }
  intros a Ha. lia.
Qed.
(* W_check_shape_ends.v:3203 cshe_epi_m_x and :551 cshe_epi_x at R *)
Lemma l3_epi_m_xR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK = 16528) by reflexivity. rewrite WS in Hceil. pose proof alloc_ceiling_val as ACV.
destruct HFR as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
assert (Hspv : spZ regs = spZ regs0 - 144).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. unfold spZ in Hceil, H47. lia. }
remember (Eimg (Ereg regs (cshe_svextra regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 144) by (rewrite E2; exact Hspv).
assert (N1 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 136) 8 (bv_unsigned (getr regs0 1)))
  by (replace (spZ regs0 - 144 + 136) with (spZ regs0 - 8) by lia; exact M1).
assert (N8 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 128) 8 (bv_unsigned (getr regs0 8)))
  by (replace (spZ regs0 - 144 + 128) with (spZ regs0 - 16) by lia; exact M8).
assert (N9 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 120) 8 (bv_unsigned (getr regs0 9)))
  by (replace (spZ regs0 - 144 + 120) with (spZ regs0 - 24) by lia; exact M9).
assert (N18 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 112) 8 (bv_unsigned (getr regs0 18)))
  by (replace (spZ regs0 - 144 + 112) with (spZ regs0 - 32) by lia; exact M18).
assert (N19 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 104) 8 (bv_unsigned (getr regs0 19)))
  by (replace (spZ regs0 - 144 + 104) with (spZ regs0 - 40) by lia; exact M19).
assert (N20 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 96) 8 (bv_unsigned (getr regs0 20)))
  by (replace (spZ regs0 - 144 + 96) with (spZ regs0 - 48) by lia; exact M20).
assert (N21 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 88) 8 (bv_unsigned (getr regs0 21)))
  by (replace (spZ regs0 - 144 + 88) with (spZ regs0 - 56) by lia; exact M21).
assert (N22 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 80) 8 (bv_unsigned (getr regs0 22)))
  by (replace (spZ regs0 - 144 + 80) with (spZ regs0 - 64) by lia; exact M22).
assert (N23 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 72) 8 (bv_unsigned (getr regs0 23)))
  by (replace (spZ regs0 - 144 + 72) with (spZ regs0 - 72) by lia; exact M23).
assert (N24 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 64) 8 (bv_unsigned (getr regs0 24)))
  by (replace (spZ regs0 - 144 + 64) with (spZ regs0 - 80) by lia; exact M24).
assert (N25 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 56) 8 (bv_unsigned (getr regs0 25)))
  by (replace (spZ regs0 - 144 + 56) with (spZ regs0 - 88) by lia; exact M25).
assert (N26 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 48) 8 (bv_unsigned (getr regs0 26)))
  by (replace (spZ regs0 - 144 + 48) with (spZ regs0 - 96) by lia; exact M26).
assert (N27 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 40) 8 (bv_unsigned (getr regs0 27)))
  by (replace (spZ regs0 - 144 + 40) with (spZ regs0 - 104) by lia; exact M27).
assert (HS : st_ok_pi SEGS VAL E ss_cshe_ret
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cshe_ret. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, cshe_frmR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
    cbn [base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 40 8 (SOff 45 0) (bv_unsigned (getr regs0 27)));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 27) | zside | exact N27].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 48 8 (SOff 44 0) (bv_unsigned (getr regs0 26)));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 26) | zside | exact N26].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 56 8 (SOff 43 0) (bv_unsigned (getr regs0 25)));
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 25) | zside | exact N25].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 64 8 (SOff 42 0) (bv_unsigned (getr regs0 24)));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 24) | zside | exact N24].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 72 8 (SOff 41 0) (bv_unsigned (getr regs0 23)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 23) | zside | exact N23].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 80 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 22) | zside | exact N22].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 88 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 21) | zside | exact N21].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 96 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 20) | zside | exact N20].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 104 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 19) | zside | exact N19].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 112 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 18) | zside | exact N18].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 120 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 9) | zside | exact N9].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 128 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 8) | zside | exact N8].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 136 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | l3_v64 (getr regs0 1) | zside | exact N1].
  - apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [cshe_efacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hceil H47 Hal16 C1 C3 WS ACV. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
    apply Z.divide_sub_r; [exact Hal16 | exists 9; reflexivity]. }
assert (SHOK : sh_ok SEGS Bx [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO OUT).
unfold cfg_at. change (w64 (BASE + A_cshe_ret)) with (Z_to_bv 64 (BASE + A_cshe_ret)).
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_frmR. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (HR1 : getr (ms_regs ms) 1 = getr regs0 1) by (rewrite R1; exact E32).
assert (ZB : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r)
  by (intros z r <-; apply Z_to_bv_bv_unsigned).
assert (HPRES : aregs_preserved regs0 (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (ZB 2 (2%bv : bv 5) eq_refl), R2, Usp.
    replace (spZ regs0 - 144 + 144) with (spZ regs0) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (ZB 3 (3%bv : bv 5) eq_refl), R3, E3. exact H3.
  - rewrite (ZB 4 (4%bv : bv 5) eq_refl), R4, E4. exact H4.
  - rewrite (ZB 8 (8%bv : bv 5) eq_refl), R8. exact E34.
  - rewrite (ZB 9 (9%bv : bv 5) eq_refl), R9. exact E35.
  - assert (Hr18 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr18 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite (ZB 18 (18%bv : bv 5) eq_refl), R18. exact E36.
    + rewrite (ZB 19 (19%bv : bv 5) eq_refl), R19. exact E37.
    + rewrite (ZB 20 (20%bv : bv 5) eq_refl), R20. exact E38.
    + rewrite (ZB 21 (21%bv : bv 5) eq_refl), R21. exact E39.
    + rewrite (ZB 22 (22%bv : bv 5) eq_refl), R22. exact E40.
    + rewrite (ZB 23 (23%bv : bv 5) eq_refl), R23. exact E41.
    + rewrite (ZB 24 (24%bv : bv 5) eq_refl), R24. exact E42.
    + rewrite (ZB 25 (25%bv : bv 5) eq_refl), R25. exact E43.
    + rewrite (ZB 26 (26%bv : bv 5) eq_refl), R26. exact E44.
    + rewrite (ZB 27 (27%bv : bv 5) eq_refl), R27. exact E45. }
assert (HKEEP : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (HFr x) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_ret In] in Hin. unfold cshe_frmR in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
cbn [ms_regs ms_mem]. rewrite HR1, Hra.
apply (HQ (ms_regs ms) (ms_mem ms) _ HPRES HKEEP).
apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
Lemma l3_epi_xR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
apply (l3_epi_m_xR W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR).
intros regs' mem' md' HPRES HMEQ HJ'. apply (HQ regs' mem' md' HPRES); [| |exact HJ'].
- intros a Ha. apply (aview_eq_of SEGS). apply HMEQ.
- intros a Hp. exact (cshe_apres_meq W mem mem' a (HMEQ _) Hp).
Qed.

(* ------------------------------------------------------------------ the loop at R *)
Section loopR.
(* the entry of check_shape_ends (cshe_spec's names), and what the loop keeps needing of it *)
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (XO AT HA PF A0 O OUT : Z) (h : hsrc) (P ob : list byte).
(* the room round: the caller's room budget past this call (cshe_post_x's kr) *)
Variable kr : nat.
Local Notation H0 := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_held h))).
Local Notation Post := (cshe_post_xR B PST ARx R MT RP G regs0 ly S hp W mem md XO AT HA h P A0 0 ob kr).
Local Notation WANT := (CheckRep.want_of P (hl_recs (hs_held h))).
Local Notation LIT := (VAL A_lit_end5).
Local Notation PLEN := (Z.of_nat (length P)).
Hypothesis HPRE : afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs0 mem md ch.
Hypothesis HX0 : 0 <= XO.
Hypothesis HX16 : XO mod 16 = 0.
Hypothesis HXtop : sp0 + XO <= ly_top ly.
Hypothesis HAT8 : AT mod 8 = 0.
Hypothesis HATl : sp0 <= AT.
Hypothesis HATh : AT + 8 <= sp0 + XO.
Hypothesis HA8 : HA mod 8 = 0.
Hypothesis HAlo : 4096 <= HA.
Hypothesis HAhi : HA + ASRC <= kLowMemEnd.
Hypothesis HGa : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis Hzs : azs B (HA + 64) 32.
Hypothesis Hn26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis HOlen : Z.of_nat (length ob) = O.
Hypothesis HO40 : O <= 2 ^ 40.
Hypothesis HO32 : 0 < O -> O < 2 ^ 32.
Hypothesis HOM : amem_range OUT (O + 8).
Hypothesis HOB : ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h).
Hypothesis HA0 : 0 <= A0 <= O.
Hypothesis HROM0 : rom_view SEGS W mem.
(* the source g_s[j]: image bytes the allocator does not own, not errno, not read-only (cshe_spec's cshe_home for
   them, at its image clause; the stack and fake-frame clauses do not hold of g_s) *)
Hypothesis HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a.
(* and apart from the three other globals the loop keeps: g_gone, g_nout, g_out (objects of cshe_ro) *)
Hypothesis HAg : forall a, HA <= a < HA + ASRC -> ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\
  ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= a < VAL A_g_out + 8).
(* the prefix P at PF (cshe_spec's PF facts): a read-only literal (.str.2, 0x20ee0, at the remove arm and the exit) or
   a local of one of the entry's fake frames (prefix[48], at the gone arm); HPHOME is cshe_spec's premise for it *)
Hypothesis HPz : ~ In (Z_to_bv 8 0) P.
Hypothesis HPl : PLEN + 1 < 2 ^ 32.
Hypothesis HPF0 : 0 < PF.
Hypothesis HPFh : PF + PLEN + 8 <= 2 ^ 63.
Hypothesis HPHOME : (forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
  exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos)).
Hypothesis HPB : forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0))).
Hypothesis HPN : aview SEGS (w_H W) mem (PF + PLEN) = Some 0.
Hypothesis HPV : forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis HPM1 : amem_range PF (PLEN + 1).
Hypothesis HPM8 : amem_range PF 8.
(* P's shadow at the entry (cshe_spec's premise) and the entry's source (its held blocks are the walk's free
   footprint): what W_check_shape_ends.v's cshe_P_at carries P's facts along the journal with *)
Hypothesis HPRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1).
Hypothesis HSRC0 : asrc_at B ly S W mem HA h.
(* .str.4 " end" (A_lit_end5), the bcmp operand: its bytes (cshe_spec's garr8 premise); read-only by HEND5R *)
Hypothesis HLG : garr8 SEGS (arm W mem) LIT (bzs END5).

Lemma l3_lit_bytesR : forall k, 0 <= k < 4 ->
aview SEGS (w_H W) mem (LIT + k) = Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0))).
Proof.
intros k Hk. assert (Hk' : (Z.to_nat k < length (bzs END5))%nat) by (cbn; lia).
pose proof (garr8_mbyte SEGS (arm W mem) LIT _ (Z.to_nat k) HLG Hk') as Hm.
unfold aview. replace (LIT + k) with (LIT + Z.of_nat (Z.to_nat k)) by lia. unfold arm in Hm. rewrite Hm.
cbn [option_map]. f_equal.
assert (Hc : (Z.to_nat k = 0 \/ Z.to_nat k = 1 \/ Z.to_nat k = 2 \/ Z.to_nat k = 3)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.
(* errno's four bytes are image bytes (the runtime's api_env), none of them a byte of g_s[j]; l3_errno_img
   restated, as its lia may close over the loop's hypotheses *)
Lemma l3_errno_imgR : forall q, 0 <= q < 4 -> in_img SEGS (as_errno B + q).
Proof. intros q Hq. pose proof (pal_env B TL) as (_ & HeImg & _). apply HeImg. lia. Qed.
Lemma l3_errno_offR : forall q, 0 <= q < 4 -> ~ (HA <= as_errno B + q < HA + ASRC).
Proof. intros q Hq Hc. destruct (HAimg (as_errno B + q) Hc) as (_ & _ & He & _). lia. Qed.
(* errno's view is the entry's (cshe_post's conjunct) *)
Definition l3_errR (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j).

(* the invariant at the head, w turns left (the plain proof's cse_inv, old ASan proof 23f70bc959c
   lib/A/Prog/check_shape_ends.v:503-521, over this walk's journal) *)
Definition l3_regsR (regs1 : bvmap 5 word) (w : nat) : Prop :=
getr regs1 2 = w64 (sp0 - 144) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 8 = w64 (HA + 88) /\ getr regs1 9 = w64 PF /\ getr regs1 18 = w64 (HA + 80) /\ getr regs1 19 = w64 AT /\
getr regs1 20 = w64 LIT /\ getr regs1 24 = w64 4 /\ getr regs1 25 = w64 SB /\
getr regs1 26 = w64 ((HA + 80) / 8 + SB) /\ getr regs1 27 = w64 (Z.of_nat w + 1).
Definition l3_invR (w : nat) (ds : list (Z * list byte)) (c : Z) (W1 : world SEGS) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist),
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk /\
asrc_at B ly1 S1 W1 mem1 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT = Some (rsF, ds ++ dsF, c + cF)) /\
0 <= c /\ A0 + c <= O /\
val_mem SEGS (arm W1 mem1) AT 8 (A0 + c) /\ val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W1 mem1) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W1 mem1) (VAL A_g_out) 8 OUT /\
ob_at W1 mem1 OUT ob /\ (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
(* the room round: one free per record left past the caller's kr, and the live counts, which only fall *)
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W1 mem1 /\ cshe_saved W1 mem1 sp0 regs0 /\
val_mem SEGS (arm W1 mem1) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
l3_regsR regs1 w /\ l3_errR W1 mem1.

(* the second state of a turn, 0x85614 (after has_prefix, a0 = &l->v[i]): the line l is read (the cell `at` moved past it),
   its record i found; nothing of the allocator changed yet *)
Definition l3_midR (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist),
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk /\
asrc_at B ly1 S1 W2 mem2 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
(i < length (hl_recs H1))%nat /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) (skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob) w <> None /\
(forall rsF dsF cF, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1))
   (skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob) w = Some (rsF, dsF, cF) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, (ds ++ [nth i (hl_recs H1) (0, [])]) ++ dsF, (c + Z.of_nat (length l) + 1) + cF)) /\
0 <= c /\ A0 + (c + Z.of_nat (length l) + 1) <= O /\
val_mem SEGS (arm W2 mem2) AT 8 (A0 + (c + Z.of_nat (length l) + 1)) /\ val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W2 mem2) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W2 mem2) (VAL A_g_out) 8 OUT /\
ob_at W2 mem2 OUT ob /\ (exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W2 mem2 /\ cshe_saved W2 mem2 sp0 regs0 /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
l3_regsR regs2 (Datatypes.S w) /\ getr regs2 21 = w64 (Z.of_nat i) /\ getr regs2 10 = w64 (hl_v H1 + 16 * Z.of_nat i) /\
l3_errR W2 mem2.

(* the state at 0x855d0 (after bcmp): the line l at the stream's A0 + c is read, `at` moved past it, its stem
   found at record i (the model's find_text), the line passed the length and " end" checks *)
Definition l3_abR (w : nat) (ds : list (Z * list byte)) (c : Z) (l : list byte) (i : nat) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
exists ly1 S1 hp1 kk (H1 : hlist) (d' : list byte),
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk /\
asrc_at B ly1 S1 W2 mem2 HA (CheckRep.set_held h H1) /\
hl_v H1 = hl_v H0 /\ hl_cap H1 = hl_cap H0 /\ NoDup (CheckRep.texts H1) /\
incl (hl_recs H1) (hl_recs H0) /\ (length (hl_recs H1) + length ds = length (hl_recs H0))%nat /\
skipn (Z.to_nat (A0 + c)) ob = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l /\ l3_ok P l = true /\
CheckRep.find_text (firstn (length l - 4) l) (hl_recs H1) = Some i /\
CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w <> None /\
(forall rsF dsR cR, CheckRep.ends_run P (CheckRep.drop_nth i (hl_recs H1)) d' w = Some (rsF, dsR, cR) ->
  CheckRep.ends_run P (hl_recs H0) (skipn (Z.to_nat A0) ob) WANT =
  Some (rsF, ds ++ nth i (hl_recs H1) (0, []) :: dsR, c + (Z.of_nat (length l) + 1 + cR))) /\
0 <= c /\ A0 + c + Z.of_nat (length l) + 1 <= O /\
val_mem SEGS (arm W2 mem2) AT 8 (A0 + c + Z.of_nat (length l) + 1) /\ val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 0 /\
val_mem SEGS (arm W2 mem2) (VAL A_g_nout) 8 O /\ val_mem SEGS (arm W2 mem2) (VAL A_g_out) 8 OUT /\
ob_at W2 mem2 OUT ob /\ (exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly1 S1)) /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly1 S1) rest) /\
frames S1 = frames S /\
mo_le MT S S1 (Z.of_nat (length ds) * mo_free MT) /\ mo_ok MT S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) /\
rp_RM RP S1 (length (hl_recs H1) + kr) /\ cnt_ok RP (ablocks B ly1 S1) /\
rom_view SEGS W2 mem2 /\ cshe_saved W2 mem2 sp0 regs0 /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 24) 8 (Z.of_nat (length l)) /\
val_mem SEGS (arm W2 mem2) (sp0 - 144 + 32) 8 (OUT + (A0 + c)) /\
l3_regsR regs2 (Datatypes.S w) /\ getr regs2 10 = w64 0 /\ getr regs2 22 = w64 (Z.of_nat (length l)) /\
getr regs2 23 = w64 (OUT + (A0 + c)) /\ l3_errR W2 mem2.

(* the first part of a turn: next_line, the length check and bcmp of " end", from the head to 0x855d0 *)
Lemma l3_A1R : forall w ds c W1 regs1 mem1 md1, l3_invR (Datatypes.S w) ds c W1 regs1 mem1 md1 ->
(forall l i W2 regs2 mem2 md2, l3_abR w ds c l i W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3b)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c W1 regs1 mem1 md1 HI HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (ly1 & S1 & hp1 & kk & H1 & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & HRUN & HREL & Hc0 & HcO & MAT & MG & MNO & MOUT & HOBt & HOBK & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & HREGS & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
(* the model: this turn's line l, its record i *)
assert (Hex : exists rsF dsF cF,
  CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w) = Some (rsF, dsF, cF)).
{ destruct (CheckRep.ends_run P (hl_recs H1) (skipn (Z.to_nat (A0 + c)) ob) (Datatypes.S w)) as [[[x y] z]|];
  [exists x, y, z; reflexivity | exfalso; exact (HRUN eq_refl)]. }
destruct Hex as (rsF & dsF & cF & ER).
destruct (l3_ends_S P _ _ w rsF dsF cF ER) as (l & d' & i & dsR & cR & Ed & Hnz & Hok & Hft & HrR & EdsF & EcF).
destruct (l3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold l3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply l3_leqb in Hend.
assert (HlenS : length (skipn (Z.to_nat (A0 + c)) ob) = (length l + Datatypes.S (length d'))%nat) by (rewrite Ed, length_app; reflexivity).
rewrite length_skipn in HlenS.
assert (HAl : A0 + c + Z.of_nat (length l) + 1 <= O) by lia.
assert (Hob1 : ob <> []) by (intros E0; rewrite E0 in HlenS; cbn in HlenS; lia).
destruct HOBK as [E0 | (CO & HCO & HOin)]; [exfalso; exact (Hob1 E0)|].
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (Hw26 : (Datatypes.S w <= length (hl_recs H1))%nat) by (apply (l3_ends_len P _ _ (skipn (Z.to_nat (A0 + c)) ob)); rewrite ER; discriminate).
assert (HN0 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cshe_l3_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l)) (Z.of_nat (Datatypes.S w))
  R2 R8 R18 R24 R25 R26 R27 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' HlnR Hlen32 Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
assert (V18 : base_val E (Some 18%nat) = HA + 80).
{ cbn [base_val]. rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl), R18.
  apply unsigned_lit_small. unfold ASRC, kLowMemEnd in HAhi. lia. }
paj_run_to_tok_xR RUNTOG HS HJ0 SHOK Bspan AF_fr_next_line.
{ cbv [ss_mem ss_cshe_l3 cshe_l3_fr cshe_l3_hd].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (OUT + (A0 + c))) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length l))) by exact (EX 3%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
(* the run to the call wrote nothing but l->n's window, which it did not store to either *)
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. apply (aview_kept_out E (ss_mem ss_cshe_l3) (w_H W1) mem1 (ms_mem ms) HFr a Ha).
  intros (rg & Hin & Hrg). cbn [ss_mem ss_cshe_l3 In] in Hin. unfold cshe_l3_fr, cshe_l3_hd in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg; [lia|]. rewrite V18 in Hrg. lia. }
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREn : afn_pre_x SEGS B ARx NL_STK ly1 S1 hp1 W1 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W1 (ms_mem ms) mdc kk
    (ms_regs ms) NL_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold NL_STK, NL_FRAME, ESTACK. lia.
  - unfold NL_STK, NL_FRAME, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
assert (HO0 : 0 < O) by lia.
assert (HOw : forall a, OUT <= a < OUT + CO -> ~ (sp0 - CSHE_STK <= a < sp0 + XO)) by (intros a Ha; lia).
destruct (Z.mod_divide (sp0 - 144) 16 ltac:(lia)) as [Hd16 _]. destruct (Hd16 HSPa) as [q16 Hq16]. clear Hd16.
eapply (SRrG_bind SEGS R R_trans).
{ apply l3_lift_wle. apply (NL W1 ly1 S1 hp1 (ms_regs ms) (ms_mem ms) mdc [] (XO + 144) AT (sp0 - 144 + 32) (sp0 - 144 + 24)
    (A0 + c) O OUT ob HPREn).
  - lia.
  - rewrite Zplus_mod, HX16. reflexivity.
  - rewrite Usp1, Etop. lia.
  - rewrite Usp1. intros a Ha. apply HPRi. rewrite WS. lia.
  - rewrite Q10, E19. reflexivity.
  - rewrite Q11, Usp. reflexivity.
  - rewrite Q12, Usp. reflexivity.
  - exact HAT8.
  - replace (sp0 - 144 + 32) with ((2 * q16 + 4) * 8) by lia. apply Z_mod_mult.
  - replace (sp0 - 144 + 24) with ((2 * q16 + 3) * 8) by lia. apply Z_mod_mult.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - rewrite Usp1. lia.
  - lia.
  - lia.
  - lia.
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (l3_ra_stack ly1 S1 (hp := hp1) W1 (ms_mem ms) mdc); [exact HAR1m | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [intros k Hk; apply KEEPr; lia | exact MAT].
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact MNO].
    intros k Hk. pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
    apply KEEPr; [lia|]. intros Hc. destruct (HAg (VAL A_g_nout + k) ltac:(unfold ASRC; lia)) as (_ & Hn & _). apply Hn. lia.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact MOUT].
    intros k Hk. pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
    apply KEEPr; [lia|]. intros Hc. destruct (HAg (VAL A_g_out + k) ltac:(unfold ASRC; lia)) as (_ & _ & Hn). apply Hn. lia.
  - exact HOlen.
  - intros k Hk. rewrite KEEPr; [exact (HOBt k Hk) | lia |].
    intros Hc. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))).
  - lia.
  - intros _. split; [lia|]. split; [lia|]. split; [exact (HO32 HO0)|]. intros a Ha. rewrite Usp1. unfold NL_STK, NL_FRAME, ESTACK. lia.
  - intros _. split; [rewrite Ed; apply in_or_app; right; left; reflexivity|]. split; [exact HOM|].
    split; [apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia]|].
    split; [apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms) mdc OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]|].
    intros a Hr. rewrite KEEPr; [exact (HROM a Hr) | |].
    + destruct Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
    + intros Hc. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
cbv beta. intros W2 c2 HR2 (Hwle2 & regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
subst W2.
destruct HARM as [(HAeq & _) | (ln & HAlt & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
assert (Hln : ln = l).
{ destruct Hfl as (rest & Hsk & Hnz'). rewrite Ed in Hsk. destruct (l3_nul_unique l ln d' rest Hsk Hnz Hnz') as [-> _]. reflexivity. }
subst ln.
rewrite Usp1 in HJn, HFRn.
assert (HJc' : ajournal_gx_x SEGS B PST ARx G (XO + 144) (nl_cells AT (sp0 - 144 + 32) (sp0 - 144 + 24)) NL_STK (sp0 - 144) []
  ly1 S1 hp1 W1 (ms_mem ms) mdc [] ly1 S1 hp1 W1 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha) | exact HJn]. }
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W1 (ms_mem ms) mdc kk NL_STK (sp0 - 144) (XO + 144) (nl_cells AT (sp0 - 144 + 32) (sp0 - 144 + 24)) [] []
  ly1 S1 hp1 W1 mem2 md2 0 HJ0 (l3_jR HJc')
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
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HXOn; [lia|].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRn; [lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W1) (ms_mem ms) mem2 a); [intros Hp; exact (HPn a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; rewrite OLDa by lia; exact U18).
apply (st_ok_pi_add_region Ea _ _ cshe_l3_cells) in HS; [| reflexivity | | ].
2: { unfold region_ok, cshe_l3_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
  cbn [base_val]. rewrite UspA. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 144) 24 8 (SOff 35 0) (Z.of_nat (length l)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vlen2].
  + apply (chunk_ok_val SEGS Ea _ (sp0 - 144) 32 8 (SOff 34 0) (OUT + (A0 + c)));
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vln2]. }
2: { apply all_disjoint_of_extents. unfold cshe_l3_cells, extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem]. rewrite V18a. cbn [base_val]. rewrite UspA.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. lia. }
assert (HAR2 : ARx ly1 S1 hp1 W1 mem2 md2) by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem2 md2 kk HJ2).
assert (F25 : ew Ea 25 = w64 SB) by (rewrite OLDa by lia; exact E25).
assert (F18 : ew Ea 18 = w64 (HA + 80)) by (rewrite OLDa by lia; exact E18).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB F25) by (unfold SB; lia). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80) F18) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite Q1.
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. unfold cshe_l3_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNG BRR HS SHOK2 Bspan.
{ (* next_line returned 0: it found the line *)
  exfalso. rewrite branch_eq_U, (U_atom Ea 40 1 F40), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem add_cond]. unfold cshe_l3_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* the two runs since next_line wrote nothing but l->n's window *)
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha Hno.
  lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ =>
    rewrite (aview_kept_out _ _ _ _ _ Hf a Ha) end.
  - lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end.
  - intros (rg & Hin & Hrg).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U18a in Hrg; lia|]).
    destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
set (xb := OUT + (A0 + c) + Z.of_nat (length l) - 4).
assert (R10b : getr (ms_regs ms1) 10 = w64 xb).
{ rewrite T10, (OLDa 34%nat), (OLDa 35%nat) by lia. rewrite E34, E35. rewrite unsigned_lit_small by lia.
  rewrite YI08.alu64_add_lit. unfold w64, xb. f_equal. lia. }
assert (R11b : getr (ms_regs ms1) 11 = w64 LIT) by (rewrite T11, (OLDa 20%nat) by lia; exact E20).
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 144) by (unfold spZ; rewrite T2; exact UspA).
(* the rom view and the stream, carried to the call *)
assert (ROMK1 : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  assert (Hno : ~ (HA + 88 <= a < HA + 92)) by (intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr)).
  rewrite KEEP1 by lia. rewrite HFRn; [ | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
  - apply KEEPr; lia.
  - intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (HROM1 : rom_view SEGS W1 (ms_mem ms1)) by (intros a Hr; rewrite ROMK1 by exact Hr; exact (HROM a Hr)).
assert (ROMW : forall a, in_rom SEGS a -> aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W) mem a)
  by (intros a Hr; rewrite (HROM1 a Hr); symmetry; exact (HROM0 a Hr)).
assert (OBK1 : ob_at W1 (ms_mem ms1) OUT ob).
{ intros k Hk. rewrite KEEP1; [exact (Hob2 k Hk) | lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
assert (HAR3 : ARx ly1 S1 hp1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2))
  by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ2).
pose proof (pa_obj_img 31 ltac:(lia)) as HLR. change (A_OBJ 31) with A_lit_end5 in HLR.
assert (HLITr : forall k, 0 <= k < 4 -> aview SEGS (w_H W1) (ms_mem ms1) (LIT + k) =
  Some (bv_unsigned (nth (Z.to_nat k) CheckRep.END4 (Z_to_bv 8 0)))).
{ intros k Hk. rewrite ROMW by (apply HEND5R; lia). exact (l3_lit_bytesR k Hk). }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W1) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (OBK1 (A0 + c + k)) by lia.
  do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
  apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
eapply (SRrG_bind SEGS R R_trans).
{ apply (l3_bcmp_gx_at_xR (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms1) (ms_mem ms1) CSHE_STK sp0 FPc
    ly S hp W mem md [] ly1 S1 hp1 _ kk xb LIT 4 (-144) (Z_to_bv 64 (BASE + 13028)) HG HX16 HJ2 R10b R11b T12).
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
  - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia].
  - intros _. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | unfold xb; lia | unfold xb; lia | lia].
  - exact (proj1 (HEND5S ly1 S1 hp1 W1 (ms_mem ms1) _ HAR3)).
  - intros Hp4. exact (proj2 (HEND5S ly1 S1 hp1 W1 (ms_mem ms1) _ HAR3) Hp4). }
cbv beta. intros W3 c3 HR3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros k Hk. unfold xb. replace (OUT + (A0 + c) + Z.of_nat (length l) - 4 + k) with
    (OUT + (A0 + c) + (Z.of_nat (length l) - 4 + k)) by lia.
  rewrite HLINE by lia. rewrite HLITr by lia. do 2 f_equal. rewrite <- Hend, l3_nth_skipn. f_equal. lia. }
(* what the turn kept so far, from the head's memory mem1: every byte outside this function's stack window and
   l->n, and presence *)
assert (KEEPc3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CSHE_STK <= a < sp0 + XO) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hw Hn. rewrite Hfr3; [| exact Ha | rewrite WS in Hw; unfold ESTACK; lia].
  rewrite KEEP1 by assumption. rewrite HFRn; [ | exact Ha | rewrite WS in Hw; unfold NL_STK, NL_FRAME, ESTACK; lia |].
  - apply KEEPr; assumption.
  - intros (rg & Hin & Hrg). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia. }
assert (PRES3 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem3 a).
{ intros a Hp. apply Hpres3.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPn. apply (apresent_grows _ _ _ _ HG0). exact Hp. }
assert (ROMK3 : forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite Hfr3; [exact (ROMW a Hr) | lia | unfold ESTACK; lia]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W1) (ms_mem ms1) mem3 a); [intros Hp; exact (Hpres3 a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F56 : ew Eb 56 = w64 0) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv; exact Hv0).
clear HEb.
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
(* ---- 0x855d0: the state l3_abR *)
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
prreg HS (25%bv : bv 5) N25. prreg HS (27%bv : bv 5) N27.
prreg_raw HS (26%bv : bv 5) N26.
(* l->n's value is still n (the region based at s2, chunk 8) *)
pose proof (st_ok_pi_region_nth Eb _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg2 U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnH3.
assert (FRK3 : forall a, sp0 - 144 <= a < sp0 + XO -> ~ (sp0 - 144 + 24 <= a < sp0 - 144 + 40) -> ~ (AT <= a < AT + 8) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hc1 Hc2. rewrite Hfr3 by (unfold ESTACK; lia). rewrite KEEP1 by lia. rewrite HXOn by
    (try lia; intros (rg & Hin & Hrg); cbn [nl_cells In] in Hin; destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrg; lia).
  apply KEEPr; lia. }
assert (CK3 : forall a, sp0 - 144 <= a < sp0 + XO -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha. rewrite Hfr3 by (unfold ESTACK; lia). apply KEEP1; lia. }
replace (BASE + 13028) with (BASE + A_cshe_l3b) by (unfold A_cshe_l3b, AF_fr_check_shape_ends; lia).
apply (HKont l i W1 regs3 mem3 md3).
exists ly1, S1, hp1, kk, H1, d'.
split; [exact HJ3|].
split.
{ apply (l3_src_step ly1 S1 md1 W1 W1 mem1 mem3 HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha Hw Hn. apply KEEPc3; assumption.
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W1) (w_H W1) mem1 mem3 (HA + 80 + 8) 4 (hl_n H1) k MnH MnH3). cbn. lia.
  - exact PRES3.
  - apply wle_refl. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split; [exact Ed|]. split; [exact Hnz|]. split; [exact Hok|]. split; [exact Hft|].
split; [rewrite HrR; discriminate|].
split.
{ intros rsF' dsR' cR' Hx. apply HREL. rewrite Ed. exact (l3_ends_step P (hl_recs H1) l d' i w rsF' dsR' cR' Hnz Hok Hft Hx). }
split; [exact Hc0|]. split; [exact HAl|].
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [intros k Hk'; apply CK3; cbn in Hk'; lia|].
  replace (A0 + c + Z.of_nat (length l) + 1) with (A0 + c + Z.of_nat (length l) + 1) by lia. exact Vat2. }
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
pose proof (proj1 (HGR (VAL A_g_gone) ltac:(unfold inG, cshe_ro; apply Exists_exists; exists (VAL A_g_gone, 1); split; [left; reflexivity | unfold in_zr; cbn; lia]))) as Igg.
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MG].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_gone + k) ltac:(unfold ASRC; lia)) as (Hn1x & _). apply Hn1x. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MNO].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_nout + k) ltac:(unfold ASRC; lia)) as (_ & Hn1x & _). apply Hn1x. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact MOUT].
  intros k Hk'. cbn in Hk'. apply KEEPc3; [lia | rewrite WS; lia |].
  intros Hc'. destruct (HAg (VAL A_g_out + k) ltac:(unfold ASRC; lia)) as (_ & _ & Hn1x). apply Hn1x. lia. }
split.
{ intros k Hk'. rewrite KEEPc3; [exact (HOBt k Hk') | lia | rewrite WS; lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
split; [exists CO; split; [exact HCO | exact HOin]|].
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split; [exact HRMr|]. split; [exact HCNTr|].
split; [intros a Hr; rewrite (ROMK3 a Hr); exact (HROM0 a Hr)|].
split.
{ apply (l3_saved_kept W1 W1 mem1 mem3 sp0 regs0); [|exact HSAV].
  intros a Ha. apply FRK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem3); [|exact M16]. intros k Hk'. cbn in Hk'. apply FRK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [|exact Vlen2]. intros k Hk'. cbn in Hk'. apply CK3; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 mem3); [|exact Vln2]. intros k Hk'. cbn in Hk'. apply CK3; lia. }
split.
{ unfold l3_regsR.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split; [|rewrite N27, OLDba by lia; exact E27].
  rewrite N26. unfold w64, cshe_l3_shv. apply bv_eq.
  change (bv_unsigned (sv_denot Eb (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))))
    with (U Eb (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 25 0))).
  rewrite (l3_U_sh Eb 18 0 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | exact E25 | lia]).
  rewrite Z.add_0_r. assert (HD80 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite unsigned_lit_small; [reflexivity | unfold SB; lia]. }
split; [rewrite N10, F56; reflexivity|].
split; [rewrite N22, OLDba by lia; exact E35|].
split; [rewrite N23, OLDba by lia; exact E34|].
intros q Hq. pose proof (pa_img_range _ (l3_errno_imgR q Hq)) as HeR.
rewrite KEEPc3; [exact (HERR q Hq) | lia | rewrite WS; lia | intros Hc; apply (l3_errno_offR q Hq); unfold ASRC; lia].
Qed.

(* the second part of a turn: list_find of the line's stem, has_prefix of the line, the shadow check of l->v and
   a0 = &l->v[i], from 0x855d0 to 0x85614 *)
Lemma l3_A2R : forall w ds c l i W2 regs2 mem2 md2, l3_abR w ds c l i W2 regs2 mem2 md2 ->
(forall W3 regs3 mem3 md3, l3_midR w ds c l i W3 regs3 mem3 md3 ->
  SRrG SEGS R W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + A_cshe_l3s)) mem3 (seg_rom SEGS)) md3) Post) ->
SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3b)) mem2 (seg_rom SEGS)) md2) Post.
Proof.
intros w ds c l i W2 regs2 mem2 md2 HAB HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAB as (ly1 & S1 & hp1 & kk & H1 & d' & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & Ed & Hnz & Hok & Hft & HRUN & HREL &
  Hc0 & HAl & MAT & MG & MNO & MOUT & HOBt & (CO & HCO & HOin) & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & M24 & M32 &
  HREGS & R10 & R22 & R23 & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
destruct (l3_find_text _ _ _ Hft) as (Hi & Hti & Hfirst).
pose proof Hok as Hok'. unfold l3_ok in Hok'. apply andb_prop in Hok' as [Hok1 Hpre]. apply andb_prop in Hok1 as [H4 Hend].
apply Nat.leb_le in H4. apply l3_leqb in Hend.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem2 md2 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W2 mem2 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W2 mem2 md2 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by (apply (l3_ends_len P _ _ d'); exact HRUN).
rewrite (l3_drop_len _ _ Hi) in Hw26.
assert (HN0 : (length (hl_recs H1) <= length (hl_recs H0))%nat) by lia.
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 mem2 md2 (HA + 64) 32 HAR1 Hzs) as HRA64.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
assert (HlnR : 4096 <= OUT + (A0 + c) <= 140737479966720) by lia.
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hlen32 : 4 <= Z.of_nat (length l) <= 2 ^ 32) by (pose proof (HO32 ltac:(lia)); lia).
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
destruct (cshe_l3b_state W2 regs2 mem2 (sp0 - 144) HA (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l)) (Z.of_nat (Datatypes.S w))
  R2 R8 R18 R24 R25 R26 R27 R10 R22 R23 HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' HlnR Hlen32 Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia]) M24 M32) as [HS SHOK].
remember (Eimg (Ereg regs2 (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs2 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (OUT + (A0 + c)) (Z.of_nat (length l))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 (Z.of_nat (length l))) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (OUT + (A0 + c))) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
paj_run_to_tok_xR RUNTOG HS HJ0 SHOK Bspan AF_fr_list_find.
{ cbv [ss_mem ss_cshe_l3b cshe_l3b_cells cshe_l3_fr cshe_l3_hd].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2; exact Usp).
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms)) |- _ => l3_wkeep Hf U18 end. }
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
(* l->n is still n *)
pose proof (st_ok_pi_region_nth E _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region E _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg2 U18 ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as MnHr.
assert (PRESr : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) by (intros a Hp; exact (apresent_grows _ _ _ _ HG0 Hp)).
assert (HSRCr : asrc_at B ly1 S1 W2 (ms_mem ms) HA (CheckRep.set_held h H1)).
{ apply (l3_src_step ly1 S1 md2 W2 W2 mem2 (ms_mem ms) HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha _ Hn. apply KEEPr; assumption.
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W2) (w_H W2) mem2 (ms_mem ms) (HA + 80 + 8) 4 (hl_n H1) k MnH MnHr). cbn. lia.
  - exact PRESr.
  - apply wle_refl. }
pose proof HSRCr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAHr & _).
destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 _ _ kk HJ0)
  as (memS & HJi & HgS).
pose proof HJi as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRi & _).
assert (HAR1m : ARx ly1 S1 hp1 W2 (ms_mem ms) mdc) by exact (proj1 HJi).
assert (HPREf : afn_pre_x SEGS B ARx LFIND_STK ly1 S1 hp1 W2 (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS md [] ly1 S1 hp1 W2 (ms_mem ms) mdc kk
    (ms_regs ms) LFIND_STK (- 144 - XO) [] HJi).
  - rewrite Usp1. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia. }
assert (HLINE : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KEEPr; cycle 1; [lia | |].
  - intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + (A0 + c) + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + (A0 + c) + k) ltac:(unfold ASRC; lia))).
  - replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (HOBt (A0 + c + k)) by lia.
    do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
    apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
set (sb := firstn (length l - 4) l).
assert (Hsb : length sb = (length l - 4)%nat) by (unfold sb; rewrite length_firstn; lia).
eapply (SRrG_bind SEGS R R_trans).
{ apply l3_lift_wle. apply (LFIND W2 ly1 S1 hp1 (ms_regs ms) (ms_mem ms) mdc [] (HA + 80) H1 true (OUT + (A0 + c)) sb HPREf).
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11, E23. reflexivity.
  - rewrite Q12, E22, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hsb. lia.
  - exact HAHr.
  - rewrite Zplus_mod, HA8. reflexivity.
  - lia.
  - unfold kLowMemEnd. lia.
  - eapply range_addressable_sub; [exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 (ms_mem ms) mdc (HA + 64) 32 HAR1m Hzs) | lia | lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - lia.
  - rewrite Hsb. lia.
  - rewrite Hsb. lia.
  - intros k Hk. rewrite Hsb in Hk. rewrite HLINE by lia. do 2 f_equal. unfold sb. rewrite nth_firstn.
    destruct (Z.to_nat k <? length l - 4)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia].
  - intros a Ha. rewrite Usp1. unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - rewrite Hsb. unfold amem_range in HOM |- *. lia.
  - rewrite Hsb. eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia].
  - rewrite Hsb. intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms) _ OUT CO); [exact HAR1m | exact HOin | lia | lia | lia]. }
cbv beta. intros W3 c3 HR3 (Hwle3 & -> & regs3 & mem3 & md3 & -> & HJf & HPf & HPRf & HFRf & HRES).
assert (HRESi : getr regs3 10 = w64 (Z.of_nat i)).
{ destruct HRES as [(j & (Hj1 & Hj2 & Hj3) & Hr10) | (Hnf & _)].
  - rewrite Hr10. do 2 f_equal. apply (l3_first_unique (hl_recs H1) sb j i Hj2 Hj3 Hti Hfirst).
  - exfalso. exact (Hnf i Hi Hti). }
rewrite Usp1 in HJf, HFRf.
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W2 (ms_mem ms) mdc kk LFIND_STK (sp0 - 144) 0 [] [] [] ly1 S1 hp1 W2 mem3 md3 0 HJ0 (l3_jR HJf)
  ltac:(rewrite WS; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
jafter_call_keep_pi HS 36%nat regs3 (mrestrict (w_H W2) mem3) HPf [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3b_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRf; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia.
  - intros a Ha Hw. apply (writable_kept (w_H W2) (ms_mem ms) mem3 a); [intros Hp; exact (HPRf a Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 (Z.of_nat i)) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact HRESi).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (HAR2 : ARx ly1 S1 hp1 W2 mem3 md3) by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 mem3 md3 kk HJ2).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W2 mem3 md3 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB) by (rewrite ?OLDa by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80)) by (rewrite ?OLDa by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite Q1.
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNG BRR HS SHOK2 Bspan.
{ (* bltz: list_find found the record, i >= 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit_small; lia).
  cbn [sv_denot] in Hc. rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. unfold w64 in Hc.
  rewrite bv_signed_small in Hc by (rewrite Hu; lia). rewrite Hu in Hc. change (bv_signed (Z_to_bv 64 0)) with 0 in Hc. lia. }
clear Hc.
paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 Bspan AF_fr_has_prefix.
{ cbn [ss_mem add_cond]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (Usp2 : spZ (ms_regs ms1) = sp0 - 144) by (unfold spZ; rewrite P2; exact UspA).
(* what list_find and the runs kept of mem2 *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hn.
  transitivity (aview SEGS (w_H W2) (ms_mem ms0) a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => l3_wkeep Hf U18a end. }
  transitivity (aview SEGS (w_H W2) mem3 a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end. }
  rewrite HFRf by assumption. apply KEEPr; assumption. }
assert (ROMK : forall a, in_rom SEGS a -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KEEP2; [rewrite (HROM a Hr); symmetry; exact (HROM0 a Hr) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
assert (HLINE2 : forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W2) (ms_mem ms1) (OUT + (A0 + c) + k) =
  Some (bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)))).
{ intros k Hk. rewrite KEEP2; cycle 1; [lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia | |].
  - intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + (A0 + c) + k) HAR1 HOin ltac:(lia)).
    exact (proj1 (HAimg (OUT + (A0 + c) + k) ltac:(unfold ASRC; lia))).
  - replace (OUT + (A0 + c) + k) with (OUT + (A0 + c + k)) by lia. rewrite (HOBt (A0 + c + k)) by lia.
    do 2 f_equal. replace (Z.to_nat (A0 + c + k)) with (Z.to_nat (A0 + c) + Z.to_nat k)%nat by lia.
    apply (l3_nth_line ob l d' (Z.to_nat (A0 + c)) (Z.to_nat k) Ed). lia. }
(* the stack's bounds, for P's distance from has_prefix's scratch below *)
pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & Hceil0 & Hslo0 & _) & _).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdh := mdq) in * end.
destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W2 _ _ kk HJ2)
  as (memS2 & HJi2 & HgS2).
assert (HAR3 : ARx ly1 S1 hp1 W2 (ms_mem ms1) mdh) by exact (proj1 HJi2).
assert (HPREh : afn_pre_x SEGS B ARx HP_STK ly1 S1 hp1 W2 (ms_regs ms1) (ms_mem ms1) mdh []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FPc ly S hp W memS2 md [] ly1 S1 hp1 W2 (ms_mem ms1) mdh kk
    (ms_regs ms1) HP_STK (- 144 - XO) [] HJi2).
  - rewrite Usp2. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HX16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
  - rewrite P3, OLDa, E3 by lia. exact Hgp0.
  - rewrite P4, OLDa, E4 by lia. exact Htp0.
  - apply achain_low. unfold s0Z. rewrite P8, U18a. rewrite unsigned_lit_small by lia. lia. }
(* P's bytes, shadow and bound at the call, in both homes (W_check_shape_ends.v cshe_P_at) *)
destruct (l3_P_at_xR XO [(AT, AT + 8)] CSHE_STK sp0 ly S hp W mem md HA h PF PLEN (proj1 HPRE) HSRC0
  ltac:(lia) HPRA HPHOME ly1 S1 hp1 W2 (ms_mem ms1) mdh kk HJ2 ROMK) as (PK & HRAP & HHVP & PLOW).
eapply (SRrG_bind SEGS R R_trans).
{ apply l3_lift_wle. apply (W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP W2 ly1 S1 hp1 (ms_regs ms1) (ms_mem ms1) mdh []
    (OUT + (A0 + c)) (Z.of_nat (length l)) PF PLEN HPREh).
  - rewrite P10, OLDa, E23 by lia. reflexivity.
  - rewrite P11, OLDa, E22 by lia. reflexivity.
  - rewrite P12, OLDa, E9 by lia. reflexivity.
  - lia.
  - lia.
  - exact HPl.
  - exact HPF0.
  - lia.
  - lia.
  - lia.
  - split; [lia|]. split.
    + intros k Hk. exists (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0))). split.
      * rewrite PK by lia. exact (HPB k Hk).
      * intros H0z. apply HPz. assert (Hn0 : nth (Z.to_nat k) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0z; reflexivity).
        rewrite <- Hn0. apply nth_In. lia.
    + intros _. rewrite PK by lia. exact HPN.
  - intros a Ha. rewrite PK by lia. apply HPV. lia.
  - unfold hp_off. rewrite Usp2. intros a Ha. pose proof (PLOW a ltac:(lia)).
    unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *. lia.
  - exact HPM1.
  - exact HPM8.
  - exact HRAP.
  - exact HHVP.
  - intros a Ha. pose proof (Z.mod_pos_bound (PF + PLEN) 8 ltac:(lia)). rewrite PK by lia. apply HPV. lia.
  - intros a Hr. rewrite ROMK by exact Hr. exact (HROM0 a Hr).
  - intros Hle. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros a Ha. replace a with (OUT + (A0 + c) + (a - (OUT + (A0 + c)))) by lia. rewrite HLINE2 by lia. discriminate.
    + unfold hp_off. rewrite Usp2. intros a Ha. unfold HP_STK, ESTACK. lia.
    + unfold amem_range in HOM |- *. lia.
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia].
    + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W2 (ms_mem ms1) _ OUT CO); [exact HAR3 | exact HOin | lia | lia | lia].
    + eapply range_addressable_sub; [exact HRAP | lia | lia].
    + intros Hpos. exact (l3_shv_sub _ PF (PLEN + 1) PLEN ltac:(lia) ltac:(lia) HHVP). }
cbv beta. intros W4 c4 HR4 (Hwle4 & regs4 & mem4 & md4 & -> & HJh & HPh & HPRh & HFRh & HRESh).
assert (Hpref : PLEN <= Z.of_nat (length l) /\ hp_prefix_of W2 (ms_mem ms1) (OUT + (A0 + c)) PF PLEN).
{ unfold CheckRep.prefixb in Hpre. apply andb_prop in Hpre as [Hp1 Hp2]. apply Nat.leb_le in Hp1. apply l3_leqb in Hp2.
  split; [lia|]. intros k Hk. rewrite HLINE2 by lia. rewrite PK by lia. rewrite (HPB k Hk).
  do 2 f_equal. rewrite <- Hp2. rewrite nth_firstn. destruct (Z.to_nat k <? length P)%nat eqn:Ek; [reflexivity | apply Nat.ltb_ge in Ek; lia]. }
assert (Hr10h : getr regs4 10 = w64 1).
{ destruct HRESh as [(_ & _ & Hr) | (Hnp & _)]; [exact Hr | exfalso; exact (Hnp (proj1 Hpref) (proj2 Hpref))]. }
rewrite Usp2 in HJh, HFRh.
assert (HJc' : ajournal_gx_x SEGS B PST ARx G 0 [] HP_STK (sp0 - 144) [] ly1 S1 hp1 W2 (ms_mem ms1) mdh [] ly1 S1 hp1 W4 mem4 md4 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|]. apply ajournal_gx_nil_x. exact HJh. }
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G CSHE_STK sp0 XO [(AT, AT + 8)] FPc ly S hp W mem md []
  ly1 S1 hp1 W2 (ms_mem ms1) mdh kk HP_STK (sp0 - 144) 0 [] [] [] ly1 S1 hp1 W4 mem4 md4 0 HJ2 (l3_jR HJc')
  ltac:(rewrite WS; unfold HP_STK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_r in HJ3.
jafter_call_keep_pi HS 52%nat regs4 (mrestrict (w_H W4) mem4) HPh [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold cshe_l3b_cells. repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HFRh; unfold HP_STK, ESTACK; lia.
  - intros a Ha Hw. apply (l3_writable_kept_w W2 W4 (ms_mem ms1) mem4 a); [intros Hp; exact (HPRh a Hp) | exact Hwle4 | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (F56 : ew Eb 56 = w64 1) by (rewrite HEb; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hr10h).
clear HEb.
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (HAR4 : ARx ly1 S1 hp1 W4 mem4 md4) by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W4 mem4 md4 kk HJ3).
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (SHOK3 : sh_ok SEGS Bx1 cshe_l3_SH Eb (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W4 mem4 md4 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB) by (rewrite ?OLDba by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
rewrite P1.
paj_run_tok_xR RUNG HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUNG BRR HS SHOK3 Bspan.
{ exfalso. rewrite branch_eq_U, (U_atom Eb 56 1 F56), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 Bspan A_cshe_l3s.
{ cbn [ss_mem add_cond]. unfold cshe_l3b_cells.
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* ---- 0x85614: the state l3_midR *)
assert (KEEPall : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W4) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hn.
  transitivity (aview SEGS (w_H W4) (ms_mem ms2) a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem ms3)) |- _ => l3_wkeep Hf U18b end. }
  transitivity (aview SEGS (w_H W4) mem4 a).
  { lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem4) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
  rewrite HFRh by (try exact Ha; unfold HP_STK, LFIND_STK, LFIND_FRAME, ESTACK in *; lia). apply KEEP2; assumption. }
assert (PRESall : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W4) (ms_mem ms3) a).
{ intros a Hp.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem ms3)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem4) (mrestrict _ (ms_mem ms2)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPRh.
  lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply HPRf. exact (apresent_grows _ _ _ _ HG0 Hp). }
pose proof (st_ok_pi_region_nth Eb _ _ 2 cshe_l3_hd HS ltac:(vm_compute; reflexivity)) as HRg3. cbn [ms_mem restrict] in HRg3.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 0) (hl_n H1) HRg3 U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnH4.
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20. prreg HS (21%bv : bv 5) N21. prreg HS (24%bv : bv 5) N24.
prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
replace (BASE + 13096) with (BASE + A_cshe_l3s) by (unfold A_cshe_l3s, AF_fr_check_shape_ends; lia).
apply (HKont W4 (ms_regs ms3) (ms_mem ms3) _).
exists ly1, S1, hp1, kk, H1.
split; [exact HJ3|].
split.
{ apply (l3_src_step ly1 S1 md2 W2 W4 mem2 (ms_mem ms3) HA (CheckRep.set_held h H1) (sp0 - CSHE_STK) (sp0 + XO) HAR1 HSRC).
  - intros a Ha. exact (proj1 (HAimg a Ha)).
  - lia.
  - intros a Ha Hw Hn. apply KEEPall; [exact Ha | rewrite WS in Hw; unfold LFIND_STK, LFIND_FRAME, ESTACK; lia | exact Hn].
  - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
    apply (l3_aview_of_val_mem2 (w_H W2) (w_H W4) mem2 (ms_mem ms3) (HA + 80 + 8) 4 (hl_n H1) k MnH MnH4). cbn. lia.
  - exact PRESall.
  - exact Hwle4. }
split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HINC|]. split; [exact HLEN|].
split; [exact Hi|].
assert (Esk : skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob = d').
{ replace (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) with (Z.to_nat (A0 + c) + length l + 1)%nat by lia.
  exact (l3_skip_line ob l d' (Z.to_nat (A0 + c)) Ed). }
rewrite Esk.
split; [exact HRUN|].
split.
{ intros rsF dsF cF Hx. rewrite (HREL rsF dsF cF Hx). rewrite <- app_assoc. cbn [app]. f_equal. f_equal. lia. }
split; [lia|]. split; [lia|].
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. change (A_OBJ 13) with A_g_nout in HnoR.
pose proof (pa_obj_img 15 ltac:(lia)) as HoR. change (A_OBJ 15) with A_g_out in HoR.
assert (KV : forall x n v, 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
  (forall a, x <= a < x + Z.of_nat n -> ~ (sp0 - 144 - LFIND_STK <= a < sp0 - 144) /\ ~ (HA + 88 <= a < HA + 92)) ->
  val_mem SEGS (arm W2 mem2) x n v -> val_mem SEGS (arm W4 (ms_mem ms3)) x n v).
{ intros x n v Hx0 Hx1 Hx2 Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W4) mem2 (ms_mem ms3)); [|exact Hv].
  intros k Hk. destruct (Hx2 (x + k) ltac:(lia)) as [Hw Hn]. apply KEEPall; [lia | exact Hw | exact Hn]. }
split.
{ replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + c + Z.of_nat (length l) + 1) by lia.
  apply KV; [lia | lia | intros a Ha; split; lia | exact MAT]. }
split.
{ apply KV; [lia | lia | | exact MG]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (Hn1x & _). apply Hn1x. lia. }
split.
{ apply KV; [lia | lia | | exact MNO]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & Hn1x & _). apply Hn1x. lia. }
split.
{ apply KV; [lia | lia | | exact MOUT]. intros a Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. split; [unfold LFIND_STK, LFIND_FRAME, ESTACK; lia|].
  intros Hc'. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & _ & Hn1x). apply Hn1x. lia. }
split.
{ intros k Hk'. rewrite KEEPall; [exact (HOBt k Hk') | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W2 mem2 md2 OUT CO (OUT + k) HAR1 HOin ltac:(lia)).
  exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))). }
split; [exists CO; split; [exact HCO | exact HOin]|].
split; [exact HPERM|]. split; [exact HFRS|]. split; [exact HMLE|]. split; [exact HMOK|].
split; [exact HRMr|]. split; [exact HCNTr|].
split.
{ intros a Hr. pose proof Hr as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HIR.
  rewrite KEEPall; [exact (HROM a Hr) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hr). }
split.
{ apply (l3_saved_kept W2 W4 mem2 (ms_mem ms3) sp0 regs0); [|exact HSAV].
  intros a Ha. apply KEEPall; lia. }
split.
{ apply KV; [lia | lia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; lia | exact M16]. }
split.
{ unfold l3_regsR.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split; [|rewrite N27, OLDba by lia; exact E27].
  rewrite N26, (OLDba 18%nat), (OLDba 25%nat) by lia. rewrite E18, E25. unfold w64.
  rewrite l3_srl3 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
split.
{ rewrite N21. rewrite OLDb by lia. exact F40. }
rewrite N10, (OLDba 32%nat) by lia. rewrite E32. rewrite OLDb by lia. rewrite F40. unfold w64.
assert (Hi26 : Z.of_nat i < 2 ^ 26) by (unfold hl_n in Hn26; lia).
split; [rewrite l3_sll4 by lia; rewrite YI08.alu64_add_lit; f_equal; lia|].
intros q Hq. pose proof (pa_img_range _ (l3_errno_imgR q Hq)) as HeR.
rewrite KEEPall; [exact (HERR q Hq) | lia | unfold LFIND_STK, LFIND_FRAME, ESTACK; lia |].
intros Hc; apply (l3_errno_offR q Hq); unfold ASRC; lia.
Qed.

(* the third part of a turn: the inlined list_drop (free(v[i].s), __asan_memmove of the records above, n - 1),
   s11 - 1 and the back-edge: to the head when turns are left, else to the epilogue and the post *)
Lemma l3_BR : forall w ds c l i W1 regs1 mem1 md1, l3_midR w ds c l i W1 regs1 mem1 md1 ->
(forall W2 regs2 mem2 md2 ds' c', (1 <= w)%nat -> l3_invR w ds' c' W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cshe_l3)) mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3s)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros w ds c l i W1 regs1 mem1 md1 HM HKont.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HM as (ly1 & S1 & hp1 & kk & H1 & HJ0 & HSRC & HV & HC & HND & HINC & HLEN & Hi & HRUN & HREL & Hc1 & HcO &
  MAT & MG & MNO & MOUT & HOBt & (CO & HCO & HOin) & HPERM & HFRS & HMLE & HMOK & HRMr & HCNTr & HROM & HSAV & M16 & HREGS & R21 & R10 & HERR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R24 & R25 & R26 & R27).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (QA : ASTACK = 16384) by reflexivity.
assert (HSPb : 2 ^ 46 <= sp0 - 144 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (HSPa : (sp0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
assert (HAhi' : HA + 96 <= 0x7fff8000) by (unfold ASRC, kLowMemEnd in HAhi; lia).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ0) as HAR1.
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO HAR1 HOin) as (O16 & O4096 & Oceil & Oapp & Opres & _).
assert (HreqO : CO <= req_size CO) by (unfold req_size; destruct (CO =? 0) eqn:Eq; [apply Z.eqb_eq in Eq|]; lia).
pose proof HSRC as (_ & _ & _ & _ & HAwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAH & _).
assert (HAH1 : alist_at B ly1 S1 W1 mem1 (HA + 80) H1 true) by exact HAH. clear HAH.
pose proof HAH1 as (MvH & MnH & McH & MwH & (HnleC & HcapLt) & HvvH & HNDvH & HninH & HFallH).
assert (Hn1 : 1 <= hl_n H1) by (unfold hl_n; lia).
destruct HvvH as [(Hc00 & _) | (Hcpos & HvinH & HjunkH & HgarrH)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HvinH) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (HreqV : req_size (AREC * hl_cap H1) = AREC * hl_cap H1)
  by (unfold req_size; destruct (AREC * hl_cap H1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
assert (HvR : 4096 <= hl_v H1 <= 140737479966720) by (rewrite HreqV in Vceil; unfold AREC in Vceil; lia).
assert (Hn1' : 1 <= hl_n H1 <= 2 ^ 26) by (unfold hl_n in *; lia).
assert (Hi26 : Z.of_nat i < hl_n H1) by (unfold hl_n; lia).
assert (Hw26 : (w <= length (CheckRep.drop_nth i (hl_recs H1)))%nat) by exact (l3_ends_len P _ _ _ HRUN).
rewrite (l3_drop_len _ _ Hi) in Hw26.
assert (Hw1 : 1 <= Z.of_nat (Datatypes.S w) < 2 ^ 26) by (unfold hl_n in Hn26; lia).
(* the record i: its block, and its text pointer in the vector's slot *)
set (r := nth i (hl_recs H1) (0, [])).
assert (HinR : In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly1 S1)).
{ rewrite Forall_forall in HFallH. exact (proj1 (HFallH r (nth_In _ _ Hi))). }
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 _ _ HAR1 HinR) as (R16 & R4096 & Rceil & Rapp & Rpres & _).
assert (HreqR : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.of_nat (length (snd r)) + 1 =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia | reflexivity]).
destruct (l3_rec_fields ly1 S1 W1 mem1 (HA + 80) H1 true i HAH1 Hi) as (Ms0 & _).
fold r in Ms0. rewrite Z.mod_small in Ms0 by lia.
set (EA := hl_v H1 + 16 * Z.of_nat i).
assert (HEAlo : 4096 <= EA) by (unfold EA; lia).
assert (HEAhi : EA + 16 <= hl_v H1 + AREC * hl_cap H1) by (unfold EA, AREC, hl_n in *; lia).
assert (HEA16 : EA mod 16 = 0).
{ unfold EA. rewrite Zplus_mod, V16. replace (16 * Z.of_nat i) with (Z.of_nat i * 16) by lia. rewrite Z_mod_mult. reflexivity. }
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (HA + 64) 32 HAR1 Hzs) as HRA64.
destruct (cshe_l3s_state W1 regs1 mem1 (sp0 - 144) HA (hl_v H1) (hl_n H1) (fst r) 4 (Z.of_nat (Datatypes.S w)) EA (Z.of_nat i)
  R2 R8 R18 R24 R25 R26 R27 R10 R21 HEAlo ltac:(unfold AREC in HEAhi; rewrite HreqV in Vceil; unfold AREC in Vceil; lia) HEA16
  ltac:(unfold hl_n in Hn26; lia) ltac:(unfold AREC in HEAhi; rewrite HreqV in Vceil; unfold AREC in Vceil; rewrite WS in Hslo; lia)
  ltac:(destruct (Z_lt_le_dec EA (HA + 96)) as [Hx|Hx]; [right|left; exact Hx];
        destruct (Z_lt_le_dec (EA + 16) (HA + 81)) as [Hy|Hy]; [lia|];
        exfalso; apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (Z.max EA (HA + 80)) HAR1 HvinH
          ltac:(rewrite HreqV; unfold AREC in *; lia));
        exact (proj1 (HAimg (Z.max EA (HA + 80)) ltac:(unfold ASRC; lia))))
  ltac:(rewrite HreqV in Vapp; unfold in_app, kLowShadowBeg, kHighMemBeg, AREC in Vapp |- *; unfold AREC in HEAhi; lia) HSPb HSPa HA8 HAlo HAhi' HvR V16 Hn1' ltac:(rewrite HreqR in Rceil; lia) ltac:(lia) Hw1 M16 MvH
  ltac:(replace (HA + 88) with (HA + 80 + 8) by lia; exact MnH)
  ltac:(intros j Hj; replace (HA + 88 + j) with (HA + 80 + (8 + j)) by lia; apply MwH; lia)
  ltac:(eapply range_addressable_sub; [exact HRA64 | lia | lia])
  Ms0
  ltac:(eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1));
        [exact HAR1 | exact HvinH | lia | rewrite HreqV; unfold AREC in *; lia])) as [HS SHOK].
remember (Eimg (Ereg regs1 (cshe_l3_extra (hl_v H1) (hl_n H1) (fst r) 4))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose (RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNG := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (cshe_l3_extra (hl_v H1) (hl_n H1) (fst r) 4) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = w64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EEo 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EEo 4%nat 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = w64 PF) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = w64 EA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = w64 (HA + 80)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 AT) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 LIT) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (Z.of_nat i)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v H1)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n H1)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (fst r)) by exact (EX 2%nat ltac:(lia)).
clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = HA + 80) by (rewrite E18; apply unsigned_lit_small; lia).
assert (V18 : base_val E (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18).
(* ---- 0x85614 .. 0x85628: the shadow checks of v[i] and l->v, a0 = v[i].s, jal free ---- *)
paj_run_tok_xR RUNG HS HJ0 SHOK Bspan.
{ cbv [ss_mem ss_cshe_l3s cshe_l3_fr cshe_l3_hd cshe_l3_slot].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18 in Ha; apply HGa; lia|].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem1) (mrestrict _ (ms_mem ms)) |- _ => l3_wkeep Hf U18 end. }
assert (Usp1 : spZ (ms_regs ms) = sp0 + -144) by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite Q2, Usp; lia).
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HAR1m : ARx ly1 S1 hp1 W1 (ms_mem ms) mdc) by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 W1 _ _ kk HJ0).
(* ---- free(v[i].s) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (l3_free_gxR XO [(AT, AT + 8)] W1 (ms_regs ms) (ms_mem ms) CSHE_STK sp0 FPc ly S hp W mem md [] ly1 S1 hp1 mdc kk
    (fst r) (Z.of_nat (length (snd r)) + 1) (-144) (Z_to_bv 64 (BASE + 13120)) [] (length (hl_recs (ldrop_list H1 i)) + kr)
    HJ0 HX16 HinR).
  - rewrite Q10, E34. reflexivity.
  - exact Usp1.
  - reflexivity.
  - lia.
  - rewrite WS, QA. lia.
  - rewrite Q3, E3. exact Hgp0.
  - rewrite Q4, E4. exact Htp0.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly1 _ (spZ (ms_regs ms)) (HA + 88) [] (ms_regs ms)).
    + apply achain_low. lia.
    + rewrite Usp1. rewrite WS in Hslo. lia.
    + unfold s0Z. rewrite Q8, U18. rewrite unsigned_lit_small by lia. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_check_shape_ends + 0x27c); [exact HCTX_cshe_l3|].
    unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. unfold AF_fr_check_shape_ends. lia.
  - (* the free's room: one record fewer is left past it *)
    apply (l3_rm_cast RP S1 _ _ HRMr). change (hl_recs (ldrop_list H1 i)) with (CheckRep.drop_nth i (hl_recs H1)).
    rewrite (l3_drop_len _ _ Hi). lia.
  - exact HCNTr.
  - intros _ k Hk. exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; lia].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r, Z.of_nat (length (snd r)) + 1)).
    unfold list_blks. apply in_or_app. right.
    apply (in_map (fun rr => (fst rr, Z.of_nat (length (snd rr)) + 1))). apply HINC. apply nth_In. exact Hi.
  - pose proof (mo_free_nonneg MT ML) as Hf0.
    apply (mok_station MT S1 S1 (Z.of_nat (length (hl_recs H1)) * mo_free MT) 0 (mo_free MT) ML HMOK
      (mo_le_refl MT ML S1) Hf0). unfold hl_n in Hn1. nia. }
cbv beta. intros W2 c2 HR2 (ly2 & S2 & hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle & HRM2 & HEf & Hpres2).
assert (HAR2 : ARx ly2 S2 hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
assert (IMGK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a /\
  (apresent (w_H W1) (ms_mem ms) a -> apresent (w_H W2) mem2 a)).
{ intros a Hia Ho He. split; [exact (proj1 (proj2 (proj2 HK)) a Hia Ho He)|].
  apply (Hpres2 a Hia).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 hp1 W1 (ms_mem ms) _ a HAR1m Hia) Hw)).
  - intros Hw. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 hp2 W2 mem2 md2 a HAR2 Hia) Hw)).
  - exact He.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 (ms_mem ms) _ (fst r) _ a HAR1m HinR Hr Hia). }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK); rewrite ?WS, ?QA in *; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    exact (proj1 (IMGK a Hia Ho He)).
  - intros a Ha Hw. destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    apply (l3_writable_kept_img W1 W2 (ms_mem ms) mem2 a Hia); [exact (proj2 (IMGK a Hia Ho He)) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = sp0 - 144) by (rewrite OLDa by lia; exact Usp).
assert (U18a : bv_unsigned (ew Ea 18) = HA + 80) by (rewrite OLDa by lia; exact U18).
assert (V18a : base_val Ea (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18a).
assert (SHOK2 : sh_ok SEGS Bx1 cshe_l3_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem2 md2 (HA + 64) 32 HAR2 Hzs).
  - unfold Bx1. rewrite (U_atom Ea 25 SB) by (rewrite ?OLDa by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Ea 18 (HA + 80)) by (rewrite ?OLDa by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18a in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (F21 : ew Ea 21 = w64 (Z.of_nat i)) by (rewrite OLDa by lia; exact E21).
assert (F32 : ew Ea 32 = Z_to_bv 64 (hl_v H1)) by (rewrite OLDa by lia; exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 (hl_n H1)) by (rewrite OLDa by lia; exact E33).
assert (Uspm : spZ (ms_regs ms0) = sp0 - 144)
  by (change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)); rewrite P2; exact UspA).
assert (R10m : getr (ms_regs ms0) 10 = w64 EA).
{ rewrite P10, F21, F32. unfold w64. rewrite l3_sll4 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
assert (R11m : getr (ms_regs ms0) 11 = w64 (EA + 16)).
{ rewrite P11, F21, F32. unfold w64. rewrite l3_sll4 by lia. rewrite !YI08.alu64_add_lit. f_equal; lia. }
assert (R12m : getr (ms_regs ms0) 12 = w64 (AREC * (hl_n H1 - Z.of_nat i - 1))).
{ rewrite P12, F21, F33. unfold w64. rewrite l3_count_eq by lia. unfold AREC. f_equal; lia. }
assert (VNE : hl_v H1 <> fst r) by (intros Heq; apply HninH; rewrite Heq; apply in_map; apply nth_In; exact Hi).
assert (Hvin2 : In (hl_v H1, AREC * hl_cap H1) (ablocks B ly2 S2)).
{ pose proof HvinH as Hv1. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hv1.
  apply in_app_or in Hv1 as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply VNE. first [exact Ex | exact (eq_sym Ex)]. }
assert (HAR3 : ARx ly2 S2 hp2 W2 (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2))
  by exact (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 _ _ (kk + 1) HJ2).
destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ _ _ HAR3 Hvin2) as (V16' & V4096' & Vceil' & Vapp' & Vpres' & _).
rewrite HreqV in Vceil', Vapp', Vpres'.
assert (ROMIMG : forall a, in_rom SEGS a -> in_img SEGS a)
  by (intros a Hr; destruct Hr as (sg & Hsg & _ & Hra); exists sg; split; [exact Hsg | exact Hra]).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
  rewrite KEEPr; [exact (HROM a Hrom) | lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom). }
assert (ROM2 : rom_view SEGS W2 mem2) by (eapply (acall_kept_rom_view_x SEGS B ARx LAWS); [exact HAR2 | exact HK | exact ROMNS | exact ROM1]).
assert (KEEPm : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => l3_wkeep Hf U18a end. }
assert (ROMK : rom_view SEGS W2 (ms_mem ms0)).
{ intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
  rewrite KEEPm; [exact (ROM2 a Hrom) | lia |].
  intros Hcz. exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom). }
assert (Ecap : (hl_cap H0 =? 0) = false) by (apply Z.eqb_neq; rewrite <- HC; lia).
assert (HvFP : forall a, hl_v H1 <= a < hl_v H1 + AREC * hl_cap H1 -> inFP FPc a).
{ intros a Ha. exists (hl_v H0, hl_v H0 + req_size (AREC * hl_cap H0)).
  split; [|cbn [fst snd]; rewrite <- HV, <- HC, HreqV; lia].
  unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v H0, AREC * hl_cap H0)).
  unfold list_blks. rewrite Ecap. apply in_or_app. left. left. reflexivity. }
assert (HEAeq : EA = hl_v H1 + 16 * Z.of_nat i) by reflexivity. clearbody EA.
assert (HnC : hl_n H1 <= hl_cap H1) by lia.
(* ---- the memmove of the records above i, 0x85660 ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G XO [(AT, AT + 8)] ESTACK (SIGMA WS_asan_memmove)
  (fun a => EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) _
  W2 (ms_regs ms0) (ms_mem ms0) CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 _ (kk + 1)
  (- 144) (Z_to_bv 64 (BASE + 13176)) HG HX16 HJ2).
- exact Uspm.
- reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite WS. unfold ESTACK. lia.
- rewrite P3, OLDa, E3 by lia. exact Hgp0.
- rewrite P4, OLDa, E4 by lia. exact Htp0.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec EA a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (EA + AREC * (hl_n H1 - Z.of_nat i - 1))) as [Hd2|Hd2]; [left; lia | right; lia].
- intros a Ha HGb. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact (proj1 (HG a HGb))].
- intros a Ha HnG. split; [|unfold AREC in *; lia].
  right. left. split; [apply HvFP; unfold AREC in *; lia|].
  exists (hl_v H1), (AREC * hl_cap H1). split; [exact Hvin2 | rewrite HreqV; unfold AREC in *; lia].
- intros HPRE2 HSC.
  assert (MNIMG : forall a, EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1) -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2).
    rewrite HreqV. unfold AREC in *. lia. }
  apply (AMOVE ly2 S2 hp2 W2 (ms_regs ms0) (ms_mem ms0) _
    EA (EA + 16) (AREC * (hl_n H1 - Z.of_nat i - 1)) HPRE2 R10m R11m R12m).
  + unfold AREC in *; lia.
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres' a ltac:(unfold AREC in *; lia))).
    * exact (proj2 (Vpres' a ltac:(unfold AREC in *; lia))).
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + lia.
  + unfold AREC in *; lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres' a ltac:(unfold AREC in *; lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. unfold AREC, ESTACK in *. lia.
  + apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite HreqV; unfold AREC in *; lia | exact Hpos].
  + exact ROMK.
  + intros Hpos. split; (apply (l3_amem_of_app _ _ _ _ Vapp'); unfold AREC in *; lia).
  + exact MNIMG. }
cbv beta. intros W3 c3 HR3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 mem3 md3 (kk + 1) HJ3) as HAR4.
assert (MOFF : forall a, in_img SEGS a -> ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1))).
{ intros a Hia Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 hp2 W2 (ms_mem ms0) _ (hl_v H1) (AREC * hl_cap H1) a HAR3 Hvin2);
  [rewrite HreqV; unfold AREC in *; lia | exact Hia]. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UspA, ?U18a.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold AREC, ESTACK in *; lia.
  - intros a Ha _. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (HAimg a ltac:(unfold ASRC; lia)) as (Hia & _).
    pose proof (pa_img_range a Hia). apply Hfr3; [lia | exact (MOFF a Hia) | unfold ESTACK; lia].
  - intros a Ha Hw. apply (l3_writable_kept_w W2 W2 (ms_mem ms0) mem3 a); [intros Hp; exact (Hpres3 a Hp) | apply wle_refl | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 52)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
assert (OLDba : forall m, (m < 36)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (UspB : bv_unsigned (ew Eb 2) = sp0 - 144) by (rewrite OLDb by lia; exact UspA).
assert (U18b : bv_unsigned (ew Eb 18) = HA + 80) by (rewrite OLDb by lia; exact U18a).
assert (V18b : base_val Eb (Some 18%nat) = HA + 80) by (cbn [base_val]; exact U18b).
assert (SHOK3 : sh_ok SEGS Bx1 cshe_l3_SH Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, cshe_l3_SH. constructor; [|constructor].
  eapply shent_ok_of_range.
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 hp2 W2 mem3 md3 (HA + 64) 32 HAR4 Hzs).
  - unfold Bx1. rewrite (U_atom Eb 25 SB) by (rewrite ?OLDba by lia; first [exact E25 | unfold SB; lia]). reflexivity.
  - rewrite (U_atom Eb 18 (HA + 80)) by (rewrite ?OLDba by lia; first [exact E18 | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
paj_run_tok_xR RUNG HS HJ3 SHOK3 Bspan.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
(* ---- 0x85678, the back-edge: first what the turn kept, from (W1, mem1) to (W2, ms_mem ms1) ---- *)
pose proof alloc_ceiling_val as ACV.
assert (HSPc : alloc_ceiling + 16528 <= sp0) by (rewrite WS in Hslo; lia).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FPc ly S hp W mem md [] ly2 S2 hp2 W2 (ms_mem ms1) _ (kk + 1) HJ3) as HARF.
assert (KEEPf : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms1)) |- _ => l3_wkeep Hf U18b end. }
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) -> ~ (sp0 - 144 - ESTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn Hd Hs. rewrite (KEEPf a Ha Hn). rewrite (Hfr3 a Ha Hd ltac:(lia)). exact (KEEPm a Ha Hn). }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 88 <= a < HA + 92) -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hia Ho He Hn. pose proof (pa_img_range a Hia) as Har.
  rewrite (KALL a ltac:(lia) Hn (MOFF a Hia) ltac:(unfold ESTACK; lia)).
  rewrite (proj1 (proj2 (proj2 HK)) a Hia Ho He). apply KEEPr; [lia | exact Hn]. }
assert (KBLK : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <= a < pb + req_size nb ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1)) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros pb nb a Hin Ha Hnr Hnm.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W1 mem1 md1 pb nb HAR1 Hin) as (_ & Hp4096 & Hpc & _ & _ & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb a HAR1 Hin Ha).
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (intros Hc; apply Hni; exact (proj1 (HAimg a ltac:(unfold ASRC; lia)))).
  rewrite (KALL a ltac:(lia) Hnw Hnm ltac:(unfold ESTACK; lia)).
  replace a with (pb + (a - pb)) by lia.
  rewrite (proj1 (proj2 HK) pb nb (a - pb) Hin ltac:(lia) ltac:(cbv beta; lia)).
  replace (pb + (a - pb)) with a by lia. apply KEEPr; [lia | exact Hnw]. }
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 144 - ASTACK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hs.
  assert (Hnw : ~ (HA + 88 <= a < HA + 92)) by (unfold ASRC, kLowMemEnd in HAhi; lia).
  rewrite (KALL a ltac:(lia) Hnw ltac:(unfold AREC in *; lia) ltac:(rewrite QA in Hs; unfold ESTACK; lia)).
  rewrite (proj1 HK a Ha ltac:(lia)). apply KEEPr; [lia | exact Hnw]. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (AREC * hl_cap H1) (fst r)
  (Z.of_nat (length (snd r)) + 1) HAR1 HvinH HinR ltac:(intros Heq; injection Heq as Heq _; exact (VNE Heq))) as DJ.
unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite HreqV, HreqR in DJ.
assert (KMOV : forall k, 0 <= k < AREC * (hl_n H1 - 1 - Z.of_nat i) ->
  aview SEGS (w_H W2) (ms_mem ms1) (hl_v H1 + AREC * Z.of_nat i + k) =
  aview SEGS (w_H W1) mem1 (hl_v H1 + AREC * Z.of_nat i + AREC + k)).
{ intros k Hk. unfold AREC in *.
  assert (Hni1 : ~ in_img SEGS (EA + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (16 * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hni2 : ~ in_img SEGS (EA + 16 + k))
    by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 (hl_v H1) (16 * hl_cap H1)); [exact HAR1 | exact HvinH | rewrite HreqV; lia]).
  assert (Hnw1 : ~ (HA + 88 <= EA + k < HA + 92))
    by (intros Hc; apply Hni1; exact (proj1 (HAimg (EA + k) ltac:(unfold ASRC; lia)))).
  assert (Hnw2 : ~ (HA + 88 <= EA + 16 + k < HA + 92))
    by (intros Hc; apply Hni2; exact (proj1 (HAimg (EA + 16 + k) ltac:(unfold ASRC; lia)))).
  replace (hl_v H1 + 16 * Z.of_nat i + k) with (EA + k) by lia.
  replace (hl_v H1 + 16 * Z.of_nat i + 16 + k) with (EA + 16 + k) by lia.
  rewrite (KEEPf (EA + k) ltac:(lia) Hnw1).
  rewrite (Hmov k ltac:(lia)).
  rewrite (KEEPm (EA + 16 + k) ltac:(lia) Hnw2).
  replace (EA + 16 + k) with (hl_v H1 + (16 * Z.of_nat i + 16 + k)) by lia.
  rewrite (proj1 (proj2 HK) (hl_v H1) (16 * hl_cap H1) (16 * Z.of_nat i + 16 + k) HvinH ltac:(rewrite HreqV; lia)
    ltac:(cbv beta; lia)).
  replace (hl_v H1 + (16 * Z.of_nat i + 16 + k)) with (EA + 16 + k) by lia.
  apply KEEPr; [lia | exact Hnw2]. }
assert (KPRES : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W1) mem1 a -> apresent (w_H W2) (ms_mem ms1) a).
{ intros a Hia Ho He Hp.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem3) (mrestrict _ (ms_mem ms1)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply Hpres3.
  lazymatch goal with Hg : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem ms0)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  apply (proj2 (IMGK a Hia Ho He)).
  lazymatch goal with Hg : mem_grows (mrestrict _ mem1) (mrestrict _ (ms_mem ms)) |- _ => apply (apresent_grows _ _ _ _ Hg) end.
  exact Hp. }
assert (BLK2 : forall pb nb, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> In (pb, nb) (ablocks B ly2 S2)).
{ intros pb nb Hin Hne2. destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hin.
  apply in_app_or in Hin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. apply Hne2. first [exact Ex | exact (eq_sym Ex)]. }
assert (KOFF : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> pb <= a < pb + req_size nb ->
  ~ (fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1))).
{ intros pb nb a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 Hin HinR
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. lia. }
assert (KOFV : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> hl_v H1 -> pb <= a < pb + req_size nb ->
  ~ (EA <= a < EA + AREC * (hl_n H1 - Z.of_nat i - 1))).
{ intros pb nb a Hin Hne Ha Hc.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 pb nb (hl_v H1) (AREC * hl_cap H1) HAR1 Hin HvinH
    ltac:(intros Heq; injection Heq as Heq _; exact (Hne Heq))) as DJx.
  unfold zdisjoint in DJx. cbn [fst snd] in DJx. rewrite HreqV in DJx. unfold AREC in *. lia. }
assert (KBK : forall pb nb a, In (pb, nb) (ablocks B ly1 S1) -> pb <> fst r -> pb <> hl_v H1 -> pb <= a < pb + req_size nb ->
  abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros pb nb a Hin Hp1 Hp2 Ha. split.
  - exact (KBLK pb nb a Hin Ha (KOFF pb nb a Hin Hp1 Ha) (KOFV pb nb a Hin Hp2 Ha)).
  - intros Hw. destruct (alx_blocks _ _ _ LAWS ly2 S2 hp2 W2 (ms_mem ms1) _ pb nb HARF (BLK2 pb nb Hin Hp1)) as (_ & _ & _ & _ & Hpr & _).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hpr a Ha))). }
assert (KHD : forall a, HA <= a < HA + ASRC -> ~ (HA + 88 <= a < HA + 92) -> abyte_kept W1 mem1 W2 (ms_mem ms1) a).
{ intros a Ha Hw. destruct (HAimg a Ha) as (Hia & Ho & He & _). split.
  - exact (KIMG a Hia Ho He Hw).
  - intros Hwr. apply (l3_writable_kept_img W1 W2 mem1 (ms_mem ms1) a Hia); [intros Hp; exact (KPRES a Hia Ho He Hp) | exact Hwr]. }
(* l->n after the store: n - 1 *)
pose proof (st_ok_pi_region_nth Eb _ _ 1
  (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
  HS ltac:(vm_compute; reflexivity)) as HRgF. cbn [ms_mem restrict] in HRgF.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgF U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnF.
(* the record i's place in the list, and the list without it *)
destruct (nth_split (hl_recs H1) (0, []) Hi) as (RA & RB & Hsp & HlA).
fold r in Hsp.
assert (Hdrop : CheckRep.drop_nth i (hl_recs H1) = RA ++ RB) by (rewrite Hsp, <- HlA; apply l3_drop_split).
assert (Hldr : hl_recs (ldrop_list H1 i) = RA ++ RB) by exact Hdrop.
assert (Hrnot : ~ In (fst r) (map fst (RA ++ RB))).
{ pose proof HNDvH as ND1. apply NoDup_ListNoDup in ND1. rewrite Hsp, map_app in ND1. cbn [map] in ND1.
  rewrite map_app. exact (List.NoDup_remove_2 _ _ _ ND1). }
assert (HinRA : forall x, In x (RA ++ RB) -> In x (hl_recs H1)).
{ intros x Hx. rewrite Hsp. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HE2 : alist_at B ly2 S2 W2 (ms_mem ms1) (HA + 80) (ldrop_list H1 i) true).
{ apply (ALDROP ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) (HA + 80) H1 true i HAH1 Hi).
  - exact Hbl.
  - intros a Ha. exact (proj1 (KHD a ltac:(unfold ASRC; lia) ltac:(lia))).
  - intros k Hk. destruct (HAimg (HA + 80 + k) ltac:(unfold ASRC; lia)) as (Hia & Ho & He & _).
    apply (l3_writable_kept_img W1 W2 mem1 (ms_mem ms1) (HA + 80 + k) Hia); [intros Hp; exact (KPRES _ Hia Ho He Hp) | exact (MwH k Hk)].
  - exact MnF.
  - intros k Hk. exact (KMOV k Hk).
  - intros a Ha.
    assert (Ha2 : hl_v H1 <= a < hl_v H1 + req_size (AREC * hl_cap H1)) by (rewrite HreqV; unfold AREC in *; lia).
    exact (KBLK (hl_v H1) (AREC * hl_cap H1) a HvinH Ha2 (KOFF (hl_v H1) (AREC * hl_cap H1) a HvinH VNE Ha2)
      ltac:(unfold AREC in *; lia)).
  - intros r' Hr' a Ha. rewrite Hldr in Hr'.
    assert (Hin' : In (fst r', Z.of_nat (length (snd r')) + 1) (ablocks B ly1 S1)).
    { rewrite Forall_forall in HFallH. exact (proj1 (HFallH r' (HinRA r' Hr'))). }
    assert (Hne1 : fst r' <> fst r) by (intros Heq; apply Hrnot; rewrite <- Heq; apply in_map; exact Hr').
    assert (Hne2 : fst r' <> hl_v H1) by (intros Heq; apply HninH; rewrite <- Heq; apply in_map; exact (HinRA r' Hr')).
    exact (proj1 (KBK _ _ a Hin' Hne1 Hne2 ltac:(pose proof (l3_req_ge (Z.of_nat (length (snd r')) + 1) ltac:(lia)); lia))). }
(* ---- the source with the shorter held list ---- *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPD & _ & _ & _ & _ & _ & _ & _ & HPIN & HPJLEN & _ & _ & HED & _ & _).
cbn [CheckRep.set_held hs_pending hs_partial hs_pjunk hs_expected] in HPD, HPIN, HPJLEN, HED.
assert (HreqP : req_size APARTIAL = APARTIAL)
  by (unfold req_size, APARTIAL; destruct (6000 =? 0) eqn:Ez; [discriminate | reflexivity]).
assert (NDB : NoDup (hs_blocks (CheckRep.set_held h H1)))
  by (pose proof HSRC as HSRCx; repeat (destruct HSRCx as [_ HSRCx]); exact HSRCx).
apply NoDup_ListNoDup in NDB.
change (hs_blocks (CheckRep.set_held h H1)) with
  (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks H1) in NDB.
rewrite (l3_lb H1 Hcpos), Hsp, map_app in NDB. cbn [map] in NDB.
assert (ND1 : ~ In (fst r) (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
  hl_v H1 :: map fst RA ++ map fst RB)).
{ assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
    hl_v H1 :: map fst RA) ++ fst r :: map fst RB)) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_2 in Hx. rewrite <- !app_assoc in Hx. exact Hx. }
assert (ND2 : ~ In (hl_v H1) (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h))).
{ assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++
    hl_v H1 :: (map fst RA ++ fst r :: map fst RB))) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_2 in Hx. intros Hc. apply Hx. apply in_or_app. left. exact Hc. }
assert (NDnew : NoDup (hs_blocks (CheckRep.set_held h (ldrop_list H1 i)))).
{ apply NoDup_ListNoDup.
  change (hs_blocks (CheckRep.set_held h (ldrop_list H1 i))) with
    (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (ldrop_list H1 i)).
  rewrite (l3_lb (ldrop_list H1 i) Hcpos), Hldr, map_app.
  assert (Hx : List.NoDup ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++
    hl_v H1 :: map fst RA) ++ fst r :: map fst RB)) by (rewrite <- !app_assoc; exact NDB).
  apply List.NoDup_remove_1 in Hx. rewrite <- !app_assoc in Hx. exact Hx. }
assert (SFP : akept W1 mem1 W2 (ms_mem ms1)
  (gfp (hs_partial h) (bzs (hs_pjunk h)) :: alist_fp (HA + 16) (hs_pending h) ++ alist_fp (HA + 64) (hs_expected h))).
{ intros rr Hrr a Ha. cbn [In] in Hrr. destruct Hrr as [<- | Hrr].
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, HPJLEN in Ha.
    apply (KBK (hs_partial h) APARTIAL a HPIN).
    + intros Hc. apply ND1. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
    + intros Hc. apply ND2. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
    + rewrite HreqP. lia.
  - apply in_app_or in Hrr as [Hrr | Hrr]; revert rr Hrr a Ha.
    + apply (l3_list_kept_P ly1 S1 W1 W2 mem1 md1 (ms_mem ms1) (HA + 16) (hs_pending h) false
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HPD).
      * intros x Hx. apply KHD; [unfold ASRC; lia | lia].
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. split; intros Hc; [apply ND1 | apply ND2]; rewrite <- Hc; rewrite !in_app_iff; cbn [In]; tauto.
    + apply (l3_list_kept_P ly1 S1 W1 W2 mem1 md1 (ms_mem ms1) (HA + 64) (hs_expected h) true
        (fun b => b <> fst r /\ b <> hl_v H1) HAR1 HED).
      * intros x Hx. apply KHD; [unfold ASRC; lia | lia].
      * intros b n x Hin (Hb1 & Hb2) Hx. exact (KBK b n x Hin Hb1 Hb2 Hx).
      * intros b Hb. split; intros Hc; [apply ND1 | apply ND2]; rewrite <- Hc; rewrite !in_app_iff; cbn [In]; tauto. }
assert (ABLK : forall (lst : hlist) LA lines, alist_at B ly1 S1 W1 mem1 LA lst lines ->
  forall b, In b (alist_blks lst) -> In b (ablocks B ly1 S1)).
{ intros lst LA lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
  - destruct (hl_cap lst =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
    destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
  - apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HFa).
    rewrite Forall_forall in HFa. exact (proj1 (HFa x Hx)). }
assert (ABF : forall (lst : hlist) b, In b (alist_blks lst) -> In (fst b) (list_blocks lst)).
{ intros lst b Hb. unfold alist_blks, list_blocks in Hb |- *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
  - left. destruct (hl_cap lst =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst]. left. reflexivity.
  - right. apply in_map_iff in Hb as (x & <- & Hx). cbn [fst]. apply in_map. exact Hx. }
assert (SBLK : forall b, In b ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h)) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb. cbn [In] in Hb. destruct Hb as [<- | Hb].
  - apply (BLK2 _ _ HPIN). intros Hc. apply ND1. rewrite <- Hc. apply in_or_app. right. left. reflexivity.
  - apply in_app_or in Hb as [Hb | Hb]; destruct b as [pb nb].
    + apply (BLK2 pb nb (ABLK _ _ _ HPD _ Hb)). intros Hc. apply ND1. rewrite <- Hc. pose proof (ABF _ _ Hb) as Hb'.
      cbn [fst] in Hb'. rewrite !in_app_iff. cbn [In]. tauto.
    + apply (BLK2 pb nb (ABLK _ _ _ HED _ Hb)). intros Hc. apply ND1. rewrite <- Hc. pose proof (ABF _ _ Hb) as Hb'.
      cbn [fst] in Hb'. rewrite !in_app_iff. cbn [In]. tauto. }
assert (SRC2 : asrc_at B ly2 S2 W2 (ms_mem ms1) HA (CheckRep.set_held h (ldrop_list H1 i))).
{ apply (l3_src_held ly1 S1 W1 mem1 ly2 S2 W2 (ms_mem ms1) HA h H1 (ldrop_list H1 i) HSRC).
  - intros x Hx. apply KHD; [unfold ASRC; lia | lia].
  - exact SFP.
  - exact SBLK.
  - exact HE2.
  - exact NDnew. }
(* ---- the stream's block, the globals, the frame ---- *)
assert (HO0 : 0 < O) by lia.
assert (HOUTnb : ~ In OUT (hs_blocks h)).
{ destruct HOB as [E0 | (CO0 & _ & _ & Hni)]; [rewrite E0 in HOlen; cbn in HOlen; lia | exact Hni]. }
assert (HOr : OUT <> fst r).
{ intros Heq. apply HOUTnb. rewrite Heq.
  assert (Hm : In (fst r) (list_blocks (hs_held h)))
    by (unfold list_blocks; apply in_or_app; right; apply in_map; apply HINC; apply nth_In; exact Hi).
  unfold hs_blocks. rewrite !in_app_iff. tauto. }
assert (HOv : OUT <> hl_v H1).
{ intros Heq. apply HOUTnb. rewrite Heq, HV.
  assert (Hm : In (hl_v H0) (list_blocks (hs_held h))) by (unfold list_blocks; rewrite Ecap; left; reflexivity).
  unfold hs_blocks. rewrite !in_app_iff. tauto. }
assert (OBF : ob_at W2 (ms_mem ms1) OUT ob).
{ intros k Hk. pose proof (l3_req_ge CO ltac:(lia)) as HqC.
  rewrite (proj1 (KBK OUT CO (OUT + k) HOin HOr HOv ltac:(lia))). exact (HOBt k Hk). }
assert (KG : forall a, inG cshe_ro a -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a).
{ intros a Hg Hn. destruct (HGR a Hg) as (Hia & Ho & _). destruct (HGRR a Hg) as (He & _). exact (KIMG a Hia Ho He Hn). }
assert (GG : forall a, VAL A_g_gone <= a < VAL A_g_gone + 1 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (Hx & _). apply Hx. lia. }
assert (GN : forall a, VAL A_g_nout <= a < VAL A_g_nout + 8 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_nout, 8). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & Hx & _). apply Hx. lia. }
assert (GO : forall a, VAL A_g_out <= a < VAL A_g_out + 8 -> inG cshe_ro a /\ ~ (HA + 88 <= a < HA + 92)).
{ intros a Ha. split.
  - unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_out, 8). split; [right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - intros Hc. destruct (HAg a ltac:(unfold ASRC; lia)) as (_ & _ & Hx). apply Hx. lia. }
assert (MGF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_gone) 1 0).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MG].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GG (VAL A_g_gone + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MNOF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_nout) 8 O).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MNO].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GN (VAL A_g_nout + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MOUTF : val_mem SEGS (arm W2 (ms_mem ms1)) (VAL A_g_out) 8 OUT).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MOUT].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. destruct (GO (VAL A_g_out + k) ltac:(lia)) as [Hg Hn]. exact (KG _ Hg Hn). }
assert (MATF : val_mem SEGS (arm W2 (ms_mem ms1)) AT 8 (A0 + (c + Z.of_nat (length l) + 1))).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact MAT].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. apply KHI; [lia | rewrite QA; lia]. }
assert (SAVF : cshe_saved W2 (ms_mem ms1) sp0 regs0).
{ apply (l3_saved_kept W1 W2 mem1 (ms_mem ms1) sp0 regs0); [|exact HSAV]. intros a Ha. apply KHI; [lia | rewrite QA; lia]. }
assert (M16F : val_mem SEGS (arm W2 (ms_mem ms1)) (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 (ms_mem ms1)); [|exact M16].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. apply KHI; [lia | rewrite QA; lia]. }
assert (ROMF : rom_view SEGS W2 (ms_mem ms1)).
{ intros a Hrom. pose proof (ROMIMG a Hrom) as Hia. pose proof (pa_img_range a Hia) as Har.
  assert (Hn : ~ (HA + 88 <= a < HA + 92))
    by (intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom)).
  rewrite (KEEPf a ltac:(lia) Hn). rewrite (Hfr3 a ltac:(lia) (MOFF a Hia) ltac:(unfold ESTACK; lia)). exact (ROMK a Hrom). }
(* ---- the allocator's side and the model's ---- *)
assert (PERMF : forall rest, Permutation (ablocks B ly S) (cshe_ds_blks (ds ++ [r]) ++ rest) ->
  Permutation (ablocks B ly2 S2) rest).
{ intros rest Hpm.
  assert (Hpm1 : Permutation (ablocks B ly S) (cshe_ds_blks ds ++ (fst r, Z.of_nat (length (snd r)) + 1) :: rest)).
  { unfold cshe_ds_blks in Hpm |- *. rewrite map_app in Hpm. cbn [map] in Hpm. rewrite <- app_assoc in Hpm. exact Hpm. }
  pose proof (HPERM _ Hpm1) as Hp1.
  destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hp1.
  exact (Permutation_app_inv l1 l2 [] rest _ Hp1). }
assert (FRSF : frames S2 = frames S) by (rewrite Hfrs2; exact HFRS).
pose proof (mo_free_nonneg MT ML) as Hf0.
assert (MLEF : mo_le MT S S2 (Z.of_nat (length (ds ++ [r])) * mo_free MT)).
{ replace (Z.of_nat (length (ds ++ [r])) * mo_free MT) with (Z.of_nat (length ds) * mo_free MT + mo_free MT)
    by (rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat]; ring).
  exact (mle_station MT S S1 S2 _ _ ML HMLE Hle). }
assert (HLD : (length (hl_recs (ldrop_list H1 i)) + 1 = length (hl_recs H1))%nat).
{ change (hl_recs (ldrop_list H1 i)) with (CheckRep.drop_nth i (hl_recs H1)). rewrite (l3_drop_len _ _ Hi). lia. }
assert (MOKF : mo_ok MT S2 (Z.of_nat (length (hl_recs (ldrop_list H1 i))) * mo_free MT)).
{ assert (HLD' : Z.of_nat (length (hl_recs H1)) = Z.of_nat (length (hl_recs (ldrop_list H1 i))) + 1) by (rewrite <- HLD; lia).
  apply (mok_station MT S1 S2 (Z.of_nat (length (hl_recs H1)) * mo_free MT) (mo_free MT) _ ML HMOK Hle);
    [apply Z.mul_nonneg_nonneg; lia | rewrite HLD'; lia]. }
(* the room round: the free's post room, and the live counts one block fewer *)
assert (CNTF : cnt_ok RP (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HCNTr. exact (l3_cnt_del RP l1 _ l2 HCNTr). }
assert (ERRF : l3_errR W2 (ms_mem ms1)).
{ intros q Hq. pose proof (l3_errno_imgR q Hq) as Hie. pose proof (pa_img_range _ Hie) as Har.
  assert (Hw : ~ (HA + 88 <= as_errno B + q < HA + 92)) by (intros Hc; apply (l3_errno_offR q Hq); unfold ASRC; lia).
  rewrite (KALL (as_errno B + q) ltac:(lia) Hw (MOFF _ Hie) ltac:(unfold ESTACK; lia)).
  rewrite (HEf q Hq). rewrite (KEEPr (as_errno B + q) ltac:(lia) Hw). exact (HERR q Hq). }
(* ---- the memory facts, carried to a later memory that kept every byte but l->n and wrote n - 1 there ---- *)
assert (TRANS : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) (ms_mem ms1) a) ->
  val_mem SEGS (arm W2 m') (HA + 80 + 8) 4 (hl_n H1 - 1) ->
  (forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) m' a) ->
  asrc_at B ly2 S2 W2 m' HA (CheckRep.set_held h (ldrop_list H1 i)) /\
  val_mem SEGS (arm W2 m') AT 8 (A0 + (c + Z.of_nat (length l) + 1)) /\
  val_mem SEGS (arm W2 m') (VAL A_g_gone) 1 0 /\ val_mem SEGS (arm W2 m') (VAL A_g_nout) 8 O /\
  val_mem SEGS (arm W2 m') (VAL A_g_out) 8 OUT /\ ob_at W2 m' OUT ob /\ rom_view SEGS W2 m' /\
  cshe_saved W2 m' sp0 regs0 /\ val_mem SEGS (arm W2 m') (sp0 - 144 + 16) 8 ((HA + 88) / 8 + SB) /\ l3_errR W2 m').
{ intros m' Hk Hn' Hp'.
  assert (VK : forall x n v, (forall a, x <= a < x + Z.of_nat n -> 0 <= a < 2 ^ 64 /\ ~ (HA + 88 <= a < HA + 92)) ->
    val_mem SEGS (arm W2 (ms_mem ms1)) x n v -> val_mem SEGS (arm W2 m') x n v).
  { intros x n v Hx Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms1) m'); [|exact Hv].
    intros k Hk'. destruct (Hx (x + k) ltac:(lia)) as [Hb Hn]. exact (Hk _ Hb Hn). }
  assert (GB : forall a, inG cshe_ro a -> 0 <= a < 2 ^ 64)
    by (intros a Hg; pose proof (pa_img_range a (proj1 (HGR a Hg))); lia).
  split.
  { apply (l3_src_step ly2 S2 _ W2 W2 (ms_mem ms1) m' HA (CheckRep.set_held h (ldrop_list H1 i)) alloc_ceiling alloc_ceiling HARF SRC2).
    - intros a Ha. exact (proj1 (HAimg a Ha)).
    - lia.
    - intros a Ha _ Hn. exact (Hk a Ha Hn).
    - intros k Hk4. replace (HA + 88 + k) with (HA + 80 + 8 + k) by lia.
      exact (l3_aview_of_val_mem2 (w_H W2) (w_H W2) (ms_mem ms1) m' (HA + 80 + 8) 4 (hl_n H1 - 1) k MnF Hn' ltac:(cbn; lia)).
    - exact Hp'.
    - apply wle_refl. }
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; lia | exact MATF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GG a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MGF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GN a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MNOF]|].
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; destruct (GO a Ha) as [Hg Hn]; exact (conj (GB a Hg) Hn) | exact MOUTF]|].
  split.
  { intros k Hk'. pose proof (l3_req_ge CO ltac:(lia)) as HqC.
    assert (Hni : ~ in_img SEGS (OUT + k)) by (apply (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W1 mem1 md1 OUT CO); [exact HAR1 | exact HOin | lia]).
    rewrite (Hk (OUT + k) ltac:(lia) ltac:(intros Hc; apply Hni; exact (proj1 (HAimg (OUT + k) ltac:(unfold ASRC; lia))))).
    exact (OBF k Hk'). }
  split.
  { intros a Hrom. pose proof (pa_img_range a (ROMIMG a Hrom)) as Har.
    rewrite (Hk a ltac:(lia) ltac:(intros Hcz; exact (proj2 (proj2 (proj2 (HAimg a ltac:(unfold ASRC; lia)))) Hrom))).
    exact (ROMF a Hrom). }
  split.
  { apply (l3_saved_kept W2 W2 (ms_mem ms1) m' sp0 regs0); [|exact SAVF]. intros a Ha. apply Hk; [lia|].
    unfold ASRC, kLowMemEnd in HAhi. lia. }
  split; [apply VK; [intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; split; [lia | unfold ASRC, kLowMemEnd in HAhi; lia] | exact M16F]|].
  intros q Hq. pose proof (pa_img_range _ (l3_errno_imgR q Hq)) as HeR.
  rewrite (Hk (as_errno B + q) ltac:(lia) ltac:(intros Hc; apply (l3_errno_offR q Hq); unfold ASRC; lia)). exact (ERRF q Hq). }
assert (F27 : ew Eb 27 = w64 (Z.of_nat (Datatypes.S w) + 1)) by (rewrite OLDba by lia; exact E27).
psrr_branch_tok RUNG BRR HS SHOK3 Bspan.
{ (* taken: s11 - 1 > 1, back to the head *)
  rewrite branch_ltu_U, (U_atom_off Eb 27 (Z.of_nat (Datatypes.S w) + 1) (-1) F27), U_lit in Hc by lia.
  apply Z.ltb_lt in Hc.
  destruct w as [|w']; [exfalso; lia|].
  paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 Bspan A_cshe_l3.
  { cbn [ss_mem add_cond].
    apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
    apply awr_ok_x_nil. }
  pmkst HS.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
  prreg HS (20%bv : bv 5) N20. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26.
  prreg HS (27%bv : bv 5) N27.
  assert (KEEPj : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
  pose proof (st_ok_pi_region_nth Eb _ _ 1
    (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
    HS ltac:(vm_compute; reflexivity)) as HRgJ. cbn [ms_mem restrict] in HRgJ.
  pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgJ U18b ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)) as MnJ.
  assert (PRESj : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a).
  { intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
      exact (apresent_grows _ _ _ a Hg Hp) end. }
  destruct (TRANS (ms_mem ms2) KEEPj MnJ PRESj) as (SRCj & MATj & MGj & MNOj & MOUTj & OBj & ROMj & SAVj & M16j & ERRj).
  replace (BASE + 12976) with (BASE + A_cshe_l3) by (unfold A_cshe_l3, AF_fr_check_shape_ends; lia).
  apply (HKont W2 (ms_regs ms2) (ms_mem ms2) _ (ds ++ [r]) (c + Z.of_nat (length l) + 1)); [lia|].
  exists ly2, S2, hp2, (kk + 1), (ldrop_list H1 i).
  split; [exact HJ3|].
  split; [exact SRCj|].
  split; [exact HV|]. split; [exact HC|].
  split; [exact (l3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND)|].
  split; [intros x Hx; apply HINC; exact (l3_incl_drop (hl_recs H1) i x Hx)|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [exact HRUN|].
  split; [exact HREL|].
  split; [lia|]. split; [exact HcO|].
  split; [exact MATj|]. split; [exact MGj|]. split; [exact MNOj|]. split; [exact MOUTj|].
  split; [exact OBj|].
  split; [right; exists CO; split; [exact HCO | exact (BLK2 OUT CO HOin HOr)]|].
  split; [exact PERMF|]. split; [exact FRSF|]. split; [exact MLEF|]. split; [exact MOKF|].
  split; [exact HRM2|]. split; [exact CNTF|].
  split; [exact ROMj|]. split; [exact SAVj|]. split; [exact M16j|].
  split; [|exact ERRj].
  unfold l3_regsR.
  split; [rewrite N2, OLDba by lia; exact E2|].
  split; [rewrite N3, OLDba by lia; exact E3|].
  split; [rewrite N4, OLDba by lia; exact E4|].
  split; [rewrite N8, U18b; unfold w64; f_equal; lia|].
  split; [rewrite N9, OLDba by lia; exact E9|].
  split; [rewrite N18, OLDba by lia; exact E18|].
  split; [rewrite N19, OLDba by lia; exact E19|].
  split; [rewrite N20, OLDba by lia; exact E20|].
  split; [rewrite N24; reflexivity|].
  split; [rewrite N25, OLDba by lia; exact E25|].
  split.
  { rewrite N26, (OLDba 18%nat), (OLDba 25%nat) by lia. rewrite E18, E25. unfold w64.
    rewrite l3_srl3 by lia. rewrite YI08.alu64_add_lit. f_equal; lia. }
  rewrite N27, F27. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia. }
rewrite branch_ltu_U, (U_atom_off Eb 27 (Z.of_nat (Datatypes.S w) + 1) (-1) F27), U_lit in Hc by lia.
apply Z.ltb_ge in Hc.
destruct w as [|w']; [|exfalso; lia].
(* ---- the last turn: on to the epilogue 0x85690 ---- *)
paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 Bspan A_cshe_ret.
{ cbn [ss_mem add_cond].
  apply awr_ok_x_cons; [intros a Ha; exfalso; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite V18b in Ha; apply HGa; lia|].
  apply awr_ok_x_nil. }
pmkst HS.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
assert (KEEPj : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ => l3_wkeep Hf U18b end. }
pose proof (st_ok_pi_region_nth Eb _ _ 1
  (YP09.mkRegion (Some 18%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 (-1))); YP09.mkChunk 0 (CVal 8 (SOff 32 0))])
  HS ltac:(vm_compute; reflexivity)) as HRgJ. cbn [ms_mem restrict] in HRgJ.
pose proof (field_of_region Eb _ 18 (HA + 80) _ _ _ _ _ 8 4 (SOff 33 (-1)) (hl_n H1 - 1) HRgJ U18b ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite OLDba by lia; rewrite E33; rewrite unsigned_lit_small by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as MnJ.
assert (PRESj : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a).
{ intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
destruct (TRANS (ms_mem ms2) KEEPj MnJ PRESj) as (_ & _ & _ & _ & _ & _ & _ & SAVj & _ & _).
replace (BASE + 13220) with (BASE + A_cshe_ret) by (unfold A_cshe_ret, AF_fr_check_shape_ends; lia).
apply (l3_epi_xR W ly S hp mem md XO [(AT, AT + 8)] FPc ly2 S2 hp2 W2 regs0 (ms_regs ms2) (ms_mem ms2) _ (kk + 1) Post HJ3 Hra0 Hal16).
- rewrite WS. lia.
- lia.
- rewrite N2, OLDba by lia. exact E2.
- rewrite N3, OLDba by lia. exact E3.
- rewrite N4, OLDba by lia. exact E4.
- exact SAVj.
- intros regs' mem' md' Hpr Hk' Hp' HJ'.
  assert (KEEPe : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) (ms_mem ms1) a)
    by (intros a Ha Hn; rewrite (Hk' a Ha); exact (KEEPj a Ha Hn)).
  assert (MnE : val_mem SEGS (arm W2 mem') (HA + 80 + 8) 4 (hl_n H1 - 1)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms2) mem'); [|exact MnJ].
    intros k Hk. apply Hk'. unfold ASRC, kLowMemEnd in HAhi. lia. }
  destruct (TRANS mem' KEEPe MnE ltac:(intros a Hp; exact (Hp' a (PRESj a Hp))))
    as (SRCe & MATe & MGe & _ & _ & _ & _ & _ & _ & ERRe).
  exists ly2, S2, hp2, regs', mem', md', (kk + 1), (ldrop_list H1 i), (ds ++ [r]), (c + Z.of_nat (length l) + 1).
  split; [reflexivity|].
  split; [exact HJ'|].
  split; [exact Hpr|].
  split; [exact ERRe|].
  split; [exact SRCe|].
  split; [exact HV|]. split; [exact HC|].
  split; [exact (l3_nodup_drop (fun r0 => bzs (snd r0)) (hl_recs H1) i HND)|].
  split.
  { right. split; [reflexivity|].
    rewrite (HREL (CheckRep.drop_nth i (hl_recs H1)) [] 0 eq_refl). rewrite app_nil_r, Z.add_0_r. reflexivity. }
  split; [lia|].
  split; [replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + (c + Z.of_nat (length l) + 1)) by lia; exact MATe|].
  split; [exact MGe|].
  split; [exact PERMF|]. split; [exact FRSF|].
  split; [|exact (RMM_of RP S2 kr (length (hl_recs (ldrop_list H1 i)) + kr) ltac:(lia) HRM2)].
  apply (mle_weaken MT S S2 _ _ ML MLEF). unfold cshe_cost, hl_n.
  assert (Hl : Z.of_nat (length (ds ++ [r])) <= Z.of_nat (length (hl_recs H0))) by (rewrite length_app; cbn [length]; lia).
  apply Z.mul_le_mono_nonneg_r; [exact Hf0 | exact Hl].
Qed.
(* the loop, by induction on the turns left: each turn is l3_A1R (to 0x855d0), l3_A2R (to 0x85614), l3_BR (the drop and
   the back-edge); the last turn ends in the epilogue and cshe_post *)
Lemma l3_loopR : forall n ds c W1 regs1 mem1 md1, l3_invR (Datatypes.S n) ds c W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1) Post.
Proof using All - AFREE.
induction n as [|n IH]; intros ds c W1 regs1 mem1 md1 HI;
  apply (l3_A1R _ ds c W1 regs1 mem1 md1 HI); intros l i W2 regs2 mem2 md2 HAB;
  apply (l3_A2R _ ds c l i W2 regs2 mem2 md2 HAB); intros W3 regs3 mem3 md3 HM;
  apply (l3_BR _ ds c l i W3 regs3 mem3 md3 HM); intros W4 regs4 mem4 md4 ds' c' Hw HI'.
- lia.
- exact (IH ds' c' W4 regs4 mem4 md4 HI').
Qed.
End loopR.

(* ------------------------------------------------------------------ the top lemma at R: W_cshe_top.v's Hypothesis L3R *)
Lemma cshe_l3_top_xR : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob
  (W1 : world SEGS) hp1 regs1 mem1 md1 s5v,
let H := hs_held h in
let PLEN := Z.of_nat (length P) in
let want := Z.of_nat (CheckRep.want_of P (hl_recs H)) in
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA <= a < HA + ASRC -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall a, HA <= a < HA + ASRC -> cshe_home B ly S a) ->
NoDup (CheckRep.texts H) ->
hl_n H < 2 ^ 26 ->
(forall a, hl_v H <= a < hl_v H + AREC * hl_cap H -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs H) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF AT 8 ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> PLEN + 1 < 2 ^ 32 -> 0 < PF -> PF + PLEN + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + PLEN) = Some 0 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (PLEN + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
mo_ok MT S (cshe_cost MT H) ->
(* the branch *)
gone = 0 -> 0 < want -> 0 < hl_n H ->
(* the state at loop 3's head 0x8559c *)
R W W1 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp1 W1 mem1 md1 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) ->
(forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W1) mem1 a) ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 (spZ regs) regs ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 8) 8 3 ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
(* s5 (x21) still holds loop 1's s5v; 0x8557c computed want = a0 + s5 with 0 <= a0 <= 2 (cshe_tst_ok) *)
0 <= s5v < 2 ^ 26 -> 0 <= want - s5v <= 2 ->
getr regs1 2 = w64 (spZ regs - 144) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 10 = w64 want ->
getr regs1 18 = w64 (HA + 80) -> getr regs1 19 = w64 AT -> getr regs1 20 = w64 (VAL A_lit_end5) ->
getr regs1 21 = w64 s5v -> getr regs1 22 = w64 0 -> getr regs1 23 = w64 (SB + (hl_v H + AREC * hl_n H) / 8) ->
getr regs1 24 = w64 4 -> getr regs1 25 = w64 SB -> getr regs1 26 = w64 ((HA + 80) / 8 + SB) ->
getr regs1 27 = w64 (want + 1) ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
forall kr : nat, rp_RM RP S (length (hl_recs H) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1)
  (cshe_post_xR B PST ARx R MT RP G regs ly S hp W mem md XO AT HA h P A0 gone ob kr).
Proof using All - AFREE.
cbv zeta.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob W1 hp1 regs1 mem1 md1 s5v
  HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HAoff HAhome HND HnH
  HVoff HRoff HAT8 HATlo HAThi HATra MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1
  HPhome HE5 HROM Mg Rg MO MOUT HOB HOlen HO40 HO32 HOmr HOblk HA0 HFN HMO
  Hgone Hwant Hn0 Hwle HJ1 HK1 HP1 HPf1 HSRC1 HROM1 HSAV1 M8 M16 MAT1 MG1 HERR1 Hs5 Hs5w
  R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 kr HRM0 HCNT0.
subst gone.
assert (EWx : exists w', CheckRep.want_of P (hl_recs (hs_held h)) = Datatypes.S w').
{ destruct (CheckRep.want_of P (hl_recs (hs_held h))) as [|w']; [cbn in Hwant; lia | exists w'; reflexivity]. }
destruct EWx as (w' & EW).
assert (HAimg : forall a, HA <= a < HA + ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ in_rom SEGS a).
{ intros a Ha.
  assert (Hg : inG cshe_ro a).
  { unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384).
    split; [right; right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; unfold ASRC in *; lia]. }
  destruct (HGR a Hg) as (Hi & Ho & _). destruct (HGRR a Hg) as (He & _).
  destruct (HGS a ltac:(unfold ASRC in *; lia)) as (_ & Hr & _).
  split; [exact Hi|]. split; [exact Ho|]. split; [exact He | exact Hr]. }
assert (HAg : forall a, HA <= a < HA + ASRC -> ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\
  ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\ ~ (VAL A_g_out <= a < VAL A_g_out + 8)).
{ intros a Ha. destruct (HGS a ltac:(unfold ASRC in *; lia)) as (_ & _ & G1 & G2 & G3).
  split; [exact G1|]. split; [exact G2 | exact G3]. }
assert (HPV : forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None)
  by (intros a Ha; exact (proj1 (HPvis a Ha))).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as ACV.
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (KW : forall a, in_img SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Hi. pose proof (pa_img_range a Hi). apply HK1; [lia | rewrite WS in *; lia]. }
apply (l3_loopR regs ly S hp W mem md ch XO AT HA PF A0 O OUT h P ob kr HPRE HXO0 HXO16 HXtop HAT8 HATlo HAThi Hal8 Hlo HAhiK
  HGin Hzs HnH HOlen HO40 HO32 HOmr HOblk HA0 HROM HAimg HAg HPnz HP32 HPF0 HPFk HPhome HPby HPnul HPV HPmr1 HPmr8
  HPra1 HSRC HE5
  w' [] 0 W1 regs1 mem1 md1).
unfold l3_invR, l3_regsR.
exists ly, S, hp1, 0, (hs_held h).
split; [exact HJ1|].
split; [rewrite l3_set_held_id; exact HSRC1|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|].
split; [apply incl_refl|].
split; [cbn [length]; lia|].
split; [rewrite Z.add_0_r, <- EW; exact (HFN eq_refl)|].
split; [intros rsF dsF cF Hx; rewrite Z.add_0_r, <- EW in Hx; rewrite Hx; reflexivity|].
split; [lia|]. split; [lia|].
split; [rewrite Z.add_0_r; exact MAT1|].
split; [exact MG1|].
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) mem mem1); [|exact MO]. intros k Hk. apply KW.
  destruct (HGR (VAL A_g_nout + k)) as (Hi & _); [|exact Hi].
  unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_nout, 8).
  split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) mem mem1); [|exact MOUT]. intros k Hk. apply KW.
  destruct (HGR (VAL A_g_out + k)) as (Hi & _); [|exact Hi].
  unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_out, 8).
  split; [right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk; lia]. }
split.
{ destruct HOblk as [E0 | (CO & HCO & HOin & _)].
  - subst ob. intros k Hk. cbn [length Z.of_nat] in Hk. lia.
  - intros k Hk. destruct (alx_blocks _ _ _ LAWS ly S hp W mem md OUT CO HAR0 HOin) as (_ & O4 & Oc & _).
    pose proof (l3_req_ge CO ltac:(lia)).
    rewrite (HK1 (OUT + k) ltac:(lia) ltac:(rewrite WS in *; lia)). exact (HOB k Hk). }
split; [destruct HOblk as [E0 | (CO & HCO & HOin & _)]; [left; exact E0 | right; exists CO; split; assumption]|].
split; [intros rest Hp; exact Hp|].
split; [reflexivity|].
split; [exact (mo_le_refl MT ML S)|].
split; [exact HMO|].
split; [exact HRM0|]. split; [exact HCNT0|].
split; [exact HROM1|]. split; [exact HSAV1|]. split; [exact M16|].
split; [|exact HERR1].
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R24|]. split; [exact R25|].
split; [exact R26|].
rewrite EW in R27. exact R27.
Qed.
End wR.
End c.
End b.
End a.
