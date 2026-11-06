(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACgc.v:176-178;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-51, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:154-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg3.v; 1387 of its 1578 lines of code are new or changed and 2349 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC4b YC45 YC81 YC85 IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn5_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn5_sh_nb : forall a c d j, 8 <= j < 11 -> nth (Z.to_nat j) (rbn_sh a true c d) 0 = 0.
Proof.
intros a c d j Hj. assert (j = 8 \/ j = 9 \/ j = 10) as [-> | [-> | ->]] by lia; destruct a, c, d; reflexivity.
Qed.
Lemma rbn5_sh_tb : forall j, 0 <= j < 64 -> ~ (16 <= j < 19) ->
  nth (Z.to_nat j) (rbn_sh true true true false) 0 = nth (Z.to_nat j) (rbn_sh true true false false) 0.
Proof.
intros j Hj Hn.
assert (E : forall k, (k < 64)%nat -> ~ (16 <= k < 19)%nat ->
  nth k (rbn_sh true true true false) 0 = nth k (rbn_sh true true false false) 0).
{ intros k Hk Hk2. do 64 (destruct k as [|k]; [first [reflexivity | lia]|]). lia. }
apply E; lia.
Qed.
Lemma rbn5_sh_tb3 : forall j, 16 <= j < 19 -> nth (Z.to_nat j) (rbn_sh true true true false) 0 = 0.
Proof. intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia; reflexivity. Qed.
Lemma rbn5_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb.
pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn5_out_get : forall (regs2 : bvmap 5 word) (r : bv 5) v,
  getr regs2 (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs2 r = v.
Proof. intros regs2 r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma rbn5_le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma rbn5_nth_skipn : forall (l : list Z) m i, nth i (skipn m l) 0 = nth (m + i) l 0.
Proof.
induction l as [|c l IH]; intros m i; destruct m as [|m]; cbn [skipn nth Nat.add]; try reflexivity.
- destruct i; reflexivity.
- apply IH.
Qed.
Definition rbn5T_ss : sstate :=
  mkSS (AF_reac_box_name + 0x460) sr_atoms
    [YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
     YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
     YP09.mkRegion (Some 18%nat) 16 19 16 19 []] None
    (mkFacts [] [] [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0);
                    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0), SOff 33 0)]).
Definition rbn5D_ss : sstate :=
  mkSS (AF_reac_box_name + 0x3c0) sr_atoms
    [YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
     YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
    (mkFacts [(33%nat, mkAF 1 255 0)] [] [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0)]).
Definition rbn5A_ss : sstate :=
  mkSS (AF_reac_box_name + 0x370) sr_atoms
    [YP09.mkRegion (Some 9%nat) 24 32 24 32 []; YP09.mkRegion (Some 9%nat) 48 56 48 56 [];
     YP09.mkRegion (Some 9%nat) 72 80 72 80 []] None (mkFacts [] [] []).
Definition rbn5_dirty (A a : Z) : Prop :=
  A - 8192 <= a < A \/ A + 24 <= a < A + 32 \/ A + 48 <= a < A + 56 \/ A + 72 <= a < A + 80.
Definition rbn5_wok (r : YP09.region) : bool :=
  (match YP09.r_base r with
   | Some nb => Nat.eqb nb 9 &&
       (((24 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 32)) || ((48 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 56)) ||
        ((72 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 80)))
   | None => false end) || (YP09.r_whi r <=? YP09.r_wlo r).
Definition rbn5_R24 : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 23 0))].
Definition rbn5_R48 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [YP09.mkChunk 48 (CVal 8 (SOff 19 128))].
Definition rbn5_R72 : YP09.region := YP09.mkRegion (Some 9%nat) 72 80 72 80 [YP09.mkChunk 72 (CVal 8 (SOff 26 0))].
Lemma rbn5_tail4 : forall (s w : list Z) (P W4 : Z) (rd : Z -> option Z),
  (4 <= length s)%nat -> length w = 4%nat ->
  (forall j, 0 <= j < Z.of_nat (length s) + 1 -> rd (P + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0)) ->
  (forall j, 0 <= j < 5 -> rd (W4 + j) = Some (nth (Z.to_nat j) (w ++ [0]) 0)) ->
  ((forall i, 0 <= i < 4 -> rd (P + Z.of_nat (length s) - 4 + i) = rd (W4 + i)) <-> skipn (length s - 4) s = w).
Proof.
intros s w P W4 rd Hs Hw HS HW. split.
- intros H. apply (nth_ext _ _ 0 0). { rewrite length_skipn. lia. }
  intros i Hi. rewrite length_skipn in Hi. rewrite rbn5_nth_skipn.
  specialize (H (Z.of_nat i) ltac:(lia)).
  replace (P + Z.of_nat (length s) - 4 + Z.of_nat i) with (P + (Z.of_nat (length s) - 4 + Z.of_nat i)) in H by lia.
  rewrite (HS (Z.of_nat (length s) - 4 + Z.of_nat i)) in H by lia. rewrite (HW (Z.of_nat i)) in H by lia.
  injection H as H. rewrite app_nth1 in H by lia. rewrite app_nth1 in H by lia. rewrite Nat2Z.id in H.
  replace (Z.to_nat (Z.of_nat (length s) - 4 + Z.of_nat i)) with (length s - 4 + i)%nat in H by lia. exact H.
- intros H i Hi.
  replace (P + Z.of_nat (length s) - 4 + i) with (P + (Z.of_nat (length s) - 4 + i)) by lia.
  rewrite (HS (Z.of_nat (length s) - 4 + i)) by lia. rewrite (HW i) by lia. f_equal.
  rewrite app_nth1 by lia. rewrite app_nth1 by lia. rewrite <- H. rewrite rbn5_nth_skipn. f_equal. lia.
Qed.
Lemma rbn5_hull_sub : forall (rd : Z -> option Z) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> a' + n' <= a + n -> 0 < n' -> shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono a a' H1) as M1. pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)) as M2.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M1). pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M2). lia.
Qed.
Lemma rbn5_agree_havoc : forall k E E0 ws, (32 <= k)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (havoc E k ws).
Proof.
intros k E E0 ws Hk [H1 H2]. split; [intros n Hn; rewrite ew_havoc_old by lia; exact (H1 n Hn) | cbn [havoc ed]; exact H2].
Qed.
Lemma rbn5_ag : forall E (regs1 : bvmap 5 word) n (r : bv 5), env_agree 32 (Ereg regs1 []) E ->
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs1 r.
Proof. intros E regs1 n r H Hr Hn. rewrite (proj1 H n Hn). apply ew_Ereg_nat. exact Hr. Qed.
Lemma rbn5_sv0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma rbn5_svk : forall E n v d, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n d) = Z_to_bv 64 (v + d).
Proof. intros E n v d H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma rbn5_den_U : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof.
intros E e v H Hv. apply bv_eq. change (bv_unsigned (sv_denot E e)) with (U E e). rewrite H, unsigned_lit_small by lia.
reflexivity.
Qed.
Lemma rbn5_br_eq0 : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros E n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma rbn5_br_ne0 : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros E n v Hn Hb Hv. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.
Lemma rbn5_awrA : forall E rs STK sp0 FP bl0 blc ly own A,
  bv_unsigned (ew E 9) = A -> sp0 - STK <= A + 24 -> A + 80 <= sp0 -> forallb rbn5_wok rs = true ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own A HA H1 H2 Hok a (r & Hin & Hx).
rewrite forallb_forall in Hok. specialize (Hok r Hin). unfold rbn5_wok in Hok.
apply orb_true_iff in Hok as [Hok | Hok].
- destruct (YP09.r_base r) as [nb|] eqn:Eb; [|discriminate Hok].
  apply andb_true_iff in Hok as [Hn Hok]. apply Nat.eqb_eq in Hn. subst nb.
  try rewrite Eb in Hx. cbn [base_val] in Hx. rewrite HA in Hx.
  left. apply orb_true_iff in Hok as [[Hok | Hok]%orb_true_iff | Hok];
  apply andb_true_iff in Hok as [Hl Hh]; apply Z.leb_le in Hl; apply Z.leb_le in Hh; lia.
- apply Z.leb_le in Hok. lia.
Qed.
Ltac rbn5_rget HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H
  end;
  lazymatch type of H with _ = sv_denot _ (sr_get ?srs ?rr) =>
    let e := eval vm_compute in (sr_get srs rr) in change (sr_get srs rr) with e in H end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn5_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn5_cells_app : forall mm l1 l2, rbn_cells mm (l1 ++ l2) <-> rbn_cells mm l1 /\ rbn_cells mm l2.
Proof.
intros mm l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [rbn_cells app]; [tauto|]. rewrite IH. tauto.
Qed.
Lemma rbn5_locs4_clean : forall X pos a n v, In (a, n, v) (rbn_locs4 X pos) ->
  forall k, 0 <= k < Z.of_nat n -> ~ rbn5_dirty (rbn_A X) (a + k) /\ rbn_A X + 8 <= a + k < rbn_A X + 180.
Proof.
intros X pos a n v H k Hk. unfold rbn_locs4 in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; unfold rbn5_dirty; lia|]). destruct H.
Qed.
Definition rbn5_keep (W : world SEGS) (A : Z) (m0 m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ rbn5_dirty A a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
Lemma rbn5_locs4_rng : forall X pos a n v, In (a, n, v) (rbn_locs4 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180 /\ ~ (rbn_A X + 24 <= a < rbn_A X + 32) /\
  ~ (rbn_A X + 48 <= a < rbn_A X + 56) /\ ~ (rbn_A X + 72 <= a < rbn_A X + 80).
Proof.
intros X pos a n v H. unfold rbn_locs4 in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5_locs6_rng : forall X pos a n v, In (a, n, v) (rbn_locs6 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180.
Proof.
intros X pos a n v H. unfold rbn_locs6 in H. apply in_app_or in H. destruct H as [H | H];
[pose proof (rbn5_locs4_rng X pos a n v H); lia|]. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn5_w4_digits : forall X, rbm_args X -> Forall (fun c => 0 < c < 256) (rbm_w4 X).
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
apply bn_ok_in in Hi. apply bn_ok_in in Ho. unfold rbm_w4.
assert (A : forallb (fun i => forallb (fun o => forallb (fun c => (0 <? c) && (c <? 256)) (bn_w4 i o)) bn_oks) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A _ Hi). rewrite forallb_forall in A. specialize (A _ Ho).
rewrite forallb_forall in A. apply Forall_forall. intros c Hc. specialize (A c Hc).
apply andb_prop in A as [A1 A2]. apply Z.ltb_lt in A1. apply Z.ltb_lt in A2. lia.
Qed.
Lemma rbn5_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn5_NM_cases : forall X,
  (4 <= Z.of_nat (length (rbm_stem X)) /\ skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X /\
   rbm_NM X = rbm_stem X) \/
  (~ (4 <= Z.of_nat (length (rbm_stem X)) /\ skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X) /\
   rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X).
Proof.
intros X. unfold rbm_NM, bn_NM, rbm_stem, rbm_w4. cbv zeta.
set (s := bn_stem (ri_f X) (ri_sd X)). set (w := bn_w4 (ri_i X) (ri_o X)).
assert (Hleq : forall a b, bn_leq a b = true <-> a = b).
{ induction a as [|x a IH]; intros [|y b]; cbn [bn_leq]; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as <- <-. rewrite Z.eqb_refl. cbn. apply IH. reflexivity. }
destruct (4 <=? Z.of_nat (length s)) eqn:H4; destruct (bn_leq (skipn (length s - 4) s) w) eqn:Hl; cbn [andb].
- left. apply Z.leb_le in H4. apply Hleq in Hl. auto.
- right. split; [|reflexivity]. intros [_ He]. apply Hleq in He. congruence.
- right. split; [|reflexivity]. intros [He _]. apply Z.leb_gt in H4. lia.
- right. split; [|reflexivity]. intros [He _]. apply Z.leb_gt in H4. lia.
Qed.
Lemma rbn5_NB_ne : forall X, (1 <= length (rbm_NB X))%nat.
Proof.
intros X. assert (H : rbm_NM X <> []).
{ destruct (rbn5_NM_cases X) as [(_ & _ & ->) | (_ & ->)]; [exact (rbn5_stem_ne X)|].
  destruct (rbm_stem X); discriminate. }
unfold rbm_NB. destruct (rbm_NM X) as [|c l]; [exfalso; exact (H eq_refl)|]. cbn [firstn length]. lia.
Qed.
Lemma rbn5_vm1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hb. f_equal.
rewrite (rbn5_le1 _ Hr). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rbn5_aview_vm1 : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite (rbn5_le1 _ Hr).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
Lemma rbn5_garr8_view : forall H (m : word -> option byte) a l,
  garr8 SEGS (mrestrict H m) a l -> forall j, 0 <= j < Z.of_nat (length l) ->
  aview SEGS H m (a + j) = Some (nth (Z.to_nat j) l 0).
Proof.
intros H m a l HG j Hj. destruct (HG (Z.to_nat j) ltac:(lia)) as [Hv Hr].
rewrite Z2Nat.id in Hv by lia. exact (rbn5_aview_vm1 H m _ _ Hv Hr).
Qed.
Lemma rbn5_VB : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v.
Proof. intros E k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. Qed.
Lemma rbn5_kept_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn5_keep_run : forall W A m0 m1 m2 E rs, rbn5_keep W A m0 m1 ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> bv_unsigned (ew E 9) = A ->
  forallb rbn5_wok rs = true -> rbn5_keep W A m0 m2.
Proof.
intros W A m0 m1 m2 E rs HK HF HA Hok a Ha Hd. rewrite <- (HK a Ha Hd).
apply (rbn5_kept_frame E rs (w_H W) m1 m2 (rbn5_dirty A) HF); [| exact Ha | exact Hd].
intros x (r & Hin & Hx).
rewrite forallb_forall in Hok. specialize (Hok r Hin). unfold rbn5_wok in Hok.
apply orb_true_iff in Hok as [Hok | Hok].
- destruct (YP09.r_base r) as [nb|] eqn:Eb; [|discriminate Hok].
  apply andb_true_iff in Hok as [Hn Hok]. apply Nat.eqb_eq in Hn. subst nb.
  try rewrite Eb in Hx. cbn [base_val] in Hx. rewrite HA in Hx. unfold rbn5_dirty.
  apply orb_true_iff in Hok as [[Hok | Hok]%orb_true_iff | Hok];
  apply andb_true_iff in Hok as [Hl Hh]; apply Z.leb_le in Hl; apply Z.leb_le in Hh; lia.
- apply Z.leb_le in Hok. lia.
Qed.
Lemma rbn5_keep_call : forall W A m0 m1 m2, rbn5_keep W A m0 m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (A - 8192 <= a < A) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  rbn5_keep W A m0 m2.
Proof. intros W A m0 m1 m2 HK HC a Ha Hd. rewrite (HC a Ha) by (unfold rbn5_dirty in Hd; lia). exact (HK a Ha Hd). Qed.
Lemma rbn5_shadow_addr_rng : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 47 /\ shadow_addr x = SHADOW_OFF + x / 8.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF. split; [|reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.
Lemma rbn5T_entry : forall (W : world SEGS) (regs : bvmap 5 word) m D n SH,
  getr regs 27 = w64 D -> getr regs 24 = w64 n -> getr regs 22 = w64 SHADOW_OFF -> getr regs 18 = w64 SH ->
  0 <= D -> 0 <= n -> D + n + 1 <= 2 ^ 47 -> 0 <= SH -> SH + 19 <= 2 ^ 47 ->
  apresent (w_H W) m (D + n) -> aview SEGS (w_H W) m (shadow_addr (D + n)) = Some 0 ->
  (forall o, 16 <= o < 19 -> apresent (w_H W) m (SH + o)) ->
  (D + n + 1 <= shadow_addr (D + n) \/ shadow_addr (D + n) + 1 <= D + n) ->
  (D + n + 1 <= SH + 16 \/ SH + 19 <= D + n) ->
  (shadow_addr (D + n) + 1 <= SH + 16 \/ SH + 19 <= shadow_addr (D + n)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [D + n; shadow_addr (D + n)]))) rbn5T_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x460))) m (seg_rom SEGS))).
Proof.
intros W regs m D n SH H27 H24 H22 H18 HD Hn HDn HSH0 HSH Hp Hs0 Hs3 Dj1 Dj2 Dj3.
rewrite restrict_mkst_fx.
destruct (rbn5_shadow_addr_rng (D + n) ltac:(lia)) as (SR & SE).
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [D + n; shadow_addr (D + n)]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (D + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr (D + n)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E27 : ew E 27 = Z_to_bv 64 D) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
unfold rbn5T_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (rbn5_VB E 32%nat (D + n) E32) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); replace (D + n + o) with (D + n) by lia; exact Hp|].
    apply Forall_nil.
  + rewrite (rbn5_VB E 33%nat _ E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (rbn5_vm1 _ _ _ _ Hs0).
  + rewrite (rbn5_VB E 18%nat SH E18) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hs3; lia|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (rbn5_VB E 32%nat _ E32), (rbn5_VB E 33%nat _ E33), (rbn5_VB E 18%nat _ E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; [exact I|]. cbn [f_alias alias_ok]. split; [|split; [|exact I]].
  + apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 D E27), (U_atom E 24 n E24), (U_atom E 32 (D + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
  + apply U_inj. rewrite !U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 32 (D + n) E32), (U_atom E 22 SHADOW_OFF E22), (U_atom E 33 _ E33) by (unfold SHADOW_OFF; lia).
    rewrite U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Q : 0 <= (D + n) / 8 <= D + n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite (zcanon_id ((D + n) / 8)) by (unfold M64; lia).
    rewrite SE, Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.
Lemma rbn5D_entry : forall (W : world SEGS) (regs : bvmap 5 word) m D n W4 c0,
  getr regs 27 = w64 D -> getr regs 24 = w64 n -> getr regs 25 = w64 W4 ->
  0 <= D -> 0 <= n -> D + n + 1 <= 2 ^ 47 -> 0 <= W4 -> W4 + 1 <= 2 ^ 47 -> 1 <= c0 <= 255 ->
  apresent (w_H W) m (D + n) -> val_mem SEGS (mrestrict (w_H W) m) W4 1 c0 ->
  (D + n + 1 <= W4 \/ W4 + 1 <= D + n) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [D + n; c0]))) rbn5D_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x3c0))) m (seg_rom SEGS))).
Proof.
intros W regs m D n W4 c0 H27 H24 H25 HD Hn HDn HW0 HW1 Hc0 Hp Hv Dj.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [D + n; c0]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (D + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E27 : ew E 27 = Z_to_bv 64 D) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 W4) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
unfold rbn5D_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (rbn5_VB E 32%nat (D + n) E32) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); replace (D + n + o) with (D + n) by lia; exact Hp|].
    apply Forall_nil.
  + rewrite (rbn5_VB E 25%nat W4 E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 33 0) c0);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (rbn5_VB E 32%nat _ E32), (rbn5_VB E 25%nat _ E25) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [split; [|exact I] | split; [exact I|]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
    split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
  + cbn [alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 D E27), (U_atom E 24 n E24), (U_atom E 32 (D + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Lemma rbn5_chunkv : forall E ss H ms0 i r n b off w e v,
  st_ok_pi SEGS VAL E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms0)) (b + off) (N.to_nat w) v.
Proof.
intros E ss H ms0 i r n b off w e v HS Hi Hb Hn Hc He Hv Hw.
pose proof (st_ok_pi_region_nth E ss _ i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb in C. cbn [base_val] in C. rewrite Hn in C.
exact (val_of_chunk_ok SEGS E _ b off w e v C He Hv Hw).
Qed.
Lemma rbn5_env_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma rbn5_d64 : forall x, x mod 64 = 0 -> x / 8 = 8 * (x / 64) /\ x = 64 * (x / 64).
Proof.
intros x Hx. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
split; [|exact D]. rewrite D at 1. replace (64 * (x / 64)) with (8 * (x / 64) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity.
Qed.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI)}.
Lemma rbn5_fa : forall X pos lyc1 Sc1 W1 m md Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 m md Er sh -> forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh HM c p.
destruct HM as (_ & HJ & _). destruct HJ as (_ & L1 & _).
destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F1. reflexivity.
Qed.
Lemma rbn5_A_rng : forall X, rbn_cx B G X ->
  alloc_ceiling + 8496 <= rbn_SP X /\ rbn_SP X - 304 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47 /\ rbn_A X mod 32 = 0 /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (spZ (ri_regs X)) 16 ltac:(lia)) as D2. rewrite Hal, Z.add_0_r in D2.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|exact Hal]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma rbn5_F_facts : forall X pos lyc1 Sc1 W1 m md Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 64 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) m a /\ ~ in_img SEGS a) /\
  (forall j, 0 <= j < 64 -> apresent (w_H W1) m (rbn_SH X pos + j)) /\
  rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 /\ rbn_SH X pos mod 8 = 0 /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd.
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh HM.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md Er sh HM 3 pos) as FA.
destruct HM as (_ & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & Happ & Hpr & Hsh).
destruct (frame_al64 SEGS B _ _ _ _ _ 3 pos HAR1 Hin3) as (H64 & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
set (F := frame_addr lyc1 3 pos) in *.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite H64, Z.add_0_r in DF.
assert (E8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia;
  rewrite Z.div_mul by lia; reflexivity).
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact H64|]. split; [exact Happ|].
split.
{ intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha. }
split.
{ intros j Hj. exact (proj1 (Hsh j ltac:(change (512 / 8) with 64; lia))). }
split; [reflexivity|].
split; [unfold shadow_addr; rewrite E8; replace (SHADOW_OFF + 8 * (F / 64)) with ((268431360 + F / 64) * 8)
  by (unfold SHADOW_OFF; lia); apply Z_mod_mult|].
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd. split; [lia|].
pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)).
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
Qed.
Lemma rbn5_mid_kept : forall X pos lyc1 Sc1 W1 m md m2 md2 sh sh',
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X - 104) ->
     ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  rbn_shadow_at W1 m2 (rbn_SH X pos) sh' ->
  rbn_mid B X pos lyc1 Sc1 W1 m2 md2 (fun _ => False) sh'.
Proof.
intros X pos lyc1 Sc1 W1 m md m2 md2 sh sh' HX HM HJ2 HEQ Hsh2.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ sh HM) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ sh HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & _ & _ & _ & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
pose proof HM as (HW1 & HJ1 & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
split; [exact HW1|]. split; [exact HJ2|]. split; [exact Hperm|].
split.
{ destruct HX as (_ & HRO0 & _). subst W1.
  exact (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO0). }
split.
{ unfold rbn_kept. intros a Hfp (q & N & Hq & Ha) Hne.
  transitivity (aview SEGS (w_H W1) m a); [|exact (HK a Hfp (ex_intro _ q (ex_intro _ N (conj Hq Ha))) Hne)].
  assert (Hq1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hq).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hq1) as (_ & Hb4 & Hbc & [Hh1 Hh2] & _ & _ & HN).
  destruct (req_size_pos N ltac:(lia)) as [_ HNr].
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hq1 Hin3) as Hd.
  rewrite FA in Hd. change (fs_frame_bytes 3) with 512 in Hd. fold (rbn_F X pos) in Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh2. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
  apply HEQ; lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m2); [|exact (Hfr j r Hj)].
  intros k Hk. unfold kHighShadowEnd in SHhi. apply HEQ; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m2); [|exact Hfl].
  intros k Hk. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi. apply HEQ; lia. }
exact Hsh2.
Qed.
Definition rbn5_S (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (m : word -> option byte) (md : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true false false) /\
  rbn_cells (mrestrict (w_H W1) m) (rbn_locs6 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\ rbm_args X.
Definition rbn5_R (X : rbn_in) (pos : Z) (regs : bvmap 5 word) : Prop :=
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\ getr regs 25 = w64 (rbn_F X pos + 32) /\
  getr regs 27 = w64 (rbn_F X pos + 64).
Lemma rbn5_tail_post : forall X pos regs lyc1 Sc1 W1 m md regs2 m2 md2,
  rbn_cx B G X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length (rbm_NB X))) -> getr regs 30 = w64 (rbm_ovf 23 (rbm_NM X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X) ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m2 md2 0 ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 24; 27; 29; 30]%bv -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) ->
     ~ (rbn_SH X pos + 16 <= a < rbn_SH X pos + 19) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  aview SEGS (w_H W1) m2 (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) = Some 0 ->
  (forall j, 16 <= j < 19 -> aview SEGS (w_H W1) m2 (rbn_SH X pos + j) = Some 0) ->
  rbn_st6 B X pos regs2 lyc1 Sc1 W1 m2 md2.
Proof.
intros X pos regs lyc1 Sc1 W1 m md regs2 m2 md2 HX (HM & HC & HW4 & HA) ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27)
  R24 R30 R29 HG HJ2 KR HEQ Hz Hs.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & _ & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_NB_ne X) as Hn1. assert (Hn23 : (length (rbm_NB X) <= 23)%nat) by apply firstn_le_length.
set (n := Z.of_nat (length (rbm_NB X))) in *.
assert (Hn : 1 <= n <= 23) by (subst n; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (Hsh2 : rbn_shadow_at W1 m2 (rbn_SH X pos) (rbn_sh true true true false)).
{ intros j Hj. rewrite rbn5_sh_len in Hj.
  destruct (Z_lt_le_dec j 16) as [Hj1 | Hj1]; [|destruct (Z_lt_le_dec j 19) as [Hj2 | Hj2]].
  - rewrite (HEQ (rbn_SH X pos + j)) by lia. rewrite (rbn5_sh_tb j) by lia. apply Hsh0. rewrite rbn5_sh_len. lia.
  - rewrite (Hs j) by lia. rewrite rbn5_sh_tb3 by lia. reflexivity.
  - rewrite (HEQ (rbn_SH X pos + j)) by lia. rewrite (rbn5_sh_tb j) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
unfold rbn_st6. split.
{ apply (rbn5_mid_kept X pos lyc1 Sc1 W1 m md m2 md2 _ _ HX HM HJ2); [|exact Hsh2].
  intros a Ha Hw Hf Hsh. apply HEQ; lia. }
split.
{ unfold rbn_rbase. rewrite !KR by (cbn; tauto). auto 10. }
rewrite !KR by (cbn; tauto).
split; [exact R18|]. split; [exact R27|]. split; [exact R24|]. split; [exact R30|]. split; [exact R29|].
split.
{ apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HC].
  intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin). apply HEQ; lia. }
split; [|exact HA].
apply (garr8_app1 SEGS (mrestrict (w_H W1) m) (mrestrict (w_H W1) m2) (rbn_F X pos + 64) (rbm_NB X) 0 HG).
- fold n. apply rbn5_vm1. exact Hz.
- lia.
- intros a Ha. apply (mbyte_of_aview SEGS). apply HEQ; lia.
Qed.
Lemma rbn5_own_frame : forall X pos lyc1 Sc1 W1 m md Er sh STK sp0 FP bl0 blc a,
  rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  (rbn_F X pos <= a < rbn_F X pos + 512 \/ rbn_SH X pos <= a < rbn_SH X pos + 64) ->
  awr_byte STK sp0 FP bl0 blc lyc1 [(3, pos)] a.
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh STK sp0 FP bl0 blc a HM Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md Er sh HM 3 pos) as FA.
right; right; right. exists 3, pos. split; [left; reflexivity|]. unfold in_zr. cbn [fst snd].
rewrite FA. change (fs_frame_bytes 3) with 512. change (512 / 8) with 64.
unfold rbn_SH, rbn_F in Ha. destruct Ha; [left | right]; lia.
Qed.
Lemma rbn5_tail : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B G X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length (rbm_NB X))) -> getr regs 30 = w64 (rbm_ovf 23 (rbm_NM X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X) ->
  SRr SEGS W1 (rbn_cfg RBN_L2X regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HS5 HR R24 R30 R29 HGNB.
pose proof HS5 as (HM & _ & _ & _). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof HM as (_ & HJ & _ & _ & _ & _ & _ & Hsh0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_NB_ne X) as Hn1. assert (Hn23 : (length (rbm_NB X) <= 23)%nat) by apply firstn_le_length.
set (n := Z.of_nat (length (rbm_NB X))) in *.
assert (Hn : 1 <= n <= 23) by (subst n; lia).
set (F := rbn_F X pos) in *. set (SH := rbn_SH X pos) in *.
destruct (rbn5_d64 _ HF64) as (EF8 & EF).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
assert (Hsc : shadow_addr (F + 64 + n) = SH + (8 + n / 8)).
{ rewrite ESH. unfold shadow_addr. pose proof (Z.div_mod (F + 64 + n) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (F + 64 + n) 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
assert (Hn8 : 0 <= n / 8 < 3) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hs0 : aview SEGS (w_H W1) m (shadow_addr (F + 64 + n)) = Some 0).
{ rewrite Hsc, (Hsh0 (8 + n / 8)) by (rewrite rbn5_sh_len; lia). rewrite rbn5_sh_nb by lia. reflexivity. }
pose proof (rbn5T_entry W1 regs m (F + 64) n SH R27 R24 B22 R18 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) (proj1 (HFpr (F + 64 + n) ltac:(lia))) Hs0 ltac:(intros o Ho; apply HSHp; lia)
  ltac:(rewrite Hsc; lia) ltac:(lia) ltac:(rewrite Hsc; lia)) as HS.
remember (Eimg (Ereg regs (map (Z_to_bv 64) [F + 64 + n; shadow_addr (F + 64 + n)]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [F + 64 + n; shadow_addr (F + 64 + n)])) E)
  by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 64 + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
clear HE.
assert (HW : forall a, in_wrange E (ss_mem rbn5T_ss) a -> a = F + 64 + n \/ SH + 16 <= a < SH + 19).
{ intros a (r & Hr & Hw). unfold rbn5T_ss in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; rewrite ?(rbn5_VB E 18%nat _ E18) in Hw by lia; lia. }
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_L2X) with (BASE + (AF_reac_box_name + 0x460)) by (unfold RBN_L2X; lia).
assert (AWR : awr_ok E (ss_mem rbn5T_ss) REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ablocks B (ri_lyc X) (ri_Sc X))
  (ablocks B lyc1 Sc1) lyc1 [(3, pos)]).
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HM). destruct (HW a Ha); lia. }
paj_run_sh RUNP HS HJ; [exact AWR|].
cbn [ms_mem mkst] in HFr.
pose proof (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) _ HFr HW) as K1. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
2: { exfalso. cbn [branch_taken sv_denot] in Hc. rewrite E24 in Hc.
     rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. apply negb_false_iff in Hc. apply bv_eqb_eq in Hc.
     apply (f_equal bv_unsigned) in Hc. rewrite !unsigned_lit_small in Hc by lia. lia. }
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_P6).
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HM).
  destruct Ha as (r & Hr & Hw).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
  cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; rewrite ?(rbn5_VB E 18%nat _ E18) in Hw by lia; lia. }
cbn [ms_mem mkst] in HFr.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = F + 64 + n \/ SH + 16 <= a < SH + 19) ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a).
{ apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) _ HFr).
  intros a (r & Hr & Hw).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
  cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; rewrite ?(rbn5_VB E 18%nat _ E18) in Hw by lia; lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 27; 29; 30]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pose proof (rbn5_chunkv E _ (w_H W1) ms0 0 _ 32 (F + 64 + n) 0 1 (SLit 0) 0 HS eq_refl eq_refl
  ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Z0.
pose proof (rbn5_chunkv E _ (w_H W1) ms0 2 _ 18 SH 16 1 (SLit 0) 0 HS eq_refl eq_refl
  ltac:(rewrite E18; apply unsigned_lit_small; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Z16.
pose proof (rbn5_chunkv E _ (w_H W1) ms0 2 _ 18 SH 17 1 (SLit 0) 0 HS eq_refl eq_refl
  ltac:(rewrite E18; apply unsigned_lit_small; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Z17.
pose proof (rbn5_chunkv E _ (w_H W1) ms0 2 _ 18 SH 18 1 (SLit 0) 0 HS eq_refl eq_refl
  ltac:(rewrite E18; apply unsigned_lit_small; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Z18.
rewrite Z.add_0_r in Z0. change (N.to_nat 1) with 1%nat in Z0, Z16, Z17, Z18.
pmkst HS. apply SRr_ret.
exists pos, (ms_regs ms0), lyc1, Sc1, (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md))
          mat0 (with_vm_backing (m_vm_lazy md) mat md)).
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_P6) with (BASE + (AF_reac_box_name + RBN_P6)) by lia.
  reflexivity. }
apply (rbn5_tail_post X pos regs lyc1 Sc1 W1 m md _ _ _ HX HS5 HR R24 R30 R29 HGNB HJ KR).
- intros a Ha H1 H2. rewrite (K2 a Ha) by tauto. apply K1; [exact Ha | tauto].
- apply (rbn5_aview_vm1 _ _ _ _ Z0). lia.
- intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia;
  [exact (rbn5_aview_vm1 _ _ _ _ Z16 ltac:(lia)) | exact (rbn5_aview_vm1 _ _ _ _ Z17 ltac:(lia))
  | exact (rbn5_aview_vm1 _ _ _ _ Z18 ltac:(lia))].
Qed.
Lemma rbn5_lbuf_fr : forall X pos lyc1 Sc1 W1 m md Er sh j c,
  rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  0 <= j -> 0 <= c -> j + c <= Z.of_nat (length sh) -> j + c <= 64 ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1 m
    (rbn_F X pos + 8 * j) (8 * c).
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh j c HM Hj Hc Hl H64 Hz.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ sh HM 3 pos) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ sh HM) as (HF4096 & HFceil & HF64 & HFapp & HFpr & _).
pose proof asan_consts as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
destruct (rbn5_d64 _ HF64) as (_ & EF).
assert (HF8 : rbn_F X pos mod 8 = 0) by (rewrite EF; replace (64 * (rbn_F X pos / 64)) with ((8 * (rbn_F X pos / 64)) * 8) by lia;
  apply Z.mod_mul; lia).
split; [lia|]. split; [lia|]. split.
{ apply (in_app_sub _ _ _ _ HFapp); lia. }
split.
{ apply zero_shadow_range.
  - replace (rbn_F X pos + 8 * j) with (rbn_F X pos + j * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
  - replace (8 * c) with (c * 8) by lia. apply Z.mod_mul. lia.
  - intros i Hi. replace (8 * c / 8) with c in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite shadow_of_addr_add8. change (shadow_of_addr SHADOW_OFF (rbn_F X pos)) with (rbn_SH X pos).
    replace (rbn_SH X pos + j + i) with (rbn_SH X pos + (j + i)) by lia.
    rewrite (Hsh0 (j + i)) by lia. rewrite (Hz (j + i)) by lia. reflexivity. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn5_w4_ra : forall X pos lyc1 Sc1 W1 m md Er,
  rbn_mid B X pos lyc1 Sc1 W1 m md Er (rbn_sh true true false false) ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + 32) 5.
Proof.
intros X pos lyc1 Sc1 W1 m md Er HM x Hx.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HM) as (_ & _ & HF64 & _ & _ & _ & ESH & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
destruct (rbn5_d64 _ HF64) as (EF8 & EF).
exists 5. split.
- change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  assert (E4 : shadow_addr x = rbn_SH X pos + 4).
  { rewrite ESH. unfold shadow_addr.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  rewrite E4, (Hsh0 4) by (rewrite rbn5_sh_len; lia). reflexivity.
- right. split; [|lia]. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.
Hypothesis L2F : rbn_L2_fits B.
Hypothesis L2O : rbn_L2_ovf B.
Lemma rbn5_l2 : forall X pos regs lyc1 Sc1 W1 m md pre ov1,
  rbn_cx B G X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length pre)) -> getr regs 30 = w64 ov1 -> (ov1 = 0 \/ ov1 = 1) ->
  getr regs 13 = w64 (hd 0 (rbm_w4 X)) -> getr regs 21 = w64 (rbn_F X pos + 33) ->
  getr regs 10 = w64 (rbn_F X pos + 33) -> getr regs 12 = w64 23 -> getr regs 29 = w64 (rbn_F X pos + 128) ->
  (length pre <= 23)%nat ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) pre ->
  firstn 23 (pre ++ rbm_w4 X) = rbm_NB X ->
  (if 23 <? Z.of_nat (length pre) + 4 then 1 else ov1) = rbm_ovf 23 (rbm_NM X) ->
  SRr SEGS W1 (rbn_cfg RBN_L2 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md pre ov1 HX HS5 HR R24 R30 Hov R13 R21 R10 R12 R29 Hpre HGp HNB HOV.
pose proof HS5 as (HM & HC & HW4 & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (_ & HJ & _ & _ & _ & _ & _ & Hsh0).
pose proof (rbn5_w4_len X HA) as Hw4. pose proof (rbn5_w4_digits X HA) as Hdg.
assert (Hne : rbm_w4 X <> []) by (intros E; rewrite E in Hw4; discriminate).
assert (Hsrc : rbn_lsrc W1 m (rbn_F X pos + 32) (rbm_w4 X ++ [0])).
{ split; [exact HW4|]. rewrite length_app, Hw4. cbn [length Nat.add]. change (Z.of_nat 5) with 5.
  split; [lia|]. split; [lia|]. split; [lia|]. exact (rbn5_w4_ra X pos lyc1 Sc1 W1 m md _ HM). }
assert (Hbuf : rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1
  m (rbn_F X pos + 64) 24).
{ exact (rbn5_lbuf_fr X pos lyc1 Sc1 W1 m md _ _ 8 3 HM ltac:(lia) ltac:(lia)
    ltac:(rewrite rbn5_sh_len; lia) ltac:(lia) ltac:(intros i Hi; apply rbn5_sh_nb; lia)). }
assert (Hsep : rbn_F X pos + 32 + Z.of_nat (length (rbm_w4 X)) + 1 <= rbn_F X pos + 64 \/
  rbn_F X pos + 64 + 24 <= rbn_F X pos + 32) by (rewrite Hw4; lia).
assert (R21' : getr regs 21 = w64 (rbn_F X pos + 32 + 1)) by (rewrite R21; f_equal; lia).
assert (R10' : getr regs 10 = w64 (rbn_F X pos + 32 + 1)) by (rewrite R10; f_equal; lia).
assert (POST : forall nF ovF wr W2 c2,
  rbn_lpost B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m 0 regs RBN_L2X [10; 11; 13; 14; 15; 16; 21; 24; 30]
    (rbn_F X pos + 64) (Z.of_nat (length pre)) wr [(24, nF); (30, ovF)] W2 c2 ->
  pre ++ wr = rbm_NB X -> nF = Z.of_nat (length (rbm_NB X)) -> ovF = rbm_ovf 23 (rbm_NM X) ->
  (Z.of_nat (length pre) + Z.of_nat (length wr) <= 23) ->
  SRr SEGS W2 c2 (rbn_at6 B X)).
{ intros nF ovF wr W2 c2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HK & HO & HEQ & HGw) HNB' -> -> Hlen.
  pose proof (Forall_inv HO) as O24. pose proof (Forall_inv (Forall_inv_tail HO)) as O30.
  cbn [fst snd] in O24, O30.
  assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [10; 11; 13; 14; 15; 16; 21; 24; 30] = false ->
    getr regs2 r = getr regs r) by (intros r Hr; exact (rbn5_keep_get regs regs2 _ r HK Hr)).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
  assert (HEQ' : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 87) ->
    aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) m a) by (intros a Ha Hn; apply HEQ; lia).
  assert (Hsh2 : rbn_shadow_at W1 mem2 (rbn_SH X pos) (rbn_sh true true false false)).
  { intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (HEQ' (rbn_SH X pos + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
  apply (rbn5_tail X pos regs2 lyc1 Sc1 W1 mem2 md2 HX).
  - split; [exact (rbn5_mid_kept X pos lyc1 Sc1 W1 m md mem2 md2 _ _ HX HM HJ2 ltac:(intros a Ha _ Hf _; apply HEQ'; lia) Hsh2)|].
    split.
    { apply (rbn5_cells_kept (w_H W1) (w_H W1) m mem2); [|exact HC].
      intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin).
      destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _). apply HEQ'; lia. }
    split; [|exact HA].
    apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HW4|]. intros x Hx.
    rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply HEQ'; lia.
  - split; [unfold rbn_rbase; rewrite !KG by reflexivity; auto 10|].
    rewrite !KG by reflexivity. auto.
  - apply rbn5_out_get. exact O24.
  - apply rbn5_out_get. exact O30.
  - rewrite KG by reflexivity. exact R29.
  - rewrite <- HNB'. apply garr8_app. split.
    + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HGp|]. intros x Hx.
      apply (mbyte_of_aview SEGS). apply HEQ; lia.
    + exact HGw. }
unfold rbn_cfg.
destruct (Z_le_gt_dec (Z.of_nat (length pre) + 4) 23) as [Hf | Hg].
- pose proof (L2F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 regs (rbn_F X pos + 32) (rbn_F X pos + 64)
    (Z.of_nat (length pre)) ov1 (rbm_w4 X) ltac:(rewrite Hw4; lia)) as R.
  unfold rbn_L2_run in R.
  eapply SRr_bind; [apply R; first [exact HJ | exact Hne | exact Hdg | exact Hsrc | exact Hbuf | exact Hsep
    | lia | exact Hov | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite <- HNB. rewrite firstn_all2 by (rewrite length_app, Hw4; lia). reflexivity.
  + rewrite <- HNB. rewrite firstn_all2 by (rewrite length_app, Hw4; lia). rewrite length_app, Hw4. lia.
  + rewrite <- HOV. replace (23 <? Z.of_nat (length pre) + 4) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  + rewrite Hw4. lia.
- pose proof (L2O REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 regs (rbn_F X pos + 32) (rbn_F X pos + 64)
    (Z.of_nat (length pre)) ov1 (rbm_w4 X) ltac:(rewrite Hw4; lia)) as R.
  unfold rbn_L2_run in R.
  eapply SRr_bind; [apply R; first [exact HJ | exact Hne | exact Hdg | exact Hsrc | exact Hbuf | exact Hsep
    | lia | exact Hov | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite <- HNB. rewrite firstn_app, (firstn_all2 pre) by lia. f_equal. f_equal. lia.
  + rewrite <- HNB. rewrite firstn_length_le by (rewrite length_app, Hw4; lia). reflexivity.
  + rewrite <- HOV. replace (23 <? Z.of_nat (length pre) + 4) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  + rewrite firstn_length_le by (rewrite Hw4; lia). lia.
Qed.
Lemma rbn5_dash : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B G X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X ->
  getr regs 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  getr regs 30 = w64 (rbm_ovf 23 (rbm_stem X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) ->
  SRr SEGS W1 (rbn_cfg 0x3c0 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HS5 HR HNM R24 R30 R29 HGS.
pose proof HS5 as (HM & HC & HW4 & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof HM as (_ & HJ & _ & _ & _ & _ & _ & Hsh0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as Hw4. pose proof (rbn5_w4_digits X HA) as Hdg.
assert (Hc0 : 0 < hd 0 (rbm_w4 X) < 256)
  by (clear - Hw4 Hdg; revert Hw4 Hdg; destruct (rbm_w4 X) as [|c ws]; intros Hw4 Hdg; [discriminate Hw4 | exact (Forall_inv Hdg)]).
assert (Hv0 : val_mem SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 32) 1 (hd 0 (rbm_w4 X))).
{ destruct (HW4 0%nat ltac:(rewrite length_app; lia)) as [Hv _]. cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  revert Hv. clear - Hw4. destruct (rbm_w4 X) as [|c ws]; [discriminate Hw4|]. intros Hv. exact Hv. }
pose proof (rbn5_stem_ne X) as Hsne.
assert (Hn23 : (length (firstn 23 (rbm_stem X)) <= 23)%nat) by apply firstn_le_length.
assert (Hn1 : (1 <= length (firstn 23 (rbm_stem X)))%nat)
  by (clear - Hsne; destruct (rbm_stem X); [exfalso; exact (Hsne eq_refl) | cbn [firstn length]; lia]).
set (n := Z.of_nat (length (firstn 23 (rbm_stem X)))) in *.
assert (Hn : 1 <= n <= 23) by (subst n; lia).
set (F := rbn_F X pos) in *. set (SH := rbn_SH X pos) in *.
set (c0 := hd 0 (rbm_w4 X)) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
pose proof (rbn5D_entry W1 regs m (F + 64) n (F + 32) c0 R27 R24 R25 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) (proj1 (HFpr (F + 64 + n) ltac:(lia))) Hv0 ltac:(lia)) as HS.
remember (Eimg (Ereg regs (map (Z_to_bv 64) [F + 64 + n; c0]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [F + 64 + n; c0])) E)
  by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 64 + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 (F + 32)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E30 : ew E 30 = Z_to_bv 64 (rbm_ovf 23 (rbm_stem X))) by (rewrite (EE 30%nat 30%bv eq_refl); exact R30).
clear HE.
assert (HW : forall a, in_wrange E (ss_mem rbn5D_ss) a -> a = F + 64 + n).
{ intros a (r & Hr & Hw). unfold rbn5D_ss in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + 0x3c0) with (BASE + (AF_reac_box_name + 0x3c0)) by lia.
paj_run_sh RUNP HS HJ.
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HM). rewrite (HW a Ha). lia. }
cbn [ms_mem mkst] in HFr.
pose proof (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) _ HFr HW) as K1. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- assert (Hn23' : n = 23).
  { rewrite branch_ltu_U, U_SLit, (U_atom E 24 n E24) in Hc by lia.
    rewrite (zcanon_id 22) in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_L2).
  { intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HM).
    destruct Ha as (r & Hr & Hw).
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
    cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
    rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 64 + n ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a).
  { apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) _ HFr).
    intros a (r & Hr & Hw).
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
    cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
    rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> F + 64 + n ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m a)
    by (intros a Ha Hne; rewrite (K2 a Ha Hne); exact (K1 a Ha Hne)).
  clear K1 K2 HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 25; 27; 29]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  prreg HS (24%bv : bv 5) G24. prreg HS (30%bv : bv 5) G30. prreg HS (13%bv : bv 5) G13.
  prreg HS (21%bv : bv 5) G21. prreg HS (10%bv : bv 5) G10. prreg HS (12%bv : bv 5) G12.
  pmkst HS.
  replace (BASE + 9996) with (BASE + AF_reac_box_name + RBN_L2) by (unfold AF_reac_box_name, RBN_L2; lia).
  assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X - 104) ->
     ~ (F <= a < F + 504) -> ~ (SH <= a < SH + 64) -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m a)
    by (intros a Ha _ Hf _; apply KM; [exact Ha | lia]).
  assert (Hsh2 : rbn_shadow_at W1 (ms_mem ms0) SH (rbn_sh true true false false)).
  { intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (KM (SH + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
  eapply (rbn5_l2 X pos (ms_regs ms0) lyc1 Sc1 W1 (ms_mem ms0) _ (firstn 23 (rbm_stem X)) 1 HX).
  + split; [exact (rbn5_mid_kept X pos lyc1 Sc1 W1 m md _ _ _ _ HX HM HJ HEQ Hsh2)|].
    split.
    { apply (rbn5_cells_kept (w_H W1) (w_H W1) m (ms_mem ms0)); [|exact HC].
      intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin). apply KM; lia. }
    split; [|exact HA].
    apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HW4|]. intros x Hx.
    rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply KM; lia.
  + split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|].
    rewrite !KR by (cbn; tauto). auto.
  + rewrite G24, E24. fold n. reflexivity.
  + rewrite G30. reflexivity.
  + right; reflexivity.
  + rewrite G13, E33. reflexivity.
  + rewrite G21, E25, unsigned_lit_small by lia. f_equal. lia.
  + rewrite G10, E25, unsigned_lit_small by lia. f_equal. lia.
  + rewrite G12. reflexivity.
  + rewrite KR by (cbn; tauto). exact R29.
  + lia.
  + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HGS|]. intros x Hx.
    apply (mbyte_of_aview SEGS). apply KM; lia.
  + unfold rbm_NB. rewrite HNM.
    assert (HL : (23 <= length (rbm_stem X))%nat).
    { subst n. rewrite length_firstn in Hn23'. lia. }
    rewrite firstn_app, (firstn_app 23 (rbm_stem X)).
    replace (23 - length (firstn 23 (rbm_stem X)))%nat with 0%nat by (rewrite length_firstn; lia).
    replace (23 - length (rbm_stem X))%nat with 0%nat by lia. cbn [firstn]. rewrite !app_nil_r.
    rewrite firstn_firstn. reflexivity.
  + rewrite HNM. unfold rbm_ovf. rewrite length_app. cbn [length]. rewrite Hw4.
    assert (HL : (23 <= length (rbm_stem X))%nat) by (subst n; rewrite length_firstn in Hn23'; lia).
    replace (23 <? Z.of_nat (length (rbm_stem X) + 5)) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (23 <? Z.of_nat (length (firstn 23 (rbm_stem X))) + 4); reflexivity.
- assert (Hn22 : n <= 22).
  { rewrite branch_ltu_U, U_SLit, (U_atom E 24 n E24) in Hc by lia.
    rewrite (zcanon_id 22) in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. lia. }
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_L2).
  { intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HM).
    destruct Ha as (r & Hr & Hw).
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
    cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
    rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 64 + n ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a).
  { apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) _ HFr).
    intros a (r & Hr & Hw).
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
    cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
    rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> F + 64 + n ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m a)
    by (intros a Ha Hne; rewrite (K2 a Ha Hne); exact (K1 a Ha Hne)).
  clear K1 K2 HF HFr HG.
  pose proof (rbn5_chunkv E _ (w_H W1) ms0 0 _ 32 (F + 64 + n) 0 1 (SLit 45) 45 HS eq_refl eq_refl
    ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Z45.
  rewrite Z.add_0_r in Z45. change (N.to_nat 1) with 1%nat in Z45.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 25; 27; 29; 30]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  prreg HS (24%bv : bv 5) G24. prreg HS (13%bv : bv 5) G13.
  prreg HS (21%bv : bv 5) G21. prreg HS (10%bv : bv 5) G10. prreg HS (12%bv : bv 5) G12.
  pmkst HS.
  replace (BASE + 9996) with (BASE + AF_reac_box_name + RBN_L2) by (unfold AF_reac_box_name, RBN_L2; lia).
  assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X - 104) ->
     ~ (F <= a < F + 504) -> ~ (SH <= a < SH + 64) -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m a)
    by (intros a Ha _ Hf _; apply KM; [exact Ha | lia]).
  assert (HL : (length (rbm_stem X) <= 22)%nat).
  { subst n. rewrite length_firstn in Hn22. lia. }
  assert (Hfs : firstn 23 (rbm_stem X) = rbm_stem X) by (apply firstn_all2; lia).
  assert (Hov0 : rbm_ovf 23 (rbm_stem X) = 0)
    by (unfold rbm_ovf; replace (23 <? Z.of_nat (length (rbm_stem X))) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
  assert (Hsh2 : rbn_shadow_at W1 (ms_mem ms0) SH (rbn_sh true true false false)).
  { intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (KM (SH + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
  eapply (rbn5_l2 X pos (ms_regs ms0) lyc1 Sc1 W1 (ms_mem ms0) _ (firstn 23 (rbm_stem X) ++ [45])
    (rbm_ovf 23 (rbm_stem X)) HX).
  + split; [exact (rbn5_mid_kept X pos lyc1 Sc1 W1 m md _ _ _ _ HX HM HJ HEQ Hsh2)|].
    split.
    { apply (rbn5_cells_kept (w_H W1) (w_H W1) m (ms_mem ms0)); [|exact HC].
      intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin). apply KM; lia. }
    split; [|exact HA].
    apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HW4|]. intros x Hx.
    rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply KM; lia.
  + split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|].
    rewrite !KR by (cbn; tauto). auto.
  + rewrite G24, E24, unsigned_lit_small by lia. rewrite length_app. cbn [length]. fold n. f_equal. lia.
  + rewrite KR by (cbn; tauto). exact R30.
  + left; exact Hov0.
  + rewrite G13, E33. reflexivity.
  + rewrite G21, E25, unsigned_lit_small by lia. f_equal. lia.
  + rewrite G10, E25, unsigned_lit_small by lia. f_equal. lia.
  + rewrite G12. reflexivity.
  + rewrite KR by (cbn; tauto). exact R29.
  + rewrite length_app. cbn [length]. lia.
  + apply (garr8_app1 SEGS (mrestrict (w_H W1) m) (mrestrict (w_H W1) (ms_mem ms0)) (F + 64)
      (firstn 23 (rbm_stem X)) 45 HGS).
    * fold n. exact Z45.
    * lia.
    * intros a Ha. apply (mbyte_of_aview SEGS). apply KM; lia.
  + unfold rbm_NB. rewrite HNM, Hfs, <- app_assoc. reflexivity.
  + rewrite HNM, Hov0. unfold rbm_ovf. rewrite Hfs, !length_app. cbn [length]. rewrite Hw4.
    replace (Z.of_nat (length (rbm_stem X) + 1) + 4) with (Z.of_nat (length (rbm_stem X) + 5)) by lia.
    destruct (23 <? Z.of_nat (length (rbm_stem X) + 5)); reflexivity.
Qed.
Lemma rbn5_stem_at : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P m,
  rbn_cx B G X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P -> rbn5_keep W1 (rbn_A X) memc1 m ->
  (forall j, 0 <= j < Z.of_nat (length (rbm_stem X)) + 1 ->
     aview SEGS (w_H W1) m (P + j) = Some (nth (Z.to_nat j) (rbm_stem X ++ [0]) 0)) /\
  (forall a, P <= a < P + Z.of_nat (length (rbm_stem X)) + 1 -> ~ (rbn_SP X - 8496 <= a < rbn_SP X)) /\
  0 < P /\ Z.of_nat (length (rbm_stem X)) < 2 ^ 31 /\ amem_range P (Z.of_nat (length (rbm_stem X)) + 8) /\
  Forall (fun c => 0 < c < 256) (rbm_stem X) /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF P (Z.of_nat (length (rbm_stem X)) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W1) m) P (Z.of_nat (length (rbm_stem X)) + 1) /\
  (forall a, P + Z.of_nat (length (rbm_stem X)) < a <
     P + Z.of_nat (length (rbm_stem X)) - (P + Z.of_nat (length (rbm_stem X))) mod 8 + 8 ->
     aview SEGS (w_H W1) m a <> None) /\
  (forall j, 0 <= j < 5 -> aview SEGS (w_H W1) m (rbn_F X pos + 32 + j) = Some (nth (Z.to_nat j) (rbm_w4 X ++ [0]) 0)) /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + 32) 5 /\
  shadow_hull_vis (aview SEGS (w_H W1) m) (rbn_F X pos + 32) 4.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P m HX H5 KP.
destruct H5 as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW4 & _ & HSTP & HA).
destruct HSTP as ((Hchr & Hlen31 & HP0 & Hamr & HGs & Hras & Hhull & Htl) & Hstw).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as Hw4.
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
pose proof Hamr as Hamr'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr'.
assert (HW : forall a, P <= a < P + Z.of_nat (length (rbm_stem X)) + 1 -> ~ (rbn_SP X - 8496 <= a < rbn_SP X))
  by (intros a Ha; rewrite <- WS; exact (proj1 (Hstw a Ha))).
assert (SHK : forall s, 0 <= s < 2 ^ 64 -> ~ (rbn_SP X - 8496 <= s < rbn_SP X) ->
  aview SEGS (w_H W1) m s = aview SEGS (w_H W1) memc1 s)
  by (intros s Hs Hn; apply KP; [exact Hs | unfold rbn5_dirty; lia]).
assert (HLO : kHighShadowEnd <= rbn_SP X - 8496) by (rewrite C2; lia).
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
split.
{ intros j Hj. rewrite (SHK (P + j)) by first [lia | apply HW; lia].
  apply (rbn5_garr8_view _ _ _ _ HGs). rewrite length_app. cbn [length]. lia. }
split; [exact HW|]. split; [exact HP0|]. split; [exact Hlen31|]. split; [exact Hamr|]. split; [exact Hchr|].
split.
{ apply (range_addressable_kept_win (aview SEGS (w_H W1) memc1) _ (rbn_SP X - 8496) (rbn_SP X));
    [exact SHK | exact HLO | lia | lia | exact Hras]. }
split.
{ apply (shadow_hull_vis_kept_win (aview SEGS (w_H W1) memc1) _ (rbn_SP X - 8496) (rbn_SP X));
    [exact SHK | exact HLO | lia | lia | lia | exact Hhull]. }
split.
{ intros a Ha.
  assert (Hd : ~ rbn5_dirty (rbn_A X) a).
  { pose proof (HW (P + Z.of_nat (length (rbm_stem X))) ltac:(lia)) as Hk.
    pose proof (Z.div_mod (P + Z.of_nat (length (rbm_stem X))) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (P + Z.of_nat (length (rbm_stem X))) 8 ltac:(lia)).
    pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as DA. rewrite AR5, Z.add_0_r in DA.
    unfold rbn5_dirty. lia. }
  rewrite (KP a ltac:(lia) Hd). exact (Htl a Ha). }
split.
{ intros j Hj. rewrite (KP (rbn_F X pos + 32 + j)) by first [lia | unfold rbn5_dirty; lia].
  apply (rbn5_garr8_view _ _ _ _ HW4). rewrite length_app, Hw4. cbn [length]. lia. }
split.
{ apply (range_addressable_kept_win (aview SEGS (w_H W1) memc1) _ (rbn_SP X - 8496) (rbn_SP X));
    [exact SHK | exact HLO | lia | lia | exact (rbn5_w4_ra X pos lyc1 Sc1 W1 memc1 mdc1 _ HM)]. }
assert (H1 : shadow_hull_vis (aview SEGS (w_H W1) memc1) (rbn_F X pos + 32) 4).
{ intros s Hs. destruct (rbn5_d64 _ HF64) as (EF8 & EF).
  replace (rbn_F X pos + 32 + 4 - 1) with (rbn_F X pos + 35) in Hs by lia.
  unfold shadow_addr in Hs.
  pose proof (Z.div_mod (rbn_F X pos + 32) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (rbn_F X pos + 32) 8 ltac:(lia)).
  pose proof (Z.div_mod (rbn_F X pos + 35) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (rbn_F X pos + 35) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (rbn_F X pos + 32) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (rbn_F X pos + 32) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (rbn_F X pos + 35) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (rbn_F X pos + 35) / 8) 8 ltac:(lia)).
  assert (Hj : 0 <= s - rbn_SH X pos < 64) by (rewrite ESH; unfold SHADOW_OFF in *; lia).
  replace s with (rbn_SH X pos + (s - rbn_SH X pos)) by lia.
  apply (aview_some_of_apresent SEGS). apply HSHp. exact Hj. }
apply (shadow_hull_vis_kept_win (aview SEGS (w_H W1) memc1) _ (rbn_SP X - 8496) (rbn_SP X));
  [exact SHK | exact HLO | lia | lia | lia | exact H1].
Qed.
Lemma rbn5_hand : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsF mF mdF,
  rbn_cx B G X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mF mdF 0 ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 27; 30]%bv -> getr regsF r = getr regs1 r) ->
  getr regsF 29 = w64 (rbn_F X pos + 128) ->
  rbn5_keep W1 (rbn_A X) memc1 mF ->
  val_mem SEGS (mrestrict (w_H W1) mF) (rbn_A X + 24) 8 (ri_token X) ->
  val_mem SEGS (mrestrict (w_H W1) mF) (rbn_A X + 48) 8 (rbn_F X pos + 128) ->
  val_mem SEGS (mrestrict (w_H W1) mF) (rbn_A X + 72) 8 (rbn_F X pos) ->
  rbn5_S X pos lyc1 Sc1 W1 mF mdF /\ rbn5_R X pos regsF /\
  getr regsF 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) /\
  getr regsF 30 = w64 (rbm_ovf 23 (rbm_stem X)) /\ getr regsF 29 = w64 (rbn_F X pos + 128) /\
  garr8 SEGS (mrestrict (w_H W1) mF) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsF mF mdF HX H5 HJF KR R29F KP V24 V48 V72.
destruct H5 as (HM & HRB & R18 & R26 & R20 & R23 & R25 & R27 & R24 & R30 & R12 & HC & HW4 & HNP & HSTP & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
pose proof (rbn5_w4_len X HA) as Hw4.
pose proof (firstn_le_length 23 (rbm_stem X)) as Hfl.
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8496 <= a < rbn_SP X - 104) ->
  aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hn; apply KP; [exact Ha | unfold rbn5_dirty; lia]).
split.
{ split.
  - apply (rbn5_mid_kept X pos lyc1 Sc1 W1 memc1 mdc1 mF mdF _ _ HX HM HJF).
    + intros a Ha Hw _ _. apply KE; [exact Ha | exact Hw].
    + intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (KE (rbn_SH X pos + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia.
  - split.
    + unfold rbn_locs6. apply rbn5_cells_app. split.
      * apply (rbn5_cells_kept (w_H W1) (w_H W1) memc1 mF); [|exact HC].
        intros a n0 v k Hin Hk. destruct (rbn5_locs4_clean X pos a n0 v Hin k Hk) as [Hd Hr]. apply KP; [lia | exact Hd].
      * cbn [rbn_cells]. split; [exact V24|]. split; [exact V48|]. split; [exact V72 | exact I].
    + split; [|exact HA].
      apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HW4|]. intros x Hx.
      rewrite length_app, Hw4 in Hx. cbn [length] in Hx.
      apply (mbyte_of_aview SEGS). apply KE; lia. }
split.
{ unfold rbn5_R, rbn_rbase. rewrite !KR by (cbn; tauto). auto 10. }
split; [rewrite KR by (cbn; tauto); exact R24|].
split; [rewrite KR by (cbn; tauto); exact R30|].
split; [exact R29F|].
apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNP|]. intros x Hx.
apply (mbyte_of_aview SEGS). apply KE; lia.
Qed.
Lemma rbn5_hand_st : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P E ss ms mdF,
  rbn_cx B G X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W1) ms) -> env_agree 32 (Ereg regs1 []) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 27; 30]%bv = true ->
  sr_get (ss_regs ss) 29 = SOff 19 128 ->
  ss_mem ss = [rbn5_R24; rbn5_R48; rbn5_R72] ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 (ms_mem ms) mdF 0 ->
  rbn5_keep W1 (rbn_A X) memc1 (ms_mem ms) ->
  rbn5_S X pos lyc1 Sc1 W1 (ms_mem ms) mdF /\ rbn5_R X pos (ms_regs ms) /\
  getr (ms_regs ms) 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) /\
  getr (ms_regs ms) 30 = w64 (rbm_ovf 23 (rbm_stem X)) /\ getr (ms_regs ms) 29 = w64 (rbn_F X pos + 128) /\
  garr8 SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P E ss ms mdF HX H5 HS HAE Hl H29 Hmem HJF KP.
pose proof H5 as (HM & HRB & _ & R26 & _ & R23 & _).
destruct HRB as (_ & _ & _ & _ & B9 & B19 & _).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & _).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htok & _).
pose proof asan_consts as (C1 & _).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [] _ HS HAE Hl) as KR. cbn [ms_regs restrict] in KR.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (rbn5_ag E regs1 9 9%bv HAE eq_refl ltac:(lia)), B9; apply unsigned_lit_small; lia).
assert (G29 : getr (ms_regs ms) 29 = w64 (rbn_F X pos + 128)).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (29%bv : bv 5) HS) as R. rewrite H29 in R. rewrite R.
  apply rbn5_svk; [|lia]. rewrite (rbn5_ag E regs1 19 19%bv HAE eq_refl ltac:(lia)). exact B19. }
assert (V24 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 24) 8 (ri_token X)).
{ exact (rbn5_chunkv E ss (w_H W1) ms 0 rbn5_R24 9 (rbn_A X) 24 8 (SOff 23 0) (ri_token X) HS
    ltac:(rewrite Hmem; reflexivity) eq_refl U9 ltac:(cbn; tauto)
    ltac:(apply rbn5_sv0; rewrite (rbn5_ag E regs1 23 23%bv HAE eq_refl ltac:(lia)); exact R23)
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (V48 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 48) 8 (rbn_F X pos + 128)).
{ exact (rbn5_chunkv E ss (w_H W1) ms 1 rbn5_R48 9 (rbn_A X) 48 8 (SOff 19 128) (rbn_F X pos + 128) HS
    ltac:(rewrite Hmem; reflexivity) eq_refl U9 ltac:(cbn; tauto)
    ltac:(apply rbn5_svk; [rewrite (rbn5_ag E regs1 19 19%bv HAE eq_refl ltac:(lia)); exact B19 | lia])
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (V72 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 72) 8 (rbn_F X pos)).
{ exact (rbn5_chunkv E ss (w_H W1) ms 2 rbn5_R72 9 (rbn_A X) 72 8 (SOff 26 0) (rbn_F X pos) HS
    ltac:(rewrite Hmem; reflexivity) eq_refl U9 ltac:(cbn; tauto)
    ltac:(apply rbn5_sv0; rewrite (rbn5_ag E regs1 26 26%bv HAE eq_refl ltac:(lia)); exact R26)
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
exact (rbn5_hand X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P (ms_regs ms) (ms_mem ms) mdF HX H5 HJF KR G29 KP V24 V48 V72).
Qed.
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Lemma rbn5_strlen_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= kk -> kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  first_byte SEGS W memT x (kk + 1) 0 kk -> src_ok SEGS W regsT memT x (kk + 1) ->
  (forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> amem_range x (kk + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (kk + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (kk + 1) ->
  (forall a, x + kk < a < x + kk - (x + kk) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 kk /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk o raw
  HJ Ha0 Hx0 Hk0 Hk32 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsrc Hwin Hamr Hras Hhull Hslack Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try lia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
eapply SRr_mono.
{ exact (ASTRLEN lyc Sc W regsT memT mdc x kk HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsrc
    ltac:(rewrite Hsp'; exact Hwin) Hamr Hras Hhull Hslack Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma rbn5_sp_facts : forall X (regsT : bvmap 5 word), rbn_cx B G X -> getr regsT 2 = w64 (rbn_A X) ->
  spZ regsT = rbn_SP X + (rbn_A X - rbn_SP X) /\ (rbn_A X - rbn_SP X) mod 16 = 0 /\ rbn_A X - rbn_SP X <= 0 /\
  2 * ESTACK - (rbn_A X - rbn_SP X) <= REAC_BOX_NAME_STK.
Proof.
intros X regsT HX R2.
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
split; [unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia|].
split.
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (rbn_SP X) 16 ltac:(lia)) as D2.
  rewrite AR5, Z.add_0_r in D1. rewrite AR6, Z.add_0_r in D2.
  replace (rbn_A X - rbn_SP X) with ((2 * (rbn_A X / 32) - rbn_SP X / 16) * 16) by lia. apply Z_mod_mult. }
split; lia.
Qed.
Lemma rbn5_strlen_call : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsT memT mdT,
  rbn_cx B G X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memT mdT 0 ->
  rbn5_keep W1 (rbn_A X) memc1 memT ->
  getr regsT 10 = w64 P -> getr regsT 2 = w64 (rbn_A X) -> getr regsT 3 = w64 (as_gp B) ->
  getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + 9900) ->
  SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 9900)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
         [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length (rbm_stem X))) /\
       rbn5_keep W1 (rbn_A X) memc1 mem2 /\ (forall a, apresent (w_H W1) memT a -> apresent (w_H W1) mem2 a) /\
       (forall a, rbn_A X <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memT a)).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsT memT mdT HX H5 HJT KP R10 R2 R3 R4 R1.
destruct (rbn5_stem_at X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P memT HX H5 KP)
  as (SV & HW & HP0 & Hlen31 & Hamr & Hchr & Hras & Hhull & Htl & _).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
destruct (rbn5_sp_facts X regsT HX R2) as (Hsp & HAmod & Hneg & Hbud).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hamr as Hamr'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr'.
pose proof HX as (_ & HRO0 & _).
eapply SRr_mono.
{ apply (rbn5_strlen_at W1 regsT memT REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X)
    (ri_memc X) (ri_mdc X) [(3, pos)] lyc1 Sc1 mdT 0 P (Z.of_nat (length (rbm_stem X))) (rbn_A X - rbn_SP X)
    (Z_to_bv 64 (BASE + 9900)) HJT R10 HP0 ltac:(lia) ltac:(lia) ltac:(lia) Hsp HAmod Hneg Hbud R3 R4 R1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])).
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) (rbm_stem X) 0). split.
      * rewrite (SV i) by lia. f_equal. apply app_nth1. lia.
      * pose proof (proj1 (Forall_forall _ _) Hchr _ (nth_In (rbm_stem X) 0 (ltac:(lia) : (Z.to_nat i < length (rbm_stem X))%nat))) as Hc0.
        cbv beta in Hc0. lia.
    + intros _. rewrite (SV (Z.of_nat (length (rbm_stem X)))) by lia. f_equal. rewrite Nat2Z.id.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros a Ha. split.
    + replace a with (P + (a - P)) by lia. rewrite (SV (a - P)) by lia. discriminate.
    + rewrite Hsp, Hes. pose proof (HW a ltac:(lia)). lia.
  - intros a Ha. pose proof (HW a ltac:(lia)). rewrite Hes. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - exact Hras.
  - exact Hhull.
  - exact Htl.
  - exact (aro_unowned_of_arodata SEGS _ _ B _
      (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJT HRO0)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hfr2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact Ha02|].
split.
{ apply (rbn5_keep_call W1 _ memc1 memT mem2 KP). intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hes; lia]. }
split; [exact Hpres2|].
intros a Ha. apply Hfr2; [lia | rewrite Hes; lia].
Qed.
Lemma rbn5_bcmp_call : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsT memT mdT,
  rbn_cx B G X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memT mdT 0 ->
  rbn5_keep W1 (rbn_A X) memc1 memT -> 4 <= Z.of_nat (length (rbm_stem X)) ->
  getr regsT 10 = w64 (P + Z.of_nat (length (rbm_stem X)) - 4) -> getr regsT 11 = w64 (rbn_F X pos + 32) ->
  getr regsT 12 = w64 4 -> getr regsT 2 = w64 (rbn_A X) -> getr regsT 3 = w64 (as_gp B) ->
  getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + 9932) ->
  SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2 (v : word),
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 9932)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
         [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
       (v = w64 0 <-> skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X) /\
       rbn5_keep W1 (rbn_A X) memc1 mem2 /\ (forall a, apresent (w_H W1) memT a -> apresent (w_H W1) mem2 a) /\
       (forall a, rbn_A X <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memT a)).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regsT memT mdT HX H5 HJT KP Hk4 R10 R11 R12 R2 R3 R4 R1.
destruct (rbn5_stem_at X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P memT HX H5 KP)
  as (SV & HW & HP0 & Hlen31 & Hamr & Hchr & Hras & Hhull & Htl & W4V & Hra4 & Hhl4).
pose proof H5 as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & HF64 & HFapp & _).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
destruct (rbn5_sp_facts X regsT HX R2) as (Hsp & HAmod & Hneg & Hbud).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as Hw4.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hamr as Hamr'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr'.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
eapply SRr_mono.
{ apply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IS___interceptor_trampoline_bcmp) ABCMP W1 regsT memT
    REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) [(3, pos)]
    lyc1 Sc1 mdT 0 (P + Z.of_nat (length (rbm_stem X)) - 4) (rbn_F X pos + 32) 4 (rbn_A X - rbn_SP X)
    (Z_to_bv 64 (BASE + 9932)) HJT R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hsp HAmod Hneg Hbud R3 R4 R1 ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])).
  - intros a Ha. split.
    + replace a with (P + (a - P)) by lia. rewrite (SV (a - P)) by lia. discriminate.
    + rewrite Hsp, Hes. pose proof (HW a ltac:(lia)). lia.
  - intros a Ha. split.
    + replace a with (rbn_F X pos + 32 + (a - (rbn_F X pos + 32))) by lia. rewrite (W4V (a - (rbn_F X pos + 32))) by lia.
      discriminate.
    + rewrite Hsp, Hes. lia.
  - intros a Ha. pose proof (HW a ltac:(lia)). rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (range_addressable_sub _ _ P (Z.of_nat (length (rbm_stem X)) + 1)); [exact Hras | lia | lia].
  - intros _. apply (rbn5_hull_sub _ P (Z.of_nat (length (rbm_stem X)) + 1)); [exact Hhull | lia | lia | lia].
  - apply (range_addressable_sub _ _ (rbn_F X pos + 32) 5); [exact Hra4 | lia | lia].
  - intros _. exact Hhl4. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Ha02 & Hcmp & Hfr2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact Ha02|].
split.
{ rewrite Hcmp. exact (rbn5_tail4 (rbm_stem X) (rbm_w4 X) P (rbn_F X pos + 32) (aview SEGS (w_H W1) memT)
    ltac:(lia) Hw4 SV W4V). }
split.
{ apply (rbn5_keep_call W1 _ memc1 memT mem2 KP). intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hes; lia]. }
split; [exact Hpres2|].
intros a Ha. apply Hfr2; [lia | rewrite Hes; lia].
Qed.
Ltac rbn5_kp KP U :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let K := fresh "KP" in
    pose proof (rbn5_keep_run _ _ _ m1 m2 Ex rs KP HFr U ltac:(vm_compute; reflexivity)) as K;
    clear KP; rename K into KP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac rbn5_awr U := apply (rbn5_awrA _ _ _ _ _ _ _ _ _ _ U); [lia | lia | vm_compute; reflexivity].
Ltac rbn5_kq U Hab Hpres :=
  lazymatch goal with HS2 : ?Q -> _ |- _ =>
    lazymatch Q with Forall _ _ =>
      let HQ := fresh "HQ" in
      assert (HQ : Q);
      [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
        (eapply (region_kept_aview _ _ _ _ 9%nat _ _ _ _ _ _ U);
         [ intros aa Haa; apply Hab; lia | exact Hpres ])
      | specialize (HS2 HQ); clear HQ ] end end.
Theorem rbn_seg5 : rbn_seg5_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H5.
pose proof H5 as (HM & HRB & R18 & R26 & R20 & R23 & R25 & R27 & R24 & R30 & R12 & _ & _ & _ & HSTP & _).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & _).
pose proof HM as (_ & HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct HSTP as ((_ & _ & HP0 & Hamr & _) & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 []) E) by (subst E; apply rbn5_env_agree).
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (rbn5_ag E regs1 9 9%bv HAE eq_refl ltac:(lia)), B9; apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = Z_to_bv 64 4) by (rewrite (rbn5_ag E regs1 12 12%bv HAE eq_refl ltac:(lia)); exact R12).
assert (HS : st_ok_pi SEGS VAL E rbn5A_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x370))) memc1 (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. unfold rbn5A_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U9;
    (split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | apply Forall_nil]).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [exact I | split; exact I]. }
clear HE.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_P5) with (BASE + (AF_reac_box_name + 0x370)) by (unfold RBN_P5; lia).
assert (KP : rbn5_keep W1 (rbn_A X) memc1 memc1) by (intros a _ _; reflexivity).
paj_run_shc RUNP RUNC HS HJ; [rbn5_awr U9|].
rbn5_kp KP U9.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U, (U_atom E 12 4 E12), U_SLit in Hc by lia.
  rewrite (zcanon_id 4) in Hc by (unfold M64; lia). rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ; [rbn5_awr U9|].
rbn5_kp KP U9.
rbn5_rget HS (10%bv : bv 5) Ra0. rbn5_rget HS (1%bv : bv 5) Rra. rbn5_rget HS (2%bv : bv 5) Rsp.
rbn5_rget HS (3%bv : bv 5) Rgp. rbn5_rget HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ apply (rbn5_strlen_call X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P _ _ _ HX H5 HJ KP).
  - rewrite Ra0. apply rbn5_sv0. rewrite (rbn5_ag E regs1 20 20%bv HAE eq_refl ltac:(lia)). exact R20.
  - rewrite Rsp. apply rbn5_sv0. rewrite (rbn5_ag E regs1 2 2%bv HAE eq_refl ltac:(lia)). exact B2.
  - rewrite Rgp. apply rbn5_sv0. rewrite (rbn5_ag E regs1 3 3%bv HAE eq_refl ltac:(lia)). exact B3.
  - rewrite Rtp. apply rbn5_sv0. rewrite (rbn5_ag E regs1 4 4%bv HAE eq_refl ltac:(lia)). exact B4.
  - rewrite Rra. exact (codeptr_val E 9900 HEI). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & KP2 & Hpres2 & Hab2).
clear Ra0 Rra Rsp Rgp Rtp.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
rbn5_kq U9 Hab2 Hpres2.
clear HS KP. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename KP2 into KP.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E516 : ew E2 516 = Z_to_bv 64 (Z.of_nat (length (rbm_stem X)))).
{ rewrite HE2. change 516%nat with (512 + 4)%nat. rewrite (YN3v.ew_havoc_new _ 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
  cbn [nth map CLOB]. exact Ha02. }
assert (HAE2 : env_agree 32 (Ereg regs1 []) E2) by (rewrite HE2; apply rbn5_agree_havoc; [lia | exact HAE]).
assert (U9b : bv_unsigned (ew E2 9) = rbn_A X)
  by (rewrite (rbn5_ag E2 regs1 9 9%bv HAE2 eq_refl ltac:(lia)), B9; apply unsigned_lit_small; lia).
clear HE2.
paj_run_shc RUNP RUNC HS HJ2; [rbn5_awr U9b|].
rbn5_kp KP U9b.
psrr_branch_pi RUNP BR HS.
- assert (Hk4 : Z.of_nat (length (rbm_stem X)) < 4).
  { rewrite branch_ltu_U, (U_atom E2 516 _ E516), U_SLit in Hc by lia.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. exact Hc. }
  paj_run_to_sh RUNTOP HS HJ2 (AF_reac_box_name + 0x3c0); [rbn5_awr U9b|].
  rbn5_kp KP U9b.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    destruct (rbn5_hand_st X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P E2 _ msx _ HX H5 HS HAE2
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 KP)
      as (HS5 & HR5 & G24 & G30 & G29 & HG5) end.
  assert (HNM : rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X)
    by (destruct (rbn5_NM_cases X) as [(Hc4 & _) | (_ & H)]; [lia | exact H]).
  pmkst HS.
  replace (BASE + 9944) with (BASE + AF_reac_box_name + 0x3c0) by (unfold AF_reac_box_name; lia).
  exact (rbn5_dash X pos _ lyc1 Sc1 W1 _ _ HX HS5 HR5 HNM G24 G30 G29 HG5).
- assert (Hk4 : 4 <= Z.of_nat (length (rbm_stem X))).
  { rewrite branch_ltu_U, (U_atom E2 516 _ E516), U_SLit in Hc by lia.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ2; [rbn5_awr U9b|].
  rbn5_kp KP U9b.
  rbn5_rget HS (10%bv : bv 5) Ra0. rbn5_rget HS (11%bv : bv 5) Ra1. rbn5_rget HS (12%bv : bv 5) Ra2.
  rbn5_rget HS (1%bv : bv 5) Rra. rbn5_rget HS (2%bv : bv 5) Rsp.
  rbn5_rget HS (3%bv : bv 5) Rgp. rbn5_rget HS (4%bv : bv 5) Rtp.
  pmkst HS.
  eapply SRr_bind.
  { apply (rbn5_bcmp_call X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P _ _ _ HX H5 HJ2 KP Hk4).
    - rewrite Ra0. apply rbn5_den_U; [|lia]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff.
      rewrite (rbn5_ag E2 regs1 20 20%bv HAE2 eq_refl ltac:(lia)), R20, E516.
      unfold w64. rewrite !unsigned_lit_small by lia. unfold zcanon, M64. rewrite Z.add_0_r.
      rewrite (Z.mod_small (Z.of_nat (length (rbm_stem X))) (2 ^ 64)) by lia.
      rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
    - rewrite Ra1. apply rbn5_sv0. rewrite (rbn5_ag E2 regs1 25 25%bv HAE2 eq_refl ltac:(lia)). exact R25.
    - rewrite Ra2. reflexivity.
    - rewrite Rsp. apply rbn5_sv0. rewrite (rbn5_ag E2 regs1 2 2%bv HAE2 eq_refl ltac:(lia)). exact B2.
    - rewrite Rgp. apply rbn5_sv0. rewrite (rbn5_ag E2 regs1 3 3%bv HAE2 eq_refl ltac:(lia)). exact B3.
    - rewrite Rtp. apply rbn5_sv0. rewrite (rbn5_ag E2 regs1 4 4%bv HAE2 eq_refl ltac:(lia)). exact B4.
    - rewrite Rra. exact (codeptr_val E2 9932 HEI2). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv3 & Hcmp & KP3 & Hpres3 & Hab3).
  clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
  jafter_call_keep_hi HS 528%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2]%nat HS3.
  rbn5_kq U9b Hab3 Hpres3.
  clear HS KP. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS. rename KP3 into KP.
  remember (havoc E2 528 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
  assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
  assert (E532 : ew E3 532 = v).
  { rewrite HE3. change 532%nat with (528 + 4)%nat. rewrite (YN3v.ew_havoc_new _ 528 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    cbn [nth map CLOB]. exact Hv3. }
  assert (HAE3 : env_agree 32 (Ereg regs1 []) E3) by (rewrite HE3; apply rbn5_agree_havoc; [lia | exact HAE2]).
  assert (U9c : bv_unsigned (ew E3 9) = rbn_A X)
    by (rewrite (rbn5_ag E3 regs1 9 9%bv HAE3 eq_refl ltac:(lia)), B9; apply unsigned_lit_small; lia).
  clear HE3.
  paj_run_shc RUNP RUNC HS HJ3; [rbn5_awr U9c|].
  rbn5_kp KP U9c.
  psrr_branch_pi RUNP BR HS.
  + pose proof (rbn5_br_eq0 E3 532 v E532 Hc) as Hv0. apply Hcmp in Hv0.
    assert (HNM : rbm_NM X = rbm_stem X)
      by (destruct (rbn5_NM_cases X) as [(_ & _ & H) | (Hn & _)]; [exact H | exfalso; apply Hn; split; [lia | exact Hv0]]).
    paj_run_to_sh RUNTOP HS HJ3 (AF_reac_box_name + 0x460); [rbn5_awr U9c|].
    rbn5_kp KP U9c.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      destruct (rbn5_hand_st X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P E3 _ msx _ HX H5 HS HAE3
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ3 KP)
        as (HS5 & HR5 & G24 & G30 & G29 & HG5) end.
    pmkst HS.
    replace (BASE + 10104) with (BASE + AF_reac_box_name + RBN_L2X) by (unfold AF_reac_box_name, RBN_L2X; lia).
    apply (rbn5_tail X pos _ lyc1 Sc1 W1 _ _ HX HS5 HR5).
    * unfold rbm_NB. rewrite HNM. exact G24.
    * rewrite HNM. exact G30.
    * exact G29.
    * unfold rbm_NB. rewrite HNM. exact HG5.
  + pose proof (rbn5_br_ne0 E3 532 v E532 Hc) as Hv0.
    assert (HNM : rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X)
      by (destruct (rbn5_NM_cases X) as [(_ & Hsk & _) | (_ & H)]; [exfalso; exact (Hv0 (proj2 Hcmp Hsk)) | exact H]).
    paj_run_to_sh RUNTOP HS HJ3 (AF_reac_box_name + 0x3c0); [rbn5_awr U9c|].
    rbn5_kp KP U9c.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      destruct (rbn5_hand_st X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P E3 _ msx _ HX H5 HS HAE3
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ3 KP)
        as (HS5 & HR5 & G24 & G30 & G29 & HG5) end.
    pmkst HS.
    replace (BASE + 9944) with (BASE + AF_reac_box_name + 0x3c0) by (unfold AF_reac_box_name; lia).
    exact (rbn5_dash X pos _ lyc1 Sc1 W1 _ _ HX HS5 HR5 HNM G24 G30 G29 HG5).
Qed.
End h.
End f.
End d.
