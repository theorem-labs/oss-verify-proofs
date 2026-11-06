(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/rec_canonical.v (a working branch 1d526f2e737) for
   fuzz_command.asan-ubsan (entry 0x897e8, 115 instructions). The malloc wrapper call and its null/abort edge are one
   program call of xmalloc here (0x89814, PCall CS_xmalloc), taken through cl_callS (PaCall.v) with the statement's
   HXMALLOC at the walk's own fx and HSIG (cmd_sig_prog, CmdObj.v: the call target); s0 holds len there, below
   alloc_ceiling, so achain_low gives xmalloc's frame chain, and xmalloc's journal keeps the frame. The copy loop
   keeps i (a4) and o (a3) and recomputes text + i and out + o per byte; ~out (a2), ~text (a5) and text != 0 (a6)
   feed the UBSan checks. The walk is cut at the xmalloc return (0x89818: the empty-line check), the outer head
   (0x8983c), the word-scan head (0x8984c), the word start (0x8989c), the copy head (0x898d0), the tail (0x89954) and
   the store of the terminator (0x8995c, where the empty line enters). Of the seven UBSan trap branches (to the unimp
   at 0x89988) the executor decides six from the seeds' facts: 0x8985c and 0x89860 from text, text + i >= 4096 (the
   block law), 0x898a4, 0x898d0, 0x898f4 and 0x89954 from ~out, ~text >= 2^64 - 1 - CEIL_MAX and o, i <= LMAX; the
   walk refutes 0x89850 (text + i < text) at the branch, since text + i < 2^64. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_canonical.v, with its module paths and module names changed; 1605 of its 1733 lines of code are new or changed and 2250 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
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
Lemma rbn5_bn_tk_len : forall l seen, (length (bn_tk seen l) <= length l)%nat.
Proof.
induction l as [|c l IH]; intros seen; cbn [bn_tk length]; [lia|].
destruct ((c =? 45) && negb seen)%bool; cbn [length]; [specialize (IH true); lia | specialize (IH seen); lia].
Qed.
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
Lemma rbn5_skip_eq : forall (s w : list Z) k, length w = 4%nat -> (k + 4 = length s)%nat ->
  (skipn k s = w <-> forall i, (i < 4)%nat -> nth (k + i) s 0 = nth i w 0).
Proof.
intros s w k Hw Hs. split.
- intros <- i Hi. rewrite nth_skipn. reflexivity.
- intros H. apply (nth_ext _ _ 0 0).
  + rewrite length_skipn. lia.
  + intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. apply H. lia.
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
    (mkFacts [] [] [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0)]).
Definition rbn5M_ss (pc : Z) : sstate :=
  mkSS pc (sr_set sr_atoms 23%bv (SLit 4))
    [YP09.mkRegion (Some 9%nat) 48 56 48 48 [YP09.mkChunk 48 (CVal 8 (SOff 19 128))]] None (mkFacts [] [] []).
Definition rbn5H_ss : sstate :=
  mkSS (AF_reac_box_name + RBN_P5) (sr_set sr_atoms 12%bv (SLit 4))
    [YP09.mkRegion (Some 9%nat) 24 32 24 32 []; YP09.mkRegion (Some 9%nat) 48 56 48 56 [];
     YP09.mkRegion (Some 9%nat) 72 80 72 80 []] None (mkFacts [] [] []).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma rbn5_dash_m1 : forall X, rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X -> length (rbm_w4 X) = 4%nat ->
  (length (rbm_stem X) <= 22)%nat ->
  firstn 23 ((firstn 23 (rbm_stem X) ++ [45]) ++ rbm_w4 X) = rbm_NB X /\
  (if 23 <? Z.of_nat (length (firstn 23 (rbm_stem X) ++ [45])) + 4 then 1 else rbm_ovf 23 (rbm_stem X)) =
    rbm_ovf 23 (rbm_NM X).
Proof.
intros X HN Hw HL. rewrite (firstn_all2 (rbm_stem X)) by lia. unfold rbm_NB. rewrite HN, <- app_assoc.
split; [reflexivity|].
unfold rbm_ovf. rewrite !length_app. cbn [length]. rewrite Hw.
replace (23 <? Z.of_nat (length (rbm_stem X))) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.of_nat (length (rbm_stem X) + 1) + 4) with (Z.of_nat (length (rbm_stem X) + 5)) by lia.
reflexivity.
Qed.
Lemma rbn5_dash_m2 : forall X, rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X -> (23 <= length (rbm_stem X))%nat ->
  firstn 23 (firstn 23 (rbm_stem X) ++ rbm_w4 X) = rbm_NB X /\ 1 = rbm_ovf 23 (rbm_NM X).
Proof.
intros X HN HL. unfold rbm_NB. rewrite HN.
assert (Hf : length (firstn 23 (rbm_stem X)) = 23%nat) by (apply firstn_length_le; lia).
split.
- rewrite !firstn_app, Hf. replace (23 - length (rbm_stem X))%nat with 0%nat by lia.
  replace (23 - 23)%nat with 0%nat by lia. cbn [firstn]. rewrite !app_nil_r, firstn_firstn. reflexivity.
- unfold rbm_ovf. rewrite length_app. cbn [length].
  replace (23 <? Z.of_nat (length (rbm_stem X) + S (length (rbm_w4 X)))) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma rbn5_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
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
Lemma rbn5_le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
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
Lemma rbn5_VB : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v.
Proof. intros E k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. Qed.
Lemma rbn5_kept_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn5_shadow_addr_rng : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 47 /\ shadow_addr x = SHADOW_OFF + x / 8.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF. split; [|reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.
Lemma rbn5T_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) m D n SH,
  getr regs 27 = w64 D -> getr regs 24 = w64 n -> getr regs 22 = w64 SHADOW_OFF -> getr regs 18 = w64 SH ->
  0 <= D -> 0 <= n -> D + n + 1 <= 2 ^ 47 -> 0 <= SH -> SH + 19 <= 2 ^ 47 ->
  apresent (w_H W) m (D + n) -> aview SEGS (w_H W) m (shadow_addr (D + n)) = Some 0 ->
  (forall o, 16 <= o < 19 -> apresent (w_H W) m (SH + o)) ->
  (D + n + 1 <= shadow_addr (D + n) \/ shadow_addr (D + n) + 1 <= D + n) ->
  (D + n + 1 <= SH + 16 \/ SH + 19 <= D + n) ->
  (shadow_addr (D + n) + 1 <= SH + 16 \/ SH + 19 <= shadow_addr (D + n)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [D + n; shadow_addr (D + n)]))) rbn5T_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x460))) m (seg_rom SEGS))).
Proof.
intros fq W regs m D n SH H27 H24 H22 H18 HD Hn HDn HSH0 HSH Hp Hs0 Hs3 Dj1 Dj2 Dj3.
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
Lemma rbn5D_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) m D n Q c,
  getr regs 27 = w64 D -> getr regs 24 = w64 n -> getr regs 25 = w64 Q ->
  0 <= D -> 0 <= n -> D + n + 1 <= 2 ^ 47 -> 0 <= Q -> Q + 1 <= 2 ^ 47 -> 0 <= c < 256 ->
  apresent (w_H W) m (D + n) -> val_mem SEGS (mrestrict (w_H W) m) Q 1 c ->
  (D + n + 1 <= Q \/ Q + 1 <= D + n) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [D + n; c]))) rbn5D_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x3c0))) m (seg_rom SEGS))).
Proof.
intros fq W regs m D n Q c H27 H24 H25 HD Hn HDn HQ0 HQ Hc Hp Hv Dj.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [D + n; c]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (D + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E27 : ew E 27 = Z_to_bv 64 D) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 Q) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
unfold rbn5D_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (rbn5_VB E 32%nat (D + n) E32) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); replace (D + n + o) with (D + n) by lia; exact Hp|].
    apply Forall_nil.
  + rewrite (rbn5_VB E 25%nat Q E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 33 0) c);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (rbn5_VB E 32%nat _ E32), (rbn5_VB E 25%nat _ E25) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; [exact I|]. cbn [f_alias alias_ok]. split; [|exact I].
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 27 D E27), (U_atom E 24 n E24), (U_atom E 32 (D + n) E32) by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma rbn5_chunk1 {fq : YK11.FPState} : forall E ss H ms0 i r n b off v,
  st_ok_pi SEGS VAL E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) (YP09.r_chunks r) -> 0 <= v < 256 ->
  aview SEGS H (ms_mem ms0) (b + off) = Some v.
Proof.
intros E ss H ms0 i r n b off v HS Hi Hb Hn Hbr Hc Hv.
pose proof (st_ok_pi_region_nth E ss _ i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb, (rbn5_VB E n b Hn Hbr) in C.
apply rbn5_aview_vm1; [|exact Hv].
exact (val_of_chunk_ok SEGS E _ b off 1 (SLit v) v C eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma rbn5_env_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma rbn5_reg_U {fq : YK11.FPState} : forall E ss H ms0 (r : bv 5) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms0) -> sr_get (ss_regs ss) r = e -> U E e = v ->
  getr (ms_regs ms0) r = w64 v.
Proof.
intros E ss H ms0 r e v HS He Hv. pose proof (st_ok_pi_restrict_reg H E ss ms0 r HS) as R.
rewrite He, denot_lit_U, Hv in R. exact R.
Qed.
Lemma rbn5_garr8_aview : forall H (m : word -> option byte) base l j,
  garr8 SEGS (mrestrict H m) base l -> (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m base l j HG Hj. destruct (HG j Hj) as [Hv Hr]. exact (rbn5_aview_vm1 H m _ _ Hv Hr). Qed.
Lemma rbn5_ra_sub : forall (rd rd' : Z -> option Z) x n x' n',
  (forall s, 0 <= s < 2 ^ 64 -> rd' s = rd s) -> 0 <= x -> x + n <= 2 ^ 63 ->
  range_addressable rd SHADOW_OFF x n -> x <= x' -> x' + n' <= x + n -> range_addressable rd' SHADOW_OFF x' n'.
Proof.
intros rd rd' x n x' n' Hrd H0 H63 H Hx Hn y Hy. destruct (H y ltac:(lia)) as (sv & Hs & Hok).
exists sv. split; [|exact Hok]. rewrite Hrd; [exact Hs|].
change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.
Lemma rbn5_hull_sub : forall (rd rd' : Z -> option Z) x n x' n',
  (forall s, 0 <= s < 2 ^ 64 -> rd' s = rd s) -> 0 <= x -> x + n <= 2 ^ 63 ->
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd' x' n'.
Proof.
intros rd rd' x n x' n' Hrd H0 H63 H Hx Hn Hn' s Hs.
pose proof (shadow_mono x x' Hx) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2).
assert (B1 : 0 <= shadow_addr x / 8 * 8) by (unfold shadow_addr, SHADOW_OFF; apply Z.mul_nonneg_nonneg; [|lia];
  apply Z.div_pos; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia | lia]).
assert (B2 : shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 63).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)). lia. }
rewrite Hrd by lia. apply H. lia.
Qed.
Lemma rbn5_amem_shadow : forall x a n, amem_range a n -> 0 <= a -> a <= x < a + n ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg.
Proof.
intros x a n Ham Ha Hx. unfold shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn5_str_win : forall (W : world SEGS) (m m2 : word -> option byte) a s lo hi,
  rbn_str W m a s -> lo mod 8 = 0 -> kHighShadowEnd <= lo ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> ~ (lo <= x < hi)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m x) ->
  rbn_str W m2 a s.
Proof.
intros W m m2 a s lo hi (Hf & Hg & Ha0 & Ha1 & Hl & Ham & Hra & Hhv & Htl) Hlo8 Hlo Hdis HE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsb : forall x, a <= x < a + Z.of_nat (length s) + 1 ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg)
  by (intros x Hx; exact (rbn5_amem_shadow x a _ Ham ltac:(lia) ltac:(lia))).
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE; [lia|]. apply Hdis. lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|]. split.
{ intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs.
  destruct (Hsb x ltac:(lia)) as [S1 S2].
  rewrite (HE _) by (unfold SHADOW_OFF in *; lia). exact Hs. }
split.
{ intros sx Hsx. destruct (Hsb a ltac:(lia)) as [S1 _].
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Hsx by lia.
  destruct (Hsb (a + Z.of_nat (length s)) ltac:(lia)) as [_ S2].
  pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (shadow_addr (a + Z.of_nat (length s))) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (shadow_addr (a + Z.of_nat (length s))) 8 ltac:(lia)) as M2.
  rewrite (HE _) by (unfold SHADOW_OFF in *; lia). apply Hhv.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) by lia. exact Hsx. }
intros x Hx.
pose proof (Z.div_mod (a + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod lo 8 ltac:(lia)) as D2.
pose proof (Hdis (a + Z.of_nat (length s)) ltac:(lia)) as Hy.
rewrite (HE x) by lia. exact (Htl x Hx).
Qed.
Lemma rbn5_pres : forall (regs regs2 : bvmap 5 word), aregs_preserved regs regs2 ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 HP r Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma rbn5_bcmp_model : forall X (rd : Z -> option Z) x y,
  4 <= Z.of_nat (length (rbm_stem X)) -> length (rbm_w4 X) = 4%nat ->
  (forall i, 0 <= i < 4 -> rd (x + i) = Some (nth (length (rbm_stem X) - 4 + Z.to_nat i) (rbm_stem X) 0)) ->
  (forall i, 0 <= i < 4 -> rd (y + i) = Some (nth (Z.to_nat i) (rbm_w4 X) 0)) ->
  ((forall i, 0 <= i < 4 -> rd (x + i) = rd (y + i)) -> rbm_NM X = rbm_stem X) /\
  (~ (forall i, 0 <= i < 4 -> rd (x + i) = rd (y + i)) -> rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X).
Proof.
intros X rd x y HL Hw H1 H2.
assert (EQ : (forall i, 0 <= i < 4 -> rd (x + i) = rd (y + i)) <->
  skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X).
{ rewrite (rbn5_skip_eq (rbm_stem X) (rbm_w4 X) (length (rbm_stem X) - 4) Hw ltac:(lia)). split.
  - intros H i Hi. specialize (H (Z.of_nat i) ltac:(lia)). rewrite H1, H2 in H by lia. rewrite Nat2Z.id in H.
    injection H as H. exact H.
  - intros H i Hi. rewrite H1, H2 by lia. f_equal. apply H. lia. }
split.
- intros Heq. apply EQ in Heq. destruct (rbn5_NM_cases X) as [(_ & _ & ->) | (Hn & _)]; [reflexivity|].
  exfalso. apply Hn. split; [lia | exact Heq].
- intros Hne. destruct (rbn5_NM_cases X) as [(_ & Hk & _) | (_ & ->)]; [|reflexivity].
  exfalso. apply Hne. apply EQ. exact Hk.
Qed.
Lemma rbn5_reg_Uc {fq : YK11.FPState} : forall E ss H ms0 (r : bv 5) e v,
  st_ok SEGS E ss (restrict H ms0) -> sr_get (ss_regs ss) r = e -> U E e = v ->
  getr (ms_regs ms0) r = w64 v.
Proof.
intros E ss H ms0 r e v HS He Hv. pose proof (st_ok_restrict_reg SEGS H E ss ms0 r HS) as R.
rewrite He, denot_lit_U, Hv in R. exact R.
Qed.
Lemma rbn5_chunk8c {fq : YK11.FPState} : forall E ss H ms0 i r n b off e v,
  st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H (ms_mem ms0)) (b + off) 8 v.
Proof.
intros E ss H ms0 i r n b off e v HS Hi Hb Hn Hbr Hc He Hv.
pose proof (st_ok_region_nth E ss _ i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb, (rbn5_VB E n b Hn Hbr) in C.
exact (val_of_chunk_ok SEGS E _ b off 8 e v C He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma rbn5_mc_rom : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Proof.
intros a Ha. apply (pa_rom_ok 0x10368 32 a).
- cbn. repeat (first [left; reflexivity | right]).
- unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha. lia.
Qed.
Lemma rbn5M_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) m pc A F,
  getr regs 23 = w64 4 -> getr regs 9 = w64 A -> getr regs 19 = w64 F ->
  0 <= A -> A + 56 <= 2 ^ 64 -> 0 <= F -> F + 128 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) (A + 48) 8 (F + 128) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (rbn5M_ss pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros fq W regs m pc A F H23 H9 H19 HA0 HA HF0 HF Hv.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
unfold rbn5M_ss. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H23].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (rbn5_VB E 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ _ 48 8 (SOff 19 128) (F + 128));
    [cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Hv].
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn5H_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) m A,
  getr regs 12 = w64 4 -> getr regs 9 = w64 A -> 0 <= A -> A + 80 <= 2 ^ 64 ->
  (forall o, 24 <= o < 80 -> apresent (w_H W) m (A + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) rbn5H_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P5))) m (seg_rom SEGS))).
Proof.
intros fq W regs m A H12 H9 HA0 HA Hp.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl); exact H9).
unfold rbn5H_ss. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H12].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  rewrite (rbn5_VB E 9%nat A E9) by lia; (split; [lia|]); (split; [lia|]);
  (split; [intros o Ho; apply (apresent_writable SEGS); apply Hp; lia | apply Forall_nil]).
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (rbn5_VB E 9%nat A E9) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn5_cells_app : forall (mm : word -> option byte) l1 l2,
  rbn_cells mm l1 -> rbn_cells mm l2 -> rbn_cells mm (l1 ++ l2).
Proof.
intros mm l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; intros H1 H2; [exact H2|].
destruct H1 as [Ha Ht]. split; [exact Ha | exact (IH Ht H2)].
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn5_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn5_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8784 <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8784 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0 /\ ri_sp0 X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|exact Hal]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma rbn5_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 64 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a) /\
  (forall j, 0 <= j < 64 -> apresent (w_H W1) memc1 (rbn_SH X pos + j)) /\
  rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 /\ rbn_SH X pos mod 8 = 0 /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
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
Lemma rbn5_d64 : forall x, x mod 64 = 0 -> x / 8 = 8 * (x / 64) /\ x = 64 * (x / 64).
Proof.
intros x Hx. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
split; [|exact D]. rewrite D at 1. replace (64 * (x / 64)) with (8 * (x / 64) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma rbn5_oframe : forall X pos lyc1 Sc1 W1 m md Er sh cid p a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er sh -> In (cid, p) (frames (ri_Sc X)) ->
  (in_zr a (frame_rng (ri_lyc X) (cid, p)) \/
   in_zr a (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  0 <= a < alloc_ceiling /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512) /\ ~ (rbn_SH X pos <= a < rbn_SH X pos + 64).
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh cid p a HX HM Hcp Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md Er sh HX HM) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md Er sh HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & _ & _ & ESH & _ & _ & SHhi).
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid p HAR1 Hcp1) as (Hc64 & Hb64 & Hb64').
destruct (in_split _ _ Hcp) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA in Hd. rewrite FA in Hc4096, Hcceil, Hcapp, Hc64.
change (fs_frame_bytes 3) with 512 in Hd.
fold (rbn_F X pos) in Hd. rewrite ESH. clear ESH.
destruct (rbn5_d64 _ HF64) as (EF8 & EF). destruct (rbn5_d64 _ Hc64) as (Ec8 & Ec).
destruct (rbn5_d64 _ Hb64) as (Eb8 & Eb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hcapp. unfold kHighShadowEnd in SHhi.
unfold in_zr, frame_rng, shadow_addr in Ha. cbn [fst snd] in Ha. unfold SHADOW_OFF in *.
rewrite EF8, Ec8, Eb8 in *. destruct Ha as [Ha | Ha]; lia.
Qed.
Lemma rbn5_mid_kept : forall X pos lyc1 Sc1 W1 m md m2 md2 sh sh',
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8784 <= a < rbn_SP X - 104) ->
     ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  rbn_shadow_at W1 m2 (rbn_SH X pos) sh' ->
  rbn_mid B X pos lyc1 Sc1 W1 m2 md2 (fun _ => False) sh'.
Proof.
intros X pos lyc1 Sc1 W1 m md m2 md2 sh sh' HX HM HJ2 HEQ Hsh2.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ sh HX HM) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ sh HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & _ & _ & _ & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (HL : forall a, 0 <= a < alloc_ceiling -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a)
  by (intros a Ha Hf Hs; apply HEQ; lia).
assert (HH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - 8784 <= a < rbn_SP X) ->
  aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a)
  by (intros a Ha Hw; unfold kHighShadowEnd in SHhi; apply HEQ; lia).
assert (HI : forall a, in_img SEGS a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a).
{ intros a Hia. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow, SHlo.
  apply HL; [lia | intros Hf; exact (proj2 (HFpr a ltac:(lia)) Hia) | lia]. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  rewrite (HI a Hia). exact (Hro a Hro0 Ho He). }
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (HH a) by lia. exact (K1 a Ha Hn' He).
  - intros b mm j Hb Hj He.
    assert (Hb1 : In (b, mm) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb1) as (_ & Hb4 & Hbc & [Hh1 Hh2] & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA in Hd. change (fs_frame_bytes 3) with 512 in Hd. fold (rbn_F X pos) in Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold in_app, zone2, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh1, Hh2, HFapp.
    unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
    rewrite (HL (b + j)) by lia. exact (K2 b mm j Hb Hj He).
  - intros a Hia Ho He. rewrite (HI a Hia). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    destruct (rbn5_oframe X pos lyc1 Sc1 W1 m md _ sh cid p a HX HM Hcp Ha) as (O1 & O2 & O3).
    rewrite (HL a) by lia. exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn' Hp.
    apply (apresent_transfer SEGS (w_H W1) (w_H W1) m m2 a); [lia | | apply HH; lia | exact (K5 a Ha Hn' Hp)].
    intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
  - intros a Ha. apply Hpres2. lia. }
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
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length (rbm_NB X))) -> getr regs 30 = w64 (rbm_ovf 23 (rbm_NM X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 24; 27; 29; 30]%bv -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) ->
     ~ (rbn_SH X pos + 16 <= a < rbn_SH X pos + 19) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  aview SEGS (w_H W1) m2 (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) = Some 0 ->
  (forall j, 16 <= j < 19 -> aview SEGS (w_H W1) m2 (rbn_SH X pos + j) = Some 0) ->
  rbn_st6 B X pos regs2 lyc1 Sc1 W1 m2 md2.
Proof.
intros X pos regs lyc1 Sc1 W1 m md regs2 m2 md2 HX (HM & HC & HW4 & HA) ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27)
  R24 R30 R29 HG HJ2 KR HEQ Hz Hs.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & _ & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
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
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  (rbn_F X pos <= a < rbn_F X pos + 512 \/ rbn_SH X pos <= a < rbn_SH X pos + 64) ->
  awr_byte STK sp0 FP bl0 blc lyc1 ((3, pos) :: ri_own X) a.
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh STK sp0 FP bl0 blc a HX HM Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md Er sh HX HM 3 pos) as FA.
right; right; right. exists 3, pos. split; [left; reflexivity|]. unfold in_zr. cbn [fst snd].
rewrite FA. change (fs_frame_bytes 3) with 512. change (512 / 8) with 64.
unfold rbn_SH, rbn_F in Ha. destruct Ha; [left | right]; lia.
Qed.
Lemma rbn5_tail : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length (rbm_NB X))) -> getr regs 30 = w64 (rbm_ovf 23 (rbm_NM X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X) ->
  SRr SEGS W1 (rbn_cfg X 0x460 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HS5 HR R24 R30 R29 HG.
pose proof HS5 as (HM & _ & _ & _). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh0).
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
pose proof (rbn5T_entry (ri_fq X) W1 regs m (F + 64) n SH R27 R24 B22 R18 ltac:(lia) ltac:(lia) ltac:(lia)
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
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := ri_fq X) (L := disco_listing) (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + 0x460) with (BASE + (AF_reac_box_name + 0x460)) by lia.
assert (AWR : awr_ok E (ss_mem rbn5T_ss) (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X))
  (ablocks B lyc1 Sc1) lyc1 ((3, pos) :: ri_own X)).
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HX HM). destruct (HW a Ha); lia. }
paj_run_sh RUNP HS HJ; [exact AWR|].
cbn [ms_mem mkst] in HFr.
pose proof (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) _ HFr HW) as K1. clear HF HFr HG0.
psrr_branch_pi RUNP BR HS.
2: { exfalso. cbn [branch_taken sv_denot] in Hc. rewrite E24 in Hc.
     rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. apply negb_false_iff in Hc. apply bv_eqb_eq in Hc.
     apply (f_equal bv_unsigned) in Hc. rewrite !unsigned_lit_small in Hc by lia. lia. }
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_P6).
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HX HM).
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
assert (E18' : ew E 18 = Z_to_bv 64 SH) by exact E18.
pose proof (rbn5_chunk1 E _ (w_H W1) ms0 0 _ 32 (F + 64 + n) 0 0 HS eq_refl eq_refl E32 ltac:(lia)
  ltac:(cbn; tauto) ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0.
pose proof (rbn5_chunk1 E _ (w_H W1) ms0 2 _ 18 SH 16 0 HS eq_refl eq_refl E18 ltac:(lia)
  ltac:(cbn; tauto) ltac:(lia)) as Z16.
pose proof (rbn5_chunk1 E _ (w_H W1) ms0 2 _ 18 SH 17 0 HS eq_refl eq_refl E18 ltac:(lia)
  ltac:(cbn; tauto) ltac:(lia)) as Z17.
pose proof (rbn5_chunk1 E _ (w_H W1) ms0 2 _ 18 SH 18 0 HS eq_refl eq_refl E18 ltac:(lia)
  ltac:(cbn; tauto) ltac:(lia)) as Z18.
pmkst HS. apply SRr_ret.
exists pos, (ms_regs ms0), lyc1, Sc1, (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md))
          mat0 (with_vm_backing (m_vm_lazy md) mat md)).
split.
{ unfold rbn_cfg, cfg_at, w64. cbn [ri_fq].
  replace (BASE + AF_reac_box_name + RBN_P6) with (BASE + 15244) by (unfold AF_reac_box_name, RBN_P6; lia).
  reflexivity. }
apply (rbn5_tail_post X pos regs lyc1 Sc1 W1 m md _ _ _ HX HS5 HR R24 R30 R29 HG HJ KR).
- intros a Ha H1 H2. rewrite (K2 a Ha) by tauto. apply K1; [exact Ha | tauto].
- exact Z0.
- intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia; assumption.
Qed.
Lemma rbn5_lbuf_fr : forall X pos lyc1 Sc1 W1 m md Er sh j c,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  0 <= j -> 0 <= c -> j + c <= Z.of_nat (length sh) -> j + c <= 64 ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 m
    (rbn_F X pos + 8 * j) (8 * c).
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh j c HX HM Hj Hc Hl H64 Hz.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ sh HX HM 3 pos) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ sh HX HM) as (HF4096 & HFceil & HF64 & HFapp & HFpr & _).
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
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er (rbn_sh true true false false) ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + 32) 5.
Proof.
intros X pos lyc1 Sc1 W1 m md Er HX HM x Hx.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM) as (_ & _ & HF64 & _ & _ & _ & ESH & _).
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
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length pre)) -> getr regs 30 = w64 ov1 -> (ov1 = 0 \/ ov1 = 1) ->
  getr regs 13 = w64 (hd 0 (rbm_w4 X)) -> getr regs 21 = w64 (rbn_F X pos + 33) ->
  getr regs 10 = w64 (rbn_F X pos + 33) -> getr regs 12 = w64 23 -> getr regs 29 = w64 (rbn_F X pos + 128) ->
  (length pre <= 23)%nat ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) pre ->
  firstn 23 (pre ++ rbm_w4 X) = rbm_NB X ->
  (if 23 <? Z.of_nat (length pre) + 4 then 1 else ov1) = rbm_ovf 23 (rbm_NM X) ->
  SRr SEGS W1 (rbn_cfg X RBN_L2 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md pre ov1 HX HS5 HR R24 R30 Hov R13 R21 R10 R12 R29 Hpre HGp HNB HOV.
pose proof HS5 as (HM & HC & HW4 & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh0).
pose proof (rbn5_w4_len X HA) as Hw4. pose proof (rbn5_w4_digits X HA) as Hdg.
assert (Hne : rbm_w4 X <> []) by (intros E; rewrite E in Hw4; discriminate).
assert (Hsrc : rbn_lsrc W1 m (rbn_F X pos + 32) (rbm_w4 X ++ [0])).
{ split; [exact HW4|]. rewrite length_app, Hw4. cbn [length Nat.add]. change (Z.of_nat 5) with 5.
  split; [lia|]. split; [lia|]. split; [lia|]. exact (rbn5_w4_ra X pos lyc1 Sc1 W1 m md _ HX HM). }
assert (Hbuf : rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  m (rbn_F X pos + 64) 24).
{ exact (rbn5_lbuf_fr X pos lyc1 Sc1 W1 m md _ _ 8 3 HX HM ltac:(lia) ltac:(lia)
    ltac:(rewrite rbn5_sh_len; lia) ltac:(lia) ltac:(intros i Hi; apply rbn5_sh_nb; lia)). }
assert (Hsep : rbn_F X pos + 32 + Z.of_nat (length (rbm_w4 X)) + 1 <= rbn_F X pos + 64 \/
  rbn_F X pos + 64 + 24 <= rbn_F X pos + 32) by (rewrite Hw4; lia).
assert (R13' : getr regs 13 = w64 (hd 0 (rbm_w4 X))) by exact R13.
assert (R21' : getr regs 21 = w64 (rbn_F X pos + 32 + 1)) by (rewrite R21; f_equal; lia).
assert (R10' : getr regs 10 = w64 (rbn_F X pos + 32 + 1)) by (rewrite R10; f_equal; lia).
assert (POST : forall nF ovF wr W2 c2,
  rbn_lpost B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m (ri_k X) regs RBN_L2X [10; 11; 13; 14; 15; 16; 21; 24; 30]
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
- pose proof (L2F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs (rbn_F X pos + 32) (rbn_F X pos + 64)
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
- pose proof (L2O (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs (rbn_F X pos + 32) (rbn_F X pos + 64)
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
Lemma rbn5_dash_post : forall X pos regs lyc1 Sc1 W1 m md regs2 m2 md2 pre ov1,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs -> getr regs 29 = w64 (rbn_F X pos + 128) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 25; 27; 29]%bv -> getr regs2 r = getr regs r) ->
  getr regs2 24 = w64 (Z.of_nat (length pre)) -> getr regs2 30 = w64 ov1 -> (ov1 = 0 \/ ov1 = 1) ->
  getr regs2 13 = w64 (hd 0 (rbm_w4 X)) -> getr regs2 21 = w64 (rbn_F X pos + 33) ->
  getr regs2 10 = w64 (rbn_F X pos + 33) -> getr regs2 12 = w64 23 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 88) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  garr8 SEGS (mrestrict (w_H W1) m2) (rbn_F X pos + 64) pre -> (length pre <= 23)%nat ->
  firstn 23 (pre ++ rbm_w4 X) = rbm_NB X ->
  (if 23 <? Z.of_nat (length pre) + 4 then 1 else ov1) = rbm_ovf 23 (rbm_NM X) ->
  SRr SEGS W1 (rbn_cfg X RBN_L2 regs2 m2 md2) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md regs2 m2 md2 pre ov1 HX (HM & HC & HW4 & HA)
  ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27) R29 HJ2 KR O24 O30 Hov O13 O21 O10 O12 HEQ HGp Hpre HNB HOV.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
pose proof (rbn5_w4_len X HA) as Hw4.
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
assert (Hsh2 : rbn_shadow_at W1 m2 (rbn_SH X pos) (rbn_sh true true false false)).
{ intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (HEQ (rbn_SH X pos + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
apply (rbn5_l2 X pos regs2 lyc1 Sc1 W1 m2 md2 pre ov1 HX); try assumption.
- split; [exact (rbn5_mid_kept X pos lyc1 Sc1 W1 m md m2 md2 _ _ HX HM HJ2 ltac:(intros a Ha _ Hf _; apply HEQ; lia) Hsh2)|].
  split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HC].
    intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin). apply HEQ; lia. }
  split; [|exact HA].
  apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HW4|]. intros x Hx.
  rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply HEQ; lia.
- split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|].
  rewrite !KR by (cbn; tauto). auto.
- rewrite KR by (cbn; tauto). exact R29.
Qed.
Ltac rbn5D_inw E32 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros ? (r & Hr & Hw);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB _ 32%nat _ E32) in Hw by lia; lia.
Lemma rbn5_dash : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) -> getr regs 30 = w64 (rbm_ovf 23 (rbm_stem X)) ->
  getr regs 29 = w64 (rbn_F X pos + 128) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) ->
  rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X ->
  SRr SEGS W1 (rbn_cfg X 0x3c0 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HS5 HR R24 R30 R29 HG HN.
pose proof HS5 as (HM & _ & HW4 & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as Hw4. pose proof (rbn5_w4_digits X HA) as Hdg.
assert (Hn23 : (length (firstn 23 (rbm_stem X)) <= 23)%nat) by apply firstn_le_length.
set (n := Z.of_nat (length (firstn 23 (rbm_stem X)))) in *.
assert (Hn : 0 <= n <= 23) by (subst n; lia).
set (c := hd 0 (rbm_w4 X)).
assert (Hcr : 0 < c < 256).
{ subst c. destruct (rbm_w4 X) as [|c0 l]; [discriminate|]. cbn [hd]. exact (Forall_inv Hdg). }
assert (Vc : val_mem SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 32) 1 c).
{ destruct (HW4 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Hv _].
  rewrite Z.add_0_r in Hv. subst c. destruct (rbm_w4 X) as [|c0 l]; [discriminate|]. exact Hv. }
set (F := rbn_F X pos) in *. set (SH := rbn_SH X pos) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
pose proof (rbn5D_entry (ri_fq X) W1 regs m (F + 64) n (F + 32) c R27 R24 R25 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) (proj1 (HFpr (F + 64 + n) ltac:(lia))) Vc ltac:(lia)) as HS.
remember (Eimg (Ereg regs (map (Z_to_bv 64) [F + 64 + n; c]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [F + 64 + n; c])) E) by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 64 + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 (F + 32)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E30 : ew E 30 = Z_to_bv 64 (rbm_ovf 23 (rbm_stem X))) by (rewrite (EE 30%nat 30%bv eq_refl); exact R30).
clear HE.
assert (HW : forall a, in_wrange E (ss_mem rbn5D_ss) a -> a = F + 64 + n).
{ intros a (r & Hr & Hw). unfold rbn5D_ss in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite ?(rbn5_VB E 32%nat _ E32) in Hw by lia; lia. }
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := ri_fq X) (L := disco_listing) (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + 0x3c0) with (BASE + (AF_reac_box_name + 0x3c0)) by lia.
assert (AWR : awr_ok E (ss_mem rbn5D_ss) (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X))
  (ablocks B lyc1 Sc1) lyc1 ((3, pos) :: ri_own X)).
{ intros a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HX HM). rewrite (HW a Ha). lia. }
paj_run_sh RUNP HS HJ; [exact AWR|].
cbn [ms_mem mkst] in HFr.
pose proof (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) _ HFr HW) as K1. clear HF HFr HG0.
assert (WRA : forall rs, (forall a, in_wrange E rs a -> a = F + 64 + n) ->
  awr_ok E rs (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc1 Sc1) lyc1 ((3, pos) :: ri_own X)).
{ intros rs Hrs a Ha. apply (rbn5_own_frame X pos lyc1 Sc1 W1 m md _ _ _ _ _ _ _ a HX HM). rewrite (Hrs a Ha). lia. }
psrr_branch_pi RUNP BR HS.
- rewrite branch_ltu_U, U_lit, (U_atom E 24 n E24) in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Hn23' : n = 23) by lia.
  paj_run_sh RUNP HS HJ; [apply WRA; rbn5D_inw E32|].
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = F + 64 + n) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) _ HFr); rbn5D_inw E32).
  clear HF HFr HG0.
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_eq_U, U_zext, (U_atom E 33 c E33), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
    change (2 ^ Z.of_N 8) with 256 in Hc0. rewrite Z.mod_small in Hc0 by lia. lia. }
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_L2); [apply WRA; rbn5D_inw E32|].
  cbn [ms_mem mkst] in HFr.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = F + 64 + n) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) (ms_mem ms0) a)
    by (apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms0) (ms_mem ms1) _ HFr); rbn5D_inw E32).
  clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 25; 27; 29]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 24%bv (SOff 24 0) n HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom; [exact E24 | lia])) as O24.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 30%bv (SLit 1) 1 HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_lit; lia)) as O30.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 13%bv (SExt false 8 (SOff 33 0)) c HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite U_zext, (U_atom E 33 c E33) by lia; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia)) as O13.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 21%bv (SOff 25 1) (F + 33) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (U_atom_off E 25 (F + 32) 1 E25) by lia; lia)) as O21.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 10%bv (SOff 25 1) (F + 33) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (U_atom_off E 25 (F + 32) 1 E25) by lia; lia)) as O10.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 12%bv (SLit 23) 23 HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_lit; lia)) as O12.
  assert (HL : (23 <= length (rbm_stem X))%nat).
  { subst n. destruct (Nat.le_gt_cases 23 (length (rbm_stem X))) as [Hl | Hl]; [exact Hl|].
    rewrite firstn_all2 in Hn23' by lia. lia. }
  destruct (rbn5_dash_m2 X HN HL) as (M1 & M2).
  pmkst HS. change (Z_to_bv 64 (BASE + 15048)) with (w64 (BASE + 15048)).
  replace (BASE + 15048) with (BASE + AF_reac_box_name + RBN_L2) by (unfold AF_reac_box_name, RBN_L2; lia).
  apply (rbn5_dash_post X pos regs lyc1 Sc1 W1 m md (ms_regs ms1) (ms_mem ms1) _ (firstn 23 (rbm_stem X)) 1
    HX HS5 HR R29 HJ KR O24 O30 ltac:(right; reflexivity) O13 O21 O10 O12).
  + intros a Ha Hr. rewrite (K3 a Ha) by lia. rewrite (K2 a Ha) by lia. apply K1; lia.
  + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HG|]. intros x Hx. apply (mbyte_of_aview SEGS).
    fold n in Hx. rewrite (K3 x) by lia. rewrite (K2 x) by lia. apply K1; lia.
  + exact Hn23.
  + exact M1.
  + rewrite <- M2. destruct (23 <? _); reflexivity.
- rewrite branch_ltu_U, U_lit, (U_atom E 24 n E24) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_sh RUNP HS HJ; [apply WRA; rbn5D_inw E32|].
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = F + 64 + n) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) _ HFr); rbn5D_inw E32).
  clear HF HFr HG0.
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_eq_U, U_zext, (U_atom E 33 c E33), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
    change (2 ^ Z.of_N 8) with 256 in Hc0. rewrite Z.mod_small in Hc0 by lia. lia. }
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_L2); [apply WRA; rbn5D_inw E32|].
  cbn [ms_mem mkst] in HFr.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = F + 64 + n) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) (ms_mem ms0) a)
    by (apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms0) (ms_mem ms1) _ HFr); rbn5D_inw E32).
  clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 25; 27; 29]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  assert (Lp : Z.of_nat (length (firstn 23 (rbm_stem X) ++ [45])) = n + 1)
    by (rewrite length_app; cbn [length]; subst n; lia).
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 24%bv (SOff 24 1) (n + 1) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom_off; [exact E24 | lia | lia])) as O24. rewrite <- Lp in O24.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 30%bv (SOff 30 0) (rbm_ovf 23 (rbm_stem X)) HS
    ltac:(vm_compute; reflexivity) ltac:(apply U_atom; [exact E30 | unfold rbm_ovf; destruct (23 <? _); lia])) as O30.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 13%bv (SExt false 8 (SOff 33 0)) c HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite U_zext, (U_atom E 33 c E33) by lia; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia)) as O13.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 21%bv (SOff 25 1) (F + 33) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (U_atom_off E 25 (F + 32) 1 E25) by lia; lia)) as O21.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 10%bv (SOff 25 1) (F + 33) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (U_atom_off E 25 (F + 32) 1 E25) by lia; lia)) as O10.
  pose proof (rbn5_reg_U E _ (w_H W1) ms1 12%bv (SLit 23) 23 HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_lit; lia)) as O12.
  pose proof (rbn5_chunk1 E _ (w_H W1) ms1 0 _ 32 (F + 64 + n) 0 45 HS eq_refl eq_refl E32 ltac:(lia)
    ltac:(cbn; tauto) ltac:(lia)) as Z45. rewrite Z.add_0_r in Z45.
  assert (HL : (length (rbm_stem X) <= 22)%nat).
  { subst n. destruct (Nat.le_gt_cases (length (rbm_stem X)) 22) as [Hl | Hl]; [exact Hl|].
    rewrite firstn_length_le in Hc by lia. lia. }
  destruct (rbn5_dash_m1 X HN Hw4 HL) as (M1 & M2).
  pmkst HS. change (Z_to_bv 64 (BASE + 15048)) with (w64 (BASE + 15048)).
  replace (BASE + 15048) with (BASE + AF_reac_box_name + RBN_L2) by (unfold AF_reac_box_name, RBN_L2; lia).
  apply (rbn5_dash_post X pos regs lyc1 Sc1 W1 m md (ms_regs ms1) (ms_mem ms1) _ (firstn 23 (rbm_stem X) ++ [45])
    (rbm_ovf 23 (rbm_stem X)) HX HS5 HR R29 HJ KR O24 O30
    ltac:(left; unfold rbm_ovf; replace (23 <? Z.of_nat (length (rbm_stem X))) with false
      by (symmetry; apply Z.ltb_ge; lia); reflexivity) O13 O21 O10 O12).
  + intros a Ha Hr. rewrite (K3 a Ha) by lia. rewrite (K2 a Ha) by lia. apply K1; lia.
  + apply (garr8_app1 SEGS (mrestrict (w_H W1) m) (mrestrict (w_H W1) (ms_mem ms1)) (F + 64) _ 45 HG).
    * apply rbn5_vm1. exact Z45.
    * lia.
    * intros x Hx. apply (mbyte_of_aview SEGS). fold n in Hx.
      rewrite (K3 x) by lia. rewrite (K2 x) by lia. apply K1; lia.
  + rewrite length_app. cbn [length]. lia.
  + exact M1.
  + exact M2.
Qed.
Lemma rbn5_cells_in : forall (mm : word -> option byte) l a n v,
  In (a, n, v) l -> rbn_cells mm l -> val_mem SEGS mm a n v.
Proof.
intros mm l a n v. induction l as [|[[a' n'] v'] t IH]; cbn [In rbn_cells]; [intros []|].
intros [E | Hin] [H1 H2]; [injection E as <- <- <-; exact H1 | exact (IH Hin H2)].
Qed.
Lemma rbn5_S_below : forall X pos lyc1 Sc1 W1 m md m2 md2,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8784 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  rbn5_S X pos lyc1 Sc1 W1 m2 md2.
Proof.
intros X pos lyc1 Sc1 W1 m md m2 md2 HX (HM & HC & HW4 & HA) HJ2 HEQ.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
pose proof (rbn5_w4_len X HA) as Hw4.
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
split.
{ apply (rbn5_mid_kept X pos lyc1 Sc1 W1 m md m2 md2 _ _ HX HM HJ2); [intros a Ha Hw _ _; apply HEQ; lia|].
  intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (HEQ (rbn_SH X pos + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia. }
split.
{ apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HC].
  intros a n0 v k Hin Hk. pose proof (rbn5_locs6_rng X pos a n0 v Hin). apply HEQ; lia. }
split; [|exact HA].
apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HW4|]. intros x Hx.
rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply HEQ; lia.
Qed.
Ltac rbn5_inw0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros ? (r & Hr & Hw);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia.
Lemma rbn5_mid2 : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 21 = w64 (rbm_ovf 23 (rbm_stem X)) -> getr regs 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  getr regs 23 = w64 4 -> garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) ->
  (getr regs 10 = w64 0 -> rbm_NM X = rbm_stem X) ->
  (getr regs 10 <> w64 0 -> rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X) ->
  SRr SEGS W1 (rbn_cfg X 0x3b4 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HS5 HR R21 R24 R23 HG HE0 HE1.
pose proof HS5 as (HM & HC & _ & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ & _).
assert (V48 : val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 48) 8 (rbn_F X pos + 128)).
{ apply (rbn5_cells_in _ (rbn_locs6 X pos)); [|exact HC]. unfold rbn_locs6. apply in_or_app. right. cbn. tauto. }
assert (Hfl : (length (firstn 23 (rbm_stem X)) <= 23)%nat) by apply firstn_le_length.
pose proof (rbn5M_entry (ri_fq X) W1 regs m (AF_reac_box_name + 0x3b4) (rbn_A X) (rbn_F X pos) R23 B9 B19
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V48) as HS.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E10 : ew E 10 = getr regs 10) by exact (EE 10%nat 10%bv eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 (rbm_ovf 23 (rbm_stem X))) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact B19).
clear HE.
assert (Hov : 0 <= rbm_ovf 23 (rbm_stem X) <= 1) by (unfold rbm_ovf; destruct (23 <? _); lia).
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := ri_fq X) (L := disco_listing) (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + 0x3b4) with (BASE + (AF_reac_box_name + 0x3b4)) by lia.
paj_run_sh RUNP HS HJ; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
cbn [ms_mem mkst] in HFr.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m a)
  by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) (fun _ => False) HFr); [rbn5_inw0 | exact Ha | tauto]).
clear HF HFr HG0.
psrr_branch_pi RUNP BR HS.
- rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (V0 : getr regs 10 = w64 0).
  { rewrite U_SOff, E10, Z.add_0_r in Hc. pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. rewrite zcanon_id in Hc by (unfold M64; lia).
    apply bv_eq. rewrite Hc. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  pose proof (HE0 V0) as HNM.
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + 0x460); [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
        [rbn5_inw0 | exact Ha | tauto]).
  clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 30%bv (SOff 21 0) (rbm_ovf 23 (rbm_stem X)) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom; [exact E21 | lia])) as O30.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 29%bv (SOff 19 128) (rbn_F X pos + 128) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom_off; [exact E19 | lia | lia])) as O29.
  pmkst HS. change (Z_to_bv 64 (BASE + 15156)) with (w64 (BASE + 15156)).
  replace (BASE + 15156) with (BASE + AF_reac_box_name + 0x460) by (unfold AF_reac_box_name; lia).
  assert (HNB : rbm_NB X = firstn 23 (rbm_stem X)) by (unfold rbm_NB; rewrite HNM; reflexivity).
  apply (rbn5_tail X pos (ms_regs ms0) lyc1 Sc1 W1 (ms_mem ms0) _ HX).
  + apply (rbn5_S_below X pos lyc1 Sc1 W1 m md _ _ HX HS5 HJ). intros a Ha _. rewrite K2, K1 by lia. reflexivity.
  + split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|]. rewrite !KR by (cbn; tauto). auto.
  + rewrite KR by (cbn; tauto). rewrite HNB. exact R24.
  + rewrite HNM. exact O30.
  + exact O29.
  + rewrite HNB. apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HG|]. intros x Hx.
    apply (mbyte_of_aview SEGS). rewrite K2, K1 by lia. reflexivity.
- rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (V0 : getr regs 10 <> w64 0) by (intros V; apply Hc; rewrite U_SOff, E10, V; reflexivity).
  pose proof (HE1 V0) as HNM.
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + 0x3c0); [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
        [rbn5_inw0 | exact Ha | tauto]).
  clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 30%bv (SOff 21 0) (rbm_ovf 23 (rbm_stem X)) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom; [exact E21 | lia])) as O30.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 29%bv (SOff 19 128) (rbn_F X pos + 128) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom_off; [exact E19 | lia | lia])) as O29.
  pmkst HS. change (Z_to_bv 64 (BASE + 14996)) with (w64 (BASE + 14996)).
  replace (BASE + 14996) with (BASE + AF_reac_box_name + 0x3c0) by (unfold AF_reac_box_name; lia).
  apply (rbn5_dash X pos (ms_regs ms0) lyc1 Sc1 W1 (ms_mem ms0) _ HX).
  + apply (rbn5_S_below X pos lyc1 Sc1 W1 m md _ _ HX HS5 HJ). intros a Ha _. rewrite K2, K1 by lia. reflexivity.
  + split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|]. rewrite !KR by (cbn; tauto). auto.
  + rewrite KR by (cbn; tauto). exact R24.
  + exact O30.
  + exact O29.
  + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HG|]. intros x Hx.
    apply (mbyte_of_aview SEGS). rewrite K2, K1 by lia. reflexivity.
  + exact HNM.
Qed.
Ltac rbn5_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
    let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end;
  unfold acallee_saved; lia.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Lemma rbn5_aj_strlen : forall (fq : YK11.FPState) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk
  (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= kk -> kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 ->
  first_byte SEGS W memT x (kk + 1) 0 kk -> src_ok SEGS W regsT memT x (kk + 1) -> amem_range x (kk + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (kk + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (kk + 1) ->
  (forall a, x + kk < a < x + kk - (x + kk) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memT ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA DS___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := fq) regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
      aregs_preserved regsT regs2 /\ getr regs2 10 = w64 kk /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
         aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros fq W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk o raw
  HJ Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsrc Ham Hra Hhv Htl Hcv Hsp' Hal Hneg Hbud Hgp Htp Hra1 Hraw.
pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra1. exact Hraw. }
eapply SRr_mono.
{ exact (ASTRLEN fq lyc Sc W regsT memT mdc x kk HPRE Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsrc Ham Hra Hhv Htl Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hres | exact Hfr].
Qed.
Lemma rbn5_mid1 : forall X pos regs lyc1 Sc1 W1 m md P,
  rbn_cx B X -> rbn5_S X pos lyc1 Sc1 W1 m md -> rbn5_R X pos regs ->
  getr regs 21 = w64 (rbm_ovf 23 (rbm_stem X)) -> getr regs 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  getr regs 23 = w64 4 -> getr regs 20 = w64 P -> getr regs 10 = w64 (Z.of_nat (length (rbm_stem X))) ->
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) -> rbn_stp X pos W1 m P ->
  SRr SEGS W1 (rbn_cfg X 0x394 regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md P HX HS5 HR R21 R24 R23 R20 R10 HG HSTP.
pose proof HS5 as (HM & HC & HW4 & HA). pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R25 & R27).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ & _).
pose proof HSTP as ((Hfs & Hgs & HP0 & HP1 & HLl & Ham & HPra & HPhv & _) & Hdis).
pose proof (rbn5_w4_len X HA) as Hw4.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (V48 : val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 48) 8 (rbn_F X pos + 128)).
{ apply (rbn5_cells_in _ (rbn_locs6 X pos)); [|exact HC]. unfold rbn_locs6. apply in_or_app. right. cbn. tauto. }
assert (Hfl : (length (firstn 23 (rbm_stem X)) <= 23)%nat) by apply firstn_le_length.
pose proof (rbn5M_entry (ri_fq X) W1 regs m (AF_reac_box_name + 0x394) (rbn_A X) (rbn_F X pos) R23 B9 B19
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V48) as HS.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat (length (rbm_stem X)))) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E20 : ew E 20 = Z_to_bv 64 P) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (rbm_ovf 23 (rbm_stem X))) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact B19).
assert (E25 : ew E 25 = Z_to_bv 64 (rbn_F X pos + 32)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
clear HE.
assert (Hov : 0 <= rbm_ovf 23 (rbm_stem X) <= 1) by (unfold rbm_ovf; destruct (23 <? _); lia).
set (L := Z.of_nat (length (rbm_stem X))) in *.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := ri_fq X) (L := disco_listing) (PI := PI)) as BR.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + 0x394) with (BASE + (AF_reac_box_name + 0x394)) by lia.
paj_run_sh RUNP HS HJ; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
cbn [ms_mem mkst] in HFr.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m a)
  by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) m (ms_mem ms) (fun _ => False) HFr); [rbn5_inw0 | exact Ha | tauto]).
clear HF HFr HG0.
psrr_branch_pi RUNP BR HS.
- rewrite branch_ltu_U, U_lit, (U_atom E 10 L E10) in Hc by lia. apply Z.ltb_lt in Hc.
  assert (HNM : rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X)
    by (destruct (rbn5_NM_cases X) as [(Hk & _) | (_ & HN)]; [lia | exact HN]).
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + 0x3c0); [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  cbn [ms_mem mkst] in HFr.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
        [rbn5_inw0 | exact Ha | tauto]).
  clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 30%bv (SOff 21 0) (rbm_ovf 23 (rbm_stem X)) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom; [exact E21 | lia])) as O30.
  pose proof (rbn5_reg_U E _ (w_H W1) ms0 29%bv (SOff 19 128) (rbn_F X pos + 128) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom_off; [exact E19 | lia | lia])) as O29.
  pmkst HS. change (Z_to_bv 64 (BASE + 14996)) with (w64 (BASE + 14996)).
  replace (BASE + 14996) with (BASE + AF_reac_box_name + 0x3c0) by (unfold AF_reac_box_name; lia).
  apply (rbn5_dash X pos (ms_regs ms0) lyc1 Sc1 W1 (ms_mem ms0) _ HX).
  + apply (rbn5_S_below X pos lyc1 Sc1 W1 m md _ _ HX HS5 HJ). intros a Ha _. rewrite K2, K1 by lia. reflexivity.
  + split; [unfold rbn_rbase; rewrite !KR by (cbn; tauto); auto 10|]. rewrite !KR by (cbn; tauto). auto.
  + rewrite KR by (cbn; tauto). exact R24.
  + exact O30.
  + exact O29.
  + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HG|]. intros x Hx.
    apply (mbyte_of_aview SEGS). rewrite K2, K1 by lia. reflexivity.
  + exact HNM.
- rewrite branch_ltu_U, U_lit, (U_atom E 10 L E10) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) (ms_mem ms) a)
    by (intros a Ha; apply (rbn5_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
        [rbn5_inw0 | exact Ha | tauto]).
  clear HF HFr HG0.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m a)
    by (intros a Ha; rewrite K2, K1 by lia; reflexivity).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  pose proof (rbn5_reg_Uc E _ (w_H W1) ms0 10%bv (SAlu ALU_ADD (SOff 10 (-4)) (SOff 20 0)) (P + L - 4) HS
    ltac:(vm_compute; reflexivity)
    ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom_off E 10 L (-4) E10), (U_atom E 20 P E20) by lia;
          replace (P + L - 4) with (L + -4 + P) by lia; apply zcanon_id; unfold M64; lia)) as G10.
  pose proof (rbn5_reg_Uc E _ (w_H W1) ms0 11%bv (SOff 25 0) (rbn_F X pos + 32) HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_atom; [exact E25 | lia])) as G11.
  pose proof (rbn5_reg_Uc E _ (w_H W1) ms0 12%bv (SLit 4) 4 HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_lit; lia)) as G12.
  pose proof (rbn5_reg_Uc E _ (w_H W1) ms0 23%bv (SLit 4) 4 HS ltac:(vm_compute; reflexivity)
    ltac:(apply U_lit; lia)) as G23.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  pose proof (rbn5_reg_Uc E _ (w_H W1) ms0 1%bv (SOff 240 14984) (BASE + 14984) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite U_SOff; change 240%nat with A_TEXT; rewrite (HEI A_TEXT (conj (le_n A_TEXT) A_LIM_text));
          apply zcanon_id; unfold M64; lia)) as G1.
  assert (Gsp : spZ (ms_regs ms0) = rbn_A X)
    by (unfold spZ; rewrite KR by (cbn; tauto); rewrite B2; unfold w64; apply unsigned_lit_small; lia).
  assert (Hav : forall a, P <= a < P + L + 1 -> aview SEGS (w_H W1) m a <> None).
  { intros a Ha. replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia.
    rewrite (rbn5_garr8_aview _ _ _ _ _ Hgs) by (rewrite length_app; cbn [length]; lia). discriminate. }
  assert (Ho16 : (rbn_A X - ri_sp0 X) mod 16 = 0).
  { pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (ri_sp0 X) 16 ltac:(lia)) as DS.
    rewrite AR7, Z.add_0_r in DA. rewrite AR8, Z.add_0_r in DS.
    replace (rbn_A X - ri_sp0 X) with ((2 * (rbn_A X / 32) - ri_sp0 X / 16) * 16) by lia. apply Z_mod_mult. }
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (ABCMP (ri_fq X)) W1 (ms_regs ms0) (ms_mem ms0) (ri_STK X) (ri_sp0 X)
      (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 _ (ri_k X)
      (P + L - 4) (rbn_F X pos + 32) 4 (rbn_A X - ri_sp0 X) (w64 (BASE + 14984)) HJ G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Gsp. lia.
    - exact Ho16.
    - lia.
    - unfold ESTACK. lia.
    - rewrite KR by (cbn; tauto). exact B3.
    - rewrite KR by (cbn; tauto). exact B4.
    - exact G1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. rewrite Gsp. split; [rewrite KM by lia; apply Hav; lia|].
      pose proof (Hdis a ltac:(lia)) as [Hd _]. unfold ESTACK. lia.
    - intros a Ha. rewrite Gsp. split; [rewrite KM by lia; apply (aview_some_of_apresent SEGS); apply HFpr; lia|].
      unfold ESTACK. lia.
    - intros a Ha. pose proof (Hdis a ltac:(lia)) as [Hd _]. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - unfold amem_range in Ham |- *. lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    - apply (rbn5_ra_sub (aview SEGS (w_H W1) m) _ P (L + 1)); [exact KM | lia | lia | exact HPra | lia | lia].
    - intros _. apply (rbn5_hull_sub (aview SEGS (w_H W1) m) _ P (L + 1)); [exact KM | lia | lia | exact HPhv | lia | lia | lia].
    - apply (rbn5_ra_sub (aview SEGS (w_H W1) m) _ (rbn_F X pos + 32) 5); [exact KM | lia | lia | | lia | lia].
      exact (rbn5_w4_ra X pos lyc1 Sc1 W1 m md _ HX HM).
    - intros _. pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ _ HX HM 3 pos) as FA.
      eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc1 Sc1 W1 (ms_mem ms0) _ 3 pos); [exact (proj1 HJ) | |
        rewrite FA; unfold rbn_F; lia | rewrite FA; change (fs_frame_bytes 3) with 512; unfold rbn_F; lia | lia].
      pose proof HM as (_ & Hfrs1 & _). rewrite Hfrs1. left. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr2 & _).
  replace (BASE + 14984) with (BASE + AF_reac_box_name + 0x3b4) by (unfold AF_reac_box_name; lia).
  assert (HL4 : 4 <= Z.of_nat (length (rbm_stem X))) by (subst L; lia).
  assert (Hxb : forall i, 0 <= i < 4 -> aview SEGS (w_H W1) (ms_mem ms0) (P + L - 4 + i) =
    Some (nth (length (rbm_stem X) - 4 + Z.to_nat i) (rbm_stem X) 0)).
  { intros i Hi. rewrite KM by lia.
    replace (P + L - 4 + i) with (P + Z.of_nat (length (rbm_stem X) - 4 + Z.to_nat i)) by (subst L; lia).
    rewrite (rbn5_garr8_aview _ _ _ _ _ Hgs) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity. }
  assert (Hyb : forall i, 0 <= i < 4 -> aview SEGS (w_H W1) (ms_mem ms0) (rbn_F X pos + 32 + i) =
    Some (nth (Z.to_nat i) (rbm_w4 X) 0)).
  { intros i Hi. rewrite KM by lia.
    replace (rbn_F X pos + 32 + i) with (rbn_F X pos + 32 + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rbn5_garr8_aview _ _ _ _ _ HW4) by (rewrite length_app, Hw4; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity. }
  destruct (rbn5_bcmp_model X (aview SEGS (w_H W1) (ms_mem ms0)) (P + L - 4) (rbn_F X pos + 32) HL4 Hw4 Hxb Hyb)
    as (M0 & M1).
  apply (rbn5_mid2 X pos regs2 lyc1 Sc1 W1 mem2 md2 HX).
  + apply (rbn5_S_below X pos lyc1 Sc1 W1 m md mem2 md2 HX HS5 HJ2). intros a Ha Hn.
    rewrite (Hfr2 a Ha) by (unfold ESTACK; lia). apply KM. exact Ha.
  + split.
    * unfold rbn_rbase. rewrite !(rbn5_pres _ _ HP) by rbn5_cs.
      rewrite !KR by (cbn; tauto). auto 10.
    * rewrite !(rbn5_pres _ _ HP) by rbn5_cs. rewrite !KR by (cbn; tauto). auto.
  + rewrite (rbn5_pres _ _ HP) by rbn5_cs. rewrite KR by (cbn; tauto). exact R21.
  + rewrite (rbn5_pres _ _ HP) by rbn5_cs. rewrite KR by (cbn; tauto). exact R24.
  + rewrite (rbn5_pres _ _ HP) by rbn5_cs. exact G23.
  + apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact HG|]. intros x Hx.
    apply (mbyte_of_aview SEGS). rewrite (Hfr2 x) by (unfold ESTACK; lia). apply KM. lia.
  + intros V0. apply M0. apply Hcmp. rewrite <- Hv. exact V0.
  + intros V0. apply M1. intros Hall. apply V0. rewrite Hv. apply Hcmp. exact Hall.
Qed.
Theorem rbn_seg5 : rbn_seg5_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H5.
pose proof HX as (HJ0 & _ & Hcv & _ & _ & _ & _ & _ & Hal & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  H16 & Rt & _).
pose proof H5 as (HM & HRB & R18 & R26 & R20 & R23 & R25 & R27 & R24 & R30 & R12 & HC & HW4 & HG & HSTP & HA).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ & Hfrs1 & Hperm & Hro1 & HK & Hfr & Hfl & Hsh0).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HSTP as (Hstr0 & Hdis).
pose proof Hstr0 as (Hfs & Hgs & HP0 & HP1 & HLl & Ham & HPra & HPhv & Htl).
pose proof (rbn5_w4_len X HA) as Hw4.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hfl23 : (length (firstn 23 (rbm_stem X)) <= 23)%nat) by apply firstn_le_length.
assert (Hov : 0 <= rbm_ovf 23 (rbm_stem X) <= 1) by (unfold rbm_ovf; destruct (23 <? _); lia).
set (L := Z.of_nat (length (rbm_stem X))) in *.
assert (HLd : L = Z.of_nat (length (rbm_stem X))) by reflexivity.
assert (Hdis' : forall x, P <= x < P + L + 1 -> ~ (rbn_SP X - 8784 <= x < rbn_SP X))
  by (intros x Hx; rewrite <- WS; exact (proj1 (Hdis x Hx))).
assert (Hlo8 : (rbn_SP X - 8784) mod 8 = 0).
{ unfold rbn_SP. pose proof (Z.div_mod (spZ (ri_regs X)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
  replace (spZ (ri_regs X) - 8784) with ((2 * (spZ (ri_regs X) / 16) - 1098) * 8) by lia. apply Z_mod_mult. }
assert (Ho16 : (rbn_A X - ri_sp0 X) mod 16 = 0).
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (ri_sp0 X) 16 ltac:(lia)) as DS.
  rewrite AR7, Z.add_0_r in DA. rewrite AR8, Z.add_0_r in DS.
  replace (rbn_A X - ri_sp0 X) with ((2 * (rbn_A X / 32) - ri_sp0 X / 16) * 16) by lia. apply Z_mod_mult. }
pose proof (rbn5H_entry (ri_fq X) W1 regs1 memc1 (rbn_A X) R12 B9 ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; apply Hpres; lia)) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 []) E) by (subst E; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 (rbn_A X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact B9).
assert (E19 : ew E 19 = Z_to_bv 64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact B19).
assert (E20 : ew E 20 = Z_to_bv 64 P) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (ri_token X)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E26 : ew E 26 = Z_to_bv 64 (rbn_F X pos)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E30 : ew E 30 = Z_to_bv 64 (rbm_ovf 23 (rbm_stem X))) by (rewrite (EE 30%nat 30%bv eq_refl); exact R30).
clear HE.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_P5) with (BASE + (AF_reac_box_name + RBN_P5)) by lia.
paj_run_shc RUNP RUNC HS HJ.
{ unfold rbn5H_ss. cbn [ss_mem].
  do 3 (eapply (awr_ok_cons_stack_off E _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ lyc1 ((3, pos) :: ri_own X) 9%nat
    (rbn_A X - ri_sp0 X)); [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |]).
  apply awr_ok_nil. }
assert (K1s : forall a, 0 <= a < 2 ^ 64 ->
  ~ (rbn_A X + 24 <= a < rbn_A X + 32 \/ rbn_A X + 48 <= a < rbn_A X + 56 \/ rbn_A X + 72 <= a < rbn_A X + 80) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
{ apply (rbn5_kept_frame E _ (w_H W1) memc1 (ms_mem ms) _ HFr).
  intros a (r & Hr & Hw). unfold rbn5H_ss in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
  rewrite (rbn5_VB E 9%nat _ E9) in Hw by lia; lia. }
clear HF HFr HG0.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8784 <= a < rbn_SP X - 104) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hn; apply K1s; lia).
pose proof (rbn5_chunk8c E _ (w_H W1) ms 0 _ 9 (rbn_A X) 24 (SOff 23 0) (ri_token X) HS eq_refl eq_refl E9
  ltac:(lia) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) Rt) as C24.
pose proof (rbn5_chunk8c E _ (w_H W1) ms 1 _ 9 (rbn_A X) 48 (SOff 19 128) (rbn_F X pos + 128) HS eq_refl eq_refl E9
  ltac:(lia) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity)
  ltac:(lia)) as C48.
pose proof (rbn5_chunk8c E _ (w_H W1) ms 2 _ 9 (rbn_A X) 72 (SOff 26 0) (rbn_F X pos) HS eq_refl eq_refl E9
  ltac:(lia) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(lia)) as C72.
pose proof (regs_kept_of_st_ok SEGS _ _ _ _ _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pose proof (rbn5_reg_Uc E _ (w_H W1) ms 10%bv (SOff 20 0) P HS ltac:(vm_compute; reflexivity)
  ltac:(apply U_atom; [exact E20 | lia])) as G10.
pose proof (rbn5_reg_Uc E _ (w_H W1) ms 21%bv (SOff 30 0) (rbm_ovf 23 (rbm_stem X)) HS ltac:(vm_compute; reflexivity)
  ltac:(apply U_atom; [exact E30 | lia])) as G21.
pose proof (rbn5_reg_Uc E _ (w_H W1) ms 23%bv (SLit 4) 4 HS ltac:(vm_compute; reflexivity)
  ltac:(apply U_lit; lia)) as G23.
pose proof pa_B_ok as (HB0 & HB1 & _).
pose proof (rbn5_reg_Uc E _ (w_H W1) ms 1%bv (SOff 240 14952) (BASE + 14952) HS ltac:(vm_compute; reflexivity)
  ltac:(rewrite U_SOff; change 240%nat with A_TEXT; rewrite (HEI A_TEXT (conj (le_n A_TEXT) A_LIM_text));
        apply zcanon_id; unfold M64; lia)) as G1.
assert (Gsp : spZ (ms_regs ms) = rbn_A X)
  by (unfold spZ; rewrite KR by (cbn; tauto); rewrite B2; unfold w64; apply unsigned_lit_small; lia).
assert (Hlo : kHighShadowEnd <= rbn_SP X - 8784) by (rewrite C2; lia).
pose proof (rbn5_str_win W1 memc1 (ms_mem ms) P (rbm_stem X) (rbn_SP X - 8784) (rbn_SP X) Hstr0 Hlo8 Hlo Hdis'
  ltac:(intros x Hx Hn; apply K1; lia)) as (_ & Hgs1 & _ & _ & _ & _ & HPra1 & HPhv1 & Htl1).
assert (Hcv1 : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W1 (ms_mem ms)).
{ intros a Ha. pose proof (mc_consts_unowned a Ha) as (Ho & He).
  assert (Hia : in_img SEGS a)
    by (destruct (rbn5_mc_rom a Ha) as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha. rewrite K1 by lia.
  destruct HK as (_ & _ & K3 & _). rewrite (K3 a Hia Ho He). exact (Hcv a ltac:(unfold MC_CONSTS_LO, MC_CONSTS_HI; lia)). }
pmkst HS.
eapply SRr_bind.
{ eapply (rbn5_aj_strlen (ri_fq X) W1 (ms_regs ms) (ms_mem ms) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X)
    (ri_W0 X) (ri_mem0 X) (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 _ (ri_k X) P L (rbn_A X - ri_sp0 X)
    (w64 (BASE + 14952)) HJ G10).
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) (rbm_stem X) 0). split.
      * replace (P + i) with (P + Z.of_nat (Z.to_nat i)) by lia.
        rewrite (rbn5_garr8_aview _ _ _ _ _ Hgs1) by (rewrite length_app; cbn [length]; lia).
        rewrite app_nth1 by lia. reflexivity.
      * pose proof (proj1 (Forall_forall _ _) Hfs (nth (Z.to_nat i) (rbm_stem X) 0)
          (nth_In (rbm_stem X) 0 (n := Z.to_nat i) ltac:(lia))) as Hq.
        cbv beta in Hq. lia.
    + intros _. change (P + L) with (P + Z.of_nat (length (rbm_stem X))).
      rewrite (rbn5_garr8_aview _ _ _ _ _ Hgs1) by (rewrite length_app; cbn [length]; lia).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros a Ha. split.
    + replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia.
      rewrite (rbn5_garr8_aview _ _ _ _ _ Hgs1) by (rewrite length_app; cbn [length]; lia). discriminate.
    + rewrite Gsp. pose proof (Hdis' a ltac:(lia)). lia.
  - exact Ham.
  - exact HPra1.
  - exact HPhv1.
  - exact Htl1.
  - exact Hcv1.
  - rewrite Gsp. lia.
  - exact Ho16.
  - lia.
  - lia.
  - rewrite KR by (cbn; tauto). exact B3.
  - rewrite KR by (cbn; tauto). exact B4.
  - exact G1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & H10' & Hfr2).
replace (BASE + 14952) with (BASE + AF_reac_box_name + 0x394) by (unfold AF_reac_box_name; lia).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8784 <= a < rbn_SP X - 104) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hn; rewrite (Hfr2 a Ha) by lia; apply K1; lia).
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
apply (rbn5_mid1 X pos regs2 lyc1 Sc1 W1 mem2 md2 P HX).
- split.
  + apply (rbn5_mid_kept X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 _ _ HX HM HJ2); [intros a Ha Hw _ _; apply K2; lia|].
    intros j Hj. rewrite rbn5_sh_len in Hj. rewrite (K2 (rbn_SH X pos + j)) by lia. apply Hsh0. rewrite rbn5_sh_len. lia.
  + split.
    * unfold rbn_locs6. apply rbn5_cells_app.
      -- apply (rbn5_cells_kept (w_H W1) (w_H W1) memc1 mem2); [|exact HC]. intros a n0 v k Hin Hk.
         rewrite (Hfr2 (a + k)).
         ++ apply K1s.
            ** pose proof (rbn5_locs4_rng X pos a n0 v Hin). lia.
            ** unfold rbn_locs4 in Hin. cbn [In] in Hin.
               repeat destruct Hin as [Hin | Hin]; try (injection Hin as <- <- <-); try destruct Hin; lia.
         ++ pose proof (rbn5_locs4_rng X pos a n0 v Hin). lia.
         ++ pose proof (rbn5_locs4_rng X pos a n0 v Hin). lia.
      -- cbn [rbn_cells]. split; [|split; [|split; [|exact I]]].
         ++ apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [|exact C24]. intros k Hk. apply Hfr2; lia.
         ++ apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [|exact C48]. intros k Hk. apply Hfr2; lia.
         ++ apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [|exact C72]. intros k Hk. apply Hfr2; lia.
    * split; [|exact HA].
      apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HW4|]. intros x Hx.
      rewrite length_app, Hw4 in Hx. cbn [length] in Hx. apply (mbyte_of_aview SEGS). apply K2; lia.
- split.
  + unfold rbn_rbase. rewrite !(rbn5_pres _ _ HP) by rbn5_cs. rewrite !KR by (cbn; tauto). auto 10.
  + rewrite !(rbn5_pres _ _ HP) by rbn5_cs. rewrite !KR by (cbn; tauto). auto.
- rewrite (rbn5_pres _ _ HP) by rbn5_cs. exact G21.
- rewrite (rbn5_pres _ _ HP) by rbn5_cs. rewrite KR by (cbn; tauto). exact R24.
- rewrite (rbn5_pres _ _ HP) by rbn5_cs. exact G23.
- rewrite (rbn5_pres _ _ HP) by rbn5_cs. rewrite KR by (cbn; tauto). exact R20.
- exact H10'.
- apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HG|]. intros x Hx.
  apply (mbyte_of_aview SEGS). apply K2; lia.
- split; [|exact Hdis].
  apply (rbn5_str_win W1 memc1 mem2 P _ (rbn_SP X - 8784) (rbn_SP X) Hstr0 Hlo8 Hlo Hdis').
  intros x Hx Hn. apply K2; lia.
Qed.
End h.
End f.
End d.
