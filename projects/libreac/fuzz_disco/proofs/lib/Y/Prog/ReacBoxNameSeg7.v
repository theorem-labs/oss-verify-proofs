(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 577 of its 1056 lines of code are new or changed and 612 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC8g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma r7_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma r7_sh_tf : forall j, (j < 24 \/ 30 <= j)%nat ->
  nth j (rbn_sh true true true false) 0 = nth j (rbn_sh true true true true) 0.
Proof.
intros j Hj.
assert (A : forallb (fun j => orb (andb (24 <=? j)%nat (j <? 30)%nat)
  (Z.eqb (nth j (rbn_sh true true true false) 0) (nth j (rbn_sh true true true true) 0))) (seq 0 64) = true)
  by (vm_compute; reflexivity).
destruct (Nat.lt_ge_cases j 64) as [H64 | H64].
- rewrite forallb_forall in A. specialize (A j ltac:(apply in_seq; lia)).
  apply orb_true_iff in A. destruct A as [A | A].
  + apply andb_true_iff in A. destruct A as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. lia.
  + apply Z.eqb_eq. exact A.
- rewrite !nth_overflow by (rewrite r7_sh_len; lia). reflexivity.
Qed.
Lemma r7_sh_t24 : forall j, (24 <= j < 30)%nat -> nth j (rbn_sh true true true true) 0 = 0.
Proof. intros j Hj. do 30 (destruct j as [|j]; [try reflexivity; lia|]). lia. Qed.
Lemma r7_sh_nb : forall j, (8 <= j < 11)%nat -> nth j (rbn_sh true true true true) 0 = 0.
Proof. intros j Hj. do 11 (destruct j as [|j]; [try reflexivity; lia|]). lia. Qed.
Lemma r7_sh_tb : forall j, (16 <= j < 19)%nat -> nth j (rbn_sh true true true false) 0 = 0.
Proof. intros j Hj. do 19 (destruct j as [|j]; [try reflexivity; lia|]). lia. Qed.
Lemma r7_firstn_Forall : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (firstn n l).
Proof.
intros P n l H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hx.
Qed.
Lemma r7_w4_chars : forall i o, bn_ok i = true -> bn_ok o = true -> Forall (fun c => 0 < c < 256) (bn_w4 i o).
Proof.
intros i o Hi Ho. apply bn_ok_in in Hi. apply bn_ok_in in Ho.
assert (A : forallb (fun i => forallb (fun o => forallb (fun c => (0 <? c) && (c <? 256)) (bn_w4 i o)) bn_oks)
  bn_oks = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A i Hi). rewrite forallb_forall in A. specialize (A o Ho).
rewrite forallb_forall in A. apply Forall_forall. intros c Hc. specialize (A c Hc).
apply andb_true_iff in A. destruct A as [A1 A2]. apply Z.ltb_lt in A1. apply Z.ltb_lt in A2. lia.
Qed.
Lemma r7_STEM_chars : forall f, Forall (fun c => 0 < c < 256) (bn_STEM f).
Proof.
intros f. unfold bn_STEM.
destruct (f =? 1); [|destruct (f =? 2); [|destruct (f =? 3)]]; repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.
Lemma r7_NM_chars : forall f sd i o, Forall (fun c => 0 < c < 256) sd -> bn_ok i = true -> bn_ok o = true ->
  Forall (fun c => 0 < c < 256) (bn_NM f sd i o).
Proof.
intros f sd i o Hs Hi Ho.
assert (Hst : Forall (fun c => 0 < c < 256) (bn_stem f sd))
  by (unfold bn_stem; destruct sd; [apply r7_STEM_chars | exact Hs]).
unfold bn_NM. cbv zeta.
match goal with |- context [if ?b then _ else _] => destruct b end; [exact Hst|].
apply Forall_app. split; [exact Hst|]. apply Forall_cons; [lia|]. apply r7_w4_chars; assumption.
Qed.
Lemma r7_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Lemma r7_keep : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
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
Lemma r7_out : forall (regs2 : bvmap 5 word) (r : bv 5) v,
  getr regs2 (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs2 r = v.
Proof. intros regs2 r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac r7cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Lemma r7_not : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma r7_vm1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma r7_av1 : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv.
rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map]. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma r7_kept : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma r7_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma r7_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma r7_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m l1 -> rbn_cells m l2 -> rbn_cells m (l1 ++ l2).
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [rbn_cells app]; intros H1 H2; [exact H2|].
destruct H1 as [H1a H1b]. split; [exact H1a | exact (IH H1b H2)].
Qed.
Lemma r7_vm04 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end
  | vm_compute; discriminate]))). lia.
Qed.
Lemma r7_cells_in : forall (m : word -> option byte) l a n v,
  rbn_cells m l -> In (a, n, v) l -> val_mem SEGS m a n v.
Proof.
intros m l a n v. induction l as [|[[a' n'] v'] t IH]; cbn [rbn_cells In]; intros HC Hin; [destruct Hin|].
destruct HC as [H1 H2]. destruct Hin as [Heq | Hin].
- injection Heq as E1 E2 E3. subst. exact H1.
- exact (IH H2 Hin).
Qed.
Lemma r7_cells_app4 : forall (m : word -> option byte) l1 l2 l3 l4 l5,
  rbn_cells m (l1 ++ l2 ++ l3 ++ l4) -> rbn_cells m l5 -> rbn_cells m (l1 ++ l2 ++ l3 ++ l4 ++ l5).
Proof.
intros m l1 l2 l3 l4 l5 H1 H2.
rewrite (app_assoc l3 l4 l5), (app_assoc l2 (l3 ++ l4) l5), (app_assoc l1 (l2 ++ l3 ++ l4) l5).
apply r7_cells_app; assumption.
Qed.
Lemma r7_c7_rng : forall X pos n1 o1 n2 o2 a n v,
  In (a, n, v) (rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos n1 o1 ++ rbn_rt X pos n2 o2) ->
  (rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64) \/ (rbn_A X + 120 <= a /\ a + Z.of_nat n <= rbn_A X + 212).
Proof.
intros X pos n1 o1 n2 o2 a n v H. unfold rbn_argc, rbn_rw, rbn_rn, rbn_rt in H. cbn [In app] in H.
repeat (destruct H as [H | H]; [injection H as E1 E2 E3; subst; lia|]). destruct H.
Qed.
Lemma r7_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma r7_NB_ne : forall X, rbm_NB X <> [].
Proof.
intros X. assert (H : rbm_NM X <> []).
{ unfold rbm_NM, bn_NM. cbv zeta. pose proof (r7_stem_ne X) as Hne. unfold rbm_stem in Hne.
  match goal with |- (if ?b then _ else _) <> [] => destruct b end; [exact Hne|].
  destruct (bn_stem (ri_f X) (ri_sd X)); discriminate. }
unfold rbm_NB. destruct (rbm_NM X) as [|c l]; [exfalso; exact (H eq_refl)|]. cbn [firstn]. discriminate.
Qed.
Definition r7_tx (X : rbn_in) (pos : Z) : Z := rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X)).
Definition r7_ws (X : rbn_in) (pos n a : Z) : Prop :=
  (rbn_A X - TSB_CH_STK <= a < rbn_A X) \/ (rbn_A X + 88 <= a < rbn_A X + 120) \/ a = r7_tx X pos \/
  (rbn_F X pos + 192 <= a < rbn_F X pos + 192 + n) \/ (rbn_SH X pos + 24 <= a < rbn_SH X pos + 30).
Definition r7_mem (X : rbn_in) (pos : Z) (W1 : world SEGS) (memc1 m : word -> option byte) (n : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ r7_ws X pos n a -> aview SEGS (w_H W1) m a = aview SEGS (w_H W1) memc1 a) /\
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 88) 8 (rbn_F X pos + 192) /\
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 96) 8 48 /\
  aview SEGS (w_H W1) m (r7_tx X pos) = Some 0 /\
  (forall j, 24 <= j < 30 -> aview SEGS (w_H W1) m (rbn_SH X pos + j) = Some 0).
Lemma r7_mem_eq : forall X pos W1 memc1 m m' n,
  r7_mem X pos W1 memc1 m n ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
  0 <= rbn_A X + 88 -> rbn_A X + 104 <= 2 ^ 64 -> 0 <= r7_tx X pos < 2 ^ 64 ->
  0 <= rbn_SH X pos + 24 -> rbn_SH X pos + 30 <= 2 ^ 64 ->
  r7_mem X pos W1 memc1 m' n.
Proof.
intros X pos W1 memc1 m m' n (HE & V88 & V96 & VTX & VSH) HQ H1 H2 H3 H4 H5.
split; [|split; [|split; [|split]]].
- intros a Ha Hn. rewrite (HQ a Ha). exact (HE a Ha Hn).
- apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m'); [|exact V88]. intros k Hk. apply HQ. lia.
- apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m'); [|exact V96]. intros k Hk. apply HQ. lia.
- rewrite (HQ _ H3). exact VTX.
- intros j Hj. rewrite (HQ (rbn_SH X pos + j)) by lia. exact (VSH j Hj).
Qed.
Definition r7_rr1 : smem :=
  [ YP09.mkRegion (Some 33%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 18%nat) 24 30 24 30 [];
    YP09.mkRegion (Some 9%nat) 88 144 88 104 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))] ].
Definition r7_ff1 : facts := mkFacts [(32%nat, mkAF 0 23 0); (34%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
  [(SAlu ALU_XOR (SOff 25 0) (SLit (-1)), SOff 34 0); (SAlu ALU_ADD (SOff 25 0) (SOff 32 0), SOff 33 0)].
Definition r7_ss1 : sstate := mkSS (AF_both3_reac_box_name + RBN_P7) sr_atoms r7_rr1 None r7_ff1.
Definition r7_E1 (regs : bvmap 5 word) (tl x nx : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 tl; Z_to_bv 64 x; Z_to_bv 64 nx]).
Lemma r7_entry1 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  (F tl A : Z),
  getr regs 25 = w64 (F + 128) -> getr regs 18 = w64 (SHADOW_OFF + F / 8) -> getr regs 9 = w64 A ->
  F mod 8 = 0 -> 4096 <= F -> F + 512 <= 2 ^ 47 -> 0 <= tl <= 23 -> 0 <= A -> A + 144 <= 2 ^ 47 ->
  (F + 512 <= SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 64 <= F) -> F + 512 <= A -> SHADOW_OFF + F / 8 + 64 <= A ->
  apresent (w_H W) memc (F + 128 + tl) ->
  (forall j, 24 <= j < 30 -> apresent (w_H W) memc (SHADOW_OFF + F / 8 + j)) ->
  (forall o, 88 <= o < 104 -> apresent (w_H W) memc (A + o)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 tl ->
  st_ok_pi SEGS VAL (r7_E1 regs tl (F + 128 + tl) (2 ^ 64 - 1 - (F + 128))) r7_ss1
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_P7))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc F tl A R25 R18 R9 HF8 HF4 HF47 Htl HA0 HA1 HFS HFA HSA Px Psh PA V136.
rewrite restrict_mkst_fx.
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
remember (F + 128 + tl) as x eqn:Hx.
remember (2 ^ 64 - 1 - (F + 128)) as nx eqn:Hnx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (r7_E1 regs tl x nx) n = getr regs r)
  by (intros n r Hn; unfold r7_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (r7_E1 regs tl x nx) 32 = Z_to_bv 64 tl)
  by (unfold r7_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (r7_E1 regs tl x nx) 33 = Z_to_bv 64 x)
  by (unfold r7_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (r7_E1 regs tl x nx) 34 = Z_to_bv 64 nx)
  by (unfold r7_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E25 : ew (r7_E1 regs tl x nx) 25 = Z_to_bv 64 (F + 128)) by (rewrite (EL 25%nat 25%bv eq_refl); exact R25).
assert (E18 : ew (r7_E1 regs tl x nx) 18 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (E9 : ew (r7_E1 regs tl x nx) 9 = Z_to_bv 64 A) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (VB : forall n v, ew (r7_E1 regs tl x nx) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (r7_E1 regs tl x nx) (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold r7_ss1. apply pa_entry_st_ok_full.
- unfold r7_E1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r7_rr1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 33%nat x E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (x + o) with x by lia. exact Px.
  + rewrite (VB 18%nat _ E18) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Psh. lia.
  + rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply PA. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ A 136 8 (SOff 32 0) tl);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 8) with 8%nat. exact V136.
- apply pairwise_disjoint_of_extents. unfold r7_rr1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 33%nat x E33), (VB 18%nat _ E18), (VB 9%nat A E9) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold r7_ff1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [split; [|split; [|exact I]]|split; [exact I|split; [|split; [|exact I]]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E34, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + cbn [sv_denot]. rewrite E25, E34, !unsigned_lit_small by lia. rewrite !Z.add_0_r. rewrite r7_not by lia.
    subst nx. reflexivity.
  + apply U_inj. rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite E25, E32, E33, !unsigned_lit_small by lia.
    rewrite !Z.add_0_r. rewrite !(zcanon_id (F + 128)), (zcanon_id tl) by (unfold M64; lia). subst x. reflexivity.
Qed.
Definition r7_rr2 : smem := [ YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition r7_ff2 : facts := mkFacts [(32%nat, mkAF 1 255 0)] [] [].
Definition r7_ss2 : sstate := mkSS (AF_both3_reac_box_name + 0x510) sr_atoms r7_rr2 None r7_ff2.
Definition r7_E2 (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Lemma r7_entry2 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  (P c : Z),
  getr regs 27 = w64 P -> 0 <= P -> P + 1 <= 2 ^ 64 -> 1 <= c <= 255 ->
  val_mem SEGS (mrestrict (w_H W) memc) P 1 c ->
  st_ok_pi SEGS VAL (r7_E2 regs c) r7_ss2
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + 0x510))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc P c R27 HP0 HP1 Hc Vc.
rewrite restrict_mkst_fx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (r7_E2 regs c) n = getr regs r)
  by (intros n r Hn; unfold r7_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (r7_E2 regs c) 32 = Z_to_bv 64 c)
  by (unfold r7_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E27 : ew (r7_E2 regs c) 27 = Z_to_bv 64 P) by (rewrite (EL 27%nat 27%bv eq_refl); exact R27).
assert (VB : forall n v, ew (r7_E2 regs c) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (r7_E2 regs c) (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold r7_ss2. apply pa_entry_st_ok_full.
- unfold r7_E2. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r7_rr2. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 27%nat P E27) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ P 0 1 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. exact Vc.
- cbn [pairwise_disjoint all_disjoint r7_rr2]. split; exact I.
- unfold r7_ff2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis L4F : rbn_L4_fits B.
Lemma r7_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma r7_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0 /\ ri_sp0 X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (H16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact H16].
rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma r7_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh -> AR SEGS B lyc1 Sc1 W1 m md ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) m a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) m (rbn_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md HX HM HAR.
pose proof (r7_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (_ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR Hin3) as (Hal & Happ & Hpr & Hspr).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|]. split.
- intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha.
- intros i Hi. exact (proj1 (Hspr i ltac:(change (512 / 8) with 64; lia))).
Qed.
Lemma r7_jpres : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.
Lemma r7_stk_sh : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k a n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  sp0 - STK + 64 <= a -> a + n + 64 <= sp0 -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) a n).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k a n HJ Ha Han Hn.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (am_layout B lyc Sc _ (proj1 HAR)) as HLY.
pose proof (lo_top lyc HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS lyc Sc W m md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz. rewrite Elo, Ehi in *.
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
    by (unfold shadow_of_addr; lia).
  apply Hz. clear - Hy Lplo Lphi Hslo Hshi Ha Han Hn. lia.
- intros Hn0 s Hs.
  replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
  rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
  clear - Hs Hn0 Lplo Lphi Hslo Hshi Ha Han Hn. unfold SHADOW_OFF in *. lia.
Qed.
Lemma r7_mid : forall X pos lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 mem2 md2 (P : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc3 Sc3 W3 mem2 md2 (ri_k X) ->
  frames Sc3 = frames Sc1 -> ablocks B lyc3 Sc3 = ablocks B lyc1 Sc1 ->
  (forall a, P a -> (rbn_A X - TSB_CH_STK <= a < rbn_A X + 152) \/ (rbn_F X pos <= a < rbn_F X pos + 504) \/
     (rbn_SH X pos + 24 <= a < rbn_SH X pos + 30)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall j, 24 <= j < 30 -> aview SEGS (w_H W3) mem2 (rbn_SH X pos + j) = Some 0) ->
  rbn_mid B X pos lyc3 Sc3 W3 mem2 md2 (fun _ => False) (rbn_sh true true true true).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 mem2 md2 P HX HM HJ2 Hfr3 Hbl3 HP HEQ HZ.
pose proof (r7_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as FA.
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (r7_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HX HM HAR1) as (HF4096 & HFceil & HFal & HFapp & HFpr & _).
destruct (r7_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Ht : TSB_CH_STK = 4112) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof (r7_sh_band (rbn_F X pos) 512 0 HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as SB0.
pose proof (r7_sh_band (rbn_F X pos) 512 63 HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as SB63.
change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in SB0, SB63.
assert (HSHc : rbn_SH X pos + 64 <= alloc_ceiling).
{ unfold rbn_SH, shadow_addr, SHADOW_OFF.
  assert (rbn_F X pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia). lia. }
assert (HSHl : SHADOW_OFF + 512 <= rbn_SH X pos).
{ unfold rbn_SH, shadow_addr. assert (512 <= rbn_F X pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (HN : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X + 152) ->
  ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ (rbn_SH X pos + 24 <= a < rbn_SH X pos + 30) ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2 H3. apply HEQ; [exact Ha|]. intros Hp. destruct (HP a Hp) as [H | [H | H]]; contradiction. }
clear HEQ HP.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr3; exact Hfrs|]. split; [rewrite Hbl3; exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (HN a) by (unfold SHADOW_OFF in *; first [lia | intros Hf; exact (proj2 (HFpr a ltac:(lia)) Hia)]).
  exact (Hro a Hro0 Ho He). }
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (HN a) by (unfold rbn_SP in *; lia). exact (K1 a Ha Hn' He).
  - intros b m j Hb Hj He.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & Hbapp & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold in_app in Hbapp. unfold kLowShadowBeg, kHighMemBeg in *.
    rewrite (HN (b + j)) by lia. exact (K2 b m j Hb Hj He).
  - intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (HN a) by (unfold SHADOW_OFF in *; first [lia | intros Hf; exact (proj2 (HFpr a ltac:(lia)) Hia)]).
    exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
    rewrite FA in Hc4096, Hcceil, Hcapp.
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct (in_split _ _ Hcp) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, Hfb3, FA in Hd.
    destruct Ha as [Ha | Ha].
    + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
      unfold in_app in Hcapp. unfold kLowShadowBeg, kHighMemBeg in *.
      rewrite (HN a) by lia. exact (K4 cid p a Hcp (or_introl Ha) He).
    + unfold in_zr in Ha. cbn [fst snd] in Ha.
      pose proof (r7_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      pose proof (shadow_range_end (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid) Hcnn) as Se1.
      assert (S1 : frame_addr (ri_lyc X) cid p + fs_frame_bytes cid <= rbn_F X pos -> a < rbn_SH X pos).
      { intros Hd1. pose proof (shadow_mono _ _ Hd1) as Sm.
        change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in Sm. lia. }
      assert (S2 : rbn_F X pos + 512 <= frame_addr (ri_lyc X) cid p -> rbn_SH X pos + 64 <= a).
      { intros Hd2. pose proof (shadow_mono _ _ Hd2) as Sm.
        assert (shadow_addr (rbn_F X pos + 512) = rbn_SH X pos + 64).
        { unfold rbn_SH, shadow_addr. rewrite (Z.div_mod (rbn_F X pos) 8) at 1 by lia. rewrite HF8, Z.add_0_r.
          replace (8 * (rbn_F X pos / 8) + 512) with ((rbn_F X pos / 8 + 64) * 8) by lia. rewrite Z.div_mul by lia. lia. }
        lia. }
      assert (Hdis : a < rbn_SH X pos \/ rbn_SH X pos + 64 <= a).
      { destruct Hd as [Hd | Hd]; first [left; exact (S1 Hd) | right; exact (S2 Hd)]. }
      assert (Hac : a < alloc_ceiling).
      { pose proof (shadow_mono _ _ Hcceil) as Sm. unfold shadow_addr, SHADOW_OFF in Sm.
        assert (alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia). lia. }
      rewrite (HN a) by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ a ltac:(lia)); lia]).
      exact (K4 cid p a Hcp (or_intror Ha) He).
  - intros a Ha Hn' Hp.
    apply (apresent_transfer SEGS (w_H W1) (w_H W3) memc1 mem2 a); [lia | | apply HN; unfold rbn_SP in *; lia | exact (K5 a Ha Hn' Hp)].
    intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W3) memc1 mem2); [|exact (Hfr j r Hj)].
  intros k Hk. apply HN; unfold rbn_SP in *; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W3) memc1 mem2); [|exact Hfl].
  intros k Hk. apply HN; [lia | lia | lia |]. intros Hs. destruct (Happ (rbn_F X pos + 504 + k) ltac:(lia)); unfold kLowShadowBeg, kHighMemBeg in *; lia. }
unfold rbn_shadow_at. intros j Hj. rewrite r7_sh_len in Hj.
destruct (Z_lt_le_dec j 24) as [Hj1 | Hj1]; [|destruct (Z_lt_le_dec j 30) as [Hj2 | Hj2]].
- rewrite (HN (rbn_SH X pos + j)) by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ (rbn_SH X pos + j) ltac:(lia)); lia]).
  rewrite (Hsh0 j) by (rewrite r7_sh_len; lia). rewrite r7_sh_tf by lia. reflexivity.
- rewrite (HZ j) by lia. rewrite r7_sh_t24 by lia. reflexivity.
- rewrite (HN (rbn_SH X pos + j)) by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ (rbn_SH X pos + j) ltac:(lia)); lia]).
  rewrite (Hsh0 j) by (rewrite r7_sh_len; lia). rewrite r7_sh_tf by lia. reflexivity.
Qed.
Lemma r7_NB_chars : forall X, rbn_cx B X -> rbm_args X -> Forall (fun c => 0 < c < 256) (rbm_NB X).
Proof.
intros X HX HA.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs).
destruct (Hargs HA) as [Hsaid _].
assert (Hsd : Forall (fun c => 0 < c < 256) (ri_sd X)).
{ destruct Hsaid as [(_ & ->) | (_ & (Hf & _) & _)]; [apply Forall_nil | exact Hf]. }
unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
unfold rbm_NB, rbm_NM. apply r7_firstn_Forall. apply r7_NM_chars; assumption.
Qed.
Lemma r7_FS : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos) /\
  kLowShadowBeg <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighMemBeg /\
  rbn_SH X pos + 64 <= alloc_ceiling /\ SHADOW_OFF + 512 <= rbn_SH X pos /\ rbn_F X pos mod 8 = 0 /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
destruct (r7_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HX HM (proj1 (proj1 HM)))
  as (HF4096 & HFceil & HFal & HFapp & _).
pose proof asan_consts as (C1 & _).
pose proof (r7_sh_band (rbn_F X pos) 512 0 HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as SB0.
pose proof (r7_sh_band (rbn_F X pos) 512 63 HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as SB63.
change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in SB0, SB63.
split; [unfold in_app in HFapp; unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [lia|]. split; [lia|].
split.
{ unfold rbn_SH, shadow_addr, SHADOW_OFF.
  assert (rbn_F X pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia). lia. }
split.
{ unfold rbn_SH, shadow_addr. assert (512 <= rbn_F X pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
split; [|split; [exact HF4096 | exact HFceil]].
pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma r7_fbuf : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c D n,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  D = rbn_F X pos + 8 * j -> n = 8 * c -> 7 <= j -> 0 < c -> Z.of_nat (length sh) = 64 -> j + c + 7 <= 64 ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  in_app D n /\ range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF D n /\
  shadow_hull_vis (aview SEGS (w_H W1) memc1) D n /\
  (forall a, D <= a < D + n ->
     awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc1 Sc1) lyc1
       ((3, pos) :: ri_own X) a /\ apresent (w_H W1) memc1 a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c D n HX HM -> -> Hj Hc Hl H64 Hz.
pose proof (r7_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM 3 pos) as FA.
destruct (r7_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh memc1 mdc1 HX HM (proj1 (proj1 HM)))
  as (HF4096 & HFceil & HFal & HFapp & HFpr & _).
pose proof asan_consts as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
split.
{ apply (in_app_sub _ _ _ _ HFapp); lia. }
split.
{ apply zero_shadow_range.
  - replace (rbn_F X pos + 8 * j) with (rbn_F X pos + j * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
  - replace (8 * c) with (c * 8) by lia. apply Z.mod_mul. lia.
  - intros i Hi. replace (8 * c / 8) with c in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite shadow_of_addr_add8. change (shadow_of_addr SHADOW_OFF (rbn_F X pos)) with (rbn_SH X pos).
    replace (rbn_SH X pos + j + i) with (rbn_SH X pos + (j + i)) by lia.
    rewrite (Hsh0 (j + i)) by lia. rewrite (Hz (j + i)) by lia. reflexivity. }
split.
{ intros s Hs. unfold shadow_addr in Hs.
  assert (Hs2 : rbn_SH X pos <= s < rbn_SH X pos + 64) by (unfold rbn_SH, shadow_addr; lia).
  replace s with (rbn_SH X pos + (s - rbn_SH X pos)) by lia.
  rewrite (Hsh0 (s - rbn_SH X pos)) by lia. discriminate. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Definition r7_regs (X : rbn_in) (pos : Z) (regs : bvmap 5 word) : Prop :=
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\
  getr regs 25 = w64 (rbn_F X pos + 128) /\ getr regs 26 = w64 (rbn_F X pos + 192) /\
  getr regs 27 = w64 (rbn_F X pos + 64).
Lemma r7_close : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 regs m md,
  rbn_cx B X -> rbn_st7 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc3 Sc3 W3 m md (ri_k X) ->
  frames Sc3 = frames Sc1 -> ablocks B lyc3 Sc3 = ablocks B lyc1 Sc1 ->
  r7_regs X pos regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ r7_ws X pos (Z.of_nat (length (rbm_NB X))) a ->
     aview SEGS (w_H W3) m a = aview SEGS (w_H W1) memc1 a) ->
  val_mem SEGS (mrestrict (w_H W3) m) (rbn_A X + 88) 8 (rbn_F X pos + 192) ->
  val_mem SEGS (mrestrict (w_H W3) m) (rbn_A X + 96) 8 48 ->
  val_mem SEGS (mrestrict (w_H W3) m) (rbn_A X + 104) 8 (Z.of_nat (length (rbm_NB X))) ->
  val_mem SEGS (mrestrict (w_H W3) m) (rbn_A X + 112) 4 0 ->
  aview SEGS (w_H W3) m (r7_tx X pos) = Some 0 ->
  (forall j, 24 <= j < 30 -> aview SEGS (w_H W3) m (rbn_SH X pos + j) = Some 0) ->
  garr8 SEGS (mrestrict (w_H W3) m) (rbn_F X pos + 192) (rbm_NB X) ->
  rbn_st8 B X pos regs lyc3 Sc3 W3 m md.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 regs m md HX H7 HJ Hfr3 Hbl3 HR HE V88 V96 V104 V112 VTX VSH HD.
pose proof H7 as (HM & _ & _ & _ & _ & HC & HNB & HTB & HA).
destruct HR as (HRB & R18 & R25 & R26 & R27).
destruct (r7_FS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (Happ & SB0 & SB63 & HSHc0 & HSHl & HF8 & HF4096 & HFceil).
unfold kLowShadowBeg, kHighMemBeg in Happ, SB0, SB63.
destruct (r7_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
pose proof asan_consts as (C1 & _).
assert (Ht : TSB_CH_STK = 4112) by reflexivity.
assert (Hlnb : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
assert (Hltb : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
unfold rbn_st8. split.
{ apply (r7_mid X pos lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 m md (r7_ws X pos (Z.of_nat (length (rbm_NB X))))
    HX HM HJ Hfr3 Hbl3).
  - intros a Ha. unfold r7_ws, r7_tx in Ha. lia.
  - exact HE.
  - exact VSH. }
split; [exact HRB|]. split; [exact R18|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
split.
{ apply r7_cells_app4.
  - apply (r7_cells_kept (w_H W1) (w_H W3) memc1 m); [|exact HC].
    intros a n v k Hin Hk. pose proof (r7_c7_rng X pos _ _ _ _ a n v Hin) as Hr.
    apply HE; [lia|]. unfold r7_ws, r7_tx. lia.
  - unfold rbn_rd. cbn [rbn_cells]. split; [exact V88|]. split; [exact V96|].
    split; [rewrite firstn_all2 by lia; exact V104|]. split; [|exact I].
    unfold rbm_ovf. replace (47 <? Z.of_nat (length (rbm_NB X))) with false by (symmetry; apply Z.ltb_ge; lia).
    exact V112. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNB|]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview SEGS). apply HE; [lia|]. unfold r7_ws, r7_tx. lia. }
split.
{ apply (garr8_app1 SEGS (mrestrict (w_H W1) memc1) (mrestrict (w_H W3) m)); [exact HTB | | lia |].
  - change (rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X))) with (r7_tx X pos). apply r7_vm1. exact VTX.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HE; [lia|]. unfold r7_ws, r7_tx. lia. }
split; [rewrite firstn_all2 by lia; exact HD | exact HA].
Qed.
Definition r7_M1 (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (memc1 : word -> option byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2,
    c2 = rbn_cfg X 0x510 regs2 mem2 md2 /\
    ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
      ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) /\
    r7_regs X pos regs2 /\ r7_mem X pos W1 memc1 mem2 0 /\
    (forall i, 0 <= i < 16 -> aview SEGS (w_H W1) mem2 (rbn_A X + 104 + i) = Some 0).
Lemma r7_s1 : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st7 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P7 regs1 memc1 mdc1) (r7_M1 X pos lyc1 Sc1 W1 memc1).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H7.
pose proof H7 as (HM & HRB & R18 & R25 & R27 & HC & _).
pose proof HM as (HJ & Hfrs & _ & _ & _ & _ & _ & Hsh).
pose proof (r7_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
destruct (r7_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HX HM (proj1 HJ))
  as (_ & _ & _ & _ & HFpr & HSpr).
destruct (r7_FS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (Happ & SB0 & SB63 & HSHc & HSHl & HF8 & HF4096 & HFceil).
unfold kLowShadowBeg, kHighMemBeg in Happ, SB0, SB63. assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
destruct (r7_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Ht : TSB_CH_STK = 4112) by reflexivity.
assert (Hltb : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
pose proof (r7_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpres.
assert (V136 : val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_A X + 136) 8 (Z.of_nat (length (rbm_TB X)))).
{ apply (r7_cells_in _ _ _ _ _ HC). apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
  unfold rbn_rt. cbn [In]. right; right; left. reflexivity. }
pose proof (r7_entry1 (ri_fq X) regs1 W1 memc1 (rbn_F X pos) (Z.of_nat (length (rbm_TB X))) (rbn_A X)
  R25 R18 B9 HF8 HF4096 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(change (SHADOW_OFF + rbn_F X pos / 8) with (rbn_SH X pos); unfold SHADOW_OFF in *; lia)
  ltac:(lia) ltac:(change (SHADOW_OFF + rbn_F X pos / 8) with (rbn_SH X pos); lia)
  (proj1 (HFpr (rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X))) ltac:(lia)))
  (fun j Hj => HSpr j ltac:(lia)) (fun o Ho => Hpres (rbn_A X + o) ltac:(lia)) V136) as HS.
pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
remember (r7_E1 regs1 (Z.of_nat (length (rbm_TB X))) (rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X)))
  (2 ^ 64 - 1 - (rbn_F X pos + 128))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r7_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 (r7_tx X pos))
  by (subst E; unfold r7_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
assert (HW1 : forall a, in_wrange E (ss_mem r7_ss1) a ->
  a = r7_tx X pos \/ (rbn_SH X pos + 24 <= a < rbn_SH X pos + 30) \/ (rbn_A X + 88 <= a < rbn_A X + 104)).
{ intros a (r & Hr & Hw). unfold r7_ss1, r7_rr1 in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite E33, unsigned_lit_small in Hw by (unfold r7_tx; lia). left. lia.
  - rewrite (EE 18%nat 18%bv eq_refl), R18 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by lia.
    right; left; lia.
  - rewrite (EE 9%nat 9%bv eq_refl), B9 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by lia.
    right; right; lia. }
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_P7) with (BASE + (AF_both3_reac_box_name + RBN_P7)) by lia.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 33%nat (r7_tx X pos));
    [reflexivity | rewrite E33; apply unsigned_lit_small; unfold r7_tx; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite FA3.
    change (fs_frame_bytes 3) with 512. unfold r7_tx in Ha. lia. }
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos));
    [reflexivity | rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite FA3.
    change (fs_frame_bytes 3 / 8) with 64. change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos). lia. }
  eapply (awr_ok_cons_stack_off E _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ lyc1 _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; rewrite unsigned_lit_small by lia; lia
    | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
pose proof (r7_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW1) as Kr.
clear HF HFr HW1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (22%bv : bv 5) Rs6. prreg HS (23%bv : bv 5) Rs7.
prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RX.
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as RSH.
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as RA.
cbn [ms_mem restrict] in RX, RSH, RA.
assert (VTX0 : aview SEGS (w_H W1) (ms_mem ms) (r7_tx X pos) = Some 0).
{ apply r7_av1; [|lia].
  pose proof (field_of_region E _ 33 (r7_tx X pos) _ 0 1 0 1 0 1 (SLit 0) 0 RX
    ltac:(rewrite E33; apply unsigned_lit_small; unfold r7_tx; lia) ltac:(left; reflexivity) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
assert (VSH0 : forall j, 24 <= j < 30 -> aview SEGS (w_H W1) (ms_mem ms) (rbn_SH X pos + j) = Some 0).
{ intros j Hj. apply r7_av1; [|lia].
  apply (field_of_region E _ 18 (rbn_SH X pos) _ 24 30 24 30 j 1 (SLit 0) 0 RSH);
    [rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia | | reflexivity
    | cbn; lia | cbn; lia].
  cbn [In]. assert (j = 29 \/ j = 28 \/ j = 27 \/ j = 26 \/ j = 25 \/ j = 24) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; repeat (first [left; reflexivity | right]). }
assert (V88 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 88) 8 (rbn_F X pos + 192)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 88 144 88 104 88 8 (SOff 19 192) (rbn_F X pos + 192) RA);
    [rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia
    | cbn [In]; repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), B19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (V96 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 96) 8 48).
{ apply (field_of_region E _ 9 (rbn_A X) _ 88 144 88 104 96 8 (SLit 48) 48 RA);
    [rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia
    | cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia]. }
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET (ri_fq X)) W1 (ms_regs ms) (ms_mem ms)
    (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X) ((3, pos) :: ri_own X)
    lyc1 Sc1 _ (ri_k X) (rbn_A X + 104) 0 16 (rbn_A X - ri_sp0 X) _ HJ).
  - rewrite Ra0, (EE 9%nat 9%bv eq_refl), B9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rsp, (EE 2%nat 2%bv eq_refl), B2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - lia.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact B3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact B4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [left; lia | rewrite Hes; lia].
  - right. unfold kHighMemBeg, kHighMemEnd. lia.
  - exact (proj1 (r7_stk_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rbn_A X + 104) 16 HJ ltac:(lia) ltac:(lia) ltac:(lia))).
  - exact (proj2 (r7_stk_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rbn_A X + 104) 16 HJ ltac:(lia) ltac:(lia) ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrm & Hpres2).
apply SRr_ret.
assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 104 <= a < rbn_A X + 120) ->
  ~ (rbn_A X - ESTACK <= a < rbn_A X) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfrm; [exact Ha | lia | lia]. }
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (r7_pres _ _ r HP2 Hr)).
split; [reflexivity|]. exists regs2, mem2, md2.
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + 0x510) with (BASE + 15312) by (unfold AF_both3_reac_box_name; lia).
  reflexivity. }
split; [exact HJ2|].
split.
{ unfold r7_regs, rbn_rbase. split.
  { split; [rewrite P, Rsp, (EE 2%nat 2%bv eq_refl) by r7cs; exact B2|].
    split; [rewrite P, Rgp, (EE 3%nat 3%bv eq_refl) by r7cs; exact B3|].
    split; [rewrite P, Rtp, (EE 4%nat 4%bv eq_refl) by r7cs; exact B4|].
    split; [rewrite P, Rs0, (EE 8%nat 8%bv eq_refl) by r7cs; exact B8|].
    split; [rewrite P, Rs1, (EE 9%nat 9%bv eq_refl) by r7cs; exact B9|].
    split; [rewrite P, Rs3, (EE 19%nat 19%bv eq_refl) by r7cs; exact B19|].
    split; [rewrite P, Rs6, (EE 22%nat 22%bv eq_refl) by r7cs; exact B22|].
    rewrite P, Rs7, (EE 23%nat 23%bv eq_refl) by r7cs; exact B23. }
  split; [rewrite P, Rs2, (EE 18%nat 18%bv eq_refl) by r7cs; exact R18|].
  split; [rewrite P, Rs9, (EE 25%nat 25%bv eq_refl) by r7cs; exact R25|].
  split.
  { rewrite P, Rs10, (EE 19%nat 19%bv eq_refl), B19 by r7cs. unfold w64. rewrite unsigned_lit_small by lia.
    reflexivity. }
  rewrite P, Rs11, (EE 27%nat 27%bv eq_refl) by r7cs. exact R27. }
split.
{ split; [|split; [|split; [|split]]].
  - intros a Ha Hn. unfold r7_ws in Hn.
    rewrite (Kc a Ha) by lia. apply Kr; [exact Ha|]. unfold r7_tx in *. lia.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [|exact V88].
    intros k Hk. apply Kc; lia.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [|exact V96].
    intros k Hk. apply Kc; lia.
  - rewrite (Kc _) by (unfold r7_tx; lia). exact VTX0.
  - intros j Hj. rewrite (Kc _) by lia. exact (VSH0 j Hj). }
intros i Hi. exact (Heff i Hi).
Qed.
Lemma r7_s2 : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2,
  rbn_cx B X -> rbn_st7 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  r7_regs X pos regs2 -> r7_mem X pos W1 memc1 mem2 0 ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H W1) mem2 (rbn_A X + 104 + i) = Some 0) ->
  SRr SEGS W1 (rbn_cfg X 0x510 regs2 mem2 md2) (rbn_at8 B X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX H7 HJ HR HMM HZ.
pose proof H7 as (HM & _ & _ & _ & _ & _ & HNB & _ & HA).
pose proof HM as (_ & Hfrs & _).
pose proof (r7_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
destruct (r7_FS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (Happ & SB0 & SB63 & HSHc & HSHl & HF8 & HF4096 & HFceil).
unfold kLowShadowBeg, kHighMemBeg in Happ, SB0, SB63. assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
destruct (r7_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlnb : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
assert (Hltb : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
pose proof HR as ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & R18 & R25 & R26 & R27).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Ht : TSB_CH_STK = 4112) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
pose proof (r7_NB_ne X) as Hne. pose proof (r7_NB_chars X HX HA) as Hch.
assert (Hc0 : 1 <= hd 0 (rbm_NB X) <= 255 /\ nth 0 (rbm_NB X ++ [0]) 0 = hd 0 (rbm_NB X)).
{ destruct (rbm_NB X) as [|c l]; [exfalso; exact (Hne eq_refl)|].
  apply Forall_inv in Hch. cbn [hd nth app]. split; [lia | reflexivity]. }
pose proof HMM as (HE & V88 & V96 & VTX & VSH).
assert (Vc0 : val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_F X pos + 64) 1 (hd 0 (rbm_NB X))).
{ destruct (garr8_nthZ SEGS _ _ _ 0 HNB ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) as [V _].
  rewrite Z.add_0_r in V. change (Z.to_nat 0) with 0%nat in V. rewrite (proj2 Hc0) in V.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact V].
  intros k Hk. apply HE; [lia|]. unfold r7_ws, r7_tx. lia. }
pose proof (r7_entry2 (ri_fq X) regs2 W1 mem2 (rbn_F X pos + 64) (hd 0 (rbm_NB X)) R27
  ltac:(lia) ltac:(lia) (proj1 Hc0) Vc0) as HS.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
remember (r7_E2 regs2 (hd 0 (rbm_NB X))) as E eqn:HE2.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; unfold r7_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (hd 0 (rbm_NB X)))
  by (subst E; unfold r7_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
clear HE2.
assert (HW2 : forall a, in_wrange E (ss_mem r7_ss2) a -> False).
{ intros a (r & Hr & Hw). unfold r7_ss2, r7_rr2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Hw; lia. }
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + 0x510) with (BASE + (AF_both3_reac_box_name + 0x510)) by lia.
paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN_L4).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (r7_kept E _ (w_H W1) mem2 (ms_mem ms) _ HFr HW2) as K.
clear HF HFr HW2.
assert (Kz : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem2 a)
  by (intros a Ha; exact (K a Ha (fun H => H))).
clear K.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (21%bv : bv 5) Rs5.
prreg HS (22%bv : bv 5) Rs6. prreg HS (23%bv : bv 5) Rs7. prreg HS (24%bv : bv 5) Rs8.
prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
assert (Hsp : spZ (ms_regs ms) = rbn_A X).
{ unfold spZ. rewrite Rsp, (EE 2%nat 2%bv eq_refl), B2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (r7_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpres.
assert (HMs : r7_mem X pos W1 memc1 (ms_mem ms) 0).
{ apply (r7_mem_eq X pos W1 memc1 mem2 (ms_mem ms) 0 HMM Kz); unfold r7_tx; lia. }
pose proof HMs as (HEs & V88s & V96s & VTXs & VSHs).
assert (HMID : rbn_mid B X pos lyc1 Sc1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) (fun _ => False)
  (rbn_sh true true true true)).
{ apply (r7_mid X pos lyc1 Sc1 W1 memc1 mdc1 lyc1 Sc1 W1 (ms_mem ms) _ (r7_ws X pos 0) HX HM HJ eq_refl eq_refl).
  - intros a Ha. unfold r7_ws, r7_tx in Ha. lia.
  - exact HEs.
  - exact VSHs. }
assert (HFoff : off_img (rbn_F X pos) 512).
{ pose proof (frm_off_imgP B lyc1 Sc1 W1 (ms_mem ms) _ 3 pos (proj1 HJ) ltac:(rewrite Hfrs; left; reflexivity)) as Ho.
  rewrite FA3 in Ho. exact Ho. }
assert (Hsrc : rbn_lsrc W1 (ms_mem ms) (rbn_F X pos + 64) (rbm_NB X ++ [0])).
{ unfold rbn_lsrc. rewrite length_app. cbn [length].
  destruct (r7_fbuf X pos lyc1 Sc1 W1 (ms_mem ms) _ _ _ 8 3 (rbn_F X pos + 64) 24 HX HMID ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(rewrite r7_sh_len; reflexivity) ltac:(lia) ltac:(intros i Hi; apply r7_sh_nb; lia))
    as (_ & Hra & _).
  split.
  { apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNB|]. intros a Ha.
    rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview SEGS). apply HEs; [lia|]. unfold r7_ws, r7_tx. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  apply (range_addressable_sub _ _ _ 24 _ _ Hra); lia. }
destruct (r7_fbuf X pos lyc1 Sc1 W1 (ms_mem ms) _ _ _ 24 6 (rbn_F X pos + 192) 48 HX HMID ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(rewrite r7_sh_len; reflexivity) ltac:(lia) ltac:(intros i Hi; apply r7_sh_t24; lia))
  as (HDia & HDra & HDhv & HDwr).
assert (Hbuf : rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  (ms_mem ms) (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48).
{ unfold rbn_lbuf.
  split; [lia|]. split; [lia|]. split; [exact HDia|].
  split.
  { unfold in_app in HDia. unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
    lia. }
  split; [unfold off_img in *; lia|].
  split; [right; lia|]. split; [left; lia|].
  split; [exact HDra|]. split; [exact HDhv|]. exact HDwr. }
assert (Hrec : rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  (ms_mem ms) (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48 0 0).
{ unfold rbn_lrec.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [right; unfold kHighMemBeg, kHighMemEnd; lia|].
  split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; right; lia|].
  split; [left; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact V88s|]. split; [replace (rbn_A X + 88 + 8) with (rbn_A X + 96) by lia; exact V96s|].
  split.
  { replace (rbn_A X + 88 + 16) with (rbn_A X + 104) by lia. apply val_mem_zero8. intros i Hi.
    rewrite Kz by lia. exact (HZ i ltac:(lia)). }
  split.
  { replace (rbn_A X + 88 + 24) with (rbn_A X + 112) by lia. apply r7_vm04. intros i Hi.
    rewrite Kz by lia. replace (rbn_A X + 112 + i) with (rbn_A X + 104 + (8 + i)) by lia. exact (HZ (8 + i) ltac:(lia)). }
  split; [exact (proj1 (r7_stk_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rbn_A X + 88) 28 HJ ltac:(lia) ltac:(lia) ltac:(lia)))|].
  split; [exact (proj2 (r7_stk_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rbn_A X + 88) 28 HJ ltac:(lia) ltac:(lia) ltac:(lia))
    ltac:(lia))|].
  intros a Ha. split; [left; lia | exact (Hpres a ltac:(lia))]. }
assert (Hsep : rbn_lsep (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48 (rbn_F X pos + 64)
  (Z.of_nat (length (rbm_NB X)) + 1)).
{ unfold rbn_lsep. split; [left; lia|]. split; [left; lia|]. right; lia. }
assert (Hlcx : rbn_lcx B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) (ri_k X) (ms_regs ms)).
{ unfold rbn_lcx. split; [exact HJ|].
  split; [exact (proj1 (proj2 (proj2 (proj2 HMID))))|].
  split; [rewrite Rgp, (EE 3%nat 3%bv eq_refl); exact B3|].
  split; [rewrite Rtp, (EE 4%nat 4%bv eq_refl); exact B4|].
  split; [rewrite Rs1, Rsp, (EE 9%nat 9%bv eq_refl), (EE 2%nat 2%bv eq_refl), B9, B2; reflexivity|].
  split; [rewrite Rs6, (EE 22%nat 22%bv eq_refl); exact B22|].
  rewrite Hsp. split; [lia|]. split; lia. }
assert (EP : BASE + 15332 = BASE + AF_both3_reac_box_name + RBN_L4) by (unfold AF_both3_reac_box_name, RBN_L4; lia).
rewrite EP.
pose proof (L4F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) (ri_k X) (ms_regs ms)
  (rbn_F X pos + 64) (rbn_F X pos + 192) 0 0 (rbm_NB X) ltac:(lia)) as R.
unfold rbn_L4_run in R. rewrite Hsp in R.
eapply SRr_bind.
{ apply R.
  - exact Hlcx.
  - exact Hrec.
  - exact Hbuf.
  - exact Hne.
  - exact Hch.
  - exact Hsrc.
  - exact Hsep.
  - lia.
  - left. reflexivity.
  - rewrite Ra0, E32. reflexivity.
  - rewrite Rs8, (EE 27%nat 27%bv eq_refl), R27. reflexivity.
  - rewrite Rs4, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite Rs5. apply bv_eq. vm_compute. reflexivity. }
cbv beta. clear HG.
intros W3 c3 _ (lyc3 & Sc3 & regs3 & mem3 & md3 & -> & HJ3 & Hfr3 & Hbl3 & _ & HK & HnF & HovF & HD & HKc).
rewrite Z.add_0_l in HnF. rewrite Z.add_0_r in HD.
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) rbn_cl4 = false -> getr regs3 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (r7_keep _ _ _ r HK Hr)).
destruct HKc as (Kc1 & _).
rewrite Hsp in Kc1. cbv beta in Kc1.
apply SRr_ret.
exists pos, regs3, lyc3, Sc3, mem3, md3.
split; [reflexivity|].
apply (r7_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc3 Sc3 W3 regs3 mem3 md3 HX H7 HJ3 Hfr3 Hbl3).
- unfold r7_regs, rbn_rbase. split.
  { split; [rewrite KG, Rsp, (EE 2%nat 2%bv eq_refl) by reflexivity; exact B2|].
    split; [rewrite KG, Rgp, (EE 3%nat 3%bv eq_refl) by reflexivity; exact B3|].
    split; [rewrite KG, Rtp, (EE 4%nat 4%bv eq_refl) by reflexivity; exact B4|].
    split; [rewrite KG, Rs0, (EE 8%nat 8%bv eq_refl) by reflexivity; exact B8|].
    split; [rewrite KG, Rs1, (EE 9%nat 9%bv eq_refl) by reflexivity; exact B9|].
    split; [rewrite KG, Rs3, (EE 19%nat 19%bv eq_refl) by reflexivity; exact B19|].
    split; [rewrite KG, Rs6, (EE 22%nat 22%bv eq_refl) by reflexivity; exact B22|].
    rewrite KG, Rs7, (EE 23%nat 23%bv eq_refl) by reflexivity; exact B23. }
  split; [rewrite KG, Rs2, (EE 18%nat 18%bv eq_refl) by reflexivity; exact R18|].
  split; [rewrite KG, Rs9, (EE 25%nat 25%bv eq_refl) by reflexivity; exact R25|].
  split; [rewrite KG, Rs10, (EE 26%nat 26%bv eq_refl) by reflexivity; exact R26|].
  rewrite KG, Rs11, (EE 27%nat 27%bv eq_refl) by reflexivity. exact R27.
- intros a Ha Hn. unfold r7_ws in Hn. rewrite Kc1 by lia. apply HEs; [exact Ha|]. unfold r7_ws. lia.
- apply (val_mem_kept SEGS (w_H W1) (w_H W3) (ms_mem ms) mem3); [|exact V88s]. intros k Hk. apply Kc1; lia.
- apply (val_mem_kept SEGS (w_H W1) (w_H W3) (ms_mem ms) mem3); [|exact V96s]. intros k Hk. apply Kc1; lia.
- replace (rbn_A X + 104) with (rbn_A X + 88 + 16) by lia. exact HnF.
- replace (rbn_A X + 112) with (rbn_A X + 88 + 24) by lia. exact HovF.
- rewrite Kc1 by (unfold r7_tx; lia). exact VTXs.
- intros j Hj. rewrite Kc1 by lia. exact (VSHs j Hj).
- exact HD.
Qed.
Theorem rbn_seg7 : rbn_seg7_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H7.
eapply SRr_bind; [exact (r7_s1 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H7)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HR2 & HM2 & HZ2).
exact (r7_s2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX H7 HJ2 HR2 HM2 HZ2).
Qed.
End h.
End f.
End d.
