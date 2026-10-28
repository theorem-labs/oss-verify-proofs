(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d UI4v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition sv_harg (nr ng nb : nat) : sv :=
SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff ng 0) (SLit 8)) (SAlu ALU_SLL (SOff nr 0) (SLit 16))) (SOff nb 0).
Definition sv_hsh (nr ng nb nT : nat) : sv := SMdw M_REMU (sv_harg nr ng nb) (SOff nT 0).
Definition sv_zx (a : sv) : sv := SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32).
Lemma U_harg : forall E nr ng nb (c : colour),
ew E nr = Z_to_bv 64 (cR c) -> ew E ng = Z_to_bv 64 (cG c) -> ew E nb = Z_to_bv 64 (cB c) -> colour_ok c ->
U E (sv_harg nr ng nb) = cR c * 65536 + cG c * 256 + cB c.
Proof.
intros E nr ng nb c Hr Hg Hb Hc. pose proof Hc as (Rr & Rg & Rb). unfold sv_harg.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E nr (cR c) Hr), (U_atom E ng (cG c) Hg), (U_atom E nb (cB c) Hb) by lia.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
rewrite (zcanon_id (cR c * 65536)), (zcanon_id (cG c * 256)) by (unfold M64; lia).
assert (L1 : Z.lor (cG c * 256) (cR c * 65536) = cR c * 65536 + cG c * 256).
{ rewrite Z.lor_comm. change 65536 with (2 ^ 16). apply lor_low_disjoint; lia. }
rewrite L1. rewrite (zcanon_id (cR c * 65536 + cG c * 256)) by (unfold M64; lia).
assert (L2 : Z.lor (cR c * 65536 + cG c * 256) (cB c) = cR c * 65536 + cG c * 256 + cB c).
{ replace (cR c * 65536 + cG c * 256) with ((cR c * 256 + cG c) * 2 ^ 8) by lia. rewrite lor_low_disjoint; lia. }
rewrite L2. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_hsh : forall E nr ng nb nT (c : colour) T,
ew E nr = Z_to_bv 64 (cR c) -> ew E ng = Z_to_bv 64 (cG c) -> ew E nb = Z_to_bv 64 (cB c) -> colour_ok c ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (sv_hsh nr ng nb nT) = hash0 T c.
Proof.
intros E nr ng nb nT c T Hr Hg Hb Hc HT RT. pose proof Hc as (Rr & Rg & Rb). unfold sv_hsh, hash0.
apply U_remuw_small; [| apply (U_atom E nT T HT); lia | | lia].
- apply (U_harg E nr ng nb c); assumption.
- lia.
Qed.
Lemma U_zx : forall E a x, U E a = x -> 0 <= x < 2 ^ 32 -> U E (sv_zx a) = x.
Proof.
intros E a x Ha Hx. unfold sv_zx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Ha.
change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2^64) with (2^32 * 2^32); nia).
rewrite Z.shiftr_div_pow2, Z.div_mul by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_add_atom : forall E n b a x, ew E n = Z_to_bv 64 b -> 0 <= b -> U E a = x -> 0 <= x -> b + x < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n 0) a) = b + x.
Proof.
intros E n b a x Hn Hb Ha Hx Hbx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n b Hn), Ha by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma find_slot_home_free : forall H ent c, ht_inv H ent -> usedz H (hash0 (ht_T H) c) = 0 -> find_slot H c = Some (hash0 (ht_T H) c).
Proof.
intros H ent c INV Hz. destruct (find_off_exists H ent INV c) as (js & Ejs).
destruct (find_off_spec H ent INV c js Ejs) as (Hjs & _ & Hbefore).
rewrite (find_slot_of_off H c js Ejs). destruct (Z.eq_dec js 0) as [->|Hne].
- rewrite cyc_0; [reflexivity | apply hash0_range; exact (inv_T_pos H ent INV)].
- exfalso. specialize (Hbefore 0 ltac:(lia)). rewrite cyc_0 in Hbefore by (apply hash0_range; exact (inv_T_pos H ent INV)).
unfold slot_stop in Hbefore. rewrite Hz in Hbefore. discriminate Hbefore.
Qed.
Lemma find_off_ge0 : forall H ent c js, ht_inv H ent -> find_off H c = Some js -> 0 <= js.
Proof. intros H ent c js INV E. exact (proj1 (proj1 (find_off_spec H ent INV c js E))). Qed.
Section f.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Lemma perm_block_once : forall Lc Ac memc mdc (x : Z * Z) l1 l2,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l1 ++ x :: l2) -> 0 < snd x -> ~ In x (l1 ++ l2).
Proof.
intros Lc Ac memc mdc x l1 l2 HH HP Hn Hin.
assert (HP' : Permutation (blocks Lc Ac) (x :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP | apply Permutation_sym, Permutation_middle]. }
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc x (l1 ++ l2) x HH HP' Hin). lia.
Qed.
Lemma tmp_not_entry : forall L A Lc Ac memc mdc (x : Z * Z) l1 l2,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l1 ++ l2) -> Permutation (blocks L A) l1 ->
In x l2 -> 0 < snd x -> ~ In x (blocks L A).
Proof.
intros L A Lc Ac memc mdc x l1 l2 HH HP HP0 Hx Hn Hin.
apply in_split in Hx as (l2a & l2b & ->).
apply (perm_block_once Lc Ac memc mdc x (l1 ++ l2a) l2b HH).
- rewrite <- app_assoc. exact HP.
- exact Hn.
- apply in_app_iff. left. apply in_app_iff. left. eapply Permutation_in; [exact HP0 | exact Hin].
Qed.
Lemma perm_sep : forall Lc Ac memc mdc (x y : Z * Z) l1 l2,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l1 ++ x :: l2) -> In y (l1 ++ l2) ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros Lc Ac memc mdc x y l1 l2 HH HP Hin.
assert (HP' : Permutation (blocks Lc Ac) (x :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP | apply Permutation_sym, Permutation_middle]. }
exact (heap_sep_perm _ _ LAWS Lc Ac memc mdc x (l1 ++ l2) y HH HP' Hin).
Qed.
End f.
Definition in_cht (C : cht) (a : Z) : Prop := exists b, In b (cht_blks C) /\ fst b <= a < fst b + snd b.
Lemma val_mem_kept : forall (m m' : word -> option byte) a n v,
val_mem ubs2segs m a n v -> (forall k, a <= k < a + Z.of_nat n -> mbyte ubs2segs m' k = mbyte ubs2segs m k) -> val_mem ubs2segs m' a n v.
Proof. intros m m' a n v H Hk j Hj. rewrite Hk by lia. apply H. exact Hj. Qed.
Lemma val_mem_kept8 : forall (m m' : word -> option byte) a v,
word_mem ubs2segs m a v -> (forall k, a <= k < a + 8 -> mbyte ubs2segs m' k = mbyte ubs2segs m k) -> word_mem ubs2segs m' a v.
Proof. intros m m' a v H Hk j Hj. rewrite Hk by lia. apply H. exact Hj. Qed.
Section o.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Variables (regs0 : bvmap 5 word) (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr delay : Z) (rest : list (Z * Z)).
Local Notation HM := (hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Lemma sep_base_cht : forall Lc Ac memc mdc pnew fimg C (y : Z * Z) a,
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C) ->
In y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) -> in_cht C a -> ~ (fst y <= a < fst y + snd y).
Proof.
intros Lc Ac memc mdc pnew fimg C y a HH HP Hy (x & Hx & Ha) Hya.
apply in_split in Hx as (c1 & c2 & Ec). rewrite Ec in HP.
rewrite app_assoc in HP.
replace ((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ c1 ++ x :: c2) with (((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ c1) ++ x :: c2) in HP by (rewrite <- app_assoc; reflexivity).
pose proof (perm_sep API Lc Ac memc mdc x y _ _ HH HP ltac:(apply in_app_iff; left; apply in_app_iff; left; exact Hy)). lia.
Qed.
Lemma cht_low : forall Lc Ac memc mdc pnew fimg C a,
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C) ->
in_cht C a -> 4096 <= a < alloc_ceiling.
Proof.
intros Lc Ac memc mdc pnew fimg C a HH HP ([b n] & Hx & Ha). cbn [fst snd] in Ha.
assert (Hin : In (b, n) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; right; apply in_app_iff; right; exact Hx).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b n (a - b) HH Hin ltac:(lia)) as (_ & Hlo & Hhi & _). lia.
Qed.
Definition hm_scratch (a : Z) : Prop := SP + 72 <= a < SP + 80 \/ SP + 88 <= a < SP + 112.
Lemma hist_mem_update : forall Lc Ac memc mdc memX pnew fimg imgl C C' i i',
heap_ok MR Lc Ac memc mdc -> alloc_ceiling <= SP -> SP + RGBA_FRAME <= 2 ^ 63 -> (fmt = 3 \/ fmt = 4) ->
HM Lc Ac memc pnew fimg imgl C i ->
(forall a, 0 <= a < 2 ^ 64 -> ~ in_cht C a -> ~ hm_scratch a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
cht_ok memX C' -> ch_c C' = ch_c C -> cht_blks C' = cht_blks C ->
ch_hS C' = ch_h C' -> ch_uS C' = ch_u C' -> ch_TS C' = ch_T C' -> zsum (map snd (ch_ent C')) <= i' ->
HM Lc Ac memX pnew fimg imgl C' i'.
Proof.
intros Lc Ac memc mdc memX pnew fimg imgl C C' i i' HH Hsp Hsp2 Hfmt
(Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & Himg & Hcht & _ & _ & _ & Hz & Hpn & Hfi & HB) KEEP Hcht' Ec Eb EhS EuS ETS Hz'.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ hm_scratch a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply KEEP; [lia | | exact Hs]. intros Hc. pose proof (cht_low Lc Ac memc mdc pnew fimg C a HH HB Hc). lia. }
assert (KB : forall y i0, In y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) -> 0 <= i0 < snd y -> mbyte ubs2segs memX (fst y + i0) = mbyte ubs2segs memc (fst y + i0)).
{ intros y i0 Hy Hi0.
assert (Hin : In y (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; rewrite app_assoc; apply in_app_iff; left; exact Hy).
destruct y as [b n]. cbn [fst snd] in *.
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b n i0 HH Hin Hi0) as (_ & Hlo & Hhi & _).
apply KEEP; [lia | | unfold hm_scratch; lia]. intros Hc. exact (sep_base_cht Lc Ac memc mdc pnew fimg C (b, n) (b + i0) HH HB Hy Hc ltac:(cbn; lia)). }
assert (KS : forall off v, 0 <= off -> off + 8 <= RGBA_FRAME -> (off + 8 <= 72 \/ (80 <= off /\ off + 8 <= 88) \/ 112 <= off) ->
slot regs0 memc off v -> slot regs0 memX off v).
{ intros off v H0 H1 H2 Hs. unfold slot in *. apply (val_mem_kept8 memc); [exact Hs|]. intros k Hk. apply KH; unfold hm_scratch, RGBA_FRAME in *; lia. }
unfold hist_mem. destruct Hslots as (M8 & M16 & M24 & M48).
split. { unfold slots_mid. unfold SL_N, SL_cfp, SL_new, SL_fimg, RGBA_FRAME in *.
repeat split; (apply KS; [lia | unfold RGBA_FRAME; lia | lia | assumption]). }
split; [apply KS; unfold SL_32, RGBA_FRAME in *; [lia | lia | lia | exact S32]|].
split; [apply KS; unfold SL_40, RGBA_FRAME in *; [lia | lia | lia | exact S40]|].
split; [apply KS; unfold SL_56, RGBA_FRAME in *; [lia | lia | lia | exact S56]|].
split; [apply KS; unfold SL_64, RGBA_FRAME in *; [lia | lia | lia | exact S64]|].
split; [apply KS; unfold SL_80, RGBA_FRAME in *; [lia | lia | lia | exact S80]|].
split; [apply KS; unfold SL_112, RGBA_FRAME in *; [lia | lia | lia | exact S112]|].
split; [apply KS; unfold SL_120, RGBA_FRAME in *; [lia | lia | lia | exact S120]|].
split. { unfold fcfg_at in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 29); [exact Hfc | reflexivity |].
intros k Hk. unfold OFF_fcfg. apply KH; unfold hm_scratch, RGBA_FRAME in *; lia. }
split. { unfold rgb_obj in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros k Hk. apply (KB (r, RGB_SIZE) k); [left; reflexivity | cbn; exact Hk]. }
split. { eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hcg |].
intros b n i0 Hbn Hi0. apply (KB (b, n) i0); [| cbn; exact Hi0]. apply in_app_iff. left. right. apply in_app_iff. left. exact Hbn. }
split. { destruct Himg as [Ha Hl]. split; [|exact Hl]. eapply arr8_frame; [exact Ha|]. intros a Ha'. destruct (fmt_okb fmt) eqn:Ef.
- replace a with (img + (a - img)) by lia. apply (KB (img, fmt * N) (a - img)); [| cbn; lia].
apply in_app_iff. left. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block. rewrite Ef. left. reflexivity.
- exfalso. unfold fmt_okb in Ef. clear - Ef Hfmt. destruct Hfmt as [-> | ->]; discriminate Ef. }
split; [exact Hcht'|]. split; [exact EhS|]. split; [exact EuS|]. split; [exact ETS|]. split; [exact Hz'|]. split; [exact Hpn|]. split; [exact Hfi|]. rewrite Eb. exact HB.
Qed.
Lemma arr8_update : forall (mem mem' : word -> option byte) base l l',
arr8 ubs2segs mem base l -> zlen l' = zlen l ->
(forall j, 0 <= j < zlen l ->
(getz l' j = getz l j /\ mbyte ubs2segs mem' (base + j) = mbyte ubs2segs mem (base + j)) \/
(mbyte ubs2segs mem' (base + j) = Some (Z_to_bv 8 (getz l' j)) /\ 0 <= getz l' j < 256)) ->
arr8 ubs2segs mem' base l'.
Proof.
intros mem mem' base l l' Ha Hl Hj j Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen in *; lia).
pose proof (arr8_getz ubs2segs mem base l (Z.of_nat j) Ha Hz) as [A B].
unfold getz in *. rewrite Nat2Z.id in *.
destruct (Hj (Z.of_nat j) Hz) as [[E1 E2] | [E1 E2]].
- rewrite Nat2Z.id in E1. rewrite E1, E2. split; [exact A | exact B].
- rewrite Nat2Z.id in E1, E2. split; [exact E1 | exact E2].
Qed.
Lemma arr32_update : forall (mem mem' : word -> option byte) base l l',
arr32 ubs2segs mem base l -> zlen l' = zlen l ->
(forall j, 0 <= j < zlen l ->
(getz l' j = getz l j /\ forall k, 0 <= k < 4 -> mbyte ubs2segs mem' (base + 4 * j + k) = mbyte ubs2segs mem (base + 4 * j + k)) \/
(val_mem ubs2segs mem' (base + 4 * j) 4 (getz l' j) /\ 0 <= getz l' j < 2 ^ 32)) ->
arr32 ubs2segs mem' base l'.
Proof.
intros mem mem' base l l' Ha Hl Hj j Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen in *; lia).
pose proof (arr32_getz ubs2segs mem base l (Z.of_nat j) Ha Hz) as [A B].
unfold getz in *. rewrite Nat2Z.id in *.
destruct (Hj (Z.of_nat j) Hz) as [[E1 E2] | [E1 E2]].
- rewrite Nat2Z.id in E1. rewrite E1. split; [|exact B]. intros k Hk. rewrite E2 by lia. apply A. exact Hk.
- rewrite Nat2Z.id in E1, E2. split; [exact E1 | exact E2].
Qed.
Definition C_hit (C : cht) (h : Z) : cht :=
mkCHT (ch_c C) (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_T C) (ch_hS C) (ch_uS C) (ch_TS C)
(ht_hit (ch_H C) h) (lset (ch_ent C) (Z.to_nat (cidx (ch_H C) h)) (key (ch_H C) h, freq (ch_H C) h + 1)).
Definition C_ins (C : cht) (h : Z) (col : colour) : cht :=
mkCHT (ch_c C) (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_T C) (ch_hS C) (ch_uS C) (ch_TS C)
(ht_ins (ch_H C) h col 1) (ch_ent C ++ [(col, 1)]).
Definition cht_apart (C : cht) : Prop :=
forall l1 x l2 y, cht_blks C = l1 ++ x :: l2 -> In y (l1 ++ l2) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Lemma cht_apart_of_perm : forall Lc Ac memc mdc (l0 : list (Z * Z)) C,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l0 ++ cht_blks C) -> cht_apart C.
Proof.
intros Lc Ac memc mdc l0 C HH HP l1 x l2 y E Hy. rewrite E in HP.
replace (l0 ++ l1 ++ x :: l2) with ((l0 ++ l1) ++ x :: l2) in HP by (rewrite <- app_assoc; reflexivity).
apply (perm_sep API Lc Ac memc mdc x y _ _ HH HP). rewrite <- app_assoc. apply in_app_iff. right. exact Hy.
Qed.

Lemma cht_apart_ij : forall C (i j : nat) x y a,
cht_apart C -> (i < j)%nat -> nth_error (cht_blks C) i = Some x -> nth_error (cht_blks C) j = Some y ->
fst x <= a < fst x + snd x -> ~ (fst y <= a < fst y + snd y).
Proof.
intros C i j x y a CA Hij Hi Hj Ha Hb.
destruct (nth_error_split _ _ Hi) as (l1 & l2 & E & Hl1).
assert (Hy : In y (l1 ++ l2)).
{ apply in_app_iff. right. rewrite E in Hj. rewrite nth_error_app2 in Hj by lia.
replace (j - length l1)%nat with (S (j - length l1 - 1)) in Hj by lia. cbn in Hj. eapply nth_error_In. exact Hj. }
pose proof (CA l1 x l2 y E Hy). lia.
Qed.
Lemma cht_ok_hit : forall (memc memX : word -> option byte) C h,
cht_ok memc C -> cht_apart C -> in_slot (ch_H C) h -> freq (ch_H C) h + 1 < 2 ^ 32 ->
val_mem ubs2segs memX (ch_f C + 4 * h) 4 (freq (ch_H C) h + 1) ->
(forall a, in_cht C a -> ~ (ch_f C + 4 * h <= a < ch_f C + 4 * h + 4) -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
cht_ok memX (C_hit C h).
Proof.
intros memc memX C h (Hobj & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & Rh & Ru & Rt) CA Hsl Hf Hv KEEP.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & _). rewrite HT in L1, L2, L3, L4, L5. destruct Hsl as [Hh Hu]. rewrite HT in Hh.
assert (IC : forall k a, match nth_error (cht_blks C) k with Some b => fst b <= a < fst b + snd b | None => False end -> in_cht C a).
{ intros k a Ha. destruct (nth_error (cht_blks C) k) as [b|] eqn:Eb; [|destruct Ha]. exists b. split; [eapply nth_error_In; exact Eb | exact Ha]. }
assert (NF : forall k y a, k <> 1%nat -> nth_error (cht_blks C) k = Some y -> fst y <= a < fst y + snd y -> ~ (ch_f C + 4 * h <= a < ch_f C + 4 * h + 4)).
{ intros k y a Hk Hy Ha Hc.
assert (E1 : nth_error (cht_blks C) 1 = Some (ch_f C, 4 * ch_T C)) by reflexivity.
destruct (Nat.lt_ge_cases k 1) as [Hlt|Hge].
- apply (cht_apart_ij C k 1%nat y (ch_f C, 4 * ch_T C) a CA Hlt Hy E1 Ha). cbn. lia.
- apply (cht_apart_ij C 1%nat k (ch_f C, 4 * ch_T C) y a CA ltac:(lia) E1 Hy); [cbn; lia | exact Ha]. }
assert (FR0 : 1 <= freq (ch_H C) h).
{ destruct Hinv as (_ & _ & _ & I4 & _). destruct (I4 h ltac:(split; [rewrite <- HT in Hh; exact Hh | exact Hu])) as (_ & _ & F). exact F. }
unfold cht_ok, C_hit. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply KEEP; [apply (IC 0%nat); cbn -[Z.add Z.mul Z.lt Z.le]; unfold CHT_SIZE in *; lia|].
apply (NF 0%nat (ch_c C, CHT_SIZE)); [lia | reflexivity | cbn; lia]. }
split. { unfold cht_arrays. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_hit]. split; [|split; [|split; [|split]]].
- apply (arr32_update memc memX (ch_f C) (ht_frequ (ch_H C))); [exact Af | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j h) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact Hv | unfold freq in *; lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. intros k Hk. apply KEEP; [apply (IC 1%nat); cbn; lia | lia].
- eapply arr8_frame; [exact Ah|]. intros a Ha. apply KEEP; [apply (IC 2%nat); cbn; lia | apply (NF 2%nat (ch_h C, 3 * ch_T C)); [lia | reflexivity | cbn; lia]].
- eapply arr8_frame; [exact Au|]. intros a Ha. apply KEEP; [apply (IC 3%nat); cbn; lia | apply (NF 3%nat (ch_u C, ch_T C)); [lia | reflexivity | cbn; lia]].
- eapply arr8_frame; [exact Ap|]. intros a Ha. apply KEEP; [apply (IC 4%nat); cbn; lia | apply (NF 4%nat (ch_p C, 3 * ch_T C)); [lia | reflexivity | cbn; lia]].
- eapply arr32_frame; [exact Ax|]. intros a Ha. apply KEEP; [apply (IC 5%nat); cbn; lia | apply (NF 5%nat (ch_x C, 4 * ch_T C)); [lia | reflexivity | cbn; lia]]. }
split; [apply (ht_hit_inv (ch_H C) (ch_ent C) Hinv h); split; [rewrite <- HT in Hh; exact Hh | exact Hu]|].
split; [exact HT|]. split; [exact Hch|]. split; [exact Rh|]. split; [exact Ru | exact Rt].
Qed.
Lemma obj_at_cht_set_cnt : forall (m m' : word -> option byte) c v0 v1 v2 v3 v4 v5 v6 v5',
obj_at ubs2segs m c LAY_Cht [v0; v1; v2; v3; v4; v5; v6] ->
(forall a, c <= a < c + 48 -> ~ (c + 40 <= a < c + 44) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
val_mem ubs2segs m' (c + 40) 4 v5' -> 0 <= v5' < 2 ^ 32 ->
obj_at ubs2segs m' c LAY_Cht [v0; v1; v2; v3; v4; v5'; v6].
Proof.
intros m m' c v0 v1 v2 v3 v4 v5 v6 v5' Hobj KEEP Hv Hr.
cbn [obj_at LAY_Cht] in Hobj |- *. unfold field_ok in *. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobj |- *.
destruct Hobj as ([A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & _).
assert (K : forall off n v, val_mem ubs2segs m (c + off) n v -> 0 <= off -> (off + Z.of_nat n <= 40 \/ 44 <= off) -> off + Z.of_nat n <= 48 -> val_mem ubs2segs m' (c + off) n v).
{ intros off n v Hvm H0 H1 H2. apply (val_mem_kept m); [exact Hvm|]. intros k Hk. apply KEEP; lia. }
split; [split; [apply K; [exact A0 | lia | cbn; lia | cbn; lia] | exact B0]|].
split; [split; [apply K; [exact A1 | lia | cbn; lia | cbn; lia] | exact B1]|].
split; [split; [apply K; [exact A2 | lia | cbn; lia | cbn; lia] | exact B2]|].
split; [split; [apply K; [exact A3 | lia | cbn; lia | cbn; lia] | exact B3]|].
split; [split; [apply K; [exact A4 | lia | cbn; lia | cbn; lia] | exact B4]|].
split; [split; [exact Hv | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hr]|].
split; [split; [apply K; [exact A6 | lia | cbn; lia | cbn; lia] | exact B6]|]. exact I.
Qed.
Definition ins_w (C : cht) (h : Z) (a : Z) : Prop :=
let cnt := ht_cnt (ch_H C) in
(ch_h C + 3 * h <= a < ch_h C + 3 * h + 3) \/ (ch_p C + 3 * cnt <= a < ch_p C + 3 * cnt + 3) \/ a = ch_u C + h \/
(ch_x C + 4 * h <= a < ch_x C + 4 * h + 4) \/ (ch_f C + 4 * h <= a < ch_f C + 4 * h + 4) \/ (ch_c C + 40 <= a < ch_c C + 44).
Lemma cht_ok_ins : forall (memc memX : word -> option byte) C h (col : colour),
cht_ok memc C -> cht_apart C -> find_slot (ch_H C) col = Some h -> usedz (ch_H C) h = 0 -> colour_ok col ->
ht_cnt (ch_H C) + 1 < ch_T C ->
let cnt := ht_cnt (ch_H C) in
mbyte ubs2segs memX (ch_h C + 3 * h) = Some (Z_to_bv 8 (cR col)) -> mbyte ubs2segs memX (ch_h C + 3 * h + 1) = Some (Z_to_bv 8 (cG col)) ->
mbyte ubs2segs memX (ch_h C + 3 * h + 2) = Some (Z_to_bv 8 (cB col)) ->
mbyte ubs2segs memX (ch_p C + 3 * cnt) = Some (Z_to_bv 8 (cR col)) -> mbyte ubs2segs memX (ch_p C + 3 * cnt + 1) = Some (Z_to_bv 8 (cG col)) ->
mbyte ubs2segs memX (ch_p C + 3 * cnt + 2) = Some (Z_to_bv 8 (cB col)) ->
mbyte ubs2segs memX (ch_u C + h) = Some (Z_to_bv 8 1) ->
val_mem ubs2segs memX (ch_x C + 4 * h) 4 cnt -> val_mem ubs2segs memX (ch_f C + 4 * h) 4 1 ->
val_mem ubs2segs memX (ch_c C + 40) 4 (cnt + 1) ->
(forall a, in_cht C a -> ~ ins_w C h a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
cht_ok memX (C_ins C h col).
Proof.
intros memc memX C h col (Hobj & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & Rh & Ru & Rt) CA Hfs Hz Hcol Hroom cnt
K0 K1 K2 P0 P1 P2 U1 X4 F4 S4 KEEP.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & _). rewrite HT in L1, L2, L3, L4, L5, C1.
pose proof (find_slot_range (ch_H C) (ch_ent C) Hinv col h Hfs) as Hh. rewrite HT in Hh. pose proof Hcol as (Rr & Rg & Rb).
assert (IC : forall k a, match nth_error (cht_blks C) k with Some b => fst b <= a < fst b + snd b | None => False end -> in_cht C a).
{ intros k a Ha. destruct (nth_error (cht_blks C) k) as [b|] eqn:Eb; [|destruct Ha]. exists b. split; [eapply nth_error_In; exact Eb | exact Ha]. }
assert (AP : forall (k k' : nat) x y a, k <> k' -> nth_error (cht_blks C) k = Some x -> nth_error (cht_blks C) k' = Some y ->
fst x <= a < fst x + snd x -> ~ (fst y <= a < fst y + snd y)).
{ intros k k' x y a Hk Hx Hy Ha. destruct (Nat.lt_ge_cases k k') as [Hlt|Hge].
- exact (cht_apart_ij C k k' x y a CA Hlt Hx Hy Ha).
- intros Hb. exact (cht_apart_ij C k' k y x a CA ltac:(lia) Hy Hx Hb Ha). }
assert (E0 : nth_error (cht_blks C) 0 = Some (ch_c C, CHT_SIZE)) by reflexivity.
assert (E1 : nth_error (cht_blks C) 1 = Some (ch_f C, 4 * ch_T C)) by reflexivity.
assert (E2 : nth_error (cht_blks C) 2 = Some (ch_h C, 3 * ch_T C)) by reflexivity.
assert (E3 : nth_error (cht_blks C) 3 = Some (ch_u C, ch_T C)) by reflexivity.
assert (E4 : nth_error (cht_blks C) 4 = Some (ch_p C, 3 * ch_T C)) by reflexivity.
assert (E5 : nth_error (cht_blks C) 5 = Some (ch_x C, 4 * ch_T C)) by reflexivity.
assert (KEEPk : forall (k : nat) x a, nth_error (cht_blks C) k = Some x -> fst x <= a < fst x + snd x ->
~ (match k with 0%nat => ch_c C + 40 <= a < ch_c C + 44 | 1%nat => ch_f C + 4 * h <= a < ch_f C + 4 * h + 4
| 2%nat => ch_h C + 3 * h <= a < ch_h C + 3 * h + 3 | 3%nat => a = ch_u C + h
| 4%nat => ch_p C + 3 * cnt <= a < ch_p C + 3 * cnt + 3 | _ => ch_x C + 4 * h <= a < ch_x C + 4 * h + 4 end) ->
mbyte ubs2segs memX a = mbyte ubs2segs memc a).
{ intros k x a Hx Ha Hown. apply KEEP; [apply (IC k); rewrite Hx; exact Ha|]. unfold ins_w. subst cnt.
assert (SEP : forall k' y, k <> k' -> nth_error (cht_blks C) k' = Some y -> forall lo hi, fst y <= lo -> hi <= fst y + snd y -> ~ (lo <= a < hi)).
{ intros k' y Hk Hy lo hi Hlo Hhi Hc. apply (AP k k' x y a Hk Hx Hy Ha). lia. }
destruct k as [|[|[|[|[|[|k]]]]]]; cbn in Hx; try (destruct k; discriminate Hx); injection Hx as <-; cbn [fst snd] in Ha;
intros [Wk|[Wp|[Wu|[Wx|[Wf|Wc]]]]].
all: try (apply Hown; solve [exact Wk | exact Wp | exact Wu | exact Wx | exact Wf | exact Wc]).
- apply (SEP 2%nat _ ltac:(lia) E2 (ch_h C + 3 * h) (ch_h C + 3 * h + 3)); [cbn; lia | cbn; lia | exact Wk].
- apply (SEP 4%nat _ ltac:(lia) E4 (ch_p C + 3 * ht_cnt (ch_H C)) (ch_p C + 3 * ht_cnt (ch_H C) + 3)); [cbn; lia | cbn; lia | exact Wp].
- apply (SEP 3%nat _ ltac:(lia) E3 (ch_u C + h) (ch_u C + h + 1)); [cbn; lia | cbn; lia | lia].
- apply (SEP 5%nat _ ltac:(lia) E5 (ch_x C + 4 * h) (ch_x C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wx].
- apply (SEP 1%nat _ ltac:(lia) E1 (ch_f C + 4 * h) (ch_f C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wf].
- apply (SEP 2%nat _ ltac:(lia) E2 (ch_h C + 3 * h) (ch_h C + 3 * h + 3)); [cbn; lia | cbn; lia | exact Wk].
- apply (SEP 4%nat _ ltac:(lia) E4 (ch_p C + 3 * ht_cnt (ch_H C)) (ch_p C + 3 * ht_cnt (ch_H C) + 3)); [cbn; lia | cbn; lia | exact Wp].
- apply (SEP 3%nat _ ltac:(lia) E3 (ch_u C + h) (ch_u C + h + 1)); [cbn; lia | cbn; lia | lia].
- apply (SEP 5%nat _ ltac:(lia) E5 (ch_x C + 4 * h) (ch_x C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wx].
- apply (SEP 0%nat _ ltac:(lia) E0 (ch_c C + 40) (ch_c C + 44)); [cbn; lia | cbn; unfold CHT_SIZE; lia | exact Wc].
- apply (SEP 4%nat _ ltac:(lia) E4 (ch_p C + 3 * ht_cnt (ch_H C)) (ch_p C + 3 * ht_cnt (ch_H C) + 3)); [cbn; lia | cbn; lia | exact Wp].
- apply (SEP 3%nat _ ltac:(lia) E3 (ch_u C + h) (ch_u C + h + 1)); [cbn; lia | cbn; lia | lia].
- apply (SEP 5%nat _ ltac:(lia) E5 (ch_x C + 4 * h) (ch_x C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wx].
- apply (SEP 1%nat _ ltac:(lia) E1 (ch_f C + 4 * h) (ch_f C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wf].
- apply (SEP 0%nat _ ltac:(lia) E0 (ch_c C + 40) (ch_c C + 44)); [cbn; lia | cbn; unfold CHT_SIZE; lia | exact Wc].
- apply (SEP 2%nat _ ltac:(lia) E2 (ch_h C + 3 * h) (ch_h C + 3 * h + 3)); [cbn; lia | cbn; lia | exact Wk].
- apply (SEP 4%nat _ ltac:(lia) E4 (ch_p C + 3 * ht_cnt (ch_H C)) (ch_p C + 3 * ht_cnt (ch_H C) + 3)); [cbn; lia | cbn; lia | exact Wp].
- apply (SEP 5%nat _ ltac:(lia) E5 (ch_x C + 4 * h) (ch_x C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wx].
- apply (SEP 1%nat _ ltac:(lia) E1 (ch_f C + 4 * h) (ch_f C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wf].
- apply (SEP 0%nat _ ltac:(lia) E0 (ch_c C + 40) (ch_c C + 44)); [cbn; lia | cbn; unfold CHT_SIZE; lia | exact Wc].
- apply (SEP 2%nat _ ltac:(lia) E2 (ch_h C + 3 * h) (ch_h C + 3 * h + 3)); [cbn; lia | cbn; lia | exact Wk].
- apply (SEP 3%nat _ ltac:(lia) E3 (ch_u C + h) (ch_u C + h + 1)); [cbn; lia | cbn; lia | lia].
- apply (SEP 5%nat _ ltac:(lia) E5 (ch_x C + 4 * h) (ch_x C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wx].
- apply (SEP 1%nat _ ltac:(lia) E1 (ch_f C + 4 * h) (ch_f C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wf].
- apply (SEP 0%nat _ ltac:(lia) E0 (ch_c C + 40) (ch_c C + 44)); [cbn; lia | cbn; unfold CHT_SIZE; lia | exact Wc].
- apply (SEP 2%nat _ ltac:(lia) E2 (ch_h C + 3 * h) (ch_h C + 3 * h + 3)); [cbn; lia | cbn; lia | exact Wk].
- apply (SEP 4%nat _ ltac:(lia) E4 (ch_p C + 3 * ht_cnt (ch_H C)) (ch_p C + 3 * ht_cnt (ch_H C) + 3)); [cbn; lia | cbn; lia | exact Wp].
- apply (SEP 3%nat _ ltac:(lia) E3 (ch_u C + h) (ch_u C + h + 1)); [cbn; lia | cbn; lia | lia].
- apply (SEP 1%nat _ ltac:(lia) E1 (ch_f C + 4 * h) (ch_f C + 4 * h + 4)); [cbn; lia | cbn; lia | exact Wf].
- apply (SEP 0%nat _ ltac:(lia) E0 (ch_c C + 40) (ch_c C + 44)); [cbn; lia | cbn; unfold CHT_SIZE; lia | exact Wc]. }
unfold cht_ok, C_ins. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split. { cbn [ht_cnt ht_ins]. apply (obj_at_cht_set_cnt memc memX (ch_c C) _ _ _ _ _ (ht_cnt (ch_H C)) _ (ht_cnt (ch_H C) + 1) Hobj).
- intros a Ha Hna. apply (KEEPk 0%nat (ch_c C, CHT_SIZE)); [reflexivity | cbn; unfold CHT_SIZE; lia | exact Hna].
- exact S4.
- pose proof (ts_chain_ok _ Hch) as (T1 & T2 & T3). clear - C1 Hroom T1 T2. lia. }
split. { unfold cht_arrays. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_ins ht_cnt].
split; [|split; [|split; [|split]]].
- apply (arr32_update memc memX (ch_f C) (ht_frequ (ch_H C))); [exact Af | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j h) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact F4 | lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. intros k Hk. apply (KEEPk 1%nat (ch_f C, 4 * ch_T C)); [reflexivity | cbn; lia | lia].
- apply (arr8_update memc memX (ch_h C) (ht_keys (ch_H C))); [exact Ah | apply zlen_set_col |].
intros j Hj. rewrite getz_set_col by lia.
destruct (Z.eqb_spec j (3 * h)) as [->|N0]; [right; split; [exact K0 | lia]|].
destruct (Z.eqb_spec j (3 * h + 1)) as [->|N1]; [right; split; [rewrite Z.add_assoc; exact K1 | lia]|].
destruct (Z.eqb_spec j (3 * h + 2)) as [->|N2]; [right; split; [rewrite Z.add_assoc; exact K2 | lia]|].
left. split; [reflexivity|]. apply (KEEPk 2%nat (ch_h C, 3 * ch_T C)); [reflexivity | cbn; lia | lia].
- apply (arr8_update memc memX (ch_u C) (ht_used (ch_H C))); [exact Au | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j h) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact U1 | lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. apply (KEEPk 3%nat (ch_u C, ch_T C)); [reflexivity | cbn; lia | lia].
- apply (arr8_update memc memX (ch_p C) (ht_pal (ch_H C))); [exact Ap | apply zlen_set_col |].
intros j Hj. rewrite getz_set_col by lia. subst cnt.
destruct (Z.eqb_spec j (3 * ht_cnt (ch_H C))) as [->|N0]; [right; split; [exact P0 | lia]|].
destruct (Z.eqb_spec j (3 * ht_cnt (ch_H C) + 1)) as [->|N1]; [right; split; [rewrite Z.add_assoc; exact P1 | lia]|].
destruct (Z.eqb_spec j (3 * ht_cnt (ch_H C) + 2)) as [->|N2]; [right; split; [rewrite Z.add_assoc; exact P2 | lia]|].
left. split; [reflexivity|]. apply (KEEPk 4%nat (ch_p C, 3 * ch_T C)); [reflexivity | cbn; lia | lia].
- apply (arr32_update memc memX (ch_x C) (ht_colidx (ch_H C))); [exact Ax | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j h) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact X4 | subst cnt; pose proof (ts_chain_ok _ Hch) as (T1 & T2 & T3); clear - C1 T1 T2; lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. intros k Hk. apply (KEEPk 5%nat (ch_x C, 4 * ch_T C)); [reflexivity | cbn; lia | lia]. }
split; [apply (ht_ins_inv (ch_H C) (ch_ent C) Hinv h col 1 Hfs Hz Hcol ltac:(lia)); rewrite HT; exact Hroom|].
split; [exact HT|]. split; [exact Hch|]. split; [exact Rh|]. split; [exact Ru | exact Rt].
Qed.
End o.
Definition PC_L : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x390).
Definition PC_PX : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x3f8).
Definition PC_INS : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x490).
Definition PC_RT : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x5f0).
Definition PC_INC : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x934).
Section q.
Variable API : AllocAPI ubs2_msyms.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation HM := (hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation SP := (sp regs0).
Definition pxc (imgl : list Z) (i : Z) : colour := mkcol (getz imgl (fmt * i)) (getz imgl (fmt * i + 1)) (getz imgl (fmt * i + 2)).
Definition pxa (imgl : list Z) (i : Z) : Z := getz imgl (fmt * i + 3).
Definition opaque_px (imgl : list Z) (i : Z) : Prop := fmt = 4 -> 128 <= pxa imgl i.
Definition body_regs (regs1 : bvmap 5 word) (C : cht) (i : Z) : Prop :=
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 9 = Z_to_bv 64 i /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2.
Definition probe_regs (regs1 : bvmap 5 word) (C : cht) (i ha : Z) : Prop :=
getr regs1 23 = Z_to_bv 64 (img + fmt * i) /\ getr regs1 24 = Z_to_bv 64 (ch_h C) /\ getr regs1 25 = Z_to_bv 64 (ch_u C) /\
getr regs1 26 = Z_to_bv 64 (ch_T C).
Definition head_regs (regs1 : bvmap 5 word) : Prop :=
getr regs1 15 = Z_to_bv 64 fmt /\ getr regs1 16 = Z_to_bv 64 3 /\ getr regs1 17 = Z_to_bv 64 N /\
getr regs1 26 = Z_to_bv 64 img /\ getr regs1 27 = Z_to_bv 64 fmt.
Definition at_L (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (j : Z) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ opaque_px imgl i /\
(exists js, find_off (ch_H C) (pxc imgl i) = Some js /\ 0 <= j <= js) /\ usedz (ch_H C) (cyc (ch_T C) (hash0 (ch_T C) (pxc imgl i)) j) <> 0 /\
getr regs1 27 = Z_to_bv 64 (cyc (ch_T C) (hash0 (ch_T C) (pxc imgl i)) j) /\ getr regs1 22 = Z_to_bv 64 j /\
getr regs1 18 = Z_to_bv 64 (2 ^ 64 - 1 - ch_u C) /\
probe_regs regs1 C i ha /\ body_regs regs1 C i /\ slot regs0 memc SL_72 ha /\
HM Lc Ac memc pnew fimg imgl C i.
Definition at_PX (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (js : Z) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ opaque_px imgl i /\
find_off (ch_H C) (pxc imgl i) = Some js /\
getr regs1 27 = Z_to_bv 64 (cyc (ch_T C) (hash0 (ch_T C) (pxc imgl i)) js) /\ getr regs1 23 = Z_to_bv 64 (img + fmt * i) /\
body_regs regs1 C i /\ slot regs0 memc SL_72 ha /\
HM Lc Ac memc pnew fimg imgl C i.
Definition at_INS (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (h : Z) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ opaque_px imgl i /\
find_slot (ch_H C) (pxc imgl i) = Some h /\ usedz (ch_H C) h = 0 /\
getr regs1 10 = Z_to_bv 64 h /\ getr regs1 27 = Z_to_bv 64 h /\ getr regs1 18 = Z_to_bv 64 fmt /\
getr regs1 23 = Z_to_bv 64 (img + fmt * i) /\ body_regs regs1 C i /\ slot regs0 memc SL_72 ha /\
HM Lc Ac memc pnew fimg imgl C i.
Definition at_RT (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C' : cht) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 18 = Z_to_bv 64 fmt /\ body_regs regs1 C' i /\ slot regs0 memc SL_72 ha /\ HM Lc Ac memc pnew fimg imgl C' (i + 1).
Definition at_INC (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C' : cht) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
hist_regs r fmt regs1 i ha C' /\ HM Lc Ac memc pnew fimg imgl C' (i + 1).
Lemma rgba_inv_mem : forall Lc Ac (memc memX : word -> option byte) mdc,
RINV Lc Ac memc mdc ->
journal ubs2_msyms (aa_MR API) RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac memX mdc ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (SP <= a < SP + 5064) -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
RINV Lc Ac memX mdc.
Proof.
intros Lc Ac memc memX mdc (HJ & Hinit & Hfrm & Hra & Hal & Htp & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & HINV') HJ' KH.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & _). pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRv : RGBA_STK = 24576) by reflexivity.
split; [exact HJ'|]. split; [exact Hinit|]. split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Htp|].
split. { intros j rr Hj k Hk. assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite KH; [exact (HRA j rr Hj k Hk) | unfold sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros k Hk. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro | exact HINV'].
Qed.
End q.
Lemma st_chunk_val_g : forall E ss ms i rg p off (n : N) e a v,
st_ok ubs2segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem ubs2segs (ms_mem ms) (a + off) (N.to_nat n) v.
Proof.
intros E ss ms i rg p off n e a v HS Hi Hb Hin Hp He Hv Hn.
pose proof (mem_ok_region ubs2segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok ubs2segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
exact (val_of_chunk_ok ubs2segs E (ms_mem ms) a off n e v Hc He Hv Hn).
Qed.

Lemma cht_blks_pos : forall C b, In (ch_T C) ts_chain -> In b (cht_blks C) -> 0 < snd b.
Proof.
intros C b Hch Hb. pose proof (ts_chain_ok _ Hch) as (T1 & _). unfold cht_blks, cht_blocks in Hb. cbn [In] in Hb.
unfold CHT_SIZE in Hb. decompose [or] Hb; subst; cbn; lia.
Qed.
Lemma cht_apart_blocks : forall C (i j : nat) x y,
cht_apart C -> (i < j)%nat -> nth_error (cht_blks C) i = Some x -> nth_error (cht_blks C) j = Some y ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros C i j x y CA Hij Hi Hj.
destruct (nth_error_split _ _ Hi) as (l1 & l2 & E & Hl1).
apply (CA l1 x l2 y E). apply in_app_iff. right. rewrite E in Hj. rewrite nth_error_app2 in Hj by lia.
replace (j - length l1)%nat with (S (j - length l1 - 1)) in Hj by lia. cbn in Hj. eapply nth_error_In. exact Hj.
Qed.
Section t.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word).
Variables (r g bef beffmt : Z) (s : cgif_st) (N img fmt : Z) (rest : list (Z * Z)).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Lemma sep_base_cht_blk : forall Lc Ac memc mdc pnew fimg C (y b : Z * Z),
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C) ->
In y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) -> In b (cht_blks C) ->
fst b + snd b <= fst y \/ fst y + snd y <= fst b.
Proof.
intros Lc Ac memc mdc pnew fimg C y b HH HP Hy Hb.
apply in_split in Hb as (c1 & c2 & Ec). rewrite Ec, app_assoc in HP.
replace ((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ c1 ++ b :: c2) with (((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ c1) ++ b :: c2) in HP by (rewrite <- app_assoc; reflexivity).
apply (perm_sep API Lc Ac memc mdc b y _ _ HH HP). apply in_app_iff. left. apply in_app_iff. left. exact Hy.
Qed.
Lemma wr_byte_cht : forall Lc Ac memc mdc pnew fimg C a,
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C) ->
Permutation (blocks L A) BASE0 -> In (ch_T C) ts_chain -> in_cht C a ->
wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a.
Proof.
intros Lc Ac memc mdc pnew fimg C a HH HP HP0 Hch ([b n] & Hb & Ha). cbn [fst snd] in Ha.
right. right. exists b, n. split; [|split; [|exact Ha]].
- eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
- apply (tmp_not_entry API L A Lc Ac memc mdc (b, n) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ cht_blks C) HH HP HP0).
+ apply in_app_iff. right. exact Hb.
+ exact (cht_blks_pos C (b, n) Hch Hb).
Qed.
End t.
End d.
