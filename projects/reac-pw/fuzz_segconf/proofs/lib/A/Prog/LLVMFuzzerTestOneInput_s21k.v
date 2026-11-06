(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB_Base.v, with its module paths and module names changed; 366 of its 445 lines of code are new or changed and 1934 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of _s21 of the walk of
   the test harness's entry function LLVMFuzzerTestOneInput (segment S13, 0x857cc .. 0x858f0, proved in
   LLVMFuzzerTestOneInput_s21.v). Model facts (vlan_init, cap, the inlined m_declared at turn 0 and over no segment),
   the byte encodings of the two seeded VLAN tables, and the facts that keep a cut's state across a stretch that
   writes only bytes of the set s21_X: the two tables, the shadow byte of the frame object n, n itself, the
   runtime's window below sp and the s1 slots 96 .. 143. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_inst
LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_file_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the model ============================================ *)
Lemma s21_cap_rng : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2].
destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.
Lemma s21_nth_repeat : forall {A} (x d : A) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof. intros A x d n. induction n as [|n IH]; intros [|i] Hi; cbn; try lia; [reflexivity | apply IH; lia]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s21_xcap_rng : forall cx, 0 <= x_cap cx < 40.
Proof. intros cx. exact (s21_cap_rng (x_pl cx)). Qed.
(* vlan_init: the seeded entry ("enp1s0", 33) when flags & 1 and cap > 0 *)
Lemma s21_tab0_eq : forall cx, x_tab0 cx =
  if negb (Z.land (x_flags cx) 1 =? 0) && (0 <? x_cap cx) then [(SegModel.S_enp, 33)] else [].
Proof. intros cx. reflexivity. Qed.
Lemma s21_tab0_nil_f : forall cx, Z.land (x_flags cx) 1 = 0 -> x_tab0 cx = [].
Proof. intros cx H. rewrite s21_tab0_eq, H. reflexivity. Qed.
Lemma s21_tab0_nil_c : forall cx, x_cap cx = 0 -> x_tab0 cx = [].
Proof. intros cx H. rewrite s21_tab0_eq, H. cbn. destruct (negb _); reflexivity. Qed.
Lemma s21_tab0_one : forall cx, Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 ->
  x_tab0 cx = [(SegModel.S_enp, 33)].
Proof.
intros cx H1 H2. rewrite s21_tab0_eq. pose proof (s21_xcap_rng cx).
replace (Z.land (x_flags cx) 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
replace (0 <? x_cap cx) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* the inlined m_declared before its first turn, and over no segment *)
Lemma s21_decl0 : forall cx, x_decl cx 0 = (0, x_tab0 cx).
Proof. intros cx. reflexivity. Qed.
Lemma s21_declared_nil : forall cx, SegModel.mc_seg (x_mcF cx) = [] ->
  SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx) = (0, x_tab0 cx).
Proof. intros cx H. unfold SegModel.m_declared. rewrite H. reflexivity. Qed.

(* ============================================ bytes ============================================ *)
Lemma s21_rdword_rng : forall H (mem : word -> option byte) a v,
  rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply sa_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
Lemma s21_zs_keep : forall (rd rd' : reader) a l, sa_zs rd a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> sa_zs rd' a l.
Proof. intros rd rd' a l H HK i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s21_val_keep : forall (rd rd' : reader) a n v, sa_val rd a n v ->
  (forall i, 0 <= i < Z.of_nat n -> rd' (a + i) = rd (a + i)) -> sa_val rd' a n v.
Proof. intros rd rd' a n v H HK k Hk. rewrite HK by lia. exact (H k Hk). Qed.
Lemma s21_bytes_keep : forall (rd rd' : reader) a bs, sa_bytes rd a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs H HK k Hk. rewrite HK by lia. exact (H k Hk). Qed.
Lemma s21_rdword_keep : forall (rd rd' : reader) a v, rdword rd a = Some v ->
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = Some v.
Proof. intros rd rd' a v H HK. rewrite (rdword_ext rd rd' a HK). exact H. Qed.
Lemma s21_zs_app : forall (rd : reader) a l1 l2, sa_zs rd a l1 -> sa_zs rd (a + Z.of_nat (length l1)) l2 ->
  sa_zs rd a (l1 ++ l2).
Proof.
intros rd a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. exact (H1 i Hl).
- rewrite app_nth2 by exact Hg.
  replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
  apply H2. lia.
Qed.
Lemma s21_zs_repeat0 : forall (rd : reader) a n, (forall i, 0 <= i < Z.of_nat n -> rd (a + i) = Some 0) ->
  sa_zs rd a (repeat 0 n).
Proof.
intros rd a n H i Hi. rewrite repeat_length in Hi. rewrite s21_nth_repeat by exact Hi. apply H. lia.
Qed.
Lemma s21_bytes_of_zs : forall (rd : reader) a l, sa_zs rd a l -> Forall (fun z => 0 <= z < 256) l ->
  sa_bytes rd a (map (Z_to_bv 8) l).
Proof.
intros rd a l H HF i Hi. rewrite length_map in Hi. unfold ZB0.
rewrite (map_nth (Z_to_bv 8) l 0 i). rewrite (H i Hi). f_equal.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256.
rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hi.
Qed.

(* the two seeded entries, as the code leaves them: tab[0] = "enp1s0", NUL, 9 bytes of calloc's zeros, vid 33 as
   2 bytes; mt[0] = the same 16 bytes, vid 33 as 4 bytes *)
Definition S21_TABZ : list Z := (SegModel.S_enp ++ [0]) ++ repeat 0 9 ++ [33; 0].
Definition S21_MTZ : list Z := (SegModel.S_enp ++ [0]) ++ repeat 0 9 ++ [33; 0; 0; 0].
Lemma s21_TABZ_rng : Forall (fun z => 0 <= z < 256) S21_TABZ.
Proof. vm_compute. repeat constructor; discriminate. Qed.
Lemma s21_MTZ_rng : Forall (fun z => 0 <= z < 256) S21_MTZ.
Proof. vm_compute. repeat constructor; discriminate. Qed.
Lemma s21_cstr_enp : forall f, f = firstn 16 (map (Z_to_bv 8) S21_TABZ) \/ f = firstn 16 (map (Z_to_bv 8) S21_MTZ) ->
  seg_spec.cstr_enc 16 SegModel.S_enp f.
Proof.
intros f [-> | ->]; unfold seg_spec.cstr_enc; (split; [reflexivity|]); (split; [cbn; lia|]);
(split; [vm_compute; intros Hin; repeat (destruct Hin as [Hin|Hin]; [discriminate Hin|]); exact Hin | vm_compute; reflexivity]).
Qed.
Lemma s21_rtab_enc : seg_spec.rtab_enc [(SegModel.S_enp, 33)] (map (Z_to_bv 8) S21_TABZ).
Proof.
split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
cbn [nth fst snd]. unfold seg_spec.rvlan_enc. cbn [fst snd].
split; [reflexivity|]. split.
- apply s21_cstr_enp. left. reflexivity.
- split; [lia | vm_compute; reflexivity].
Qed.
Lemma s21_mtab_enc : seg_spec.mtab_enc [(SegModel.S_enp, 33)] (map (Z_to_bv 8) S21_MTZ).
Proof.
split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
cbn [nth fst snd]. unfold seg_spec.mvlan_enc. cbn [fst snd].
split; [reflexivity|]. split.
- apply s21_cstr_enp. right. reflexivity.
- split; [lia | vm_compute; reflexivity].
Qed.
Lemma s21_rtab_nil : forall rd a, sa_rtab rd a [].
Proof. intros rd a. exists []. split; [intros i Hi; cbn in Hi; lia | split; [reflexivity | intros i Hi; cbn in Hi; lia]]. Qed.
Lemma s21_mtab_nil : forall rd a, sa_mtab rd a [].
Proof. intros rd a. exists []. split; [intros i Hi; cbn in Hi; lia | split; [reflexivity | intros i Hi; cbn in Hi; lia]]. Qed.
(* tab[0] from its parts: the 7 bytes memcpy copied from the literal, calloc's zeros, the 2-byte vid *)
Lemma s21_rtab_one : forall (rd : reader) tab,
  sa_zs rd tab (SegModel.S_enp ++ [0]) -> (forall i, 7 <= i < 16 -> rd (tab + i) = Some 0) ->
  sa_val rd (tab + 16) 2 33 -> sa_rtab rd tab [(SegModel.S_enp, 33)].
Proof.
intros rd tab H1 H2 H3. exists (map (Z_to_bv 8) S21_TABZ). split; [|exact s21_rtab_enc].
apply s21_bytes_of_zs; [|exact s21_TABZ_rng]. unfold S21_TABZ. apply s21_zs_app; [exact H1|].
apply s21_zs_app.
- apply s21_zs_repeat0. intros i Hi. change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7.
  replace (tab + 7 + i) with (tab + (7 + i)) by lia. apply H2. change (Z.of_nat 9) with 9 in Hi. lia.
- change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7. change (Z.of_nat (length (repeat 0 9))) with 9.
  intros i Hi. cbn [length] in Hi. replace (tab + 7 + 9) with (tab + 16) by lia.
  destruct i as [|[|i]]; [| |lia].
  + exact (H3 0%nat ltac:(lia)).
  + exact (H3 1%nat ltac:(lia)).
Qed.
Lemma s21_mtab_one : forall (rd : reader) mt,
  sa_zs rd mt (SegModel.S_enp ++ [0]) -> (forall i, 7 <= i < 16 -> rd (mt + i) = Some 0) ->
  sa_val rd (mt + 16) 4 33 -> sa_mtab rd mt [(SegModel.S_enp, 33)].
Proof.
intros rd mt H1 H2 H3. exists (map (Z_to_bv 8) S21_MTZ). split; [|exact s21_mtab_enc].
apply s21_bytes_of_zs; [|exact s21_MTZ_rng]. unfold S21_MTZ. apply s21_zs_app; [exact H1|].
apply s21_zs_app.
- apply s21_zs_repeat0. intros i Hi. change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7.
  replace (mt + 7 + i) with (mt + (7 + i)) by lia. apply H2. change (Z.of_nat 9) with 9 in Hi. lia.
- change (Z.of_nat (length (SegModel.S_enp ++ [0]))) with 7. change (Z.of_nat (length (repeat 0 9))) with 9.
  intros i Hi. cbn [length] in Hi. replace (mt + 7 + 9) with (mt + 16) by lia.
  destruct i as [|[|[|[|i]]]]; [| | | |lia].
  + exact (H3 0%nat ltac:(lia)).
  + exact (H3 1%nat ltac:(lia)).
  + exact (H3 2%nat ltac:(lia)).
  + exact (H3 3%nat ltac:(lia)).
Qed.
(* the guard entry tab[cap]: memset's 18 bytes of 0x5a *)
Lemma s21_guard : forall (rd : reader) tab cap, (forall i, 0 <= i < 18 -> rd (tab + 18 * cap + i) = Some (90 mod 256)) ->
  sa_guardtab rd tab cap.
Proof.
intros rd tab cap H i Hi. unfold seg_spec.GUARD_BYTES in *. rewrite repeat_length in Hi.
rewrite s21_nth_repeat by exact Hi. unfold seg_spec.RVLAN_SIZE. rewrite H by lia. reflexivity.
Qed.

(* ============================================ the image facts ============================================ *)
Section e.
Context {B : asyms} {MT : ameter_ops}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma s21_img_rng : forall a, in_img SEGS a -> 0x10000 <= a < kImgEnd.
Proof. intros a H. exact (pa_img_range _ H). Qed.
Lemma s21_imgobj_rng : forall q n x, sa_img SEGS B q n -> q <= x < q + n -> 0x10000 <= x < kImgEnd.
Proof. intros q n x H Hx. exact (s21_img_rng x (proj1 (H x Hx))). Qed.
Lemma s21_lit_keep : forall H (mem : word -> option byte) H' (mem' : word -> option byte) a s,
  sa_lit SEGS B (aview SEGS H mem) a s ->
  (forall x, 0x10000 <= x < kImgEnd -> aview SEGS H' mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H' mem') a s.
Proof.
intros H mem H' mem' a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi) HK.
split; [exact Ha|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS H' mem' _ Hr)].
apply (s21_zs_keep _ _ _ _ Hz). intros i Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
apply HK. apply (s21_imgobj_rng a (Z.of_nat (length s) + 1)); [exact Hi | lia].
Qed.
Lemma s21_img_keep : forall cx H (mem : word -> option byte) H' (mem' : word -> option byte),
  lt_img B cx (aview SEGS H mem) ->
  (forall x, 0x10000 <= x < kImgEnd -> aview SEGS H' mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H' mem').
Proof.
intros cx H mem H' mem' (HRO & HIMG & HGI) HK.
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & (Hcp & Hci & Hrows) & Hcap & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) &
  (Hgw & (g & Hgd)) & Hlp & Hlt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Hno Her. rewrite HK; [exact (HRO a Hro Hno Her)|].
  destruct Hro as [(sg & Hsg & _ & Hlo) | Hr].
  + apply s21_img_rng. exists sg. split; [exact Hsg | exact Hlo].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgEnd. lia.
- split; [apply (s21_val_keep _ _ _ _ _ Hm40); intros i Hi; apply HK; unfold mod40A, kImgEnd; cbn in Hi; lia|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [Hl Hap]; split; [exact (s21_lit_keep _ _ _ _ _ _ Hl HK) | exact Hap]|].
  split; [intros s Hs; destruct (Hrc s Hs) as [Hl Hap]; split; [exact (s21_lit_keep _ _ _ _ _ _ Hl HK) | exact Hap]|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl).
    exists tp. split; [|exact (s21_lit_keep _ _ _ _ _ _ Hl HK)].
    apply (s21_rdword_keep _ _ _ _ Htp). intros k Hk. apply HK.
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA, kImgEnd. unfold pin_spec.CAT_N in Hi. lia. }
  split; [exact Hcap|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hw & Hl).
    exists wp. split; [|exact (s21_lit_keep _ _ _ _ _ _ Hl HK)].
    apply (s21_rdword_keep _ _ _ _ Hw). intros k Hk. apply HK. unfold wordsA, kImgEnd. lia. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi.
    apply (s21_val_keep _ _ _ _ _ (Hrr i Hi)). intros k Hk. apply HK. unfold rolesA, kImgEnd. cbn in Hk. lia. }
  split.
  { split.
    - apply (s21_rdword_keep _ _ _ _ Hgw). intros k Hk. apply HK. unfold gotwA, kImgEnd. lia.
    - exists g. apply (s21_rdword_keep _ _ _ _ Hgd). intros k Hk. apply HK. unfold guardA, kImgEnd. lia. }
  repeat (split; [assumption|]). assumption.
- intros i Hi. rewrite HK; [exact (HGI i Hi)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.

(* ============================================ blocks and the frame ============================================ *)
Lemma s21_pw_nodup : forall (l : list (Z * Z)), pairwise zdisjoint l -> (forall x, In x l -> 0 < snd x) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros Hp Hpos; [constructor|]. destruct Hp as [Hx Ht]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). unfold zdisjoint in Hx.
  specialize (Hpos x (or_introl eq_refl)). lia.
- apply IH; [exact Ht | intros y Hy; apply Hpos; right; exact Hy].
Qed.
Lemma s21_ablocks_NoDup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s21_pw_nodup; [exact Hpw|].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.
Lemma s21_nodup_app : forall {A} (l1 l2 : list A) a, List.NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
intros A l1. induction l1 as [|b l1 IH]; intros l2 a H H1 H2; [destruct H1|].
cbn [app] in H. apply List.NoDup_cons_iff in H as [Hn Hd].
destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 a Hd H1 H2)].
Qed.
(* a harness block: live, apart from the entry's blocks *)
Lemma s21_blk_new : forall cx ly S (W : world SEGS) mem md O p n,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S O -> In (p, n) O ->
  In (p, n) (ablocks B ly S) /\ ~ In (p, n) (x_bl0 B cx).
Proof.
intros cx ly S W mem md O p n HAR HP Hin. split.
- exact (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_introl Hin))).
- pose proof (Permutation_NoDup HP (s21_ablocks_NoDup ly S W mem md HAR)) as HND.
  exact (s21_nodup_app _ _ _ HND Hin).
Qed.
(* a harness block from the allocator invariant *)
Lemma s21_hblk_of_AR : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> 0 < n -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Hn.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hp. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hp).
Qed.
(* the frame's bytes are off the image *)
Lemma s21_frame_offimg : forall ly S (W : world SEGS) mem md cid pos a,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ (0x10000 <= a < kImgEnd).
Proof.
intros ly S W mem md cid pos a HAR Hin Ha Hi.
pose proof HAR as (M & LG & _). pose proof (pa_img_cover ly S md LG) as [C1 C2].
destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [Hz _].
{ right. left. exists cid, pos. split; [exact Hin | exact Ha]. }
apply Hz. unfold in_zr. lia.
Qed.

(* ============================================ the cut's numbers ============================================ *)
(* the entry sp, the base register s1, the class-3 frame and its shadow *)
Lemma s21_nums : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320 /\
  frames S = [(LT_FCLS, x_fpos cx)] /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ x_fr cx mod 32 = 0 /\ in_app (x_fr cx) 512 /\
  x_sh cx = SHADOW_OFF + x_fr cx / 8 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof HF as (HJ & _).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
rewrite Hfr0, app_nil_r in Hfrs.
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite WS in Hslo.
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR Hin) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (F4 & F5 & _).
(* the journal's layout is the entry's in the frame's address *)
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr. destruct (al_layout _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) ly (proj1 HPRE) Hly) as (_ & Efa & _).
  apply Efa. }
rewrite EF in F1, F2, F3, F4, F5. change (fs_frame_bytes LT_FCLS) with 512 in F2, F3, F5.
unfold x_s1, x_sp0, LT_FRAME in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 320) 32 ltac:(lia)).
split; [exact Hal16|]. split; [lia|].
split; [replace (spZ (x_regs cx) - 320 - (spZ (x_regs cx) - 320) mod 32) with ((spZ (x_regs cx) - 320) / 32 * 32)
  by (pose proof (Z_div_mod_eq_full (spZ (x_regs cx) - 320) 32); lia); apply Z_mod_mult|].
split; [lia|]. split; [exact Hfrs|].
split; [lia|]. split; [lia|]. split; [exact F4|]. split; [exact F5|].
split; [unfold x_sh, shadow_addr; reflexivity | exact C1].
Qed.

(* ============================================ what the segment writes ============================================ *)
(* the bytes the stretch 0x857cc .. 0x858f0 may change: the two tables, the shadow byte of n, n, the runtime's window
   below sp and the s1 slots 96 .. 143 *)
Definition s21_X (cx : lcx) (tab mt : Z) (a : Z) : Prop :=
  (tab <= a < tab + req_size (x_tabn cx)) \/ (mt <= a < mt + req_size (x_mtn cx)) \/ a = x_sh cx + 32 \/
  (x_fr cx + 256 <= a < x_fr cx + 260) \/ (x_s1 cx - 4096 <= a < x_s1 cx) \/ (x_s1 cx + 96 <= a < x_s1 cx + 144).

(* the facts of a cut that no byte of s21_X touches *)
Lemma s21_X_apart : forall cx ly S (W : world SEGS) regs mem md k o tab mt,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  In (tab, x_tabn cx) (ablocks B ly S) -> In (mt, x_mtn cx) (ablocks B ly S) ->
  (forall a, 0x10000 <= a < kImgEnd -> ~ s21_X cx tab mt a) /\
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> ~ s21_X cx tab mt a) /\
  (forall a, (x_fr cx <= a < x_fr cx + 24) \/ (x_fr cx + 504 <= a < x_fr cx + 512) -> ~ s21_X cx tab mt a) /\
  (forall a, x_s1 cx <= a < x_s1 cx + 96 \/ x_s1 cx + 144 <= a < x_s1 cx + 192 -> ~ s21_X cx tab mt a) /\
  (forall p n a, In (p, n) (ablocks B ly S) -> (p, n) <> (tab, x_tabn cx) -> (p, n) <> (mt, x_mtn cx) ->
     p <= a < p + req_size n -> ~ s21_X cx tab mt a).
Proof.
intros cx ly S W regs mem md k o tab mt HB HF Htab Hmt.
destruct (s21_nums cx ly S W regs mem md k o HB HF) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF as (HJ & _). pose proof (proj1 HJ) as HAR.
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Nfr; left; reflexivity).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR Htab) as (T1 & T2 & T3 & T4 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR Hmt) as (M1 & M2 & M3 & M4 & _).
pose proof (blk_off_imgP B ly S W mem md tab _ HAR Htab) as To.
pose proof (blk_off_imgP B ly S W mem md mt _ HAR Hmt) as Mo.
unfold off_img in To, Mo.
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr. pose proof HB as (HPRE & _).
  destruct (al_layout _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) ly (proj1 HPRE) (proj1 (proj2 HJ))) as (_ & Efa & _).
  apply Efa. }
pose proof (sep_block_frame SEGS B LAWS ly S W mem md tab _ _ _ HAR Htab Hin) as Dt.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md mt _ _ _ HAR Hmt Hin) as Dm.
rewrite EF in Dt, Dm. unfold zdisjoint in Dt, Dm. cbn [fst snd] in Dt, Dm. change (fs_frame_bytes LT_FCLS) with 512 in Dt, Dm.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt].
pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold s21_X. unfold SHADOW_OFF in Hsh.
split; [|split; [|split; [|split]]].
- intros a Ha Hx. unfold kImgEnd in Ha. pose proof (s21_frame_offimg ly S W mem md _ _ a HAR Hin) as Hfo.
  rewrite EF in Hfo. change (fs_frame_bytes LT_FCLS) with 512 in Hfo. unfold kImgEnd in Hfo.
  destruct Hx as [H|[H|[H|[H|[H|H]]]]]; [lia | lia | lia | apply Hfo; [lia | lia] | lia | lia].
- intros a Ha Hx. destruct Hx as [H|[H|[H|[H|[H|H]]]]]; lia.
- intros a Ha Hx. destruct Hx as [H|[H|[H|[H|[H|H]]]]]; lia.
- intros a Ha Hx. destruct Hx as [H|[H|[H|[H|[H|H]]]]]; lia.
- intros p n a Hpn Hnt Hnm Ha Hx.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hpn) as (P1 & P2 & P3 & P4 & _).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p n tab _ HAR Hpn Htab Hnt) as D1.
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p n mt _ HAR Hpn Hmt Hnm) as D2.
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n _ _ HAR Hpn Hin) as D3.
  rewrite EF in D3. unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3.
  change (fs_frame_bytes LT_FCLS) with 512 in D3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in P4.
  destruct Hx as [H|[H|[H|[H|[H|H]]]]]; lia.
Qed.

(* the cut's frame part kept: the registers, the saved words, the header words, 176(s1); the frame's shadow as given *)
Lemma s21_frame_keep : forall cx ly S (W : world SEGS) regs mem md k o regs' mem' md' o' (X : Z -> Prop),
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> rdW W mem' a = rdW W mem a) ->
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> ~ X a) ->
  (forall a, (x_fr cx <= a < x_fr cx + 24) \/ (x_fr cx + 504 <= a < x_fr cx + 512) -> ~ X a) ->
  (forall a, x_s1 cx + 176 <= a < x_s1 cx + 184 -> ~ X a) ->
  sa_zs (rdW W mem') (x_sh cx) (lt_fsh o') ->
  lt_frame B cx ly S W regs' mem' md' k o'.
Proof.
intros cx ly S W regs mem md k o regs' mem' md' o' X HB HF HJ' E2 E3 E4 E8 E9 HK X1 X2 X3 HSH.
destruct (s21_nums cx ly S W regs mem md k o HB HF) as (N1 & N2 & N3 & N4 & _ & N5 & N6 & _).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HD0 & HD8 & HD16 & HFL & H176 & _).
pose proof asan_consts as (C1 & _).
split; [exact HJ'|].
split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split.
{ intros i r Hi. pose proof (HSV i r Hi) as H.
  assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  cbn [LT_SAVED length] in Hi13.
  apply (s21_rdword_keep _ _ _ _ H). intros j Hj. apply HK; [lia|]. apply X1. lia. }
split; [apply (s21_rdword_keep _ _ _ _ HD0); intros j Hj; apply HK; [lia | apply X2; lia]|].
split; [apply (s21_rdword_keep _ _ _ _ HD8); intros j Hj; apply HK; [lia | apply X2; lia]|].
split; [apply (s21_rdword_keep _ _ _ _ HD16); intros j Hj; apply HK; [lia | apply X2; lia]|].
split; [apply (s21_rdword_keep _ _ _ _ HFL); intros j Hj; apply HK; [unfold LT_FLAGW; lia | apply X2; unfold LT_FLAGW; lia]|].
split; [apply (s21_rdword_keep _ _ _ _ H176); intros j Hj; apply HK; [lia | apply X3; lia]|].
exact HSH.
Qed.

(* the cut's core kept (same layout, state, events, budget) *)
Lemma s21_core_keep : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' o' tab mt,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  In (tab, x_tabn cx) (ablocks B ly S) -> In (mt, x_mtn cx) (ablocks B ly S) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_X cx tab mt a -> rdW W mem' a = rdW W mem a) ->
  sa_zs (rdW W mem') (x_sh cx) (lt_fsh o') ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o' O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' o' tab mt HB (HF & HI & HBL & HBUD) Htab Hmt HJ'
  E2 E3 E4 E8 E9 HK HSH.
destruct (s21_X_apart cx ly S W regs mem md k o tab mt HB HF Htab Hmt) as (A1 & A2 & A3 & A4 & _).
split; [|split; [|split; [exact HBL | exact HBUD]]].
- apply (s21_frame_keep cx ly S W regs mem md k o regs' mem' md' o' (s21_X cx tab mt) HB HF HJ' E2 E3 E4 E8 E9 HK
    A2 A3); [|exact HSH].
  intros a Ha. apply A4. right. lia.
- apply (s21_img_keep cx (w_H W) mem (w_H W) mem' HI). intros x Hx. apply HK; [unfold kImgEnd in Hx; lia | apply A1; exact Hx].
Qed.

(* the c and m blocks kept *)
Lemma s21_cm_keep : forall (rd rd' : reader) c m st, lt_cm rd c m st ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) ->
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st ((bs1 & Hb1 & He1) & (bs2 & Hb2 & He2)) Hc Hm.
pose proof (proj1 He1) as L1. pose proof (proj1 He2) as L2.
split; [exists bs1 | exists bs2]; (split; [|assumption]).
- apply (s21_bytes_keep _ _ _ _ Hb1). intros i Hi. apply Hc. lia.
- apply (s21_bytes_keep _ _ _ _ Hb2). intros i Hi. apply Hm. lia.
Qed.

End e.
End f.
End d.
