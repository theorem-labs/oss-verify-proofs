(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): one pass of the member loop, from the loop head KL
   (0x8e234) at pass j: the inline load8 check of &tok[2 + j] (0x8e234-0x8e238), the call of number at 0x8e244
   (through cl_callS_wide, PaNoChain.v) that writes ids[j] in this walk's class-3 side-stack frame, the refusal edge
   `beqz a0` at 0x8e248 (to KR, 0x8e278), the advance 0x8e24c-0x8e25c and `bnez s11` at 0x8e260, which re-enters
   KL at pass j + 1 or falls through to KD (0x8e264). The symbolic machinery (the cut-point seed, the call, the
   re-seat after it) is the one of the sibling segment chain_words_s2.v (KC -> KL 0), which walks the same inline
   check and the same call once, for the first word; its lemmas are copied here with the prefix cw3_ and generalised
   over the pass index. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s3.v, with its module paths and module names changed; 887 of its 1005 lines of code are new or changed and 755 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_declared_s2.v, with its module paths changed; 468 of its 549 lines of code are new or changed and 924 lines of the source are left out. *)
(* Facts segment S2 of the image-B walk of reac_segconf_declared uses (fuzz_segconf.asan-ubsan; interface
   reac_segconf_declared_d.v; the walk itself is reac_segconf_declared_s2.v): what a cut state of the walk holds
   that the cut invariants do not state, and what the call of reac_declared_vlan_split at 0x8a040 asks.
   - c's block (the reader's struct reac_segconf) reads at a cut as at the entry: the journal's block clause keeps
     every byte of a live block outside the footprint, and declared_pre keeps the table and the count cell apart
     from c (dcs2_cblk). So seg[i].ignore (+ 24) and seg[i].name (+ 0) read as declared_pre's sa_rconf gives them.
   - the read-only window reads at a cut as at the entry (dcs2_aro): the journal's image clause, with RO_IMG (the
     window lies in the image), RO (it lies below the sink head) and the footprint off the image.
   - the frame chain at s0 = sp0 for the call (dcs2_chain): the record the prologue stored at sp0 - 8 / sp0 - 16
     pushed on the entry's chain when the footprint lies below the allocator's ceiling (count cell in a frame or a
     heap block), else astack_rd from the real-stack arm's astack_pres (achain_any).
   - the zones of a cut the walk keeps (the saved registers, the slots of s1, the frame's flag word, the table and
     the count cell) lie outside the frame's shadow and outside split's window and write set.
   - split_pre at the call state (dcs2_split_pre). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa PaSB PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaCall PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* split writes parent[0 .. di] with di + 1 <= 16, and the vid cell *)
Lemma dcs2_split_copy_le : forall s di, split_copy s = Some di -> (di + 1 <= 16)%nat.
Proof.
intros s di. unfold split_copy. destruct (SegModel.strrchr s DOT) as [d|]; [|discriminate]. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  intros H; try discriminate H.
injection H as <-.
repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?] end.
match goal with H : (16 <? d + 1)%nat = false |- _ => apply Nat.ltb_ge in H end. lia.
Qed.
Lemma dcs2_split_E : forall parent vid s a, split_E parent vid s a ->
  (parent <= a < parent + 16) \/ (vid <= a < vid + 2).
Proof.
intros parent vid s a [H | H].
- left. destruct (split_copy s) as [di|] eqn:E; [|destruct H].
  pose proof (dcs2_split_copy_le s di E). lia.
- right. destruct (SegModel.vlan_split s); [exact H | destruct H].
Qed.
Lemma dcs2_split_W : forall parent vid s a, inFP (split_W parent vid s) a ->
  (parent <= a < parent + 16) \/ (vid <= a < vid + 2).
Proof.
intros parent vid s a (r & Hr & Ha). unfold split_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. destruct (split_copy s) as [di|] eqn:E; [|destruct Hr].
  pose proof (dcs2_split_copy_le s di E). destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia.
- right. destruct (SegModel.vlan_split s); [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia.
Qed.

(* the bytes of c->seg[i] through a reader, from seg_spec.rconf_enc (reac_segconf_role_lem.v's lemmas) *)
Lemma dcs2_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold le4, le_byte.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth];
    rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
    rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
Lemma dcs2_nth_firstn : forall (l : list byte) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d Hk; destruct n as [|n]; [lia | destruct k; reflexivity | lia |].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma dcs2_nth_skipn : forall (l : list byte) n k d, nth k (skipn n l) d = nth (n + k) l d.
Proof.
  induction l as [|x l IH]; intros n k d; [destruct n, k; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Lemma dcs2_nth_firstnZ : forall (l : list Z) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d Hk; destruct n as [|n]; [lia | destruct k; reflexivity | lia |].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* byte k of entry i *)
Lemma dcs2_seg_byte : forall (rd : reader) c bs rc i k,
  sa_bytes rd c bs -> seg_spec.rconf_enc rc bs -> (i < length (rc_seg rc))%nat -> (k < 356)%nat ->
  rd (c + 356 * Z.of_nat i + Z.of_nat k) = Some (bv_unsigned (nth k (seg_spec.fld (356 * i) 356 bs) ZB0)).
Proof.
  intros rd c bs rc i k HB HE Hi Hk.
  destruct HE as (L & LS & _). unfold seg_spec.SEG_C_SIZE in L.
  assert (Hlt : (356 * i + k < length bs)%nat) by lia.
  replace (c + 356 * Z.of_nat i + Z.of_nat k) with (c + Z.of_nat (356 * i + k)) by lia.
  rewrite (HB _ Hlt). f_equal. f_equal.
  unfold seg_spec.fld. rewrite dcs2_nth_firstn by lia. rewrite dcs2_nth_skipn. reflexivity.
Qed.
(* the ignore flag of c->seg[i]: 0 or 1 (seg_spec.flag_enc), its 4 bytes at + 0x18 *)
Lemma dcs2_rd_ign : forall (rd : reader) c rc i, sa_rconf rd c rc -> (i < length (rc_seg rc))%nat ->
  sa_val rd (c + 356 * Z.of_nat i + seg_spec.RS_IGNORE) 4 (if rs_ignore (nth i (rc_seg rc) rseg_d) then 1 else 0).
Proof.
  intros rd c rc i (bs & HB & HE) Hi.
  pose proof (proj1 (proj2 (proj2 HE)) i Hi) as HS.
  destruct HS as (_ & _ & _ & _ & HF & _).
  intros k Hk.
  replace (c + 356 * Z.of_nat i + seg_spec.RS_IGNORE + Z.of_nat k) with
    (c + 356 * Z.of_nat i + Z.of_nat (24 + k)) by (unfold seg_spec.RS_IGNORE; lia).
  rewrite (dcs2_seg_byte rd c bs rc i (24 + k) HB HE Hi ltac:(lia)).
  f_equal.
  replace (nth (24 + k) (seg_spec.fld (356 * i) 356 bs) ZB0) with
    (nth k (seg_spec.fldz seg_spec.RS_IGNORE 4 (seg_spec.fld (356 * i) 356 bs)) ZB0).
  - rewrite HF. apply dcs2_le4_byte; [destruct (rs_ignore (nth i (rc_seg rc) rseg_d)); lia | exact Hk].
  - set (X := seg_spec.fld (356 * i) 356 bs).
    unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat seg_spec.RS_IGNORE) with 24%nat.
    change (Z.to_nat 4) with 4%nat.
    rewrite dcs2_nth_firstn by lia. rewrite dcs2_nth_skipn. reflexivity.
Qed.
(* the name of c->seg[i]: a C string of fewer than 16 bytes at + 0, with the slack to the next 8-byte boundary
   mapped (it lies inside the 356 bytes of the entry) *)
Lemma dcs2_rd_name : forall (rd : reader) c bs rc i,
  sa_bytes rd c bs -> seg_spec.rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  sa_str rd (c + 356 * Z.of_nat i) (rs_name (nth i (rc_seg rc) rseg_d)) /\
  (length (rs_name (nth i (rc_seg rc) rseg_d)) < 16)%nat.
Proof.
  intros rd c bs rc i HB HE Hi.
  pose proof HE as (_ & _ & HSG & _).
  pose proof (HSG i Hi) as (_ & (Lc & Hlen & Hn0 & Hfz) & _).
  set (s := rs_name (nth i (rc_seg rc) rseg_d)) in *.
  split; [|exact Hlen].
  split; [split|].
  - intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
    rewrite (dcs2_seg_byte rd c bs rc i k HB HE Hi ltac:(lia)). f_equal.
    rewrite <- Hfz. rewrite dcs2_nth_firstnZ by lia. unfold seg_spec.zs.
    rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map; lia).
    rewrite map_nth.
    change (seg_spec.fld 0 16 (seg_spec.fld (356 * i) 356 bs)) with (firstn 16 (seg_spec.fld (356 * i) 356 bs)).
    rewrite dcs2_nth_firstn by lia. reflexivity.
  - exact Hn0.
  - intros x Hx.
    pose proof (Z.mod_pos_bound (c + 356 * Z.of_nat i + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
    replace x with (c + 356 * Z.of_nat i + Z.of_nat (Z.to_nat (x - c - 356 * Z.of_nat i))) by lia.
    rewrite (dcs2_seg_byte rd c bs rc i (Z.to_nat (x - c - 356 * Z.of_nat i)) HB HE Hi ltac:(lia)). discriminate.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* an application byte is not a shadow byte of a side-stack frame (chain_words_s3.v's cw3_app_shadow) *)
Lemma dcs2_app_shadow : forall x lo len g m i, in_app lo len -> lo <= x < lo + len ->
  4096 <= g -> g + m <= alloc_ceiling -> 0 <= i < m / 8 -> x <> shadow_addr g + i.
Proof.
intros x lo len g m i Happ Hx Hg Hgm Hi. pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *.
assert (D : 0 <= g / 8 /\ g / 8 + i <= (g + m) / 8) by (split; [apply Z.div_pos; lia|]; Z.div_mod_to_equations; lia).
assert (D2 : (g + m) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in D2. lia.
Qed.
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
#[local] Notation PRE := (dc_pre B DC_STK RLO RHI GOTW GUARD).
#[local] Notation JRN c ly3 S3 W3 m md3 k := (ajournal SEGS B DC_STK (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c)
  (x_mem c) (x_md c) [(1, x_fpos c)] ly3 S3 W3 m md3 k).

(* c's block reads at a cut as at the entry *)
Lemma dcs2_cblk : forall c ly3 S3 W3 m md3 k, PRE c -> JRN c ly3 S3 W3 m md3 k -> dc_un B c ly3 S3 ->
  forall j, 0 <= j < seg_spec.SEG_C_SIZE -> rdW W3 m (x_c c + j) = rdW (x_W c) (x_mem c) (x_c c + j).
Proof using.
intros c ly3 S3 W3 m md3 k HP HJ HU j Hj.
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & _ & (pb & nb & Hin & Hp1 & Hp2) & _ & HVT & HD1 & HD2 & _).
destruct HVT as (_ & _ & _ & Htbmax & _).
pose proof HU as [HPERM _ _].
assert (Hin3 : In (pb, nb) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
assert (L : (length (x_tb c) <= length (snd (dc_res c)))%nat /\ Z.of_nat (length (snd (dc_res c))) <= x_max c)
  by exact (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Htbmax)).
destruct L as [L1 L2].
unfold seg_spec.SEG_C_SIZE in Hp2, Hj. unfold sa_disj, seg_spec.SEG_C_SIZE, seg_spec.RVLAN_SIZE in HD1, HD2.
replace (x_c c + j) with (pb + (x_c c + j - pb)) by lia.
apply (K2 pb nb _ Hin Hin3).
- unfold req_size. destruct (Z.eqb_spec nb 0); lia.
- intros (r & Hr & Ha). unfold dc_FP, declared_W, vtab_W in Hr.
  apply in_app_or in Hr as [Hr | Hr].
  + destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in Ha.
    destruct HD1 as [HD1 | HD1]; lia.
  + destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|destruct Hr].
    destruct Hr as [<- | []]. cbn [fst snd] in Ha. destruct HD2 as [HD2 | HD2]; lia.
Qed.
Lemma dcs2_rconf_at : forall c ly3 S3 W3 m md3 k, PRE c -> JRN c ly3 S3 W3 m md3 k -> dc_un B c ly3 S3 ->
  exists bs, sa_bytes (rdW W3 m) (x_c c) bs /\ seg_spec.rconf_enc (x_rc c) bs.
Proof using.
intros c ly3 S3 W3 m md3 k HP HJ HU.
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & (bs & Hbs & Henc) & _).
exists bs. split; [|exact Henc].
pose proof Henc as (Hl & _). unfold seg_spec.SEG_C_SIZE in Hl.
intros kk Hk. rewrite (dcs2_cblk c ly3 S3 W3 m md3 k HP HJ HU) by (unfold seg_spec.SEG_C_SIZE; lia).
exact (Hbs kk Hk).
Qed.

(* the read-only window reads at a cut as at the entry: an image byte the footprint misses (the table's entries
   lie in a heap block and the count cell in a frame, a heap block or the real stack above sp0, none of them an
   image byte), below the sink head (RO), is kept by the journal's image clause *)
Lemma dcs2_aro : forall c ly3 S3 W3 m md3 k, dc_ro_imgP RLO RHI -> PRE c -> JRN c ly3 S3 W3 m md3 k ->
  arodata_okP SEGS RLO RHI B (rdW W3 m).
Proof using RO LAWS.
intros c ly3 S3 W3 m md3 k ROI HP HJ a Hro Hown Herr.
pose proof HP as [HAFN HROD _ _ _ _ _ _ _ _ HDP _ _].
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K3 & _).
assert (Himg : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hw]; [exists s; split; [exact Hs | lia] | exact (ROI a Hw)]. }
pose proof (pa_img_range a Himg) as HIR. unfold kImgEnd in HIR.
pose proof asan_consts as (C1 & _).
rewrite (K3 a Himg Hown Herr); [exact (HROD a Hro Hown Herr)|].
apply fp_spares_below; [unfold AOFL_HEAD; exact (ro_below_ofl_at a Hro)|].
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & Htbmax & (bt & mt & Hbt & Hbt1 & Hbt2) & _ & _ & _ & _ & _ & HDST & _).
assert (L : (length (x_tb c) <= length (snd (dc_res c)))%nat /\ Z.of_nat (length (snd (dc_res c))) <= x_max c)
  by exact (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Htbmax)).
destruct L as [L1 L2].
assert (BLK : forall b mm, In (b, mm) (ablocks B (x_ly c) (x_S c)) -> b <= a < b + mm -> False).
{ intros b mm Hb Hab. destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR0 Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos mm (proj1 Hm)) as [_ Hrq].
  exact (blk_img SEGS B LAWS _ _ _ _ _ b mm a HAR0 Hb ltac:(lia) Himg). }
intros (r & Hr & Ha). unfold dc_FP, declared_W, vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in *.
  apply (BLK bt mt Hbt). lia.
- destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|destruct Hr].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct HDST as [((cid & pos & Hcp & Hcid & Hf1 & Hf2) & _) | [((b & mm & Hb & Hb1 & Hb2) & _) | (Hsp & _)]].
  + exact (frm_img SEGS B LAWS _ _ _ _ _ cid pos a HAR0 Hcp ltac:(lia) Himg).
  + apply (BLK b mm Hb). lia.
  + lia.
Qed.

(* the frame chain at the call: s0 = sp0 *)
Lemma dcs2_chain : forall c ly3 S3 W3 m md3 k, PRE c -> JRN c ly3 S3 W3 m md3 k ->
  (forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W3 m) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
  (forall kk, 0 <= kk < 4 -> rdW W3 m (x_n c + kk) <> None) ->
  exists ch1, achain ly3 (rdW W3 m) (dc_s1 c) (dc_sp0 c) ch1.
Proof using LAWS.
intros c ly3 S3 W3 m md3 k HP HJ HSV HNV.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _].
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (DS : DC_STK = 12592) by reflexivity.
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
change (spZ (x_regs c)) with (dc_sp0 c) in *.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & Htbmax & (bt & mt & Hbt & Hbt1 & Hbt2) & _ & _ & _ & _ & _ & HDST & _).
assert (L : (length (x_tb c) <= length (snd (dc_res c)))%nat /\ Z.of_nat (length (snd (dc_res c))) <= x_max c)
  by exact (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Htbmax)).
destruct L as [L1 L2].
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR0 Hbt) as (_ & _ & Hbtc & _ & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hrq].
assert (CASE : (x_n c + 4 <= alloc_ceiling) \/ astack_pres (x_ly c) (w_H (x_W c)) (x_mem c) (spZ (x_regs c))).
{ destruct HDST as [((cid & pos & Hcp & Hcid & Hf1 & Hf2) & _) | [((b & mm & Hb & Hb1 & Hb2) & _) | (Hsp & Hot & Hpr & HAP)]].
  - left. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hcp) as (_ & Hfc & _). lia.
  - left. destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR0 Hb) as (_ & _ & Hbc & _ & _ & _ & Hm).
    pose proof (req_size_pos mm (proj1 Hm)) as [_ Hr]. lia.
  - right. exact HAP. }
assert (FPcases : forall a, inFP (dc_FP c) a -> a < alloc_ceiling \/ x_n c <= a < x_n c + 4).
{ intros a (r & Hr & Ha). unfold dc_FP, declared_W, vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct Hr as [<- | []]. cbn [fst snd] in Ha. left. unfold seg_spec.RVLAN_SIZE in *. lia.
  - destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|destruct Hr].
    destruct Hr as [<- | []]. cbn [fst snd] in Ha. right. exact Ha. }
destruct CASE as [Nlo | HAP].
- destruct (Z_lt_le_dec (dc_sp0 c) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
  + exists ((dc_sp0 c, raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
    apply (achain_ly_top (x_ly c) ly3 _ _ _ _ Etop).
    pose proof (HSV 0%nat 1 eq_refl) as H0. pose proof (HSV 1%nat 8 eq_refl) as H1.
    change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
    replace (dc_sp0 c - 8 - 8 * 0) with (dc_sp0 c - 8) in H0 by lia.
    replace (dc_sp0 c - 8 - 8 * 1) with (dc_sp0 c - 16) in H1 by lia.
    assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
    assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
    rewrite Q1 in H0. rewrite Q8 in H1.
    apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (dc_sp0 c) (s0Z (x_regs c)) (raZ (x_regs c))
      (x_ch c) (dc_s1 c) Hch).
    * lia.
    * intros a Ha. apply G1; [lia | lia | intros HF; destruct (FPcases a HF); lia].
    * exact H0.
    * exact H1.
    * exact Hra4.
    * lia.
    * clear - Hal16. Z.div_mod_to_equations. lia.
    * lia.
    * destruct Hs1 as [E1 | E1]; lia.
  + exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
- assert (HR : astack_rd ly3 (rdW W3 m) (dc_sp0 c - DC_STK)).
  { apply astack_rd_of_pres. apply (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAP).
    intros a Ha Hr. destruct (FPcases a Ha) as [Hl | Hn]; [lia|].
    replace a with (x_n c + (a - x_n c)) by lia. apply HNV. lia. }
  apply (achain_any ly3 (rdW W3 m) (dc_s1 c) (dc_sp0 c)).
  + apply (astack_rd_mono ly3 (rdW W3 m) (dc_sp0 c - DC_STK)); [destruct Hs1 as [E1 | E1]; lia | exact HR].
  + right; right; right. destruct Hs1 as [E1 | E1]; lia.
Qed.

(* the zones of a cut the walk keeps: the saved registers below sp0, the slots of s1, the frame's flag word, the
   table's entries and the count cell *)
Definition dcs2_Z (c : dcx) (ti : list (list Z * Z)) (a : Z) : Prop :=
  (dc_s1 c + 32 <= a < dc_s1 c + 96) \/ (dc_sp0 c - 104 <= a < dc_sp0 c) \/ (dc_F c + 120 <= a < dc_F c + 128) \/
  (x_tab c <= a < x_tab c + 18 * Z.of_nat (length ti)) \/ (x_n c <= a < x_n c + 4).
(* they lie outside the frame's shadow, split's stack window and split's write set *)
Lemma dcs2_Z_out : forall c ti ly3 S3 W3 m md3 k, PRE c -> JRN c ly3 S3 W3 m md3 k -> dc_un B c ly3 S3 ->
  Z.of_nat (length ti) <= x_max c ->
  forall a, dcs2_Z c ti a ->
  0 <= a < 2 ^ 64 /\ ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) /\
  ~ (dc_s1 c - DC_STK_SPLIT <= a < dc_s1 c) /\ ~ (dc_F c + 32 <= a < dc_F c + 48) /\ ~ (dc_F c + 64 <= a < dc_F c + 66).
Proof using LAWS.
intros c ti ly3 S3 W3 m md3 k HP HJ HU Hti a HZ.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _].
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HU as [HPERM Hly3 _]. subst ly3.
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & _).
assert (DS : DC_STK = 12592) by reflexivity. assert (DSS : DC_STK_SPLIT = 12352) by reflexivity.
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
change (spZ (x_regs c)) with (dc_sp0 c) in *.
assert (Hfin : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF4096 & HFc & HFapp).
change (fs_frame_bytes 1) with 128 in HFc, HFapp.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HF4096, HFc, HFapp.
(* an application byte below the ceiling is outside all four ranges *)
assert (APP : forall lo len, in_app lo len -> lo <= a < lo + len ->
  (a < dc_F c + 32 \/ dc_F c + 66 <= a) ->
  0 <= a < 2 ^ 64 /\ ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) /\
  ~ (dc_s1 c - DC_STK_SPLIT <= a < dc_s1 c) /\ ~ (dc_F c + 32 <= a < dc_F c + 48) /\
  ~ (dc_F c + 64 <= a < dc_F c + 66)).
{ intros lo len Happ Ha Hd.
  pose proof (in_app_addr lo len a Happ Ha) as Haa. pose proof (app_addr_below_ceil a Haa) as [Ha1 Ha2].
  unfold ASAN_CEIL in Ha2.
  split; [lia|]. split.
  - intros Hs. apply (dcs2_app_shadow a lo len (dc_F c) 128 (a - shadow_addr (dc_F c)) Happ Ha HF4096 HFc).
    + unfold shadow_addr, SHADOW_OFF, SB in *. change (128 / 8) with 16. lia.
    + unfold shadow_addr, SHADOW_OFF, SB in *. lia.
  - split; [destruct Hs1 as [E1 | E1]; lia | lia]. }
(* a stack byte at or above s1 + 32 *)
assert (STK : dc_s1 c + 32 <= a < dc_sp0 c ->
  0 <= a < 2 ^ 64 /\ ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) /\
  ~ (dc_s1 c - DC_STK_SPLIT <= a < dc_s1 c) /\ ~ (dc_F c + 32 <= a < dc_F c + 48) /\
  ~ (dc_F c + 64 <= a < dc_F c + 66)).
{ intros Ha. unfold dc_sp0 in *.
  assert (HFb : dc_F c / 8 < 0x7fffff800000 / 8) by (apply Z.div_lt_upper_bound; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in HFb. unfold SB.
  split; [lia|]. split; [lia|]. split; [destruct Hs1 as [E1 | E1]; lia | lia]. }
assert (STK2 : dc_sp0 c <= a < 2 ^ 47 ->
  0 <= a < 2 ^ 64 /\ ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) /\
  ~ (dc_s1 c - DC_STK_SPLIT <= a < dc_s1 c) /\ ~ (dc_F c + 32 <= a < dc_F c + 48) /\
  ~ (dc_F c + 64 <= a < dc_F c + 66)).
{ intros Ha. unfold dc_sp0 in *.
  assert (HFb : dc_F c / 8 < 0x7fffff800000 / 8) by (apply Z.div_lt_upper_bound; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in HFb. unfold SB.
  split; [lia|]. split; [lia|]. split; [destruct Hs1 as [E1 | E1]; lia | lia]. }
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & Htbmax & (bt & mt & Hbt & Hbt1 & Hbt2) & _ & _ & _ & _ & _ & HDST & _).
assert (Hbt3 : In (bt, mt) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hbt).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR3 Hbt3) as (_ & _ & _ & Hbtapp & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hrq].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bt mt 1 (x_fpos c) HAR3 Hbt3 Hfin) as Hsbt.
unfold zdisjoint in Hsbt. cbn [fst snd] in Hsbt. change (fs_frame_bytes 1) with 128 in Hsbt.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hsbt.
unfold dcs2_Z in HZ.
destruct HZ as [HZ | [HZ | [HZ | [HZ | HZ]]]].
- apply STK. destruct Hs1 as [E1 | E1]; lia.
- apply STK. destruct Hs1 as [E1 | E1]; lia.
- apply (APP (dc_F c) 128 HFapp); lia.
- apply (APP bt (req_size mt) Hbtapp); unfold seg_spec.RVLAN_SIZE in *; lia.
- destruct HDST as [((cid & pos & Hcp & Hcid & Hf1 & Hf2) & _) | [((b & mm & Hb & Hb1 & Hb2) & _) | (Hsp & Hot & _)]].
  + assert (Hcp3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hcp3) as (_ & _ & Hcapp).
    apply in_split in Hcp as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS (x_ly c) S3 W3 m md3 (1, x_fpos c) (cid, pos) [] l2 l3 HAR3
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hd.
    apply (APP _ _ Hcapp); [lia | lia].
  + assert (Hb3 : In (b, mm) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR3 Hb3) as (_ & _ & _ & Hbapp & _ & _ & Hm).
    pose proof (req_size_pos mm (proj1 Hm)) as [_ Hr].
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm 1 (x_fpos c) HAR3 Hb3 Hfin) as Hsb.
    unfold zdisjoint in Hsb. cbn [fst snd] in Hsb. change (fs_frame_bytes 1) with 128 in Hsb.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hsb.
    apply (APP b (req_size mm) Hbapp); lia.
  + apply STK2. unfold dc_sp0. lia.
Qed.

(* the frame's 16 shadow bytes lie outside split's stack window and split's write set *)
Lemma dcs2_sh_out : forall c ly3 S3 W3 m md3 k, PRE c -> JRN c ly3 S3 W3 m md3 k -> dc_un B c ly3 S3 ->
  forall o, 0 <= o < 16 ->
  0 <= SB + dc_F c / 8 + o < 2 ^ 64 /\ ~ (dc_s1 c - DC_STK_SPLIT <= SB + dc_F c / 8 + o < dc_s1 c) /\
  (forall s, ~ split_E (dc_F c + 32) (dc_F c + 64) s (SB + dc_F c / 8 + o)) /\
  ~ (dc_F c + 32 <= SB + dc_F c / 8 + o < dc_F c + 48) /\ ~ (dc_F c + 64 <= SB + dc_F c / 8 + o < dc_F c + 66).
Proof using LAWS.
intros c ly3 S3 W3 m md3 k HP HJ HU o Ho.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _].
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HU as [_ Hly3 _]. subst ly3.
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & _).
assert (DS : DC_STK = 12592) by reflexivity. assert (DSS : DC_STK_SPLIT = 12352) by reflexivity.
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
assert (Hfin : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF4096 & HFc & HFapp).
change (fs_frame_bytes 1) with 128 in HFc, HFapp.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HF4096, HFc, HFapp.
assert (HFb : dc_F c / 8 < 0x7fffff800000 / 8) by (apply Z.div_lt_upper_bound; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in HFb.
assert (NF : forall x, dc_F c <= x < dc_F c + 128 -> x <> SB + dc_F c / 8 + o).
{ intros x Hx Heq. apply (dcs2_app_shadow x (dc_F c) 128 (dc_F c) 128 o HFapp Hx HF4096 HFc);
    [change (128 / 8) with 16; lia | unfold shadow_addr; rewrite <- SB_SHADOW_OFF; exact Heq]. }
unfold dc_sp0 in *. pose proof (Z.div_pos (dc_F c) 8 ltac:(lia) ltac:(lia)).
split; [unfold SB; lia|]. split; [unfold SB; destruct Hs1 as [E1 | E1]; lia|].
assert (N1 : ~ (dc_F c + 32 <= SB + dc_F c / 8 + o < dc_F c + 48))
  by (intros Hr; exact (NF (SB + dc_F c / 8 + o) ltac:(lia) eq_refl)).
assert (N2 : ~ (dc_F c + 64 <= SB + dc_F c / 8 + o < dc_F c + 66))
  by (intros Hr; exact (NF (SB + dc_F c / 8 + o) ltac:(lia) eq_refl)).
split; [|exact (conj N1 N2)].
intros s HE. destruct (dcs2_split_E _ _ _ _ HE) as [HE1 | HE1]; [exact (N1 ltac:(lia)) | exact (N2 ltac:(lia))].
Qed.

(* the memory facts of a cut the walk keeps, and their transfer across a change that misses the zones *)
Definition dcs2_mem (c : dcx) (ti : list (list Z * Z)) (added : Z) (W3 : world SEGS) (m : word -> option byte)
  : Prop :=
  (forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W3 m) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) /\
  rdword (rdW W3 m) (dc_s1 c + 32) = Some (dc_F c) /\ rdword (rdW W3 m) (dc_s1 c + 40) = Some (dc_F c) /\
  rdword (rdW W3 m) (dc_s1 c + 56) = Some (dc_a1 c) /\ rdword (rdW W3 m) (dc_s1 c + 64) = Some (dc_a2 c) /\
  rdword (rdW W3 m) (dc_s1 c + 72) = Some (dc_a3 c) /\ rdword (rdW W3 m) (dc_F c + 120) = Some (dc_FL c) /\
  dc_tab c ti W3 m /\ dc_lslots c added W3 m.
Lemma dcs2_mem_of : forall c k ly S W regs m md ti added, dc_fi B DC_STK c k ly S W regs m md ->
  dc_tab c ti W m -> dc_lslots c added W m -> dcs2_mem c ti added W m.
Proof using.
intros c k ly S W regs m md ti added [_ _ _ _ _ _ _ G1 G2 G3 G4 G5 G6 G7] HT HL.
exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj HT HL)))))))).
Qed.
Lemma dcs2_fi_of : forall c k ly S W regs m md ti added, dcs2_mem c ti added W m ->
  JRN c ly S W m md k -> getr regs 2 = w64 (dc_s1 c) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = w64 (dc_sp0 c) -> getr regs 9 = w64 (dc_s1 c) -> getr regs 27 = w64 (SB + dc_F c / 8) ->
  dc_fi B DC_STK c k ly S W regs m md.
Proof using.
intros c k ly S W regs m md ti added (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _ & _) HJ R2 R3 R4 R8 R9 R27.
constructor; assumption.
Qed.
Lemma dcs2_mem_tr : forall c ti added (W W' : world SEGS) m m', dcs2_mem c ti added W m ->
  (forall a, dcs2_Z c ti a -> rdW W' m' a = rdW W m a) -> dcs2_mem c ti added W' m'.
Proof using.
intros c ti added W W' m m' (G1 & G2 & G3 & G4 & G5 & G6 & G7 & (T1 & T2 & T3 & T4) & (L1 & L2 & L3)) HK.
assert (RW : forall a, (forall kk, 0 <= kk < 8 -> dcs2_Z c ti (a + kk)) -> rdword (rdW W' m') a = rdword (rdW W m) a).
{ intros a Ha. apply rdword_ext. intros kk Hk. apply HK. apply Ha. exact Hk. }
unfold dcs2_Z in RW, HK.
split.
{ intros j r Hj. rewrite RW; [exact (G1 j r Hj)|].
  pose proof (proj1 (nth_error_Some dc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
  change (length dc_saved) with 13%nat in Hl. intros kk Hk. right; left. lia. }
split; [rewrite RW; [exact G2 | intros kk Hk; left; lia]|].
split; [rewrite RW; [exact G3 | intros kk Hk; left; lia]|].
split; [rewrite RW; [exact G4 | intros kk Hk; left; lia]|].
split; [rewrite RW; [exact G5 | intros kk Hk; left; lia]|].
split; [rewrite RW; [exact G6 | intros kk Hk; left; lia]|].
split; [rewrite RW; [exact G7 | intros kk Hk; right; right; left; lia]|].
split.
- split.
  + destruct T1 as (bs & Hb & Henc). exists bs. split; [|exact Henc].
    pose proof Henc as (Hbl & _).
    intros j Hj. rewrite HK; [exact (Hb j Hj)|]. right; right; right; left. lia.
  + split; [intros kk Hk; rewrite HK; [exact (T2 kk Hk) | right; right; right; right; lia]|].
    split; [exact T3 | exact T4].
- split; [rewrite RW; [exact L1 | intros kk Hk; left; lia]|].
  split; [rewrite RW; [exact L2 | intros kk Hk; left; lia] | rewrite RW; [exact L3 | intros kk Hk; left; lia]].
Qed.
(* the cut's kept part across a call with sa_noalloc *)
Lemma dcs2_un_call : forall c ly3 S3 ly4 S4, dc_un B c ly3 S3 -> sa_noalloc B ly3 S3 ly4 S4 -> dc_un B c ly4 S4.
Proof using.
intros c ly3 S3 ly4 S4 [P L (f0 & E0)] (P2 & L2 & f & E). subst.
constructor; [exact (Permutation_trans P2 P) | reflexivity | exists f; reflexivity].
Qed.

(* split_pre at the call state: the name of seg[i] in c's block, parent and vid in this call's frame with their
   shadow made addressable just before the call *)
Lemma dcs2_split_pre : forall c i ly3 S3 W3 m md3 k regs, dc_sspP B GOTW GUARD -> PRE c ->
  JRN c ly3 S3 W3 m md3 k -> dc_un B c ly3 S3 -> (i < length (dc_segs c))%nat ->
  rdW W3 m (SB + dc_F c / 8 + 4) = Some 0 -> rdW W3 m (SB + dc_F c / 8 + 5) = Some 0 ->
  rdW W3 m (SB + dc_F c / 8 + 8) = Some 2 ->
  split_pre SEGS B ly3 S3 W3 m regs (x_c c + 356 * Z.of_nat i) (dc_F c + 32) 16 (dc_F c + 64)
    (rs_name (nth i (dc_segs c) rseg_d)) GOTW GUARD.
Proof using LAWS.
intros c i ly3 S3 W3 m md3 k regs HSSP HP HJ HU Hi Sh4 Sh5 Sh8.
pose proof HP as [HAFN _ _ HC64 _ _ _ _ _ _ HDP _ _].
destruct HDP as (Hc0 & Hc16 & _ & (pb & nb & Hin & Hp1 & Hp2) & (_ & _ & Hamr & _) & _).
destruct (dcs2_rconf_at c ly3 S3 W3 m md3 k HP HJ HU) as (bs & Hbs & Henc).
pose proof HU as [HPERM Hly3 _]. subst ly3.
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (pb, nb) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
assert (Hfin : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 Hin3) as (_ & Hpb4096 & Hpbc & Hpbapp & _ & _ & Hnb).
pose proof (req_size_pos nb (proj1 Hnb)) as [_ Hrq].
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF64 & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ pb nb 1 (x_fpos c) HAR3 Hin3 Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
change (fs_frame_bytes 1) with 128 in HFc, HFapp, Hsep.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HF4096, HFc, HFapp, HF64, Hsep.
pose proof Henc as (_ & Hle32 & _).
unfold dc_segs in *.
destruct (dcs2_rd_name _ _ _ _ i Hbs Henc Hi) as [HSTR Hlen].
set (s := rs_name (nth i (rc_seg (x_rc c)) rseg_d)) in *.
set (F := dc_F c) in *.
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_C_SIZE in *.
assert (HF8 : F = 8 * (F / 8)) by (clear - HF64; Z.div_mod_to_equations; lia).
assert (RAP : range_addressable (rdW W3 m) SHADOW_OFF (F + 32) 16).
{ intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  assert (Hq : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (clear - HF8 Hx; Z.div_mod_to_equations; lia).
  destruct Hq as [Hq | Hq]; rewrite Hq.
  - replace (SHADOW_OFF + (F / 8 + 4)) with (SB + F / 8 + 4) by (unfold SB, SHADOW_OFF; lia). exact Sh4.
  - replace (SHADOW_OFF + (F / 8 + 5)) with (SB + F / 8 + 5) by (unfold SB, SHADOW_OFF; lia). exact Sh5. }
assert (RAV : range_addressable (rdW W3 m) SHADOW_OFF (F + 64) 2).
{ apply range_addressable_partial; [| clear - HF8; Z.div_mod_to_equations; lia | lia].
  unfold shadow_of_addr.
  replace (SHADOW_OFF + (F + 64) / 8) with (SB + F / 8 + 8) by (unfold SB, SHADOW_OFF; clear - HF8; Z.div_mod_to_equations; lia).
  exact Sh8. }
assert (AMF : forall o n, 0 <= o -> o + n <= 128 -> 0 <= n -> amem_range (F + o) n).
{ intros o n Ho Hn Hn0. unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  unfold kLowMemEnd, kHighMemEnd, kHighMemBeg. lia. }
assert (Hsl : x_c c + 356 * Z.of_nat i + Z.of_nat (length s) + 8 <= x_c c + 16616) by lia.
assert (AMC : amem_range (x_c c + 356 * Z.of_nat i) (Z.of_nat (length s) + 8)) by (unfold amem_range in Hamr |- *; lia).
unfold split_pre.
split; [lia|].
split; [exact HSTR|].
split; [exact Hlen|].
split.
{ unfold sa_addr. split; [lia|]. split; [lia|].
  split; [unfold amem_range in AMC |- *; lia|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ pb nb _ (Z.of_nat (length s) + 1) HAR3 Hin3); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ pb nb _ (Z.of_nat (length s) + 1) HAR3 Hin3); lia. }
split; [exact AMC|].
split; [left; exists pb, nb; split; [exact Hin3 | lia]|].
split; [lia|].
split; [reflexivity|].
split.
{ left. split; [|exact RAP]. exists 1, (x_fpos c). split; [exact Hfin|].
  change (fs_frame_bytes 1) with 128. change (frame_addr (x_ly c) 1 (x_fpos c)) with F. lia. }
split.
{ split; [lia|]. split; [lia|]. split; [apply AMF; lia|]. split; [exact RAP|].
  intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) (F + 32) 16 HAR3 Hfin);
    change (fs_frame_bytes 1) with 128; change (frame_addr (x_ly c) 1 (x_fpos c)) with F; lia. }
split.
{ unfold sa_disj, seg_spec.cstr_span.
  pose proof (Z.mod_pos_bound (- (x_c c + 356 * Z.of_nat i + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
  destruct Hsep as [Hs | Hs]; [left | right]; lia. }
split; [lia|].
split; [clear - HF8; Z.div_mod_to_equations; lia|].
split.
{ left. split; [|exact RAV]. exists 1, (x_fpos c). split; [exact Hfin|].
  change (fs_frame_bytes 1) with 128. change (frame_addr (x_ly c) 1 (x_fpos c)) with F. lia. }
split.
{ split; [lia|]. split; [lia|]. split; [apply AMF; lia|]. split; [exact RAV|].
  intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) (F + 64) 2 HAR3 Hfin);
    change (fs_frame_bytes 1) with 128; change (frame_addr (x_ly c) 1 (x_fpos c)) with F; lia. }
split; [unfold sa_disj; right; lia|].
exact (HSSP _ _ _ _ _ HAR3).
Qed.

End e.
End f.
End d.
