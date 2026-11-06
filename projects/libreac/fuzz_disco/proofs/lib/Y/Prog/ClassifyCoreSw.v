(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths changed; 1096 of its 1159 lines of code are new or changed and 428 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition SW_Bx : sv := SOff 21 0.
Definition sw_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sw_loc : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 24 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition sw_q : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0 32 0 0
    [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 16 (CVal 4 (SOff 35 0));
     YP09.mkChunk 26 (CVal 1 (SOff 36 0)); YP09.mkChunk 28 (CVal 2 (SOff 37 0))].
Definition sw_tabr : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 35)) 0 36 0 0
    (map (fun i => YP09.mkChunk (4 * Z.of_nat i) (CVal 4 (SOff (38 + i) 0))) (seq 0 9)).
Definition sw_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
    (33%nat, HPTR 2); (34%nat, mkAF 1 13 0); (35%nat, mkAF 0 1 0); (36%nat, mkAF 0 255 0);
    (37%nat, mkAF 0 (2 ^ 16 - 1) 0)] [] [].
Definition ss_sw : sstate := mkSS PC_SW sr_atoms [sw_loc; sw_q; sw_tabr] None sw_facts.

Lemma sw_ret0 : forall FB len U L, disco_classify_c.cm_ret FB len U L = 0 -> disco_classify_c.dkind FB len <> 0.
Proof.
intros FB len U L H Hk. unfold disco_classify_c.cm_ret, disco_classify_c.classify_model in H.
rewrite Hk in H. cbn in H. discriminate H.
Qed.

Lemma sw_ps_bytes : forall n fr,
  nth 0 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = Z_to_bv 8 (fst (RcParse.ctrlparse n fr)) /\
  nth 1 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 2 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 3 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  (nth 16 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = Z_to_bv 8 0 \/
   nth 16 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = Z_to_bv 8 1) /\
  nth 17 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 18 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z /\
  nth 19 (snd (RcParse.ctrlparse n fr)) RcParse.cp_z = RcParse.cp_z.
Proof.
intros n fr. unfold RcParse.ctrlparse. destruct (RcParse.cp_hdr n fr); cbn [fst snd].
- unfold RcParse.cp_struct. cbn [nth app].
  destruct (RcParse.cp_bcast fr); repeat split; first [reflexivity | left; reflexivity | right; reflexivity].
- cbn [nth repeat]. repeat split; first [reflexivity | left; reflexivity].
Qed.

Lemma sw_nth_bytes : forall l j, nth j (cls_bytes l) 0 = bv_unsigned (nth j l RcParse.cp_z).
Proof.
intros l. unfold cls_bytes. induction l as [|b l IH]; intros [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

Lemma sw_le4 : forall v k, 0 <= v < 256 -> (k < 4)%nat ->
  Z_to_bv 8 (YO0f.le_byte v 4 k) = Z_to_bv 8 (if (k =? 0)%nat then v else 0).
Proof.
intros v k Hv Hk. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia). rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Nat.eqb].
- change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r, Z.mod_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16). rewrite Z.div_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_nat 3)) with (2 ^ 24). rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac sw_lbz := unfold YO0f.le_byte; rewrite !Z.shiftr_div_pow2 by lia; cbn [Z.of_nat];
  cbn [Z.mul Z.pow Z.pow_pos Pos.mul Pos.iter Pos.add]; Z.div_mod_to_equations; lia.

Lemma sw_bytes_range : forall l j, 0 <= nth j (cls_bytes l) 0 < 256.
Proof.
intros l j. rewrite sw_nth_bytes. pose proof (bv_unsigned_in_range 8 (nth j l RcParse.cp_z)) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma sw_orole : forall FB i, length FB = 50%nat ->
  nth i (cls_bytes (cls_O_ROLE FB)) 0 = (if (i <? 6)%nat then RcParse.cp_v FB (6 + i) else 0).
Proof.
intros FB i HL. unfold cls_bytes, cls_O_ROLE, disco_classify_c.src, CtrlParsed.fld.
destruct FB as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 FB]]]]]]]]]]]]; cbn in HL; try lia.
do 24 (destruct i as [|i]; [reflexivity|]). cbn. destruct i; reflexivity.
Qed.

Lemma sw_src : forall len FB j, fst (RcParse.ctrlparse len FB) <> 0 -> (j < 6)%nat ->
  nth (4 + j) (cls_bytes (snd (RcParse.ctrlparse len FB))) 0 = RcParse.cp_v FB (6 + j).
Proof.
intros len FB j Hk Hj. rewrite sw_nth_bytes.
pose proof (RcParse.ctrlparse_fields len FB Hk) as HF. cbv zeta in HF. destruct HF as (F1 & _).
rewrite (F1 j Hj). reflexivity.
Qed.

Lemma sw_role5_one : forall F, CtrlParsed.fb F 22 = 0 ->
  (disco_classify_c.tag F = 256 \/ disco_classify_c.tag F = 770 \/ disco_classify_c.tag F = 1280) ->
  disco_classify_c.role F 5 = 1.
Proof. intros F H0 Ht. unfold disco_classify_c.role. rewrite H0. destruct Ht as [-> | [-> | ->]]; reflexivity. Qed.

Lemma sw_role5_fb : forall F, CtrlParsed.fb F 22 <> 0 -> disco_classify_c.role F 5 = 2.
Proof. intros F H. unfold disco_classify_c.role. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma sw_role5_tag : forall F, disco_classify_c.tag F <> 256 -> disco_classify_c.tag F <> 770 ->
  disco_classify_c.tag F <> 1280 -> disco_classify_c.role F 5 = 2.
Proof.
intros F H1 H2 H3. unfold disco_classify_c.role.
rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3).
destruct (CtrlParsed.fb F 22 =? 0); reflexivity.
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
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.

Definition sw_P (cx : ccx) : list Z := cls_bytes (cPS cx).
Definition sw_bc (cx : ccx) : Z := nth 16 (sw_P cx) 0.
Definition sw_fb (cx : ccx) : Z := nth 26 (sw_P cx) 0.
Definition sw_tg (cx : ccx) : Z := nth 28 (sw_P cx) 0 + 256 * nth 29 (sw_P cx) 0.

Lemma sw_bc_val : forall cx, cK cx <> 0 -> sw_bc cx = if RcParse.cp_bcast (x_FB cx) then 1 else 0.
Proof.
intros cx Hk. unfold cK, disco_classify_c.dkind in Hk. unfold sw_bc, sw_P, cPS. rewrite sw_nth_bytes.
unfold RcParse.ctrlparse in *. destruct (RcParse.cp_hdr (x_len cx) (x_FB cx)); cbn [fst snd] in *; [|lia].
unfold RcParse.cp_struct. cbn [nth app]. destruct (RcParse.cp_bcast (x_FB cx)); reflexivity.
Qed.

Lemma sw_fb_val : forall cx, cK cx <> 0 -> sw_fb cx = CtrlParsed.fb (x_FB cx) 22.
Proof.
intros cx Hk. unfold cK, disco_classify_c.dkind in Hk. unfold sw_fb, sw_P, cPS. rewrite sw_nth_bytes.
unfold RcParse.ctrlparse in *. destruct (RcParse.cp_hdr (x_len cx) (x_FB cx)); cbn [fst snd] in *; [|lia].
unfold RcParse.cp_struct. cbn [nth app]. reflexivity.
Qed.

Lemma sw_tg_val : forall cx, cK cx = 5 -> sw_tg cx = disco_classify_c.tag (x_FB cx).
Proof.
intros cx Hk. unfold cK, disco_classify_c.dkind in Hk.
destruct (RcParse.ctrlparse_rec (x_len cx) (x_FB cx) (or_introl Hk)) as (_ & _ & H28 & H29).
unfold sw_tg, sw_P, cPS, disco_classify_c.tag. rewrite !sw_nth_bytes, H28, H29.
unfold CtrlParsed.fb, RcParse.cp_b, RcParse.cp_z, CtrlParsed.zb. lia.
Qed.

Definition sw_tab (i : nat) : Z := (BASE + AF_both3_classify_core + nth i CLS_SW_ARMS 0 - VAL (A_OBJ 35)) mod 2 ^ 32.
Definition sw_extra (cx : ccx) : list word :=
  map (Z_to_bv 64) ([x_len cx; x_o cx; cK cx; sw_bc cx; sw_fb cx; sw_tg cx] ++ map sw_tab (seq 0 9)).
Definition SWE (cx : ccx) (regs : bvmap 5 word) : env := Eimg (Ereg regs (sw_extra cx)).

Lemma sw_ew : forall cx (regs : bvmap 5 word),
  ew (SWE cx regs) 32 = Z_to_bv 64 (x_len cx) /\ ew (SWE cx regs) 33 = Z_to_bv 64 (x_o cx) /\
  ew (SWE cx regs) 34 = Z_to_bv 64 (cK cx) /\ ew (SWE cx regs) 35 = Z_to_bv 64 (sw_bc cx) /\
  ew (SWE cx regs) 36 = Z_to_bv 64 (sw_fb cx) /\ ew (SWE cx regs) 37 = Z_to_bv 64 (sw_tg cx) /\
  (forall i, (i < 9)%nat -> ew (SWE cx regs) (38 + i) = Z_to_bv 64 (sw_tab i)) /\
  ew (SWE cx regs) (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35)) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (SWE cx regs) n = getr regs r).
Proof.
intros cx regs. unfold SWE.
assert (X : forall j, (j < 15)%nat -> ew (Eimg (Ereg regs (sw_extra cx))) (32 + j) = nth j (sw_extra cx) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
split; [exact (X 0%nat ltac:(lia))|]. split; [exact (X 1%nat ltac:(lia))|].
split; [exact (X 2%nat ltac:(lia))|]. split; [exact (X 3%nat ltac:(lia))|].
split; [exact (X 4%nat ltac:(lia))|]. split; [exact (X 5%nat ltac:(lia))|].
split.
- intros i Hi. replace (38 + i)%nat with (32 + (6 + i))%nat by lia. rewrite X by lia.
  unfold sw_extra. rewrite map_nth. f_equal. cbn [app nth Nat.add].
  rewrite (nth_indep _ 0 (sw_tab 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
- split; [apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia|].
  intros n r Hn. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.

Lemma sw_vm2 : forall (m : word -> option byte) a b0 b1,
  val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  val_mem SEGS m a 2 (b0 + 256 * b1).
Proof.
intros m a b0 b1 H0 H1 R0 R1 j Hj.
destruct j as [|[|j]]; [| | lia].
- specialize (H0 0%nat ltac:(lia)). rewrite H0. do 2 f_equal. sw_lbz.
- specialize (H1 0%nat ltac:(lia)). replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. rewrite H1.
  do 2 f_equal. sw_lbz.
Qed.

Lemma sw_vm4 : forall (m : word -> option byte) p l j v, garr8 SEGS m p l -> (j + 4 <= length l)%nat ->
  nth j l 0 = v -> nth (j + 1) l 0 = 0 -> nth (j + 2) l 0 = 0 -> nth (j + 3) l 0 = 0 ->
  val_mem SEGS m (p + Z.of_nat j) 4 v.
Proof.
intros m p l j v H Hl H0 H1 H2 H3 k Hk.
assert (Hv : 0 <= v < 256) by (subst v; apply (H j); lia).
replace (p + Z.of_nat j + Z.of_nat k) with (p + Z.of_nat (j + k)) by lia.
rewrite (garr8_mbyte SEGS m p l (j + k) H) by lia.
rewrite (sw_le4 v k Hv Hk).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Nat.eqb].
- rewrite Nat.add_0_r, H0. reflexivity.
- rewrite H1. reflexivity.
- rewrite H2. reflexivity.
- rewrite H3. reflexivity.
Qed.

Lemma sw_garr8_kept : forall H (m m' : word -> option byte) p l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m' (p + j) = aview SEGS H m (p + j)) ->
  garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H m') p l.
Proof.
intros H m m' p l HA HG. apply (garr8_frame SEGS _ _ p l HG).
intros a Ha. replace a with (p + (a - p)) by lia. apply (mbyte_of_aview SEGS). apply HA. lia.
Qed.

Lemma sw_vm_kept : forall H (m m' : word -> option byte) a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hq Hv j Hj. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j)).
- exact (Hv j Hj).
- apply Hq. lia.
Qed.

Lemma sw_aview_garr8 : forall H (m : word -> option byte) p l j,
  garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j HG Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. destruct (HG j Hj) as [_ R]. change (bv_modulus 8) with 256.
apply Z.mod_small. lia.
Qed.

Lemma sw_garr8_of_aview : forall H (m : word -> option byte) p l,
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l A j Hj. pose proof (A j Hj) as Aj. unfold aview in Aj.
destruct (mbyte SEGS (mrestrict H m) (p + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Aj. injection Aj as Aj.
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
split; [|rewrite <- Aj; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
rewrite <- Aj. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. change (bv_modulus 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
reflexivity.
Qed.

Lemma sw_frame_aview : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hn a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact (Hn a).
Qed.

Lemma sw_pres_grows : forall (m m' : word -> option byte) (H : word -> bool) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros m m' H a HG (Hh & b & Hb). split; [exact Hh|].
assert (Hne : mrestrict H m' (Z_to_bv 64 a) <> None).
{ apply HG. unfold mrestrict. rewrite Hh, Hb. discriminate. }
unfold mrestrict in Hne. rewrite Hh in Hne. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. apply Hne. reflexivity.
Qed.

Definition sw_kept (cx : ccx) (W3 : world SEGS) (mem3 m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cS1 cx - ESTACK <= a < cS1 cx) -> ~ (x_o cx <= a < x_o cx + 24) ->
     aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a) /\
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m a).

Lemma sw_kept_run : forall cx W3 (mem3 m m' : word -> option byte) E rs,
  sw_kept cx W3 mem3 m -> frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  mem_grows (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall a, ~ in_wrange E rs a) -> sw_kept cx W3 mem3 m'.
Proof.
intros cx W3 mem3 m m' E rs [K P] HF HG Hw. split.
- intros a Ha Hn Ho. rewrite (sw_frame_aview E rs _ m m' HF Hw a Ha). apply K; assumption.
- intros a Ha. apply (sw_pres_grows m m'); [exact HG | apply P, Ha].
Qed.

Lemma sw_rd_band : forall p n x, 0 <= p -> p + n <= 2 ^ 47 -> p <= x < p + n ->
  kLowShadowBeg <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros p n x Hp Hpn Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg in *.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1. lia.
Qed.

Lemma sw_shadow_band : forall p n s, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> kLowShadowBeg <= s < kHighMemBeg.
Proof.
intros p n s Hp Hn Hpn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold shadow_addr in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold SHADOW_OFF, kLowShadowBeg in *.
lia.
Qed.

Lemma sw_ra_kept : forall H (m m' : word -> option byte) p n,
  0 <= p -> p + n <= 2 ^ 47 ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS H m' a = aview SEGS H m a) ->
  range_addressable (aview SEGS H m) SHADOW_OFF p n -> range_addressable (aview SEGS H m') SHADOW_OFF p n.
Proof.
intros H m m' p n Hp Hpn K R. apply (range_addressable_agree (aview SEGS H m) _ SHADOW_OFF p n); [|exact R].
intros x Hx. apply K. exact (sw_rd_band p n x Hp Hpn Hx).
Qed.

Lemma sw_hull_kept : forall H (m m' : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n <= 2 ^ 47 ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS H m' a = aview SEGS H m a) ->
  shadow_hull_vis (aview SEGS H m) p n -> shadow_hull_vis (aview SEGS H m') p n.
Proof.
intros H m m' p n Hp Hn Hpn K V s Hs. rewrite K by exact (sw_shadow_band p n s Hp Hn Hpn Hs). apply V. exact Hs.
Qed.

Lemma sw_ra_sub : forall rd B0 a n a' n', range_addressable rd B0 a n -> a <= a' -> a' + n' <= a + n ->
  range_addressable rd B0 a' n'.
Proof. intros rd B0 a n a' n' R H1 H2 x Hx. apply R. lia. Qed.

Lemma sw_hull_sub : forall rd p n p' n', shadow_hull_vis rd p n -> p <= p' -> p' + n' <= p + n -> 0 < n' ->
  shadow_hull_vis rd p' n'.
Proof.
intros rd p n p' n' V H1 H2 Hn s Hs. apply V. unfold shadow_addr in *.
pose proof (Z.div_le_mono p p' 8 ltac:(lia) H1) as M1.
pose proof (Z.div_le_mono (p' + n' - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + p' / 8) 8 ltac:(lia) ltac:(lia)) as M3.
pose proof (Z.div_le_mono (SHADOW_OFF + (p' + n' - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as M4.
lia.
Qed.

Lemma sw_ra_pat : forall H (m : word -> option byte) F a n,
  0 <= F -> F mod 32 = 0 -> garr8 SEGS (mrestrict H m) (SHADOW_OFF + F / 8) PAT_A ->
  F + 32 <= a -> a + n <= F + 64 -> range_addressable (aview SEGS H m) SHADOW_OFF a n.
Proof.
intros H m F a n HF0 HFal HG Ha Hn x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M1.
pose proof (Z.div_mod F 32 ltac:(lia)) as D0.
pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
assert (Hj : 4 <= x / 8 - F / 8 < 8) by lia.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + Z.of_nat (Z.to_nat (x / 8 - F / 8))) by lia.
rewrite (sw_aview_garr8 H m _ PAT_A _ HG) by (unfold PAT_A; cbn [length]; lia).
f_equal. assert (Hc : (Z.to_nat (x / 8 - F / 8) = 4 \/ Z.to_nat (x / 8 - F / 8) = 5 \/
  Z.to_nat (x / 8 - F / 8) = 6 \/ Z.to_nat (x / 8 - F / 8) = 7)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma sw_slot_hi : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e -> BASE + k < YImgTop.IMG_TOP.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA lib_both3_0_listing pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_img_range _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia.
Qed.

Lemma sw_swrap32 : forall d, - 2 ^ 31 <= d < 2 ^ 31 -> bv_swrap 32 (d mod 2 ^ 32) = d.
Proof.
intros d Hd. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
Z.div_mod_to_equations. lia.
Qed.

Lemma sw_jr_val : forall E n m x t v, ew E n = Z_to_bv 64 x -> x = (t - v) mod 2 ^ 32 -> ew E m = Z_to_bv 64 v ->
  0 <= v < 2 ^ 31 -> 0 <= t < 2 ^ 31 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SOff m 0)) = Z_to_bv 64 t.
Proof.
intros E n m x t v Hn Hx Hm Hv Ht. subst x.
assert (R : 0 <= (t - v) mod 2 ^ 32 < 2 ^ 64) by (pose proof (Z.mod_pos_bound (t - v) (2 ^ 32) ltac:(lia)); lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SExt, (U_atom E n _ Hn R), (U_atom E m v Hm) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_mod by lia.
rewrite sw_swrap32 by lia.
cbn [zalu_raw]. unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.

Lemma sw_pin_sv : forall (fq : YK11.FPState) E ss ms (r : bv 5) e,
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> sv_denot E e = getr (ms_regs ms) r -> bv_eqb r 0 = false ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fq E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq. exact Hr.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Lemma sw_jr_pin : forall (fq : YK11.FPState) E ss ms (i : nat) n, (i < 9)%nat -> img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> ew E n = Z_to_bv 64 (sw_tab i) ->
  sr_get (ss_regs ss) 10%bv = SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SOff 276 0) ->
  ew E 276 = Z_to_bv 64 (VAL (A_OBJ 35)) ->
  st_ok_pi (fx := fq) SEGS VAL E
    (mkSST (ss_pc ss) (sr_set (ss_regs ss) 10%bv (SOff A_TEXT (AF_both3_classify_core + nth i CLS_SW_ARMS 0)))
    (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fq E ss ms i n Hi HEI HS Hn Hr H276.
pose proof (pa_obj_img_all 35%nat ltac:(unfold tfib_nobj; lia)) as [V0 V1].
pose proof pa_B_ok as (HB0 & HB1 & _).
assert (Harm : 0 <= nth i CLS_SW_ARMS 0 <= 688) by (do 9 (destruct i as [|i]; [cbn; lia|]); lia).
assert (Hslot : exists e, plookup pl_tpi (AF_both3_classify_core + nth i CLS_SW_ARMS 0) = Some e).
{ clear - Hi. do 9 (destruct i as [|i]; [eexists; vm_compute; reflexivity|]). lia. }
destruct Hslot as (e & He).
pose proof (sw_slot_hi (AF_both3_classify_core + nth i CLS_SW_ARMS 0) e ltac:(unfold AF_both3_classify_core; lia) He) as Hhi.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
apply sw_pin_sv; [exact HS | | reflexivity].
pose proof (st_ok_reg SEGS E _ ms 10%bv HS) as Hq. unfold abs_ss, setpc in Hq. cbn [ss_regs] in Hq.
rewrite Hq, Hr, codeptr_val by exact HEI. symmetry.
apply (sw_jr_val E n 276 (sw_tab i) _ (VAL (A_OBJ 35)) Hn);
  [unfold sw_tab; f_equal; ring | exact H276 | clear - V0 V1; lia | clear - HB0 Harm Hhi; unfold AF_both3_classify_core in *; lia].
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMSET : forall fq, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.
Hypothesis ROM : cls_rom_ok B.

Lemma sw_nums : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  cSP cx mod 16 = 0 /\ cSP cx - 176 <= cS1 cx <= cSP cx - 160 /\ cS1 cx mod 32 = 0 /\
  alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx - x_STK cx <= cSP cx - CLS_STK /\
  cSP cx <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  (forall a, x_sp0 cx - x_STK cx <= a < x_sp0 cx -> apresent (w_H W3) mem3 a) /\
  4096 <= cF cx fpos /\ cF cx fpos + 256 <= alloc_ceiling /\ cF cx fpos mod 32 = 0 /\
  CLS_STK = 8512 /\ ESTACK = 4096.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut.
pose proof (NOW cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as Hnow. cbv zeta in Hnow.
destruct Hnow as ((HF4 & HFc & HFal & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
pose proof Hcut as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (CS : CLS_STK = 8512) by reflexivity.
assert (HSP : cSP cx mod 16 = 0) by exact Hal.
assert (HL : x_sp0 cx - x_STK cx <= cSP cx - CLS_STK) by exact Hlo.
assert (HH : cSP cx <= x_sp0 cx) by exact Hhi.
pose proof (Z.div_mod (cSP cx - 160) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (cSP cx - 160) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (cSP cx) 16 ltac:(lia)) as D2.
unfold cS1, cls_S1.
split; [exact HSP|]. split; [split; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
split; [lia|]. split; [exact HL|]. split; [exact HH|]. split; [lia|].
split; [exact Hpres|]. split; [exact HF4|]. split; [exact HFc|]. split; [exact HFal|].
split; [exact CS | reflexivity].
Qed.

Section call.
Variables (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model).
Hypothesis Hpre : cls_pre B cx.
Hypothesis Hat : cls_at_SW B cx fpos W3 ly3 S3 regs3 mem3 md3.

Lemma sw_ctx : cSP cx mod 16 = 0 /\ cSP cx - 176 <= cS1 cx <= cSP cx - 160 /\ cS1 cx mod 16 = 0 /\
  alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx - x_STK cx <= cSP cx - 8512 /\
  cSP cx <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  4096 <= cF cx fpos /\ cF cx fpos + 256 <= alloc_ceiling /\ cF cx fpos mod 32 = 0 /\
  getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
  4096 <= x_o cx /\ x_o cx + 24 <= alloc_ceiling /\ (x_o cx + 24 <= kLowShadowBeg \/ kHighMemBeg <= x_o cx) /\
  (x_o cx + 24 <= cF cx fpos \/ cF cx fpos + 256 <= x_o cx) /\ ESTACK = 4096.
Proof.
pose proof Hat as (_ & Hc).
destruct (sw_nums cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc)
  as (Hsp16 & HS1 & HS1al & Hceil & Hstk & Hsp & H47 & Hpres & HF4 & HFc & HFal & CS & ES).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & ((_ & _ & _ & _ & HOsh) & _ & HOF & _) & HO4096 & HOc & _).
pose proof Hc as (HJ & _ & _ & _ & _ & _ & _ & _ & R3 & R4 & _).
pose proof Hpre as (_ & _ & _ & _ & Hgp & Htp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
rewrite CS in Hstk.
assert (H16 : cS1 cx mod 16 = 0).
{ unfold cS1, cls_S1. replace (32 * ((cSP cx - 160) / 32)) with ((2 * ((cSP cx - 160) / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
repeat split; try assumption; try lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
Qed.

Lemma sw_aro : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
pose proof Hpre as (_ & Haro & _).
pose proof Hat as (_ & Hc). unfold cls_cut in Hc. cbv zeta in Hc.
destruct Hc as (_ & _ & _ & _ & _ & _ & (_ & _ & K3 & _) & _).
intros a Hro Ho He. rewrite (K3 a); [exact (Haro a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

Lemma sw_tab_img : YImgTop.IMG_LO <= VAL (A_OBJ 35) /\ VAL (A_OBJ 35) + 36 <= YImgTop.IMG_TOP.
Proof.
pose proof (pa_obj_img_all 35%nat ltac:(unfold tfib_nobj; lia)) as [H0 _].
pose proof (pa_obj_win 35%nat 0 35 ltac:(unfold tfib_nobj; lia) ltac:(vm_compute; split; [discriminate | reflexivity])) as Hw.
pose proof (pa_img_range _ Hw) as HR. split; lia.
Qed.

Lemma sw_entry :
  st_ok_pi (fx := x_fq cx) SEGS VAL (SWE cx regs3) ss_sw
    (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_SW)) mem3 (seg_rom SEGS))).
Proof.
pose proof (proj2 (ROM (w_H W3) mem3 sw_aro)) as Htab.
pose proof sw_tab_img as (HT0 & HT1).
pose proof Hat as (Hret & Hcut).
pose proof sw_ctx as (Hsp16 & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & HF4 & HFc & HFal & Hgp & Htp & Ho4 & Hoc & HOsh & HOF & ES).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as Hnow. cbv zeta in Hnow.
destruct Hnow as ((_ & _ & _ & HFz & _) & _). unfold zone2, off_img in HFz.
pose proof Hcut as (HJ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV & _
  & Vo & _ & _ & VLS & _ & _ & _ & HPS & _).
destruct HPS as (HPSl & HPSg).
apply Forall_cons_iff in HRV as [Rs5 HRV]. apply Forall_cons_iff in HRV as [Rs6 HRV].
apply Forall_cons_iff in HRV as [Rs9 _]. cbn [fst snd] in Rs5, Rs6, Rs9.
pose proof (VLS eq_refl) as Vlen.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (RcParse.ctrlparse_kind_range (x_len cx) (x_FB cx)) as HKr.
pose proof (sw_ret0 _ _ _ _ Hret) as Hk0.
destruct (sw_ps_bytes (x_len cx) (x_FB cx)) as (B0 & B1 & B2 & B3 & B16 & B17 & B18 & B19).
destruct (sw_ew cx regs3) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & EO35 & EW).
set (E := SWE cx regs3) in *.
assert (U2 : bv_unsigned (ew E 2) = cS1 cx)
  by (rewrite (EW 2%nat 2%bv eq_refl), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = cS1 cx)
  by (rewrite (EW 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U22 : bv_unsigned (ew E 22) = cF cx fpos + 32)
  by (rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl), Rs6; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U21 : bv_unsigned (ew E 21) = SB)
  by (rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl), Rs5; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U35 : bv_unsigned (ew E (A_OBJ 35)) = VAL (A_OBJ 35))
  by (rewrite EO35; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 35)); lia).
assert (HK0 : nth 0 (cls_bytes (cPS cx)) 0 = cK cx).
{ rewrite sw_nth_bytes. unfold cPS. rewrite B0. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. unfold cK, disco_classify_c.dkind. apply Z.mod_small. lia. }
assert (HBC : sw_bc cx = 0 \/ sw_bc cx = 1).
{ unfold sw_bc, sw_P. rewrite sw_nth_bytes. unfold cPS. destruct B16 as [-> | ->]; [left | right]; reflexivity. }
assert (HPSb : length (cls_bytes (cPS cx)) = 36%nat) by (unfold cls_bytes; rewrite length_map; exact HPSl).
assert (RFB : 0 <= sw_fb cx < 256) by apply sw_bytes_range.
assert (RTG : 0 <= sw_tg cx < 2 ^ 16).
{ unfold sw_tg, sw_P. pose proof (sw_bytes_range (cPS cx) 28). pose proof (sw_bytes_range (cPS cx) 29). lia. }
assert (RTB : forall i, 0 <= sw_tab i < 2 ^ 32) by (intros i; unfold sw_tab; apply Z.mod_pos_bound; lia).
rewrite restrict_mkst_fx. unfold ss_sw. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, sw_loc. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (cS1 cx) 8 8 (SOff 32 0) (x_len cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Vlen.
    * apply (chunk_ok_val SEGS E _ (cS1 cx) 16 8 (SOff 33 0) (x_o cx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Vo.
  + unfold region_ok, sw_q. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ (cF cx fpos + 32) 0 4 (SOff 34 0) (cK cx));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold cK, disco_classify_c.dkind in *; zside | zside |].
      change (N.to_nat 4) with 4%nat.
      pose proof (sw_vm4 _ _ _ 0 (cK cx) HPSg ltac:(lia) HK0) as V.
      rewrite Z.add_0_r. rewrite Z.add_0_r in V. apply V.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B1. reflexivity.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B2. reflexivity.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B3. reflexivity.
    * apply (chunk_ok_val SEGS E _ (cF cx fpos + 32) 16 4 (SOff 35 0) (sw_bc cx));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 4) with 4%nat.
      apply (sw_vm4 _ _ _ 16 (sw_bc cx) HPSg ltac:(lia)).
      -- reflexivity.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B17. reflexivity.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B18. reflexivity.
      -- cbn [Nat.add]. rewrite sw_nth_bytes. unfold cPS. rewrite B19. reflexivity.
    * apply (chunk_ok_val SEGS E _ (cF cx fpos + 32) 26 1 (SOff 36 0) (sw_fb cx));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. exact (proj1 (HPSg 26%nat ltac:(lia))).
    * apply (chunk_ok_val SEGS E _ (cF cx fpos + 32) 28 2 (SOff 37 0) (sw_tg cx));
        [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 2) with 2%nat. unfold sw_tg, sw_P.
      apply sw_vm2; [exact (proj1 (HPSg 28%nat ltac:(lia))) | | apply sw_bytes_range | apply sw_bytes_range].
      replace (cF cx fpos + 32 + 28 + 1) with (cF cx fpos + 32 + Z.of_nat 29) by lia.
      exact (proj1 (HPSg 29%nat ltac:(lia))).
  + unfold region_ok, sw_tabr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U35. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HT0, HT1.
    split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) (4 * Z.of_nat i) 4 (SOff (38 + i) 0) (sw_tab i)).
    * cbn [sv_denot]. rewrite (E38 i) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn [Z.of_N]. exact (RTB i).
    * cbn. lia.
    * change (N.to_nat 4) with 4%nat. exact (Htab i ltac:(lia)).
- apply pairwise_disjoint_of_extents. unfold sw_loc, sw_q, sw_tabr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U35.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. repeat split; lia.
- unfold sw_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U2; change (2 ^ 4) with 16; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 4) with 16; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U21; rewrite Z.pow_0_r, Z.mod_1_r; unfold SB; lia|].
  split.
  { pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & Ho4m & _).
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
    change (2 ^ 2) with 4. unfold ASAN_CEIL in *. lia. }
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34; unfold cK, disco_classify_c.dkind in *;
    rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
  exact I.
Qed.

End call.

Definition sw_rd6 (cx : ccx) (W3 : world SEGS) (mem3 : word -> option byte) (p : Z) : Prop :=
  0 <= p /\ p + 6 <= 2 ^ 47 /\ amem_range p 6 /\ (p + 6 <= cS1 cx - ESTACK \/ cSP cx <= p) /\
  (p + 6 <= x_o cx \/ x_o cx + 24 <= p) /\
  (forall a, p <= a < p + 6 -> apresent (w_H W3) mem3 a) /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF p 6 /\ shadow_hull_vis (aview SEGS (w_H W3) mem3) p 6.

Lemma sw_rd6_kept : forall cx W3 (mem3 m : word -> option byte) p,
  sw_rd6 cx W3 mem3 p ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m a) ->
  sw_rd6 cx W3 m p.
Proof.
intros cx W3 mem3 m p (H0 & H47 & Ham & Hs & Ho & Hp & Hra & Hhu) K P.
split; [exact H0|]. split; [exact H47|]. split; [exact Ham|]. split; [exact Hs|]. split; [exact Ho|].
split; [intros a Ha; apply P, Hp, Ha|].
split; [exact (sw_ra_kept _ _ _ p 6 H0 H47 K Hra) | exact (sw_hull_kept _ _ _ p 6 H0 ltac:(lia) H47 K Hhu)].
Qed.

Section call2.
Variables (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model).
Hypothesis Hpre : cls_pre B cx.
Hypothesis Hat : cls_at_SW B cx fpos W3 ly3 S3 regs3 mem3 md3.

Lemma sw_band0 : forall m, sw_kept cx W3 mem3 m ->
  forall a, kLowShadowBeg <= a < kHighMemBeg -> aview SEGS (w_H W3) m a = aview SEGS (w_H W3) mem3 a.
Proof.
intros m [K _] a Ha. pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat)
  as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOsh & _ & ES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold kLowShadowBeg in *.
apply K; lia.
Qed.

Lemma sw_o_ok :
  amem_range (x_o cx) 24 /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (x_o cx) 24 /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (x_o cx) 24 /\
  (forall a, x_o cx <= a < x_o cx + 24 ->
     awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 ((2, fpos) :: x_own cx) a).
Proof.
pose proof Hat as (_ & Hc).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & ((_ & _ & Ham & _ & _) & (_ & Hra & Hhu) & _ & _) & _ & _ & Hw & _).
split; [exact Ham|]. split; [exact Hra|]. split; [exact Hhu | exact Hw].
Qed.

Lemma sw_rd6_q : sw_rd6 cx W3 mem3 (cF cx fpos + 36).
Proof.
pose proof Hat as (_ & Hc).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hc) as Hnow. cbv zeta in Hnow.
destruct Hnow as ((HF4 & HFc & HFal & Hz & Hia & HFp & _) & _).
pose proof Hc as (HJ & Hfr & _ & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSHP & _).
pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat)
  as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOF & ES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|].
split; [apply (amem_range_sub_app (cF cx fpos) 256); [exact Hia | lia | lia | lia | lia]|].
split; [left; lia|]. split; [lia|].
split; [intros a Ha; apply HFp; lia|].
split; [apply (sw_ra_pat _ _ (cF cx fpos)); [lia | exact HFal | exact HSHP | lia | lia]|].
apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 mem3 md3 2 fpos); [exact (proj1 HJ) | rewrite Hfr; left; reflexivity | | | lia];
  rewrite Hfa; change (fs_frame_bytes 2) with 256; lia.
Qed.

Lemma sw_memset : forall (fq : YK11.FPState) (regsT : bvmap 5 word) memT mdT (ra : word),
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 memT mdT (x_k cx) ->
  sw_kept cx W3 mem3 memT ->
  spZ regsT = cS1 cx -> getr regsT 3 = getr regs3 3 -> getr regsT 4 = getr regs3 4 ->
  getr regsT 10 = w64 (x_o cx) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 24 ->
  getr regsT 1 = ra -> YK0s.ret_ok ra ->
  SRr SEGS W3 (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA AS___asan_memset)) memT (seg_rom SEGS)) mdT)
   (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := fq) regs2 ra mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        ((2, fpos) :: x_own cx) ly3 S3 W3 mem2 md2 (x_k cx) /\
      aregs_preserved regsT regs2 /\
      (forall i, 0 <= i < 24 -> aview SEGS (w_H W3) mem2 (x_o cx + i) = Some 0) /\
      sw_kept cx W3 mem3 mem2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (x_o cx <= a < x_o cx + 24) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
         aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a) /\
      (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a)).
Proof.
intros fq regsT memT mdT ra HJT HKT Hsp3 G3 G4 Ha0 Ha1 Ha2 Hra1 Hra.
pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat)
  as (_ & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & _ & _ & _ & Hgp & Htp & Ho4 & Hoc & HOsh & _ & ES).
pose proof (sw_band0 memT HKT) as KB.
destruct sw_o_ok as (Ham & Hra0 & Hhu0 & Hw).
pose proof pa_segs_low as Hsegs.
eapply SRr_mono.
{ apply (aj_intrin_at SEGS B LAWS Hsegs OSet _ (AMEMSET fq) W3 regsT memT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx)
    (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 mdT (x_k cx) (x_o cx) 0 24 (cS1 cx - x_sp0 cx)
    ra HJT Ha0 Ha1 Ha2 ltac:(lia) ltac:(lia) ltac:(lia)).
  - lia.
  - rewrite Zminus_mod, HS16, Hsp0al. reflexivity.
  - lia.
  - rewrite ES. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact Hra1.
  - exact Hra.
  - intros a Ha. split; [apply Hw; lia | rewrite ES; lia].
  - exact Ham.
  - exact (sw_ra_kept _ _ _ (x_o cx) 24 ltac:(lia) ltac:(lia) KB Hra0).
  - intros _. exact (sw_hull_kept _ _ _ (x_o cx) 24 ltac:(lia) ltac:(lia) ltac:(lia) KB Hhu0).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & Hpres2).
replace (x_sp0 cx + (cS1 cx - x_sp0 cx)) with (cS1 cx) in Hfr by lia.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [intros i Hi; rewrite (Heff i Hi); reflexivity|].
destruct HKT as [KT PT].
split.
{ split; [|intros a Ha; apply Hpres2, PT, Ha].
  intros a Ha Hn Ho. rewrite (Hfr a Ha) by lia. apply KT; assumption. }
split; [intros a Ha H1 H2; apply Hfr; [exact Ha | exact H1 | exact H2] | exact Hpres2].
Qed.

Lemma sw_memcpy : forall (fq : YK11.FPState) (regsT : bvmap 5 word) memT mdT (ra : word),
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 memT mdT (x_k cx) ->
  sw_kept cx W3 mem3 memT ->
  spZ regsT = cS1 cx -> getr regsT 3 = getr regs3 3 -> getr regsT 4 = getr regs3 4 ->
  getr regsT 10 = w64 (x_o cx) -> getr regsT 11 = w64 (cF cx fpos + 36) -> getr regsT 12 = w64 6 ->
  getr regsT 1 = ra -> YK0s.ret_ok ra ->
  SRr SEGS W3 (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA AS___asan_memcpy)) memT (seg_rom SEGS)) mdT)
   (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := fq) regs2 ra mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        ((2, fpos) :: x_own cx) ly3 S3 W3 mem2 md2 (x_k cx) /\
      aregs_preserved regsT regs2 /\
      (forall i, 0 <= i < 6 -> aview SEGS (w_H W3) mem2 (x_o cx + i) = aview SEGS (w_H W3) mem3 (cF cx fpos + 36 + i)) /\
      sw_kept cx W3 mem3 mem2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (x_o cx <= a < x_o cx + 6) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
         aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a) /\
      (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a)).
Proof.
intros fq regsT memT mdT ra HJT HKT Hsp3 G3 G4 Ha0 Ha1 Ha2 Hra1 Hra.
pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat)
  as (_ & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & HF4 & HFc & _ & Hgp & Htp & Ho4 & Hoc & HOsh & HOF & ES).
pose proof (sw_band0 memT HKT) as KB.
destruct sw_o_ok as (Ham & Hra0 & Hhu0 & Hw).
destruct (sw_rd6_kept cx W3 mem3 memT _ sw_rd6_q KB (proj2 HKT))
  as (Hq0 & Hq47 & Hqam & Hqs & Hqo & Hqp & Hqra & Hqhu).
pose proof pa_segs_low as Hsegs.
eapply SRr_mono.
{ apply (aj_intrin_at SEGS B LAWS Hsegs OCpy _ (AMEMCPY fq) W3 regsT memT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx)
    (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 mdT (x_k cx) (x_o cx) (cF cx fpos + 36) 6 (cS1 cx - x_sp0 cx)
    ra HJT Ha0 Ha1 Ha2 ltac:(lia) ltac:(lia) ltac:(lia)).
  - lia.
  - rewrite Zminus_mod, HS16, Hsp0al. reflexivity.
  - lia.
  - rewrite ES. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact Hra1.
  - exact Hra.
  - intros a Ha. split; [apply Hw; lia | rewrite ES; lia].
  - unfold amem_range in *. lia.
  - refine (sw_ra_kept _ _ _ (x_o cx) 6 _ _ KB _); [lia | lia |].
    refine (sw_ra_sub _ _ _ _ _ _ Hra0 _ _); lia.
  - intros _. refine (sw_hull_kept _ _ _ (x_o cx) 6 _ _ _ KB _); [lia | lia | lia |].
    refine (sw_hull_sub _ _ _ _ _ Hhu0 _ _ _); lia.
  - split; [lia|]. split; [lia|]. split.
    + intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hqp; lia | rewrite Hsp3, ES; lia].
    + split; [lia|]. split; [exact Hqam|]. split; [exact Hqra | intros _; exact Hqhu]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & Hpres2).
replace (x_sp0 cx + (cS1 cx - x_sp0 cx)) with (cS1 cx) in Hfr by lia.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
destruct HKT as [KT PT].
split.
{ intros i Hi. rewrite (Heff i Hi). apply KT; [lia | rewrite ES; lia | lia]. }
split.
{ split; [|intros a Ha; apply Hpres2, PT, Ha].
  intros a Ha Hn Ho. rewrite (Hfr a Ha) by lia. apply KT; assumption. }
split; [intros a Ha H1 H2; apply Hfr; [exact Ha | exact H1 | exact H2] | exact Hpres2].
Qed.

Lemma sw_ko : forall (m4 mT m5 : word -> option byte),
  (forall i, 0 <= i < 24 -> aview SEGS (w_H W3) m4 (x_o cx + i) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mT a = aview SEGS (w_H W3) m4 a) ->
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W3) m5 (x_o cx + i) = aview SEGS (w_H W3) mem3 (cF cx fpos + 36 + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_o cx <= a < x_o cx + 6) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
     aview SEGS (w_H W3) m5 a = aview SEGS (w_H W3) mT a) ->
  forall i, 0 <= i < 24 ->
    aview SEGS (w_H W3) m5 (x_o cx + i) = Some (nth (Z.to_nat i) (cls_bytes (cls_O_ROLE (x_FB cx))) 0).
Proof.
intros m4 mT m5 Hset KF1 Hcpy Hfr3 i Hi.
pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat)
  as (_ & HS1 & _ & Hceil & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & Ho4 & Hoc & _ & _ & ES).
pose proof Hat as (Hret & Hc).
pose proof Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HPS & _).
destruct HPS as (HPSl & HPSg).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFBl & _).
pose proof (sw_ret0 _ _ _ _ Hret) as Hk0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite sw_orole by exact HFBl.
destruct (Z.lt_ge_cases i 6) as [H6|H6].
- rewrite (Hcpy i) by lia.
  replace (cF cx fpos + 36 + i) with (cF cx fpos + 32 + Z.of_nat (4 + Z.to_nat i)) by lia.
  rewrite (sw_aview_garr8 _ _ _ _ _ HPSg) by (unfold cls_bytes; rewrite length_map, HPSl; lia).
  replace (Z.to_nat i <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  unfold cPS. rewrite sw_src; [reflexivity | exact Hk0 | lia].
- rewrite Hfr3 by lia. rewrite KF1 by lia. rewrite Hset by lia.
  replace (Z.to_nat i <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.

End call2.

Definition sw_okO (cx : ccx) (W3 : world SEGS) (m : word -> option byte) : Prop :=
  forall i, 0 <= i < 24 ->
    aview SEGS (w_H W3) m (x_o cx + i) = Some (nth (Z.to_nat i) (cls_bytes (cls_O_ROLE (x_FB cx))) 0).

Lemma sw_okO_run : forall cx W3 (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  sw_okO cx W3 m -> 0 <= x_o cx -> x_o cx + 24 <= 2 ^ 64 -> sw_okO cx W3 m'.
Proof. intros cx W3 m m' KF KO H0 H1 i Hi. rewrite KF by lia. exact (KO i Hi). Qed.

Lemma sw_role_hi : forall FB k, 10 <= k -> disco_classify_c.role FB k = 0.
Proof.
intros FB k Hk. unfold disco_classify_c.role.
destruct (Z.eqb_spec k 1); [lia|]. destruct (Z.eqb_spec k 2); [lia|]. destruct (Z.eqb_spec k 3); [lia|].
destruct (Z.eqb_spec k 4); [lia|]. destruct (Z.eqb_spec k 6); [lia|]. destruct (Z.eqb_spec k 7); [lia|].
destruct (Z.eqb_spec k 9); [lia|]. destruct (Z.eqb_spec k 5); [lia|]. reflexivity.
Qed.

Lemma sw_close : forall cx fpos W3 ly3 S3 regs3 mem3 md3 regs6 mem6 md6,
  cls_from_ROLE B -> cls_pre B cx -> cls_at_SW B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem6 md6 (x_k cx) ->
  sw_kept cx W3 mem3 mem6 -> sw_okO cx W3 mem6 ->
  getr regs6 2 = getr regs3 2 -> getr regs6 3 = getr regs3 3 -> getr regs6 4 = getr regs3 4 ->
  getr regs6 8 = getr regs3 8 -> getr regs6 9 = getr regs3 9 -> getr regs6 18 = getr regs3 18 ->
  getr regs6 19 = getr regs3 19 -> getr regs6 20 = getr regs3 20 -> getr regs6 21 = getr regs3 21 ->
  getr regs6 22 = getr regs3 22 -> getr regs6 27 = getr regs3 27 ->
  getr regs6 11 = w64 (disco_classify_c.role (x_FB cx) (cK cx)) ->
  getr regs6 23 = w64 (x_o cx) -> getr regs6 24 = w64 SHADOW_OFF -> getr regs6 25 = w64 (x_len cx) ->
  SRr SEGS W3 (mkCfg (mkst (fx := x_fq cx) regs6 (Z_to_bv 64 (BASE + PC_ROLE)) mem6 (seg_rom SEGS)) md6) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 regs6 mem6 md6 HROLE HPRE HAT HJ6 [HK6 HP6] HO6
  G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G27 R11 R23 R24 R25. unfold sw_okO in HO6.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 HPRE (proj2 HAT)) as HN.
destruct HAT as [Hret HCUT].
pose proof HPRE as HPRE0.
unfold cls_pre in HPRE0. cbv zeta in HPRE0.
destruct HPRE0 as (HJ0 & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hch & Hsp16 & Hstk & Hsp0 &
  Htop & Hdep & Hlen & HFBl & HUl & HOBl & Hf50 & Hur & Hus & Hug & Ho0 & Ho4 & Hor & Hog & How & Hoff & HL &
  Hdou & Hdof & HdL).
pose proof HCUT as HCUT0.
unfold cls_cut in HCUT0. cbv zeta in HCUT0.
destruct HCUT0 as (HJ & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 &
  HRV & Hspill & Mo & Mf & MF & MLS & HSHPl & HSHP & MFL & HPS & HO3l & HO3 & HL3).
cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & HFpres & HFSpres & HFL4096 & HFLz & HFLc & HFLp & HFLo &
  HFLn & HFb & HFf) & _ & _ & _ & (Hoa & Hol & HoF & HoS) & Ho4096 & Hoc & Hoawr & HNL).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
pose proof Hastk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : CLS_STK = 8512) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (F := cF cx fpos) in *. set (o := x_o cx) in *.
change (spZ (x_regs cx)) with SP in *.
assert (HS1 : SP - 192 < S1 <= SP - 160).
{ subst S1. unfold cS1, cls_S1. fold SP. pose proof (Z.mod_pos_bound (SP - 160) 32 ltac:(lia)).
  pose proof (Z.div_mod (SP - 160) 32 ltac:(lia)). lia. }
assert (HSP : alloc_ceiling + CLS_STK <= SP <= 2 ^ 47) by lia.
destruct Hoa as (Ho0' & Ho47 & Hoamr & Hooff & Hoband).
assert (TR : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall x, a <= x < a + n -> ~ (o <= x < o + 24) /\ ~ (S1 - ESTACK <= x < S1)) ->
  forall i, 0 <= i < n -> aview SEGS (w_H W3) mem6 (a + i) = aview SEGS (w_H W3) mem3 (a + i)).
{ intros a n Ha Han Hx i Hi. destruct (Hx (a + i) ltac:(lia)) as [X1 X2]. apply HK6; [lia | exact X2 | exact X1]. }
apply (HROLE cx fpos W3 ly3 S3 regs6 mem6 md6 HPRE).
unfold cls_at_ROLE, cls_cut. cbv zeta. split; [exact Hret|].
try change (cF cx fpos) with F. try change (cSP cx) with SP. try change (cS1 cx) with S1. try change (x_o cx) with o.
split; [exact HJ6|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|].
split.
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 mem6 (fun a => (o <= a < o + 24) \/ (S1 - ESTACK <= a < S1))
    HPRE (proj1 HJ) Hfr Hnin Hperm Hfa Hfl Hkept).
  - intros a Ha Hn. apply HK6; [exact Ha | intros X; apply Hn; right; exact X | intros X; apply Hn; left; exact X].
  - exact HP6.
  - intros a [Ha | Ha]; [right; left; unfold cls_wr; left; exact Ha | left; lia]. }
split; [rewrite G2; exact R2|]. split; [rewrite G3; exact R3|]. split; [rewrite G4; exact R4|].
split; [rewrite G8; exact R8|]. split; [rewrite G9; exact R9|]. split; [rewrite G18; exact R18|].
split; [rewrite G19; exact R19|]. split; [rewrite G20; exact R20|]. split; [rewrite G27; exact R27|].
rewrite !Forall_cons_iff in HRV. cbn [fst snd] in HRV. destruct HRV as (V21 & V22 & V25 & _).
split.
{ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact R11.
  - exact (eq_trans G21 V21).
  - exact (eq_trans G22 V22).
  - exact R23.
  - exact R24.
  - exact R25. }
split.
{ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) Hspill p Hp) as Hv.
  assert (Hb : -104 <= snd p <= -8)
    by (unfold cls_spills in Hp; cbn [In] in Hp; repeat (destruct Hp as [<-|Hp]; [cbn [snd]; lia|]); destruct Hp).
  apply (sw_vm_kept _ mem3 mem6); [|exact Hv].
  apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_kept _ mem3 mem6); [|exact Mo]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_kept _ mem3 mem6); [|exact Mf]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_kept _ mem3 mem6); [|exact MF]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split; [intros X; discriminate X|].
split; [exact HSHPl|].
split.
{ apply (sw_garr8_kept _ mem3 mem6); [|exact HSHP]. rewrite HSHPl. change (Z.of_nat 32) with 32.
  assert (HF8 : F / 8 < 2 ^ 44 - 2 ^ 20) by (apply Z.div_lt_upper_bound; lia).
  assert (HF80 : 0 <= F / 8) by (apply Z.div_pos; lia).
  intros j Hj. apply TR with (n := 32); [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | | lia].
  intros x Hx. unfold SHADOW_OFF in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hoamr.
  split; lia. }
split.
{ apply (sw_vm_kept _ mem3 mem6); [|exact MFL]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split; [exact I|].
assert (HOL : length (cls_O_ROLE (x_FB cx)) = 24%nat).
{ unfold cls_O_ROLE, disco_classify_c.src, CtrlParsed.fld. rewrite length_app, repeat_length, length_firstn, length_skipn.
  rewrite HFBl. reflexivity. }
split; [exact HOL|].
split.
{ apply sw_garr8_of_aview. intros j Hj. unfold cls_bytes in Hj. rewrite length_map, HOL in Hj.
  rewrite (HO6 (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity. }
destruct (x_L cx) as [Lx|] eqn:EL; destruct (cLock cx) as [Lb|]; [| exact HL3 | exact HL3 | exact I].
destruct HL3 as [HLl HLg]. split; [exact HLl|].
destruct HNL as ((Hla & _ & HlF & HlS) & _ & _ & _).
destruct HdL as (Hdlo & _ & _).
apply (sw_garr8_kept _ mem3 mem6); [|exact HLg].
assert (HLc : length (cls_bytes Lb) = 12%nat) by (unfold cls_bytes; rewrite length_map; exact HLl). rewrite HLc.
destruct Hla as (Hl0 & Hl47 & _).
intros j Hj. apply TR with (n := 12); [clear - Hl0; lia | clear - Hl47; lia | | lia].
intros x Hx; split; [clear - Hx Hdlo; lia | clear - Hx HlS HS1 HCS HES; lia].
Qed.

Ltac sw_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]].

Ltac sw_wr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|]);
  destruct Hin.

Ltac sw_step KM :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let K := fresh "KM" in
    pose proof (sw_kept_run _ _ _ _ _ _ _ KM HFr HG ltac:(sw_wr)) as K;
    clear KM; rename K into KM
  end.

Ltac sw_step2 KM KO :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _ |- _ =>
    let KF := fresh "KF" in
    pose proof (sw_frame_aview _ rs _ mA mB HFr ltac:(sw_wr)) as KF;
    let K2 := fresh "KO" in
    pose proof (sw_okO_run _ _ _ _ KF KO ltac:(lia) ltac:(lia)) as K2; clear KO KF; rename K2 into KO;
    let K := fresh "KM" in
    pose proof (sw_kept_run _ _ _ _ _ _ _ KM HFr HG ltac:(sw_wr)) as K;
    clear KM HFr HG; rename K into KM
  end;
  try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end.

Ltac sw_kf KF :=
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
    pose proof (sw_frame_aview _ rs _ mA mB HFr ltac:(sw_wr)) as KF end.

Ltac sw_fix HS AG EW :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let G := fresh "G" in prreg HS r G; refine (eq_trans G _); refine (eq_trans (AG _ _) _);
    first [apply EW; reflexivity | cbv; lia] end.

Ltac sw_rv HS :=
  lazymatch goal with |- getr _ ?r = _ => let G := fresh "G" in prreg HS r G; refine (eq_trans G _) end.

Ltac sw_sp HS AG U2 :=
  unfold spZ; lazymatch goal with |- bv_unsigned (getr _ ?r) = _ =>
    let G := fresh "G" in prreg HS r G; rewrite G; first [exact U2 | rewrite (AG 2%nat) by lia; exact U2] end.

Ltac sw_shok HS :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) (mkst _ _ ?mx _)) =>
    try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
    assert (SHOK : sh_ok SEGS SW_Bx [] Ex (mrestrict (w_H Wx) mx)) by apply Forall_nil end.

Ltac sw_envU HS AG U9 U22 U9n U22n :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch type of U9 with bv_unsigned (ew _ 9) = ?v9 =>
  lazymatch type of U22 with bv_unsigned (ew _ 22) = ?v22 =>
    assert (U9n : bv_unsigned (ew Ex 9) = v9) by (rewrite (AG 9%nat) by lia; exact U9);
    assert (U22n : bv_unsigned (ew Ex 22) = v22) by (rewrite (AG 22%nat) by lia; exact U22) end end end.

Ltac sw_u35 HS EO35 U35 :=
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  assert (U35 : bv_unsigned (ew Ex 276%nat) = VAL (A_OBJ 35))
    by (rewrite EO35; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 35)); lia).

Ltac sw_tail HS AG EW E33 E32 Rs5 :=
  first [ sw_rv HS; exact E33
        | sw_rv HS; rewrite (AG 21%nat) by lia; rewrite (EW 21%nat (Z_to_bv 5 21) eq_refl); exact Rs5
        | sw_rv HS; rewrite (AG 32%nat) by lia; exact E32 ].

Ltac sw_jrpin HS T EO35 i :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
    let HEIx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
    let HS2 := fresh "HS" in
    pose proof (sw_jr_pin _ Ex ss msx i _ ltac:(lia) HEIx HS T ltac:(vm_compute; reflexivity) EO35) as HS2;
    clear HS; rename HS2 into HS end.

Ltac sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 i T :=
  let HS2 := fresh "HS" in
  pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv _ HS G10 eq_refl) as HS2; clear HS G10; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK sw_span; [solve [sw_awr] |];
  sw_step2 KM KO;
  sw_jrpin HS T EO35 i;
  paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |];
  sw_step2 KM KO.

Ltac sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5 :=
  pmkst HS;
  apply (sw_close _ _ _ _ _ _ _ _ _ _ _ HROLE Hpre Hat0 HJ KM KO); try (sw_fix HS AG EW);
    try (sw_tail HS AG EW E33 E32 Rs5); sw_rv HS.

Ltac sw_kept_b Hfr Hp U9 U22 U35 :=
  eapply region_kept_aview;
  [ first [exact U9 | exact U22 | exact U35]
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr; unfold ESTACK in *; lia
  | exact Hp ].

Theorem cls_sw : cls_from_ROLE B -> cls_from_SW B.
Proof.
intros HROLE. unfold cls_from_SW, cls_from.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0.
pose proof (sw_entry cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0) as HS.
pose proof (sw_ctx cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0)
  as (Hsp16 & HS1 & HS16 & Hceil & Hstk & Hsp & H47 & Hsp0al & HF4 & HFc & HFal & Hgp & Htp & Ho4 & Hoc & HOsh & HOF & ES).
pose proof sw_tab_img as (HT0 & HT1). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HT0, HT1.
pose proof Hat0 as (Hret & Hcut).
pose proof Hcut as (HJ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV & _).
apply Forall_cons_iff in HRV as [Rs5 HRV]. apply Forall_cons_iff in HRV as [Rs6 HRV].
apply Forall_cons_iff in HRV as [Rs9 _]. cbn [fst snd] in Rs5, Rs6, Rs9.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (RcParse.ctrlparse_kind_range (x_len cx) (x_FB cx)) as HKr.
pose proof (sw_ret0 _ _ _ _ Hret) as Hk0.
destruct (sw_ew cx regs3) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & EO35 & EW).
pose proof (E38 0%nat ltac:(lia)) as T0. pose proof (E38 1%nat ltac:(lia)) as T1. pose proof (E38 2%nat ltac:(lia)) as T2.
pose proof (E38 3%nat ltac:(lia)) as T3. pose proof (E38 4%nat ltac:(lia)) as T4. pose proof (E38 5%nat ltac:(lia)) as T5.
pose proof (E38 6%nat ltac:(lia)) as T6. pose proof (E38 7%nat ltac:(lia)) as T7. pose proof (E38 8%nat ltac:(lia)) as T8.
cbn [Nat.add] in T0, T1, T2, T3, T4, T5, T6, T7, T8. clear E38.
change (ew (SWE cx regs3) (A_OBJ 35)) with (ew (SWE cx regs3) 276%nat) in EO35.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as Hnow. cbv zeta in Hnow.
destruct Hnow as (_ & _ & _ & _ & ((_ & _ & _ & HOoff & _) & _) & _). unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOoff.
set (fq := x_fq cx) in *.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
set (E0 := SWE cx regs3) in *.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok SEGS SW_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
clearbody E0.
assert (AG : forall n, (n < 33)%nat -> ew E0 n = ew E0 n) by reflexivity.
assert (U9 : bv_unsigned (ew E0 9) = cS1 cx)
  by (rewrite (EW 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U2 : bv_unsigned (ew E0 2) = cS1 cx)
  by (rewrite (EW 2%nat 2%bv eq_refl), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (U22 : bv_unsigned (ew E0 22) = cF cx fpos + 32)
  by (rewrite (EW 22%nat (Z_to_bv 5 22) eq_refl), Rs6; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (KM : sw_kept cx W3 mem3 mem3) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
unfold cfg_at. change (w64 (BASE + PC_SW)) with (Z_to_bv 64 (BASE + PC_SW)).
paj_run_tok RUN HS HJ SHOK sw_span; [solve [sw_awr] |].
sw_step KM.
try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end.
pmkst HS.
sw_u35 HS EO35 U35.
eapply SRr_bind.
{ eapply (sw_memset cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0 fq _ _ _ _ HJ KM).
  - sw_sp HS AG U2.
  - sw_fix HS AG EW.
  - sw_fix HS AG EW.
  - sw_rv HS. exact E33.
  - sw_rv HS. reflexivity.
  - sw_rv HS. reflexivity.
  - sw_rv HS. reflexivity.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ2 & HPs & Hset & KM2 & Hfrs & Hprs).
reseat HS HJ2 HPs [0;1;2]%nat AG ltac:(sw_kept_b Hfrs Hprs U9 U22 U35).
clear KM HJ U35. rename KM2 into KM. rename HJ2 into HJ. sw_shok HS.
sw_envU HS AG U9 U22 U9b U22b. sw_u35 HS EO35 U35.
paj_run_tok RUN HS HJ SHOK sw_span; [solve [sw_awr] |].
sw_kf KF1.
sw_step KM.
try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end.
pmkst HS.
eapply SRr_bind.
{ eapply (sw_memcpy cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0 fq _ _ _ _ HJ KM).
  - sw_sp HS AG U2.
  - sw_fix HS AG EW.
  - sw_fix HS AG EW.
  - sw_rv HS. exact E33.
  - sw_rv HS. rewrite (AG 25%nat) by lia. rewrite (EW 25%nat (Z_to_bv 5 25) eq_refl). exact Rs9.
  - sw_rv HS. reflexivity.
  - sw_rv HS. reflexivity.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs5 & mem5 & md5 & -> & HJ2 & HPc & Hcpy & KM2 & Hfr3 & Hpres3).
pose proof (sw_ko cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre Hat0 _ _ _ Hset KF1 Hcpy Hfr3) as KO.
clear Hset KF1 Hcpy Hfrs Hprs.
reseat HS HJ2 HPc [0;1;2]%nat AG ltac:(sw_kept_b Hfr3 Hpres3 U9b U22b U35).
clear KM HJ U35 U9b U22b. rename KM2 into KM. rename HJ2 into HJ. sw_shok HS.
sw_envU HS AG U9 U22 U9b U22b. sw_u35 HS EO35 U35.
paj_run_tok RUN HS HJ SHOK sw_span; [solve [sw_awr] |].
sw_step2 KM KO.
psrr_branch_tok RUN BR HS SHOK sw_span.
- rewrite branch_ltu_U, U_lit, (U_atom_off _ 34 (cK cx) (-1) E34) in Hc by (unfold cK, disco_classify_c.dkind in *; lia).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
  sw_step2 KM KO.
  pmkst HS.
  sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
  rewrite sw_role_hi by lia. reflexivity.
- rewrite branch_ltu_U, U_lit, (U_atom_off _ 34 (cK cx) (-1) E34) in Hc by (unfold cK, disco_classify_c.dkind in *; lia).
  apply Z.ltb_ge in Hc. rename Hc into Hk8.
  prreg HS (10%bv : bv 5) G10. rewrite E34, unsigned_lit_small in G10 by (unfold cK, disco_classify_c.dkind in *; lia).
  assert (Hk9 : cK cx = 1 \/ cK cx = 2 \/ cK cx = 3 \/ cK cx = 4 \/ cK cx = 5 \/ cK cx = 6 \/ cK cx = 7 \/
    cK cx = 8 \/ cK cx = 9) by (unfold cK, disco_classify_c.dkind in *; lia).
  destruct Hk9 as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]]; rewrite Hk in G10.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 0%nat T0.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
    rewrite E35, (sw_bc_val cx) by lia. rewrite Hk. unfold disco_classify_c.role.
    destruct (RcParse.cp_bcast (x_FB cx)); apply bv_eq; vm_compute; reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 1%nat T1.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 2%nat T2.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 3%nat T3.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 4%nat T4.
    assert (RFB : 0 <= sw_fb cx < 256) by apply sw_bytes_range.
    assert (RTG : 0 <= sw_tg cx < 2 ^ 16)
      by (unfold sw_tg, sw_P; pose proof (sw_bytes_range (cPS cx) 28); pose proof (sw_bytes_range (cPS cx) 29); lia).
    pose proof (sw_fb_val cx ltac:(lia)) as Fb. pose proof (sw_tg_val cx Hk) as Tg.
    psrr_branch_tok RUN BR HS SHOK sw_span.
    * rewrite branch_eq_U, (U_atom _ 36 (sw_fb cx) E36), U_lit in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hfb.
      paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
      sw_step2 KM KO.
      psrr_branch_tok RUN BR HS SHOK sw_span.
      -- rewrite branch_eq_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
         paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
         sw_step2 KM KO.
         sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
         rewrite Hk, sw_role5_one; [reflexivity | lia | lia].
      -- rewrite branch_eq_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Ht1.
         paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
         sw_step2 KM KO.
         psrr_branch_tok RUN BR HS SHOK sw_span.
         ++ rewrite branch_eq_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
            paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
            sw_step2 KM KO.
            sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
            rewrite Hk, sw_role5_one; [reflexivity | lia | lia].
         ++ rewrite branch_eq_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Ht2.
            paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
            sw_step2 KM KO.
            psrr_branch_tok RUN BR HS SHOK sw_span.
            ** rewrite branch_ne_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia.
               apply negb_true_iff, Z.eqb_neq in Hc.
               paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
               sw_step2 KM KO.
               sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
               rewrite Hk, sw_role5_tag; [reflexivity | lia | lia | lia].
            ** rewrite branch_ne_U, (U_atom _ 37 (sw_tg cx) E37), U_lit in Hc by lia.
               apply negb_false_iff, Z.eqb_eq in Hc.
               paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
               sw_step2 KM KO.
               sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
               rewrite Hk, sw_role5_one; [reflexivity | lia | lia].
    * rewrite branch_eq_U, (U_atom _ 36 (sw_fb cx) E36), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK sw_span PC_ROLE; [solve [sw_awr] |].
      sw_step2 KM KO.
      sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5.
      rewrite Hk, sw_role5_fb; [reflexivity | lia].
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 5%nat T5.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 6%nat T6.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 7%nat T7.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
  + sw_go RUN RUNTO HS HJ SHOK KM KO EO35 G10 8%nat T8.
    sw_exit HROLE Hpre Hat0 HS HJ KM KO AG EW E33 E32 Rs5. rewrite Hk. reflexivity.
Qed.

End h.
End f.
End d.
