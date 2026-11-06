(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module paths and module names changed; 765 of its 806 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ClassifyCoreM4.v, with its module paths, module names and numbers changed; 65 of its 805 lines of code are new or changed and 66 lines of the source are left out. *)
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
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition m4_D (F : list byte) : list byte :=
match disco_classify_c.sdecl F with
| Some (i, o) => [CtrlParsed.zb 1; CtrlParsed.zb i; CtrlParsed.zb o]
| None => [CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0]
end.
Definition m4_A (F : list byte) (len : Z) : list byte :=
disco_classify_c.src F ++ [CtrlParsed.zb 0; CtrlParsed.zb 0]
++ Mem.le4 (Z_to_bv 64 (disco_classify_c.role F (disco_classify_c.dkind F len))).
Definition m4_C (F : list byte) : list byte :=
[CtrlParsed.zb 0; CtrlParsed.zb (disco_classify_c.slots F); CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0].
Definition m4_Z3 : list byte := [CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0].
Definition m4_Z4 : list byte := [CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0].
Lemma m4_sight : forall F len,
disco_classify_c.sight F len = m4_A F len ++ m4_D F ++ m4_C F ++ Mem.le4 (Z_to_bv 64 (disco_classify_c.geo len)).
Proof. intros F len. unfold disco_classify_c.sight, m4_A, m4_D, m4_C. rewrite <- !app_assoc. reflexivity. Qed.
Lemma m4_OQ : forall F len, cls_O_Q F len = m4_A F len ++ m4_Z3 ++ m4_C F ++ m4_Z4.
Proof. intros F len. unfold cls_O_Q, m4_A, m4_Z3, m4_C, m4_Z4. rewrite <- !app_assoc. reflexivity. Qed.
Lemma m4_A_len : forall F len, length F = 50%nat -> length (m4_A F len) = 12%nat.
Proof.
intros F len H. unfold m4_A, disco_classify_c.src, CtrlParsed.fld, Mem.le4.
rewrite !length_app, length_firstn, length_skipn, H. cbn. reflexivity.
Qed.
Lemma m4_D_len : forall F, length (m4_D F) = 3%nat.
Proof. intros F. unfold m4_D. destruct (disco_classify_c.sdecl F) as [[? ?]|]; reflexivity. Qed.
Lemma m4_cnt_range : forall f bs k, 0 <= RcLeaf.cnt f bs k <= Z.of_nat k.
Proof. intros f bs k. induction k as [|k IH]; cbn [RcLeaf.cnt]; [lia|]. destruct (f _); lia. Qed.
Lemma m4_nin : forall bs, 0 <= 4 * RcLeaf.n_in bs <= 48.
Proof. intros bs. unfold RcLeaf.n_in. pose proof (m4_cnt_range RcLeaf.is_in bs 12). cbn [Z.of_nat Pos.of_succ_nat] in *. lia. Qed.
Lemma m4_nout : forall bs, 0 <= 4 * RcLeaf.n_out bs <= 48.
Proof. intros bs. unfold RcLeaf.n_out. pose proof (m4_cnt_range RcLeaf.is_out bs 12). cbn [Z.of_nat Pos.of_succ_nat] in *. lia. Qed.
Lemma m4_D_ok : forall F, RcLeaf.decl (CtrlParsed.fld F 18 20) = true ->
4 * RcLeaf.n_in (CtrlParsed.fld F 18 20) <= 40 -> 4 * RcLeaf.n_out (CtrlParsed.fld F 18 20) <= 40 ->
m4_D F = [CtrlParsed.zb 1; CtrlParsed.zb (4 * RcLeaf.n_in (CtrlParsed.fld F 18 20)); CtrlParsed.zb (4 * RcLeaf.n_out (CtrlParsed.fld F 18 20))].
Proof.
intros F Hd Hi Ho. unfold m4_D, disco_classify_c.sdecl. cbv zeta. rewrite Hd.
rewrite (proj2 (Z.leb_le _ _) Hi), (proj2 (Z.leb_le _ _) Ho). reflexivity.
Qed.
Lemma m4_D_no : forall F, (RcLeaf.decl (CtrlParsed.fld F 18 20) = false \/
40 < 4 * RcLeaf.n_in (CtrlParsed.fld F 18 20) \/ 40 < 4 * RcLeaf.n_out (CtrlParsed.fld F 18 20)) ->
m4_D F = m4_Z3.
Proof.
intros F H. unfold m4_D, disco_classify_c.sdecl. cbv zeta.
destruct H as [H | [H | H]].
- rewrite H. reflexivity.
- rewrite (proj2 (Z.leb_gt _ _) H), andb_false_r. reflexivity.
- rewrite (proj2 (Z.leb_gt _ _) H), andb_false_r. reflexivity.
Qed.
Lemma m4_ret0 : forall F len U L O, disco_classify_c.cm_ret F len U L = 0 ->
50 <= len /\ disco_classify_c.cm_out F len U L O = disco_classify_c.sight F len.
Proof.
intros F len U L O H. unfold disco_classify_c.cm_ret, disco_classify_c.cm_out, disco_classify_c.classify_model in *.
cbv zeta in *.
destruct (Z.eqb_spec (disco_classify_c.dkind F len) 0) as [K|K]; [cbn in H; discriminate H|].
assert (H50 : 50 <= len).
{ unfold disco_classify_c.dkind, RcParse.ctrlparse in K.
  destruct (RcParse.cp_hdr len F) eqn:HE; [apply RcParse.cp_hdr_spec in HE; tauto | cbn in K; lia]. }
split; [exact H50|].
destruct (CtrlParsed.bytes_eqb (disco_classify_c.src F) U); [cbn in H; discriminate H|].
destruct (negb (disco_classify_c.dkind F len =? 1) && negb (disco_classify_c.fsum F =? 0)); [cbn in H; discriminate H|].
destruct L as [Lb|]; [|reflexivity].
destruct ((disco_classify_c.dkind F len =? 1) && negb (disco_classify_c.lv Lb =? 0)
  && negb (CtrlParsed.bytes_eqb (disco_classify_c.lm Lb) (disco_classify_c.src F))); [cbn in H; discriminate H|].
reflexivity.
Qed.
Lemma m4_pk_decl : forall p q bs, p <> 0 -> q <> 0 -> RcLeaf.ports_ok p q bs = RcLeaf.decl bs.
Proof.
intros p q bs Hp Hq. unfold RcLeaf.ports_ok. rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq). reflexivity.
Qed.
Lemma m4_cls_bytes_app : forall l1 l2, cls_bytes (l1 ++ l2) = cls_bytes l1 ++ cls_bytes l2.
Proof. intros. unfold cls_bytes. apply map_app. Qed.
Lemma m4_cls_bytes_len : forall l, length (cls_bytes l) = length l.
Proof. intros. unfold cls_bytes. apply length_map. Qed.
Definition m4_oA : YP09.region := YP09.mkRegion (Some 23%nat) 0 15 12 15
[YP09.mkChunk 12 (CVal 1 (SLit 0)); YP09.mkChunk 13 (CVal 1 (SLit 0)); YP09.mkChunk 14 (CVal 1 (SLit 0))].
Definition m4_oB : YP09.region := YP09.mkRegion (Some 23%nat) 15 24 20 24 [].
Definition m4_fsR : YP09.region := YP09.mkRegion (Some 27%nat) 0 32 0 0 [].
Definition m4_fR (pk : bool) : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 0
(if pk then [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0))] else []).
Definition m4_rR : YP09.region := YP09.mkRegion (Some (A_OBJ 36)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit CLS_RECIP))].
Definition m4_regions (pk : bool) : smem := [m4_oA; m4_oB; m4_fsR; m4_fR pk; m4_rR].
Definition m4_facts : facts := mkFacts [(24%nat, mkAF SB SB 0); (23%nat, mkAF 4096 (2 ^ 47 - 24) 2);
(32%nat, mkAF 0 48 0); (33%nat, mkAF 0 48 0)] [] [].
Definition m4_sr (pk : bool) : list sv := sr_set sr_atoms (10%bv : bv 5) (SLit (if pk then 0 else -1)).
Definition ss_m4 (pk : bool) : sstate := mkSS PC_R3 (m4_sr pk) (m4_regions pk) None m4_facts.
Definition M4Bx : sv := SOff 24 0.
Definition M4span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition M4SH : list shent := [mkSHE 23 0 24].

Definition m4_geo_sv : sv :=
let Q := SAlu ALU_SRL (SMd M_MULHU (SOff 25 (-52)) (SLit CLS_RECIP)) (SLit 5) in
SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_SUB (SOff 25 (-52)) (SMd M_MUL Q (SLit 36)))) (SLit (-1))) Q.
Lemma m4_recip : 36 * CLS_RECIP = 2 ^ 69 + 28.
Proof. vm_compute. reflexivity. Qed.
Lemma m4_div36 : forall x, 0 <= x < 2 ^ 64 ->
0 <= Z.shiftr (x * CLS_RECIP) 64 < 2 ^ 64 /\ Z.shiftr (Z.shiftr (x * CLS_RECIP) 64) 5 = x / 36.
Proof.
intros x Hx.
pose proof (Z.div_mod x 36 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as Mx.
set (q := x / 36) in *. set (r := x mod 36) in *. clearbody q r.
pose proof m4_recip as HR36.
assert (HR : 0 <= CLS_RECIP) by (unfold CLS_RECIP; apply Z.div_pos; lia).
assert (Hq : 0 <= q) by lia.
assert (E1 : x * CLS_RECIP = 2 ^ 69 * q + (28 * q + r * CLS_RECIP)) by nia.
assert (B1 : 0 <= 28 * q + r * CLS_RECIP < 2 ^ 69).
{ assert (r * CLS_RECIP <= 35 * CLS_RECIP) by nia. split; [nia|]. lia. }
assert (D69 : (x * CLS_RECIP) / 2 ^ 69 = q).
{ symmetry. apply (Z.div_unique (x * CLS_RECIP) (2 ^ 69) q (28 * q + r * CLS_RECIP)); [left; exact B1 | lia]. }
rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
change (2 ^ 64 * 2 ^ 5) with (2 ^ 69). split; [|exact D69].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
assert (CLS_RECIP < 2 ^ 64) by (unfold CLS_RECIP; apply Z.div_lt_upper_bound; lia).
nia.
Qed.


Lemma m4_geo_U : forall E len, bv_unsigned (ew E 25) = len -> 52 <= len < 2 ^ 64 ->
U E m4_geo_sv mod 2 ^ 32 = disco_classify_c.geo len.
Proof.
intros E len H21 Hl. unfold m4_geo_sv. cbv zeta.
assert (Ux : U E (SOff 25 (-52)) = len - 52) by (rewrite U_SOff, H21; apply zcanon_id; unfold M64; lia).
assert (HR : 0 <= CLS_RECIP < 2 ^ 64) by (unfold CLS_RECIP; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
destruct (m4_div36 (len - 52) ltac:(lia)) as [B64 D36].
assert (UQ : U E (SAlu ALU_SRL (SMd M_MULHU (SOff 25 (-52)) (SLit CLS_RECIP)) (SLit 5)) = (len - 52) / 36).
{ rewrite U_SAlu, U_SMd, Ux, !U_SLit. rewrite (zcanon_id CLS_RECIP) by (unfold M64; lia).
  cbn [zalu_raw zmd_raw]. change (Z.of_N 64) with 64. rewrite (zcanon_id (Z.shiftr _ 64)) by (unfold M64; lia).
  change (zcanon 5) with 5. change (Z.land 5 63) with 5. rewrite D36. apply zcanon_id. unfold M64.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite U_SAlu, UQ, U_SAlu, U_SAlu, U_SAlu, U_SMd, UQ, Ux, !U_SLit. cbn [zalu_raw zmd_raw].
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as Mx.
assert (Hq : 0 <= (len - 52) / 36 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold disco_classify_c.geo. rewrite (proj2 (Z.leb_le 52 len)) by lia. cbn [andb].
set (q := (len - 52) / 36) in *. set (r := (len - 52) mod 36) in *. clearbody q r.
change (zcanon 0) with 0. change (zcanon 36) with 36. change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite (zcanon_id (q * 36)) by (unfold M64; lia).
replace (len - 52 - q * 36) with r by lia. rewrite (zcanon_id r) by (unfold M64; lia).
destruct (Z.eqb_spec r 0) as [Er | Er].
- subst r. change (0 <? 0) with false. cbv iota. change (zcanon (zcanon 0 + (2 ^ 64 - 1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small q) by lia. rewrite (zcanon_id q) by (unfold M64; lia). reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 r)) by lia. change (zcanon (zcanon 1 + (2 ^ 64 - 1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

Lemma m4_geo_range : forall len, 0 <= disco_classify_c.geo len < 2 ^ 32.
Proof. intros len. unfold disco_classify_c.geo. destruct (_ && _); [apply Z.mod_pos_bound; lia | lia]. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PO : PAObjImg lib_both3_0_listing}.
Lemma m4_split_OQ : forall m o F len, length F = 50%nat ->
garr8 SEGS m o (cls_bytes (cls_O_Q F len)) ->
garr8 SEGS m o (cls_bytes (m4_A F len)) /\ garr8 SEGS m (o + 12) (cls_bytes m4_Z3) /\
garr8 SEGS m (o + 15) (cls_bytes (m4_C F)) /\ garr8 SEGS m (o + 20) (cls_bytes m4_Z4).
Proof.
intros m o F len HL H. rewrite m4_OQ, !m4_cls_bytes_app in H.
apply garr8_app in H as [HA H]. apply garr8_app in H as [HZ H]. apply garr8_app in H as [HC HZ4].
rewrite !m4_cls_bytes_len, m4_A_len in HZ, HC, HZ4 by exact HL.
rewrite m4_cls_bytes_len in HC, HZ4. rewrite m4_cls_bytes_len in HZ4.
cbn [length m4_Z3 m4_C Nat.add Z.of_nat Pos.of_succ_nat] in HZ, HC, HZ4.
split; [exact HA|]. split; [exact HZ|]. split; [replace (o + 15) with (o + 12 + 3) by lia; exact HC|].
replace (o + 20) with (o + 12 + 3 + 5) by lia. exact HZ4.
Qed.

Definition m4_kregs : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 27%bv].
Lemma m4_pat : PAT_A = firstn 14 PAT_B ++ [248; 248] ++ skipn 16 PAT_B /\
PAT_B = firstn 14 PAT_B ++ [0; 4] ++ skipn 16 PAT_B.
Proof. split; reflexivity. Qed.
Lemma m4_mbyte_keep : forall (Wr : Z -> Prop) (H : word -> bool) (m m' : word -> option byte) a,
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
0 <= a < 2 ^ 64 -> ~ Wr a -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
intros Wr H m m' a Hk Ha Hw. unfold mbyte. rewrite Hk; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hw.
Qed.
Lemma m4_vm_keep : forall (Wr : Z -> Prop) (H : word -> bool) (m m' : word -> option byte) a n v,
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
(forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ Wr (a + k)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros Wr H m m' a n v Hk Hr Hv k Hkn. destruct (Hr (Z.of_nat k) ltac:(lia)) as [Ha Hw].
rewrite (m4_mbyte_keep Wr H m m' _ Hk Ha Hw). exact (Hv k Hkn).
Qed.
Lemma m4_ga_keep : forall (Wr : Z -> Prop) (H : word -> bool) (m m' : word -> option byte) a l,
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
(forall k, a <= k < a + Z.of_nat (length l) -> 0 <= k < 2 ^ 64 /\ ~ Wr k) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros Wr H m m' a l Hk Hr Hg. apply (garr8_frame SEGS _ _ _ _ Hg).
intros k Hka. destruct (Hr k Hka) as [Ha Hw]. exact (m4_mbyte_keep Wr H m m' k Hk Ha Hw).
Qed.
Lemma m4_chunk_byte : forall E m n b lo hi wlo whi cs off (w : N) e i,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk off (CVal w e)) cs -> 0 <= i < Z.of_N w ->
mbyte SEGS m (b + off + i) = Some (byte_of_word (sv_denot E e) i).
Proof.
intros E m n b lo hi wlo whi cs off w e i (_ & _ & _ & Hcs) Hn Hc Hi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck i ltac:(unfold YP09.c_len; cbn [YP09.c_val cv_len]; lia)) as (bt & Hb & Hm).
cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm. injection Hb as <-. exact Hm.
Qed.
Lemma m4_garr8_bytes : forall m b (l : list byte),
(forall j, (j < length l)%nat -> mbyte SEGS m (b + Z.of_nat j) = Some (nth j l (Z_to_bv 8 0))) ->
garr8 SEGS m b (cls_bytes l).
Proof.
intros m b l H j Hj. unfold cls_bytes in *. rewrite length_map in Hj.
rewrite (nth_indep _ 0 ((fun b0 : byte => bv_unsigned b0) (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hj). f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned (nth j l (Z_to_bv 8 0))) 256) by lia.
rewrite (Z.mod_small (bv_unsigned (nth j l (Z_to_bv 8 0))) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma m4_bow0 : forall E e, byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (U E e).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma m4_HD : forall E m cs lo hi wlo whi e12 e13 e14 o (D : list byte),
region_ok SEGS E m (YP09.mkRegion (Some 23%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 23) = o ->
In (YP09.mkChunk 12 (CVal 1 e12)) cs -> In (YP09.mkChunk 13 (CVal 1 e13)) cs -> In (YP09.mkChunk 14 (CVal 1 e14)) cs ->
D = [Z_to_bv 8 (U E e12); Z_to_bv 8 (U E e13); Z_to_bv 8 (U E e14)] ->
garr8 SEGS m (o + 12) (cls_bytes D).
Proof.
intros E m cs lo hi wlo whi e12 e13 e14 o D Hr Ho H12 H13 H14 ->.
apply m4_garr8_bytes. intros j Hj. cbn [length] in Hj.
destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth].
- rewrite <- m4_bow0. replace (o + 12 + Z.of_nat 0) with (o + 12 + 0) by lia. exact (m4_chunk_byte E m 23 o lo hi wlo whi cs 12 1 e12 0 Hr Ho H12 ltac:(lia)).
- rewrite <- m4_bow0. replace (o + 12 + Z.of_nat 1) with (o + 13 + 0) by lia. exact (m4_chunk_byte E m 23 o lo hi wlo whi cs 13 1 e13 0 Hr Ho H13 ltac:(lia)).
- rewrite <- m4_bow0. replace (o + 12 + Z.of_nat 2) with (o + 14 + 0) by lia. exact (m4_chunk_byte E m 23 o lo hi wlo whi cs 14 1 e14 0 Hr Ho H14 ltac:(lia)).
Qed.
Lemma m4_le4_nth : forall g j, (j < 4)%nat -> nth j (Mem.le4 (Z_to_bv 64 g)) (Z_to_bv 8 0) =
Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 g)) (8 * Z.of_nat j)).
Proof.
intros g j Hj. unfold Mem.le4. generalize (bv_unsigned (Z_to_bv 64 g)) as z. intros z.
destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite ?Z.shiftr_shiftr by lia; f_equal; first [rewrite Z.shiftr_0_r; reflexivity | f_equal; lia].
Qed.
Lemma m4_HG : forall E m cs lo hi wlo whi e o g,
region_ok SEGS E m (YP09.mkRegion (Some 23%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 23) = o ->
In (YP09.mkChunk 20 (CVal 4 e)) cs -> U E e mod 2 ^ 32 = g -> 0 <= g < 2 ^ 32 ->
garr8 SEGS m (o + 20) (cls_bytes (Mem.le4 (Z_to_bv 64 g))).
Proof.
intros E m cs lo hi wlo whi e o g Hr Ho H20 Hg Hgr.
apply m4_garr8_bytes. intros j Hj. rewrite Mem.length_le4 in Hj.
rewrite (m4_le4_nth g j Hj). rewrite (m4_chunk_byte E m 23 o lo hi wlo whi cs 20 4 e (Z.of_nat j) Hr Ho H20 ltac:(cbn; lia)).
f_equal. unfold byte_of_word. rewrite unsigned_lit_small by lia. rewrite <- Hg.
fold (U E e). pose proof (U_range E e) as HU. unfold M64 in HU.
change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)). rewrite low_byte_mod by lia. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.
Hypothesis ROM : cls_rom_ok B.
Definition m4_pk (cx : ccx) (fpos : Z) : bool := RcLeaf.ports_ok (x_f cx + 18) (cF cx fpos + 112) (cBS cx).
Definition m4_vin (cx : ccx) (fpos : Z) : Z := if m4_pk cx fpos then 4 * RcLeaf.n_in (cBS cx) else 0.
Definition m4_vout (cx : ccx) (fpos : Z) : Z := if m4_pk cx fpos then 4 * RcLeaf.n_out (cBS cx) else 0.
Definition m4E (cx : ccx) (fpos : Z) (regs : bvmap 5 word) : env :=
Eimg (Ereg regs [Z_to_bv 64 (m4_vin cx fpos); Z_to_bv 64 (m4_vout cx fpos)]).
Definition m4_wr (cx : ccx) (fpos : Z) (a : Z) : Prop :=
(x_o cx + 12 <= a < x_o cx + 15) \/ (x_o cx + 20 <= a < x_o cx + 24) \/
(SHADOW_OFF + cF cx fpos / 8 + 14 <= a < SHADOW_OFF + cF cx fpos / 8 + 16).
Lemma m4_aro : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3.
pose proof Hpre as (_ & Haro & _).
unfold cls_at_R3, cls_cut in HR3. cbv zeta in HR3.
destruct HR3 as (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & K3 & _) & _) & _).
intros a Hro Ho He. rewrite (K3 a); [exact (Haro a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.
Lemma m4_entry : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
st_ok_pi (fx := x_fq cx) SEGS VAL (m4E cx fpos regs3) (ss_m4 (m4_pk cx fpos))
  (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_R3)) mem3 (seg_rom SEGS))) /\
sh_ok SEGS M4Bx M4SH (m4E cx fpos regs3) (mrestrict (w_H W3) mem3).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3.
pose proof (m4_aro cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3) as Haro3.
pose proof (proj1 (ROM (w_H W3) mem3 Haro3)) as Hrcp.
pose proof HR3 as (Hret & Hcut & Hpv).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as (HFx & _ & _ & _ & (HoA & HoL & HoF & HoS) & Ho4096 & Hoceil & _ & _).
destruct HFx as (HF4096 & HFceil & HF32 & HFz & HFapp & HFpres & HFSpres & _).
destruct HoA as (Ho0 & Ho47 & _ & Hoimg & Hoapp). destruct HoL as (Hopres & HoRA & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen64 & HFBl & _).
unfold cls_cut in Hcut. cbv zeta in Hcut.
destruct Hcut as (HJ & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV &
  Hspill & Ho16 & Hf24 & HF48 & HLS & HSHl & HSH & HFL & HPS & HO3l & HO3 & HLk).
rewrite Forall_forall in HRV.
pose proof (HRV (10, if RcLeaf.ports_ok (x_f cx + 18) (cF cx fpos + 112) (cBS cx) then 0 else -1) ltac:(cbn; tauto)) as R10.
pose proof (HRV (21, cF cx fpos + 112) ltac:(cbn; tauto)) as R21.
pose proof (HRV (24, SHADOW_OFF) ltac:(cbn; tauto)) as R24.
pose proof (HRV (23, x_o cx) ltac:(cbn; tauto)) as R23.
cbn [fst snd] in R10, R21, R24, R23.
destruct (m4_split_OQ _ _ _ _ HFBl HO3) as (_ & HZ3 & _ & _).
fold (m4_pk cx fpos) in R10.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho4 & _).
set (F := cF cx fpos) in *. set (o := x_o cx) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF8.
pose proof (pa_obj_img_all 36%nat ltac:(unfold tfib_nobj; lia)) as Hob36.
pose proof (pa_val_range (A_OBJ 36)) as VR36.
assert (FS : forall i, 0 <= i < 32 -> apresent (w_H W3) mem3 (SHADOW_OFF + F / 8 + i)) by exact HFSpres.
set (E := m4E cx fpos regs3).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 [Z_to_bv 64 (m4_vin cx fpos); Z_to_bv 64 (m4_vout cx fpos)]) n)
by (intros n Hn; subst E; unfold m4E; apply Eimg_low; exact Hn).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 112))
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 21 (Z_to_bv 5 21)) by reflexivity; exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 24 (Z_to_bv 5 24)) by reflexivity; exact R24).
assert (E23 : ew E 23 = Z_to_bv 64 o)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 23 (Z_to_bv 5 23)) by reflexivity; exact R23).
assert (E27 : ew E 27 = Z_to_bv 64 (SHADOW_OFF + F / 8))
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 27 (Z_to_bv 5 27)) by reflexivity; exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (m4_vin cx fpos)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (m4_vout cx fpos)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EO36 : ew E (A_OBJ 36) = Z_to_bv 64 (VAL (A_OBJ 36)))
by (subst E; unfold m4E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Vin : 0 <= m4_vin cx fpos <= 48) by (unfold m4_vin; destruct (m4_pk cx fpos); [apply m4_nin | lia]).
assert (Vout : 0 <= m4_vout cx fpos <= 48) by (unfold m4_vout; destruct (m4_pk cx fpos); [apply m4_nout | lia]).
assert (HRC : 0 <= CLS_RECIP < 2 ^ 64) by (unfold CLS_RECIP; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SHADOW_OFF in *.
assert (HS0 : st_ok_pi (fx := x_fq cx) SEGS VAL E (mkSS PC_R3 sr_atoms (m4_regions (m4_pk cx fpos)) None m4_facts)
  (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_R3)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - unfold m4_regions, m4_fR. destruct (m4_pk cx fpos); vm_compute; reflexivity.
  - unfold m4_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok.
    + unfold m4_oA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 23%nat o E23) by lia. split; [lia|]. split; [lia|]. split.
      * intros i Hi. apply (apresent_writable SEGS). apply Hopres. lia.
      * constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (chunk_ok_val SEGS E _ o 12 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
           change (N.to_nat 1) with 1%nat. replace (o + 12) with (o + 12 + Z.of_nat 0) by lia.
           exact (proj1 (HZ3 0%nat ltac:(cbn; lia))).
        -- apply (chunk_ok_val SEGS E _ o 13 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
           change (N.to_nat 1) with 1%nat. replace (o + 13) with (o + 12 + Z.of_nat 1) by lia.
           exact (proj1 (HZ3 1%nat ltac:(cbn; lia))).
        -- apply (chunk_ok_val SEGS E _ o 14 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
           change (N.to_nat 1) with 1%nat. replace (o + 14) with (o + 12 + Z.of_nat 2) by lia.
           exact (proj1 (HZ3 2%nat ltac:(cbn; lia))).
    + unfold m4_oB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 23%nat o E23) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros i Hi. apply (apresent_writable SEGS). apply Hopres. lia.
    + unfold m4_fsR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 27%nat _ E27) by lia. split; [lia|]. split; [lia|]. split; [intros i Hi; lia | constructor].
    + unfold m4_fR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 21%nat _ E21) by lia. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      destruct (m4_pk cx fpos) eqn:Hpk; [|constructor].
      destruct (Hpv Hpk) as [Vi Vo].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (F + 112) 0 4 (SOff 32 0) (m4_vin cx fpos));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        change (N.to_nat 4) with 4%nat. rewrite Z.add_0_r. unfold m4_vin. rewrite Hpk. exact Vi.
      * apply (chunk_ok_val SEGS E _ (F + 112) 4 4 (SOff 33 0) (m4_vout cx fpos));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        change (N.to_nat 4) with 4%nat. replace (F + 112 + 4) with (F + 116) by lia. unfold m4_vout. rewrite Hpk. exact Vo.
    + unfold m4_rR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 36) _ EO36) by lia. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 8 (SLit CLS_RECIP) CLS_RECIP);
      [reflexivity | cbn; lia | cbn; lia |].
      change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Hrcp.
  - apply pairwise_disjoint_of_extents. unfold m4_regions, m4_oA, m4_oB, m4_fsR, m4_fR, m4_rR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 23%nat o E23) by lia. rewrite (VB 27%nat _ E27) by lia. rewrite (VB 21%nat _ E21) by lia.
    rewrite (VB (A_OBJ 36) _ EO36) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - unfold m4_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E24, unsigned_lit_small by lia;
      rewrite Z.pow_0_r; unfold SB; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E23, unsigned_lit_small by lia;
      change (2 ^ 2) with 4;
      split; [lia|]; split; [exact Ho4 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
      rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
      rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    exact I. }
split.
- pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) (if m4_pk cx fpos then 0 else -1) HS0 R10 eq_refl) as HS1.
  exact HS1.
- unfold sh_ok, M4SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 E M4Bx 23 o 24 o 0 24 HoRA).
  + unfold U, M4Bx. cbn [sv_denot]. rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.


Lemma m4_acc_step : forall (Wr : Z -> Prop) E rs (m0 m1 m2 : word -> option byte),
(forall a, in_wrange E rs a -> Wr a) -> frame_of E rs m1 m2 ->
(forall x : word, ~ Wr (bv_unsigned x) -> m1 x = m0 x) ->
forall x : word, ~ Wr (bv_unsigned x) -> m2 x = m0 x.
Proof.
intros Wr E rs m0 m1 m2 Hw Hf H1 x Hx. rewrite (Hf x); [exact (H1 x Hx)|]. intros Hin. exact (Hx (Hw _ Hin)).
Qed.
Lemma m4_grows_trans : forall m0 m1 m2 : word -> option byte, mem_grows m0 m1 -> mem_grows m1 m2 -> mem_grows m0 m2.
Proof. intros m0 m1 m2 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Ltac m4_lits := unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SHADOW_OFF in *.
Lemma m4_close : forall cx fpos W3 ly3 S3 regs3 mem3 md3 regs4 mem4 md4,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
(forall x : word, ~ m4_wr cx fpos (bv_unsigned x) -> mrestrict (w_H W3) mem4 x = mrestrict (w_H W3) mem3 x) ->
mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem4) ->
(forall r, In r m4_kregs -> getr regs4 r = getr regs3 r) ->
getr regs4 (Z_to_bv 5 24) = w64 0 ->
garr8 SEGS (mrestrict (w_H W3) mem4) (x_o cx + 12) (cls_bytes (m4_D (x_FB cx))) ->
garr8 SEGS (mrestrict (w_H W3) mem4) (x_o cx + 20) (cls_bytes (Mem.le4 (Z_to_bv 64 (disco_classify_c.geo (x_len cx))))) ->
garr8 SEGS (mrestrict (w_H W3) mem4) (SHADOW_OFF + cF cx fpos / 8 + 14) [248; 248] ->
cls_at_X B cx fpos W3 ly3 S3 regs4 mem4 md4.
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 regs4 mem4 md4 Hpre HR3 HJ4 Hacc Hgr Hregs H23 HD HG HSH4.
pose proof HR3 as (Hret & Hcut & _).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as (HFx & _ & _ & _ & (HoA & HoL & HoF & HoS) & Ho4096 & Hoceil & _ & HLN).
destruct HFx as (HF4096 & HFceil & HF32 & HFz & HFapp & HFpres & HFSpres & HFL4096 & HFLz & HFLceil & _ & _ & HFLnot & _).
destruct HoA as (Ho0 & Ho47 & _ & Hoimg & Hoapp).
pose proof Hpre as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hstk & Hsp0 & _ & _ & Hlen64 & HFBl &
  _ & _ & _ & _ & _ & _ & Ho0' & Ho4 & _ & _ & _ & _ & HLpre & _ & _ & HLsep).
unfold cls_cut in Hcut. cbv zeta in Hcut.
destruct Hcut as (HJ & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & HRV &
  Hspill & Ho16 & Hf24 & HF48 & HLS & HSHl & HSH & HFL & HPS & HO3l & HO3 & HLk).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (m4_ret0 _ _ _ _ (x_OB cx) Hret) as [H50 Hout].
assert (HCS : 320 <= CLS_STK) by (unfold Z.le; vm_compute; discriminate).
set (F := cF cx fpos) in *. set (o := x_o cx) in *. unfold cSP in *. set (SP := spZ (x_regs cx)) in *.
assert (HS1 : SP - 192 <= cS1 cx <= SP - 160).
{ unfold cS1, cls_S1, cSP. fold SP. pose proof (Z.div_mod (SP - 160) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (SP - 160) 32 ltac:(lia)) as M1. lia. }
pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF8.
assert (Hskeep : forall a, SP - CLS_STK <= a < SP -> 0 <= a < 2 ^ 64 /\ ~ m4_wr cx fpos a).
{ intros a Ha. unfold m4_wr. fold o F. m4_lits. split; lia. }
assert (Hfkeep : forall a, F <= a < F + 256 -> 0 <= a < 2 ^ 64 /\ ~ m4_wr cx fpos a).
{ intros a Ha. unfold m4_wr. fold o F. m4_lits. split; lia. }
unfold cls_at_X, cls_cut. cbv zeta. unfold cSP. fold F o SP.
split; [exact HJ4|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|].
split.
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 mem4 (m4_wr cx fpos) Hpre (proj1 HJ) Hfr Hnin Hperm Hfa Hfl Hkept).
  - intros a Ha Hn. apply aview_eq_of. apply Hacc. rewrite unsigned_lit_small by lia. exact Hn.
  - intros a Ha. exact (apresent_grows _ _ _ _ Hgr Ha).
  - intros a Ha. fold o F. unfold m4_wr in Ha. fold o F in Ha. unfold cls_wr.
    destruct Ha as [Ha | [Ha | Ha]]; [right; left; left; lia | right; left; left; lia |].
    right; right; right; left. lia. }
split; [rewrite (Hregs 2%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R2|].
split; [rewrite (Hregs 3%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R3|].
split; [rewrite (Hregs 4%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R4|].
split; [rewrite (Hregs 8%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R8|].
split; [rewrite (Hregs 9%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R9|].
split; [rewrite (Hregs 18%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R18|].
split; [rewrite (Hregs 19%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R19|].
split; [rewrite (Hregs 20%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R20|].
split; [rewrite (Hregs 27%bv ltac:(unfold m4_kregs; cbn [In]; tauto)); exact R27|].
split; [constructor; [cbn [fst snd]; rewrite Hret; exact H23 | constructor]|].
split.
{ assert (Hsp : forall p, In p cls_spills -> -104 <= snd p <= -8).
  { intros p Hp. unfold cls_spills in Hp. cbn [In] in Hp.
    repeat (destruct Hp as [<- | Hp]; [cbn [snd]; lia|]). destruct Hp. }
  rewrite Forall_forall in Hspill |- *. intros p Hp.
  apply (m4_vm_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ _ Hacc); [|exact (Hspill p Hp)].
  intros k Hk. apply Hskeep. pose proof (Hsp p Hp). cbn in Hk. lia. }
split; [apply (m4_vm_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ _ Hacc); [intros k Hk; apply Hskeep; cbn in Hk; lia | exact Ho16]|].
split; [apply (m4_vm_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ _ Hacc); [intros k Hk; apply Hskeep; cbn in Hk; lia | exact Hf24]|].
split; [apply (m4_vm_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ _ Hacc); [intros k Hk; apply Hskeep; cbn in Hk; lia | exact HF48]|].
split; [intros Hf; discriminate Hf|].
split; [reflexivity|].
split.
{ rewrite (proj1 m4_pat). rewrite (proj2 m4_pat) in HSH.
  apply garr8_app in HSH as [HSa HSH]. apply garr8_app in HSH as [_ HSb].
  apply (proj2 (garr8_app _ _ _ _ _)). split.
  - apply (m4_ga_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ Hacc); [|exact HSa].
    intros k Hk. cbn [length firstn PAT_B] in Hk. unfold m4_wr. fold o F. m4_lits. split; lia.
  - apply (proj2 (garr8_app _ _ _ _ _)). cbn [length firstn PAT_B Z.of_nat] in HSb |- *. split.
    + unfold SHADOW_OFF in HSH4. exact HSH4.
    + apply (m4_ga_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ Hacc); [|exact HSb].
      intros k Hk. cbn [length skipn PAT_B] in Hk. unfold m4_wr. fold o F. m4_lits. split; lia. }
split; [apply (m4_vm_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ _ Hacc); [intros k Hk; apply Hfkeep; cbn in Hk; lia | exact HFL]|].
split; [exact I|].
unfold cOut. rewrite Hout.
destruct (m4_split_OQ _ _ _ _ HFBl HO3) as (HA & _ & HC & _).
split; [rewrite m4_sight, !length_app, m4_A_len, m4_D_len, Mem.length_le4 by exact HFBl; reflexivity|].
split.
{ rewrite m4_sight, !m4_cls_bytes_app.
  apply (proj2 (garr8_app _ _ _ _ _)). split.
  - apply (m4_ga_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ Hacc); [|exact HA].
    intros k Hk. rewrite m4_cls_bytes_len, m4_A_len in Hk by exact HFBl. unfold m4_wr. fold o F. m4_lits. split; lia.
  - rewrite m4_cls_bytes_len, m4_A_len by exact HFBl.
    apply (proj2 (garr8_app _ _ _ _ _)). split; [exact HD|].
    rewrite m4_cls_bytes_len, m4_D_len.
    apply (proj2 (garr8_app _ _ _ _ _)). split.
    + replace (o + Z.of_nat 12 + Z.of_nat 3) with (o + 15) by lia.
      apply (m4_ga_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ Hacc); [|exact HC].
      intros k Hk. cbn [length cls_bytes map m4_C Z.of_nat] in Hk. unfold m4_wr. fold o F. m4_lits. split; lia.
    + replace (o + Z.of_nat 12 + Z.of_nat 3 + Z.of_nat (length (cls_bytes (m4_C (x_FB cx))))) with (o + 20)
        by (cbn [length cls_bytes map m4_C Z.of_nat]; lia).
      exact HG. }
revert HLk HLN HLsep. destruct (x_L cx) as [Lb0|]; destruct (cLock cx) as [Lb|]; intros HLk HLN HLsep;
  try contradiction; [|exact I].
destruct HLk as [HLl HLg]. split; [exact HLl|].
destruct HLN as (((Hl0 & Hl47 & _ & Hlimg & Hlapp) & _ & HlF & _) & _ & _ & _).
apply (m4_ga_keep (m4_wr cx fpos) (w_H W3) mem3 mem4 _ _ Hacc); [|exact HLg].
intros k Hk. rewrite m4_cls_bytes_len, HLl in Hk. cbn [Z.of_nat] in Hk. destruct HLsep as [HLo _].
unfold m4_wr. fold o F. m4_lits. split; lia.
Qed.

Lemma m4_awr : forall cx fpos W3 ly3 S3 regs3 mem3 md3 E rs,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
(forall a, in_wrange E rs a -> m4_wr cx fpos a) ->
awr_ok E rs (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 ((2, fpos) :: x_own cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 E rs Hpre HR3 Hw a Ha.
pose proof HR3 as (_ & Hcut & _).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as (_ & _ & _ & _ & _ & _ & _ & Hoawr & _).
unfold cls_cut in Hcut. cbv zeta in Hcut. destruct Hcut as (_ & _ & _ & _ & Hfa & _).
destruct (Hw a Ha) as [Hx | [Hx | Hx]]; [apply Hoawr; lia | apply Hoawr; lia |].
unfold awr_byte. right; right; right. unfold in_frames. exists 2, fpos. split; [left; reflexivity|].
right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes 2 / 8) with 32. lia.
Qed.
Lemma m4_shok : forall cx fpos W3 ly3 S3 regs3 mem3 md3 (m : word -> option byte) E,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
(forall x : word, ~ m4_wr cx fpos (bv_unsigned x) -> mrestrict (w_H W3) m x = mrestrict (w_H W3) mem3 x) ->
ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E 23 = Z_to_bv 64 (x_o cx) ->
sh_ok SEGS M4Bx M4SH E (mrestrict (w_H W3) m).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 m E Hpre HR3 Hacc E24 E23.
pose proof HR3 as (_ & Hcut & _).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as (HFx & _ & _ & _ & (HoA & HoL & HoF & _) & Ho4096 & _ & _ & _).
destruct HFx as (HF4096 & HFceil & HF32 & _).
destruct HoA as (Ho0 & Ho47 & _ & _ & Hoapp). destruct HoL as (_ & HoRA & _).
set (F := cF cx fpos) in *. set (o := x_o cx) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF8.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF32.
unfold sh_ok, M4SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W3) m E M4Bx 23 o 24 o 0 24).
- apply (range_addressable_agree (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) m) SHADOW_OFF o 24); [|exact HoRA].
  intros x Hx. unfold shadow_of_addr. apply aview_eq_of. apply Hacc.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  rewrite unsigned_lit_small by lia. unfold m4_wr. fold o F. unfold SHADOW_OFF. lia.
- unfold U, M4Bx. cbn [sv_denot]. rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma m4_HS : forall E m cs lo hi wlo whi e14 e15 s,
region_ok SEGS E m (YP09.mkRegion (Some 27%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 27) = s ->
In (YP09.mkChunk 14 (CVal 1 e14)) cs -> In (YP09.mkChunk 15 (CVal 1 e15)) cs ->
Z_to_bv 8 (U E e14) = Z_to_bv 8 248 -> Z_to_bv 8 (U E e15) = Z_to_bv 8 248 ->
garr8 SEGS m (s + 14) [248; 248].
Proof.
intros E m cs lo hi wlo whi e14 e15 s Hr Hs H14 H15 V14 V15.
change [248; 248] with (cls_bytes [Z_to_bv 8 248; Z_to_bv 8 248]).
apply m4_garr8_bytes. intros j Hj. cbn [length] in Hj.
destruct j as [|[|j]]; [| | lia]; cbn [nth].
- rewrite <- V14, <- m4_bow0. replace (s + 14 + Z.of_nat 0) with (s + 14 + 0) by lia.
  exact (m4_chunk_byte E m 27 s lo hi wlo whi cs 14 1 e14 0 Hr Hs H14 ltac:(lia)).
- rewrite <- V15, <- m4_bow0. replace (s + 14 + Z.of_nat 1) with (s + 15 + 0) by lia.
  exact (m4_chunk_byte E m 27 s lo hi wlo whi cs 15 1 e15 0 Hr Hs H15 ltac:(lia)).
Qed.

Lemma m4_Ev : forall cx fpos W3 ly3 S3 regs3 mem3 md3, cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
ew (m4E cx fpos regs3) 25 = Z_to_bv 64 (x_len cx) /\ ew (m4E cx fpos regs3) 21 = Z_to_bv 64 (cF cx fpos + 112) /\
ew (m4E cx fpos regs3) 24 = Z_to_bv 64 SHADOW_OFF /\ ew (m4E cx fpos regs3) 23 = Z_to_bv 64 (x_o cx) /\
ew (m4E cx fpos regs3) 27 = Z_to_bv 64 (SHADOW_OFF + cF cx fpos / 8) /\
ew (m4E cx fpos regs3) 32 = Z_to_bv 64 (m4_vin cx fpos) /\ ew (m4E cx fpos regs3) 33 = Z_to_bv 64 (m4_vout cx fpos) /\
env_agree 32 (Ereg regs3 [Z_to_bv 64 (m4_vin cx fpos); Z_to_bv 64 (m4_vout cx fpos)]) (m4E cx fpos regs3).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 HR3.
pose proof HR3 as (_ & Hcut & _). unfold cls_cut in Hcut. cbv zeta in Hcut.
destruct Hcut as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R27 & HRV & _).
rewrite Forall_forall in HRV.
pose proof (HRV (25, x_len cx) ltac:(cbn; tauto)) as R25.
pose proof (HRV (21, cF cx fpos + 112) ltac:(cbn; tauto)) as R21.
pose proof (HRV (24, SHADOW_OFF) ltac:(cbn; tauto)) as R24.
pose proof (HRV (23, x_o cx) ltac:(cbn; tauto)) as R23.
cbn [fst snd] in R25, R21, R24, R23.
unfold m4E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [rewrite (ew_Ereg_nat regs3 _ 25 (Z_to_bv 5 25)) by reflexivity; exact R25|].
split; [rewrite (ew_Ereg_nat regs3 _ 21 (Z_to_bv 5 21)) by reflexivity; exact R21|].
split; [rewrite (ew_Ereg_nat regs3 _ 24 (Z_to_bv 5 24)) by reflexivity; exact R24|].
split; [rewrite (ew_Ereg_nat regs3 _ 23 (Z_to_bv 5 23)) by reflexivity; exact R23|].
split; [rewrite (ew_Ereg_nat regs3 _ 27 (Z_to_bv 5 27)) by reflexivity; exact R27|].
split; [exact (ew_Ereg_extra regs3 _ 0)|].
split; [exact (ew_Ereg_extra regs3 _ 1)|].
split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.

Lemma m4_Uv : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
cls_pre B cx -> cls_at_R3 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
bv_unsigned (ew (m4E cx fpos regs3) 25) = x_len cx /\ bv_unsigned (ew (m4E cx fpos regs3) 23) = x_o cx /\
bv_unsigned (ew (m4E cx fpos regs3) 27) = SHADOW_OFF + cF cx fpos / 8.
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3.
destruct (m4_Ev cx fpos W3 ly3 S3 regs3 mem3 md3 HR3) as (E25 & _ & _ & E23 & E27 & _).
pose proof HR3 as (_ & Hcut & _).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & _) & _ & _ & _ & ((Ho0 & Ho47 & _) & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen64 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (cF cx fpos) 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound (cF cx fpos) 8 ltac:(lia)) as MF8.
rewrite E25, E23, E27. unfold SHADOW_OFF. rewrite !unsigned_lit_small by lia. split; [reflexivity|]. split; reflexivity.
Qed.
Ltac m4_wr_one Ha :=
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
first [ lia
| lazymatch goal with U23 : bv_unsigned (ew ?E 23) = _, U27 : bv_unsigned (ew ?E 27) = _ |- _ =>
    rewrite ?U23, ?U27 in Ha; unfold m4_wr; lia end ].
Ltac m4_wr_tac :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros a (r & Hin & Ha);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (let Hr := fresh "Hr" in destruct Hin as [Hr | Hin]; [subst r; m4_wr_one Ha |]); destruct Hin.

Let RUNTOf (fq : YK11.FPState) := paj_run_to (fx := fq) B LAWS.
Let RUNTOPf (fq : YK11.FPState) := SRr_run_to_pi_AJ (fx := fq) B LAWS.
Let BRf (fq : YK11.FPState) := paj_branch (fx := fq) (PI := PI).

Ltac m4_acc :=
lazymatch goal with
| HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
  HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
  Hacc : forall x : word, ~ m4_wr ?cx ?fpos (bv_unsigned x) -> mrestrict (w_H ?W) ?m1 x = mrestrict (w_H ?W) ?m0 x,
  Hgr : mem_grows (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1) |- _ =>
  let Hacc2 := fresh "Hacc" in let Hgr2 := fresh "Hgr" in
  assert (Hacc2 : forall x : word, ~ m4_wr cx fpos (bv_unsigned x) -> mrestrict (w_H W) m2 x = mrestrict (w_H W) m0 x)
    by (apply (m4_acc_step (m4_wr cx fpos) E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) (mrestrict (w_H W) m2)); [m4_wr_tac | exact HFr | exact Hacc]);
  pose proof (m4_grows_trans _ _ _ Hgr HG) as Hgr2;
  clear Hacc Hgr HFr HG; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
  rename Hacc2 into Hacc; rename Hgr2 into Hgr
end.
Ltac m4_awr_tac := lazymatch goal with Hpre : cls_pre _ ?cx, HR3 : cls_at_R3 _ ?cx ?fpos ?W3 ?ly3 ?S3 ?regs3 ?mem3 ?md3 |- _ =>
apply (m4_awr cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ Hpre HR3); m4_wr_tac end.
Ltac m4_set_window wlo whi wtac :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msx |- _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 2 rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx 2 r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx 2 r HS ltac:(vm_compute; reflexivity)) ltac:(wtac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac m4_fs_writable :=
lazymatch goal with U27 : bv_unsigned (ew _ 27) = _, Hgr : mem_grows _ _, HFS : forall i, 0 <= i < 32 -> apresent _ _ _ |- _ =>
intros oo Hoo; cbn [YP09.r_base base_val ms_mem restrict]; rewrite U27;
apply (apresent_writable SEGS); apply (apresent_grows _ _ _ _ Hgr); apply HFS; lia end.
Ltac m4_pbranch :=
lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms), Hpre : cls_pre _ ?cx |- _ =>
let r := eval vm_compute in (sym_step_pi both3_0_tpi ss) in
lazymatch r with PStop (SR_branch ?c ?a ?b) =>
apply (BRf (x_fq cx) W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS end end.

Ltac m4_trun stop :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _, Hpre : cls_pre _ ?cx |- _ =>
paj_run_to_tok (RUNTOf (x_fq cx)) HS HJ SHOK M4span stop; [m4_awr_tac |]; m4_acc end.
Ltac m4_tbranch :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _, Hpre : cls_pre _ ?cx |- _ =>
psrr_branch_tok (RUNTOf (x_fq cx)) (BRf (x_fq cx)) HS SHOK M4span end.
Ltac m4_prun stop :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, Hpre : cls_pre _ ?cx |- _ =>
paj_run_to_sh (RUNTOPf (x_fq cx)) HS HJ stop; [m4_awr_tac |]; m4_acc end.
Ltac m4_p3 :=
m4_set_window 0 0 ltac:(idtac; intros oo Hoo; lia);
lazymatch goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end;
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict _ ?ms), Hpre : cls_pre _ ?cx, HR3 : cls_at_R3 _ ?cx ?fpos ?W3 ?ly3 ?S3 ?regs3 ?mem3 ?md3,
  Hacc : forall x : word, _ -> mrestrict _ (ms_mem ?ms) x = _, E24 : ew _ 24 = _, E23 : ew _ 23 = _ |- _ =>
  pose proof (m4_shok cx fpos W3 ly3 S3 regs3 mem3 md3 (ms_mem ms) Ex Hpre HR3 Hacc E24 E23) as SHOK end;
m4_trun PC_X.

Ltac m4_region i :=
lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf ?msx |- _ =>
let r := eval vm_compute in (nth i (ss_mem ssf) got_regionP) in
exact (st_ok_pi_region_nth Ef ssf msx i r HS ltac:(vm_compute; reflexivity)) end.
Ltac m4_inch := repeat (first [left; reflexivity | right]).
Ltac m4_fin Dt Gt :=
lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HX : cls_from_X _, Hpre : cls_pre _ ?cx, HR3 : cls_at_R3 _ ?cx ?fpos ?W3 ?ly3 ?S3 ?regs3 ?mem3 ?md3,
  Hacc : forall x : word, _ -> _ = _, Hgr : mem_grows _ _, HAE : env_agree 32 (Ereg _ ?ex) ?E0,
  U23 : bv_unsigned (ew _ 23) = _, U27 : bv_unsigned (ew _ 27) = _ |- _ =>
  let R24 := fresh "R24" in prreg HS (Z_to_bv 5 24) R24;
  pmkst HS;
  refine (HX cx fpos W3 ly3 S3 (ms_regs ms) (ms_mem ms) _ Hpre _);
  apply (m4_close cx fpos W3 ly3 S3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) _ Hpre HR3 HJ Hacc Hgr);
  [ intros rr Hrr; apply (regs_kept_of_st_ok_pi Ef ssf (restrict (w_H W) ms) regs3 ex m4_kregs HS);
    [ apply (env_agree_trans 32 _ E0 _ HAE); split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]
    | vm_compute; reflexivity | exact Hrr ]
  | exact R24
  | eapply (m4_HD Ef); [m4_region 0%nat | rewrite ?ew_ewset_other by lia; exact U23 | m4_inch | m4_inch | m4_inch | Dt ]
  | eapply (m4_HG Ef); [m4_region 1%nat | rewrite ?ew_ewset_other by lia; exact U23 | m4_inch | Gt | apply m4_geo_range ]
  | eapply (m4_HS Ef); [m4_region 2%nat | rewrite ?ew_ewset_other by lia; exact U27 | m4_inch | m4_inch | apply bv_eq; rewrite U_SLit; vm_compute; reflexivity | apply bv_eq; rewrite U_SLit; vm_compute; reflexivity ] ]
end.

Ltac m4_hc :=
lazymatch goal with Hc : branch_taken ?c (sv_denot ?E ?a) (sv_denot ?E ?b) = ?t |- _ =>
  rewrite ?branch_ltu_U, ?branch_geu_U in Hc;
  rewrite ?U_SLit in Hc;
  repeat (match type of Hc with context [U E (SOff ?n 0)] =>
     lazymatch goal with En : ew E n = Z_to_bv 64 ?v |- _ => rewrite (U_atom E n v En) in Hc by lia end end);
  repeat (match type of Hc with context [zcanon ?k] => rewrite (zcanon_id k) in Hc by (unfold M64; lia) end);
  first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc ]
end.
Ltac m4_D0 H := rewrite H; unfold m4_Z3, CtrlParsed.zb; rewrite !U_SLit; reflexivity.
Ltac m4_Dok Hd Hi Ho :=
rewrite (m4_D_ok _ Hd Hi Ho); unfold CtrlParsed.zb;
lazymatch goal with |- _ = [_; Z_to_bv 8 (U ?Ef _); _] =>
  lazymatch goal with E32 : ew _ 32 = Z_to_bv 64 (m4_vin ?cx ?fpos), E33 : ew _ 33 = Z_to_bv 64 (m4_vout ?cx ?fpos),
    Hvin : m4_vin _ _ = _, Hvout : m4_vout _ _ = _ |- _ =>
  rewrite U_SLit, (U_atom Ef 32 (m4_vin cx fpos)), (U_atom Ef 33 (m4_vout cx fpos)) by (rewrite ?ew_ewset_other by lia; first [exact E32 | exact E33 | lia]);
  rewrite Hvin, Hvout; reflexivity end end.
Ltac m4_Gge :=
lazymatch goal with U25 : bv_unsigned (ew _ 25) = _ |- _ =>
apply m4_geo_U; [rewrite ?ew_ewset_other by lia; exact U25 | lia] end.
Ltac m4_Glt :=
rewrite U_SLit; change (zcanon 0 mod 2 ^ 32) with 0; unfold disco_classify_c.geo;
rewrite (proj2 (Z.leb_gt 52 _)) by lia; reflexivity.

Theorem cls_m4 : cls_from_X B -> cls_from_R3 B.
Proof.
intros HX cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3.
destruct (m4_entry cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3) as [HS SHOK].
destruct (m4_Ev cx fpos W3 ly3 S3 regs3 mem3 md3 HR3) as (E25 & E21 & E24 & E23 & E27 & E32 & E33 & HAE).
destruct (m4_Uv cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR3) as (U25 & U23 & U27).
pose proof HR3 as (Hret & Hcut & Hpv).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as ((HF4096 & _ & _ & _ & _ & _ & HFS & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen64 & _ & _ & _ & Hf50 & _).
destruct (m4_ret0 _ _ _ _ (x_OB cx) Hret) as [H50 _].
pose proof Hcut as (HJ & _).
assert (Vin : 0 <= m4_vin cx fpos <= 48) by (unfold m4_vin; destruct (m4_pk cx fpos); [apply m4_nin | lia]).
assert (Vout : 0 <= m4_vout cx fpos <= 48) by (unfold m4_vout; destruct (m4_pk cx fpos); [apply m4_nout | lia]).
assert (HEI : img_env VAL A_LIM (m4E cx fpos regs3)) by (unfold m4E; apply Eimg_env).
assert (Hacc : forall x : word, ~ m4_wr cx fpos (bv_unsigned x) -> mrestrict (w_H W3) mem3 x = mrestrict (w_H W3) mem3 x)
by (intros; reflexivity).
assert (Hgr : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem3)) by (intros x Hx; exact Hx).
set (E := m4E cx fpos regs3) in *.
unfold cfg_at. change (w64 (BASE + PC_R3)) with (Z_to_bv 64 (BASE + PC_R3)).
revert HS. destruct (m4_pk cx fpos) eqn:Hpk; intros HS.
- assert (Hdecl : RcLeaf.decl (cBS cx) = true).
  { unfold m4_pk, RcLeaf.ports_ok in Hpk. apply andb_prop in Hpk as [_ Hd]. exact Hd. }
  assert (Hvin : m4_vin cx fpos = 4 * RcLeaf.n_in (cBS cx)) by (unfold m4_vin; rewrite Hpk; reflexivity).
  assert (Hvout : m4_vout cx fpos = 4 * RcLeaf.n_out (cBS cx)) by (unfold m4_vout; rewrite Hpk; reflexivity).
  m4_trun (AF_both3_classify_core + 0x4d4).
  m4_tbranch; m4_hc.
  + assert (HD : 40 < 4 * RcLeaf.n_in (cBS cx)) by lia.
    m4_trun (AF_both3_classify_core + 0x4d4).
    m4_set_window 14 16 ltac:(idtac; m4_fs_writable).
    m4_prun (AF_both3_classify_core + 0x530).
    m4_pbranch; m4_hc; m4_prun (AF_both3_classify_core + 0x530); m4_p3.
    * m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_intror (or_introl HD)))) ltac:(idtac; m4_Gge).
    * m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_intror (or_introl HD)))) ltac:(idtac; m4_Glt).
  + m4_trun (AF_both3_classify_core + 0x4d4).
    m4_tbranch; m4_hc.
    * assert (HD : 40 < 4 * RcLeaf.n_out (cBS cx)) by lia.
      m4_trun (AF_both3_classify_core + 0x4d4).
      m4_set_window 14 16 ltac:(idtac; m4_fs_writable).
      m4_prun (AF_both3_classify_core + 0x530).
      m4_pbranch; m4_hc; m4_prun (AF_both3_classify_core + 0x530); m4_p3.
      -- m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_intror (or_intror HD)))) ltac:(idtac; m4_Gge).
      -- m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_intror (or_intror HD)))) ltac:(idtac; m4_Glt).
    * assert (Hi : 4 * RcLeaf.n_in (cBS cx) <= 40) by lia.
      assert (Ho : 4 * RcLeaf.n_out (cBS cx) <= 40) by lia.
      m4_trun (AF_both3_classify_core + 0x4d4).
      m4_set_window 14 16 ltac:(idtac; m4_fs_writable).
      m4_prun (AF_both3_classify_core + 0x530).
      m4_pbranch; m4_hc; m4_prun (AF_both3_classify_core + 0x530); m4_p3.
      -- m4_fin ltac:(idtac; m4_Dok Hdecl Hi Ho) ltac:(idtac; m4_Gge).
      -- m4_fin ltac:(idtac; m4_Dok Hdecl Hi Ho) ltac:(idtac; m4_Glt).
- assert (HD : RcLeaf.decl (cBS cx) = false).
  { rewrite <- (m4_pk_decl (x_f cx + 18) (cF cx fpos + 112) (cBS cx)); [exact Hpk | | lia].
    destruct (Hf50 H50) as [Hf0 _]. lia. }
  m4_trun (AF_both3_classify_core + 0x4d4).
  m4_set_window 14 16 ltac:(idtac; m4_fs_writable).
  m4_prun (AF_both3_classify_core + 0x530).
  m4_pbranch; m4_hc; m4_prun (AF_both3_classify_core + 0x530); m4_p3.
  + m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_introl HD))) ltac:(idtac; m4_Gge).
  + m4_fin ltac:(idtac; m4_D0 (m4_D_no (x_FB cx) (or_introl HD))) ltac:(idtac; m4_Glt).
Qed.

End h.
End f.
End d.
