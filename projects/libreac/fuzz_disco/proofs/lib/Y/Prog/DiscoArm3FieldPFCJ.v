(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 610 of its 649 lines of code are new or changed and 3971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3AgeCall1.v, with its module paths and module names changed; 492 of its 574 lines of code are new or changed and 567 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI0s YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3JtokSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model
slot_ser_defs slot_ser_tokb disco_jscalar_model jtok_is_c slot_ser_Pq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldPFKit DiscoArm3FieldCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pcj_bytes_map : forall l : list Z, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  intros l H. induction H as [|z l Hz _ IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma pcj_forall_fs : forall {A} (P : A -> Prop) l a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof.
  intros A P l a b H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. apply H.
  rewrite <- (firstn_skipn b l). apply in_or_app. right. rewrite <- (firstn_skipn a (skipn b l)).
  apply in_or_app. left. exact Hx.
Qed.

Lemma pcj_rdword_kept : forall (rd1 rd2 : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd2 (a + k) = rd1 (a + k)) ->
  rdword rd2 a = rdword rd1 a.
Proof.
  intros rd1 rd2 a H. unfold rdword.
  assert (H0 : rd2 a = rd1 a) by (rewrite <- (Z.add_0_r a); apply H; lia).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma pcj_zle_nth : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma pcj_zle_len : forall n z, length (Z_to_le_bytes n z) = n.
Proof. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes length]. rewrite IH. reflexivity. Qed.

Lemma pcj_hexc : forall d, 0 <= d < 16 -> 0 < disco_json_text.hexc d < 256.
Proof. intros d Hd. unfold disco_json_text.hexc. destruct (d <? 10); lia. Qed.

Lemma pcj_hex2 : forall x, 0 <= x < 256 -> Forall (fun c => 0 < c < 256) (disco_json_text.hex2 x).
Proof.
  intros x Hx. unfold disco_json_text.hex2.
  constructor; [cbv beta; apply pcj_hexc; lia|]. constructor; [cbv beta; apply pcj_hexc; lia | constructor].
Qed.

Lemma pcj_nth_byte : forall (l : list byte) i, 0 <= nth i (map bv_unsigned l) 0 < 256.
Proof.
  intros l i. destruct (Nat.lt_ge_cases i (length l)) as [H|H].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact H). rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth i l (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. exact R.
  - rewrite nth_overflow by (rewrite length_map; exact H). lia.
Qed.

Lemma pcj_mac_pos : forall l : list byte,
  Forall (fun c => 0 < c < 256) (disco_json_text.mac_text (map bv_unsigned l)).
Proof.
  intros l. unfold disco_json_text.mac_text. rewrite !Forall_app.
  repeat split; first [apply pcj_hex2; apply pcj_nth_byte | repeat constructor; lia].
Qed.

Lemma pcj_dsh_oo : forall k, 30 <= k < 174 -> dsh_mac k = 0.
Proof.
  intros k Hk.
  assert (H : forallb (fun i => dsh_mac (30 + Z.of_nat i) =? 0) (seq 0 144) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat (k - 30))). cbv beta in H.
  rewrite in_seq in H. replace (30 + Z.of_nat (Z.to_nat (k - 30))) with k in H by lia.
  apply Z.eqb_eq. apply H. lia.
Qed.

Lemma pcj_mac_sh : forall F y, F mod 8 = 0 -> 1728 <= y < 1746 -> saddr_ok (F + y) (dsh_mac (y / 8)).
Proof.
  intros F y HF Hy. unfold saddr_ok.
  assert (E : y / 8 = 216 \/ y / 8 = 217 \/ y / 8 = 218) by lia.
  destruct E as [E|[E|E]]; rewrite E.
  - left. reflexivity.
  - left. reflexivity.
  - right. change (dsh_mac 218) with 2. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pcj_mbyte_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a,
  d_kept P W m W' m' -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a.
Proof.
  intros P W m W' m' a HK Ha HP. pose proof (HK a Ha HP) as E. unfold aview in E.
  destruct (mbyte SEGS (rd W' m') a) as [b1|] eqn:E1; destruct (mbyte SEGS (rd W m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma pcj_val_mem_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a nb v,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ P x) ->
  val_mem SEGS (rd W m) a nb v -> val_mem SEGS (rd W' m') a nb v.
Proof.
  intros P W m W' m' a nb v HK H0 H1 HP Hv k Hk.
  rewrite (pcj_mbyte_kept P W m W' m'); [exact (Hv k Hk) | exact HK | lia |].
  apply HP. lia.
Qed.

Lemma pcj_garr8_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a l,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
  intros P W m W' m' a l HK H0 H1 HP Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (pcj_val_mem_kept P W m W' m'); [exact HK | lia | lia | | exact Hv].
  intros x Hx. apply HP. lia.
Qed.

Lemma pcj_region_ok_kept : forall (E : env) (m m' : word -> option byte) (r : YP09.region) lo hi,
  region_ok SEGS E m r ->
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) (YP09.r_chunks r) = true ->
  (forall a, base_val E (YP09.r_base r) + lo <= a < base_val E (YP09.r_base r) + hi ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r lo hi HR Hb Hk Hw. destruct HR as (H0 & H1 & _ & HC).
  split; [exact H0|]. split; [exact H1|]. split; [exact Hw|].
  rewrite Forall_forall in HC |- *. intros c Hc ii Hii. destruct (HC c Hc ii Hii) as (b & Hb1 & Hb2).
  exists b. split; [exact Hb1|].
  pose proof (proj1 (forallb_forall _ _) Hb c Hc) as Hcb. apply andb_prop in Hcb as [Hl Hh].
  apply Z.leb_le in Hl. apply Z.leb_le in Hh.
  rewrite Hk; [exact Hb2|]. lia.
Qed.

Lemma pcj_garr8_sub : forall (m : word -> option byte) a (L : list Z) s n,
  garr8 SEGS m a L -> 0 <= s -> s + Z.of_nat n <= Z.of_nat (length L) ->
  garr8 SEGS m (a + s) (firstn n (skipn (Z.to_nat s) L)).
Proof.
  intros m a L s n G Hs Hn.
  rewrite <- (firstn_skipn (Z.to_nat s) L) in G. apply garr8_app in G. destruct G as [_ G].
  rewrite length_firstn in G. rewrite Nat.min_l in G by lia. rewrite Z2Nat.id in G by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat s) L)) in G. apply garr8_app in G. exact (proj1 G).
Qed.

Lemma pcj_view_garr8 : forall (H : word -> bool) (m : word -> option byte) base n,
  (forall j, (j < n)%nat -> aview SEGS H m (base + Z.of_nat j) <> None) ->
  exists l, length l = n /\ garr8 SEGS (mrestrict H m) base l.
Proof.
  intros H m base n. revert base. induction n as [|n IH]; intros base Hv.
  - exists []. split; [reflexivity | apply garr8_nil].
  - assert (H0 : aview SEGS H m base <> None).
    { pose proof (Hv 0%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
    unfold aview in H0. destruct (mbyte SEGS (mrestrict H m) base) as [b|] eqn:Eb; [|exfalso; apply H0; reflexivity].
    destruct (IH (base + 1)) as (l & Hlen & Hl).
    { intros j Hj. replace (base + 1 + Z.of_nat j) with (base + Z.of_nat (S j)) by lia. apply Hv. lia. }
    exists (bv_unsigned b :: l). split; [cbn [length]; lia|].
    pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
    intros [|j] Hj.
    + cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
      intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Eb. f_equal.
      unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity.
      replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
      rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
      symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [nth]. destruct (Hl j ltac:(cbn [length] in Hj; lia)) as [Hv' Hr']. split; [|exact Hr'].
      replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.

Lemma pcj_le_val : forall m a (n : nat) z, 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS m a (map bv_unsigned (Z_to_le_bytes n z)) -> val_mem SEGS m a n z.
Proof.
  intros m a n z Hz G k Hk.
  assert (Hl : length (map bv_unsigned (Z_to_le_bytes n z)) = n)
    by (rewrite length_map; apply pcj_zle_len).
  rewrite (garr8_mbyte SEGS m a _ k G) by lia.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by lia. rewrite map_nth.
  rewrite pcj_zle_nth by exact Hk. rewrite Z_to_bv_bv_unsigned.
  rewrite le_byte_small by (first [exact Hz | exact Hk]). reflexivity.
Qed.

Lemma pcj_obj_len : forall buf vpad (o : disco_json_reader_model.jobj), length vpad = 4%nat -> length o = 6%nat ->
  length (slot_ser_defs.obj_bytes buf vpad o) = 144%nat.
Proof.
  intros buf vpad o Hv Ho. unfold slot_ser_defs.obj_bytes.
  destruct o as [|t1 [|t2 [|t3 [|t4 [|t5 [|t6 [|t7 o]]]]]]]; try discriminate Ho.
  cbn [map concat]. rewrite !length_app, !(slot_ser_Pq.slot24_len buf vpad _ Hv). reflexivity.
Qed.

Lemma pcj_obj_slot0 : forall m a buf vpad (os : list disco_json_reader_model.jobj) (q : nat),
  length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os -> (q < length os)%nat ->
  garr8 SEGS m a (map bv_unsigned (slot_ser_defs.objs_bytes buf vpad os)) ->
  garr8 SEGS m (a + 144 * Z.of_nat q)
    (map bv_unsigned (slot_ser_defs.slot24 buf vpad (nth 0 (nth q os []) disco_json_reader_model.tok_none))).
Proof.
  intros m a buf vpad os. revert a. induction os as [|o os IH]; intros a q Hv Ho Hq G; [cbn in Hq; lia|].
  apply Forall_cons_iff in Ho as [Ho1 Ho2].
  unfold slot_ser_defs.objs_bytes in G. cbn [map concat] in G. rewrite map_app in G.
  apply garr8_app in G. destruct G as [G1 G2].
  destruct q as [|q].
  - cbn [nth]. replace (a + 144 * Z.of_nat 0) with a by lia.
    destruct o as [|t o']; [cbn in Ho1; lia|].
    unfold slot_ser_defs.obj_bytes in G1. cbn [map concat] in G1. rewrite map_app in G1.
    apply garr8_app in G1. exact (proj1 G1).
  - cbn [nth]. rewrite length_map, (pcj_obj_len buf vpad o Hv Ho1) in G2.
    replace (a + 144 * Z.of_nat (S q)) with (a + Z.of_nat 144 + 144 * Z.of_nat q) by lia.
    apply (IH (a + Z.of_nat 144) q Hv Ho2); [cbn [length] in Hq; lia|].
    exact G2.
Qed.

Lemma pcj_ra : forall (cx : dcx) (shf : Z -> Z) (W : world SEGS) m lo n,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= lo -> lo + n <= DFRAME_SIZE ->
  (forall y, lo <= y < lo + n -> saddr_ok (d_FB cx + y) (shf (y / 8))) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) n.
Proof.
  intros cx shf W m lo n HS H8 H0 H1 Hok x Hx. unfold d_shadow in HS.
  exists (shf ((x - d_FB cx) / 8)). split.
  - unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (shadow_addr (d_FB cx) + (x - d_FB cx) / 8) by (unfold shadow_addr; lia).
    apply HS. unfold DFRAME_SH, DFRAME_SIZE in *. lia.
  - specialize (Hok (x - d_FB cx) ltac:(lia)).
    replace (d_FB cx + (x - d_FB cx)) with x in Hok by lia. exact Hok.
Qed.

Lemma pcj_hull : forall (cx : dcx) (shf : Z -> Z) (W : world SEGS) m lo n,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 64 <= lo -> lo + n + 64 <= DFRAME_SIZE -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) n.
Proof.
  intros cx shf W m lo n HS H8 H0 Hlo Hn Hpos s Hs. unfold d_shadow in HS.
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
  rewrite HS; [discriminate|].
  unfold shadow_addr, DFRAME_SH, DFRAME_SIZE in *. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis MCRO : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DROH : d_ro_hyps B.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DCAN : d_can_hyps B tfib_K.

Theorem a3f_pfc_j : pfC_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c Hs.
unfold pf_c2, a3f_stg, d_at in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & R24 & (R1 & HRj & R10 & R11 & R12) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & ((HSL & HJ1P & H408 & HUSED) & HMAC)) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20).
pose proof HSL as (Hpc & H368 & H360).
pose proof HBODY as (TT & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo, GSTK.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof HTAB as ((rem & _ & HAP) & HgOT).
pose proof HAP as (LT1 & _ & _ & _ & _ & _ & TOK & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os LT1 TOK Hnow HJR) as (Ec & Hc8 & Los & Lo6 & HINB & _ & _).
pose proof (DiscoArm3FieldModel.a3f_obj T1 now count os p LT1 TOK Hnow HJR Hpc) as HOBJM. cbv zeta in HOBJM.
destruct HOBJM as (HMK & _).
pose proof (HMK p ltac:(lia)) as HMKp. rewrite Z.eqb_refl in HMKp.
pose proof (HMK (j - 1) ltac:(lia)) as HMKj.
assert (HMKj' : disco_json_reader_model.jtok_is (a3_text T1 now)
  (nth 0 (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) 1 (pf_mtext T1 j) = (j - 1 =? p))
  by exact HMKj.
assert (Hoin : In (nth (Z.to_nat p) os []) os) by (apply nth_In; lia).
assert (Htin : slot_ser_tokb.tok_inb (a3_text T1 now)
  (nth 0 (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none)).
{ rewrite Forall_forall in HINB. pose proof (HINB _ Hoin) as HI1. rewrite Forall_forall in HI1. apply HI1.
  rewrite Forall_forall in Lo6. pose proof (Lo6 _ Hoin) as L6. apply nth_In. lia. }
pose proof (pcj_obj_slot0 (rd W mem3) (d_obj cx OO) buf vpad os (Z.to_nat p) HVP Lo6 ltac:(lia) HOO) as HS0.
rewrite Z2Nat.id in HS0 by lia.
clear HMKj.
set (t := nth 0 (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) in *.
clearbody t.
unfold disco_json_reader_model.jtok_is in HMKp.
apply andb_prop in HMKp as [HMKp _]. apply andb_prop in HMKp as [HK1 HL17].
apply Z.eqb_eq in HK1. apply Z.eqb_eq in HL17.
rewrite slot_ser_Pq.mac_text_len in HL17. change (Z.of_nat 17) with 17 in HL17.
unfold slot_ser_tokb.tok_inb in Htin. destruct Htin as [Hk0 | (Hks0 & Hkl0 & Hkb)]; [lia|].
unfold disco_jscalar_model.jlen in Hkb.
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & HbHull).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull.
pose proof HBUF as ((Hr2 & Hrc) & HgB).
unfold a3_r in Hr2, Hrc.
assert (HNr : Z.of_nat (length (a3_text T1 now)) + 1 <= Z.max (slot_ser_defs.ser_cap op) 1) by lia.
set (N := Z.max (slot_ser_defs.ser_cap op) 1) in *.
assert (HgT : garr8 SEGS (rd W mem3) buf (a3_text T1 now)) by (apply garr8_app in HgB; exact (proj1 HgB)).
pose proof (garr8_bytes_ok SEGS _ _ _ HgT) as HBok. unfold bytes_ok in HBok.
rewrite (slot_ser_Pq.slot24_split buf vpad t) in HS0 by lia.
rewrite !map_app in HS0.
apply garr8_app in HS0. destruct HS0 as [HS0 _].
apply garr8_app in HS0. destruct HS0 as [Gvp HS0].
apply garr8_app in HS0. destruct HS0 as [Gvn Gvk].
rewrite !length_map, !Mem.length_le8 in Gvn, Gvk. change (Z.of_nat 8) with 8 in Gvn, Gvk.
unfold Mem.le8, word_to_le_bytes in Gvp, Gvn. unfold Mem.le4 in Gvk.
rewrite unsigned_lit_small in Gvp by lia.
rewrite unsigned_lit_small in Gvn by lia.
rewrite unsigned_lit_small in Gvk by lia.
assert (Mvp : val_mem SEGS (rd W mem3) (d_obj cx OO + 144 * p) 8 (buf + snd (fst t))).
{ apply pcj_le_val; [change (8 * Z.of_nat 8) with 64; lia | exact Gvp]. }
assert (Mvn : val_mem SEGS (rd W mem3) (d_obj cx OO + 144 * p + 8) 8 (snd t)).
{ apply pcj_le_val; [change (8 * Z.of_nat 8) with 64; lia | exact Gvn]. }
assert (Mvk : val_mem SEGS (rd W mem3) (d_obj cx OO + 144 * p + 16) 4
  (disco_json_reader_model.tv_kind t mod 2 ^ 32)).
{ rewrite HK1. change (1 mod 2 ^ 32) with 1. rewrite HK1 in Gvk.
  replace (d_obj cx OO + 144 * p + 16) with (d_obj cx OO + 144 * p + 8 + 8) by lia.
  apply pcj_le_val; [change (8 * Z.of_nat 4) with 32; lia | exact Gvk]. }
assert (Lw : length (pf_mtext T1 j) = 17%nat) by (unfold pf_mtext; apply slot_ser_Pq.mac_text_len).
assert (HWF : Forall (fun c => 0 < c < 256) (pf_mtext T1 j))
  by exact (pcj_mac_pos (disco_table_c.mac_of T1 (j - 1))).
set (w := pf_mtext T1 j) in *.
clearbody w.
assert (HW' : Forall (fun c => 0 <= c < 256) w).
{ apply Forall_forall. intros cc Hcc. rewrite Forall_forall in HWF. specialize (HWF cc Hcc). lia. }
destruct (pcj_view_garr8 (w_H W) mem3 (d_obj cx OMAC + Z.of_nat (length (w ++ [0]))) 7) as (l & Hl & Gl).
{ intros jj Hjj. apply (aview_some_of_apresent SEGS). apply GFpres.
  rewrite length_app, Lw. cbn [length]. unfold d_obj, dobj_off. lia. }
pose proof (garr8_bytes_ok SEGS _ _ _ Gl) as Bl. unfold bytes_ok in Bl.
assert (HFB8 : d_FB cx mod 8 = 0) by lia.
assert (SpR : spZ regs = d_A cx) by (rewrite Rsp; lia).
assert (HPIFF : jtok_is_c.jtok_match (disco_json_reader_model.tv_kind t) 1 (Z_to_bv 64 (snd t))
    (map (Z_to_bv 8) (disco_json_reader_model.tv_text (a3_text T1 now) t)) (map (Z_to_bv 8) w) <->
  disco_json_reader_model.jtok_is (a3_text T1 now) t 1 w = true).
{ exact (slot_ser_Pq.jt_iff (a3_text T1 now) t 1 w HBok HWF ltac:(lia)). }
eapply SRr_mono.
{ apply (aj_jtok_at B LAWS TJTOK fq W regs mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k (d_A cx - d_S cx) (d_obj cx OO + 144 * p) (d_obj cx OMAC) 1
    (disco_json_reader_model.tv_kind t) (buf + snd (fst t)) (snd t) (map (Z_to_bv 8) w) (map (Z_to_bv 8) l)
    (map (Z_to_bv 8) (disco_json_reader_model.tv_text (a3_text T1 now) t)) HJ HFRM0).
  - rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold TJTOK_IS_STK, ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold PFR2_OFF; lia.
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold PFR2_OFF; lia). unfold PFR2_OFF. lia.
  - exact HIMG.
  - exact (mc_cv_ok B W mem3 MCRO MCUN HIMG).
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact Mvp.
  - exact Mvn.
  - exact Mvk.
  - lia.
  - lia.
  - apply (amem_range_sub_app (d_FB cx) 4096 _ 20 GFapp GFceil); unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off. replace (d_FB cx + 240 + 144 * p) with (d_FB cx + (240 + 144 * p)) by lia.
    apply (pcj_ra cx dsh_mac W mem3 _ _ HSHD HFB8); [lia | unfold DFRAME_SIZE; lia |].
    intros y Hy. unfold saddr_ok. left. apply pcj_dsh_oo. lia.
  - unfold d_obj, dobj_off. replace (d_FB cx + 240 + 144 * p) with (d_FB cx + (240 + 144 * p)) by lia.
    apply (pcj_hull cx dsh_mac W mem3 _ _ HSHD HFB8); unfold DFRAME_SIZE; lia.
  - left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK, d_obj, dobj_off. lia.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (cc & Hc & Hcw). rewrite Forall_forall in HWF.
    specialize (HWF cc Hcw). apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc.
    unfold bv_wrap in Hc. change (bv_modulus 8) with 256 in Hc. rewrite !Z.mod_small in Hc by lia. lia.
  - rewrite map_app. cbn [map]. rewrite (pcj_bytes_map _ HW'), (pcj_bytes_map _ Bl).
    change (bv_unsigned (Z_to_bv 8 0)) with 0.
    replace (w ++ 0 :: l) with ((w ++ [0]) ++ l) by (rewrite <- app_assoc; reflexivity).
    apply garr8_app. split; [exact HMAC | exact Gl].
  - rewrite !length_map, Hl. lia.
  - unfold d_obj, dobj_off. lia.
  - rewrite !length_map, Lw, Hl. unfold d_obj, dobj_off. lia.
  - rewrite length_map, Lw. lia.
  - rewrite length_map, Lw. apply (amem_range_sub_app (d_FB cx) 4096 _ _ GFapp GFceil); unfold d_obj, dobj_off; lia.
  - rewrite length_map, Lw. change (Z.of_nat (17 + 1)) with 18. unfold d_obj, dobj_off.
    apply (pcj_ra cx dsh_mac W mem3 _ _ HSHD HFB8); [lia | unfold DFRAME_SIZE; lia |].
    intros y Hy. apply pcj_mac_sh; [exact HFB8 | lia].
  - rewrite length_map, Lw. change (Z.of_nat (17 + 1)) with 18. unfold d_obj, dobj_off.
    apply (pcj_hull cx dsh_mac W mem3 _ _ HSHD HFB8); unfold DFRAME_SIZE; lia.
  - left. rewrite SpR. rewrite !length_map, Lw, Hl. unfold TJTOK_IS_STK, ESTACK, d_obj, dobj_off. lia.
  - intros _ Hvn. rewrite length_map in Hvn. rewrite !length_map. rewrite Lw in Hvn |- *.
    assert (HL1 : length (disco_json_reader_model.tv_text (a3_text T1 now) t) = 17%nat).
    { unfold disco_json_reader_model.tv_text. rewrite length_firstn, length_skipn. lia. }
    assert (HSb : Forall (fun c => 0 <= c < 256) (disco_json_reader_model.tv_text (a3_text T1 now) t)).
    { unfold disco_json_reader_model.tv_text. apply pcj_forall_fs. exact HBok. }
    split; [exact HL1|].
    split.
    { rewrite (pcj_bytes_map _ HSb). unfold disco_json_reader_model.tv_text.
      apply pcj_garr8_sub; [exact HgT | lia | lia]. }
    split; [lia|]. split; [lia|].
    split; [apply (amem_range_sub_app buf N (buf + snd (fst t)) (Z.of_nat 17)); [exact Hbapp | lia | lia | lia | lia]|].
    split; [apply (block_shadow_range _ _ buf N (buf + snd (fst t)) (Z.of_nat 17) HbSh); lia|].
    split.
    { intros Hpos s Hs. apply HbHull.
      pose proof (YCbq.shadow_mono buf (buf + snd (fst t)) ltac:(lia)) as Sm1.
      pose proof (YCbq.shadow_mono (buf + snd (fst t) + Z.of_nat 17 - 1) (buf + N - 1) ltac:(lia)) as Sm2.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm1) as Sd1.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm2) as Sd2. lia. }
    left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK. lia. }
cbv beta. intros W2 c2 HW2 (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRMc & _ & HJ4 & HJc & HP & HAB & HKP & HRES).
clear dependent fq. rename fx2 into fq. rename HFRMc into HFRM0.
pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
unfold LLVMF_STK in GSTK4.
set (Pw := fun a => d_A cx - TJTOK_IS_STK <= a < d_A cx).
assert (HK : d_kept Pw W mem3 W2 mem2).
{ intros a Ha HPa. apply HKP; [exact Ha|]. rewrite SpR. exact HPa. }
assert (HPlo : forall a, a < alloc_ceiling -> ~ Pw a) by (intros a Ha Hp; unfold Pw, TJTOK_IS_STK, ESTACK in *; lia).
assert (HPA : forall a, d_A cx <= a -> ~ Pw a) by (intros a Ha Hp; unfold Pw in Hp; lia).
assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) nb v -> val_mem SEGS (rd W2 mem2) (d_A cx + off) nb v).
{ intros off nb v Hoff Hnb Hv. apply (pcj_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | | exact Hv].
  intros y Hy. apply HPA. lia. }
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (ES2 : bv_unsigned (ew E AT_STK) = d_S cx)
  by (rewrite (EE AT_STK 2%bv ltac:(vm_compute; reflexivity)); reflexivity).
assert (HFRM4 : d_frame cx h dsh_mac W2 mem2).
{ exists E. split; [exact HE|]. split; [|split].
  - unfold d_regions in HREG |- *. rewrite !Forall_cons_iff in HREG |- *.
    destruct HREG as (HRS & HRA & HRF & HRH & _).
    split; [|split; [|split; [|split; [|exact (Forall_nil _)]]]].
    + apply (pcj_region_ok_kept E _ _ _ (-104) 0 HRS); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. rewrite ES2.
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
      * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    + apply (pcj_region_ok_kept E _ _ _ 0 472 HRA); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. rewrite E60. unfold w64. rewrite unsigned_lit_small by lia.
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
      * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite E60. unfold w64.
        rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GSTK4. lia.
    + apply (pcj_region_ok_kept E _ _ _ 0 24 HRF); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. rewrite EF. unfold w64. rewrite unsigned_lit_small by lia.
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPlo; lia].
      * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite EF. unfold w64.
        rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GFpres4.
        unfold DFRAME_SIZE in Ho. lia.
    + apply (pcj_region_ok_kept E _ _ _ 0 384 HRH); [vm_compute; reflexivity | |].
      * unfold fshadow_region. cbn [YP09.r_base base_val]. rewrite ESH. unfold w64.
        rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        intros a Ha. apply (mbyte_of_aview SEGS).
        apply HK; [unfold shadow_addr, SHADOW_OFF in *; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF in *; lia].
      * unfold fshadow_region. cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite ESH. unfold w64.
        rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        intros o Ho. apply (apresent_writable SEGS). apply GFsh4. unfold DFRAME_SH in Ho. lia.
  - rewrite <- HFLAG. apply pcj_rdword_kept. intros kk0 Hkk0.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HK; [lia | apply HPlo; lia].
  - split; [apply KV; [lia | cbn; lia | exact V184]|].
    split; [apply KV; [lia | cbn; lia | exact V120]|].
    split; [apply KV; [lia | cbn; lia | exact V136]|].
    split; [apply KV; [lia | cbn; lia | exact V376]|].
    split; [apply KV; [lia | cbn; lia | exact V280]|].
    split; [apply KV; [lia | cbn; lia | exact V232]|].
    apply KV; [lia | cbn; lia | exact V264]. }
assert (HSHD4 : d_shadow cx dsh_mac W2 mem2).
{ intros kk0 Hkk0. rewrite <- (HSHD kk0 Hkk0). unfold DFRAME_SH in Hkk0.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF; lia]. }
pose proof (DBPC LAWS DROH DCAN cx h n (a3_xb buf op) dsh_mac dsh_mac ly3 S3 W mem3 md3 ly2 S2 W2 mem2 md2 k
  TJTOK_IS_STK (spZ regs) [] 0 HBODY (conj HBASE HJ4) HJc
  ltac:(rewrite SpR; unfold TJTOK_IS_STK, ESTACK, LLVMF_STK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
  ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
  HAB HFRM4 HSHD4) as HBODY4.
assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (Q10 : getr regs2 10 = w64 (if j - 1 =? p then 1 else 0)).
{ destruct HRES as [(HM & Q) | (HM & Q)].
  - apply HPIFF in HM. rewrite HMKj' in HM. rewrite HM. exact Q.
  - destruct (j - 1 =? p) eqn:Ejp; [|exact Q].
    exfalso. apply HM. apply HPIFF. first [exact HMKj' | rewrite HMKj'; exact Ejp]. }
assert (HLo : length (slot_ser_defs.objs_bytes buf vpad os) = (144 * Z.to_nat count)%nat).
{ exact (eq_trans (slot_ser_Pq.objs_len buf vpad os HVP Lo6) (f_equal (fun z : nat => (144 * z)%nat) Los)). }
unfold pf_c3, a3f_stg, d_at.
split.
{ destruct HFROM as (HA3 & HW0 & HT0 & HEX). split; [exact HA3|].
  split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HT0 | exact HEX]. }
exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs19|]. split; [rewrite P18; exact Rs18|].
  rewrite P20; exact Rs20. }
split; [rewrite P24; exact R24|].
split.
{ destruct HRj as (J21 & J22 & J23 & J25 & J26).
  split; [|exact Q10].
  split; [rewrite P21; exact J21|]. split; [rewrite P22; exact J22|]. split; [rewrite P23; exact J23|].
  split; [rewrite P25; exact J25 | rewrite P26; exact J26]. }
split.
{ pose proof HSP1 as ((H208 & H320) & H192 & H200).
  split; [split; [split|split]|].
  - apply KV; [lia | cbn; lia | exact H208].
  - apply KV; [lia | cbn; lia | exact H320].
  - apply KV; [lia | cbn; lia | exact H192].
  - apply KV; [lia | cbn; lia | exact H200].
  - split.
    { split; [exact (proj1 HTAB)|].
      apply (pcj_garr8_kept Pw W mem3 W2 mem2); [exact HK | unfold d_obj, dobj_off; lia | | | exact HgOT].
      - rewrite length_map, LT1. unfold d_obj, dobj_off. lia.
      - intros x Hx. rewrite length_map, LT1 in Hx. unfold d_obj, dobj_off in Hx. apply HPlo. lia. }
    split.
    { split; [unfold a3_r; lia|].
      apply (pcj_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HgB].
      - rewrite length_app. cbn [length]. lia.
      - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply HPlo. lia. }
    split; [exact HJR|]. split; [exact HVP|].
    split.
    { apply (pcj_garr8_kept Pw W mem3 W2 mem2); [exact HK | unfold d_obj, dobj_off; lia | | | exact HOO].
      - rewrite length_map, HLo. unfold d_obj, dobj_off. lia.
      - intros x Hx. rewrite length_map, HLo in Hx. unfold d_obj, dobj_off in Hx. apply HPlo. lia. }
    split; [split; [lia|]; split; [apply KV; [lia | cbn; lia | exact H368] | apply KV; [lia | cbn; lia | exact H360]]|].
    split; [exact HJ1P|].
    split; [apply KV; [lia | cbn; lia | exact H408]|].
    assert (LU : length (a3f_used p) = 32%nat) by reflexivity.
    apply (pcj_garr8_kept Pw W mem3 W2 mem2); [exact HK | unfold d_obj, dobj_off; lia | | | exact HUSED].
    + rewrite LU. unfold d_obj, dobj_off. lia.
    + intros x Hx. rewrite LU in Hx. unfold d_obj, dobj_off in Hx. apply HPlo. lia. }
split.
{ pose proof HSP0 as (H208 & H320).
  split; [apply KV; [lia | cbn; lia | exact H208] | apply KV; [lia | cbn; lia | exact H320]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
