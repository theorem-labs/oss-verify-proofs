(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 520 of its 557 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma tn_s3 : forall t n, 0 <= t -> 0 <= n < 8 -> t + 48 * n < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 t) (mul_div M_MUL (Z_to_bv 64 n) (Z_to_bv 64 48)) = Z_to_bv 64 (t + 48 * n).
Proof.
intros t n Ht Hn Htn. rewrite m_mul. unfold v_mul. rewrite !unsigned_lit_small by lia.
rewrite alu64_add_lit. f_equal. lia.
Qed.
Lemma tn_snez : forall ow, -2 ^ 31 <= ow < 2 ^ 31 ->
  alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ow) = Z_to_bv 64 (if ow =? 0 then 0 else 1).
Proof.
intros ow How. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec ow 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec (0 mod 2 ^ 64) (ow mod 2 ^ 64)); [reflexivity | exfalso; lia].
Qed.
Lemma tn_ne_nat : forall G ow now, length G = 24%nat ->
  (forall j, (j < 6 \/ 8 <= j < 17 \/ 20 <= j < 24)%nat -> nth_error (RDOC.new_entry G ow now) j = nth_error G j) /\
  (forall j, (6 <= j < 8 \/ 17 <= j < 20 \/ 28 <= j < 32)%nat -> nth_error (RDOC.new_entry G ow now) j = Some (Z_to_bv 8 0)) /\
  (forall j, (j < 4)%nat -> nth_error (RDOC.new_entry G ow now) (24 + j) = nth_error (Z_to_le_bytes 4 (if ow =? 0 then 0 else 1)) j) /\
  (forall j, (j < 8)%nat -> nth_error (RDOC.new_entry G ow now) (32 + j) = nth_error (Z_to_le_bytes 8 now) j) /\
  (forall j, (j < 8)%nat -> nth_error (RDOC.new_entry G ow now) (40 + j) = nth_error (Z_to_le_bytes 8 now) j).
Proof.
intros G ow now LG. do 24 (destruct G as [|? G]; [discriminate|]). destruct G; [|discriminate]. clear LG.
split; [|split; [|split; [|split]]]; intros j Hj;
do 48 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]); exfalso; lia.
Qed.
Lemma tn_bow_le : forall (w : word) n i, 0 <= i < Z.of_nat n ->
  Some (byte_of_word w i) = nth_error (Z_to_le_bytes n (bv_unsigned w)) (Z.to_nat i).
Proof.
intros w n i Hi. rewrite Z_to_le_bytes_st. unfold st_bytes, byte_of_word.
rewrite nth_error_zbytes by lia. f_equal. f_equal. f_equal. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tn_mbyte_of_aview : forall H m a (b : byte), aview SEGS H m a = Some (bv_unsigned b) ->
  mbyte SEGS (mrestrict H m) a = Some b.
Proof.
intros H m a b Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b'|]; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma tn_garr8_upd : forall H m m' p (L v : list byte) k,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) ->
  0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length L) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> ~ (k <= i < k + Z.of_nat (length v)) ->
     aview SEGS H m' (p + i) = aview SEGS H m (p + i)) ->
  (forall i, 0 <= i < Z.of_nat (length v) -> exists b, nth_error v (Z.to_nat i) = Some b /\
     aview SEGS H m' (p + k + i) = Some (bv_unsigned b)) ->
  garr8 SEGS (mrestrict H m') p (map (fun b : byte => bv_unsigned b) (DTC.upd L k v)).
Proof.
intros H m m' p L v k HG Hk Hkv Hout Hin.
assert (HL : length (DTC.upd L k v) = length L) by (apply RDO.upd_len; assumption).
apply garr8_of_mbytes. intros i Hi. rewrite HL in Hi.
rewrite <- (nth_error_nth' (DTC.upd L k v) (Z_to_bv 8 0)) by (rewrite HL; exact Hi).
replace (nth_error (DTC.upd L k v) i) with (nth_error (DTC.upd L k v) (Z.to_nat (Z.of_nat i)))
  by (rewrite Nat2Z.id; reflexivity).
destruct (Z_lt_le_dec (Z.of_nat i) k) as [Hlt|Hge];
[|destruct (Z_lt_le_dec (Z.of_nat i) (k + Z.of_nat (length v))) as [Hlt2|Hge2]].
- rewrite TM.upd_nth_out by lia. rewrite Nat2Z.id, (nth_error_nth' L (Z_to_bv 8 0) Hi).
  apply tn_mbyte_of_aview. rewrite (Hout (Z.of_nat i) ltac:(lia) ltac:(lia)). exact (aview_of_garr8 H m p L i HG Hi).
- rewrite TM.upd_nth_in by lia.
  destruct (Hin (Z.of_nat i - k) ltac:(lia)) as (b & Hb & Hv). rewrite Hb.
  apply tn_mbyte_of_aview. replace (p + Z.of_nat i) with (p + k + (Z.of_nat i - k)) by lia. exact Hv.
- rewrite TM.upd_nth_out by lia. rewrite Nat2Z.id, (nth_error_nth' L (Z_to_bv 8 0) Hi).
  apply tn_mbyte_of_aview. rewrite (Hout (Z.of_nat i) ltac:(lia) ltac:(lia)). exact (aview_of_garr8 H m p L i HG Hi).
Qed.
Lemma tn_cagree_sext4 : forall E b lo L off d s, 0 <= s -> (Z.to_nat s + 4 <= length (ed E d))%nat ->
  (forall j, 0 <= j < 4 -> nth_error (ed E d) (Z.to_nat (s + j)) = nth_error L (Z.to_nat (off + j - lo))) ->
  cagree E b lo L (YP09.mkChunk off (CVal 4 (SExt true 32 (SData d s 4)))).
Proof.
intros E b lo L off d s Hs Hlen H j Hj. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val Z.of_N] in Hj |- *.
unfold YP09.cbyte. cbn [sv_denot]. rewrite (byte_of_word_low32 true) by lia.
pose proof (byte_of_data_word E d s 4 (Z.to_nat j) Hs ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Hb, <- Z2Nat.inj_add by lia. apply H. exact Hj.
Qed.
Lemma tn_cagree_sdata : forall E b lo L off d s (n : nat), 0 <= s -> (Z.to_nat s + n <= length (ed E d))%nat -> (n <= 8)%nat ->
  (forall j, 0 <= j < Z.of_nat n -> nth_error (ed E d) (Z.to_nat (s + j)) = nth_error L (Z.to_nat (off + j - lo))) ->
  cagree E b lo L (YP09.mkChunk off (CVal (N.of_nat n) (SData d s (N.of_nat n)))).
Proof.
intros E b lo L off d s n Hs Hlen Hn H j Hj. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hj |- *.
rewrite nat_N_Z in Hj. unfold YP09.cbyte. cbn [sv_denot].
pose proof (byte_of_data_word E d s (N.of_nat n) (Z.to_nat j) Hs ltac:(rewrite Nat2N.id; lia) ltac:(rewrite Nat2N.id; lia)
  ltac:(rewrite Nat2N.id; lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Hb, <- Z2Nat.inj_add by lia. apply H. exact Hj.
Qed.
Lemma tn_cagree_lit : forall E b lo L off (n : nat) v z, sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat n -> nth_error (Z_to_le_bytes n z) (Z.to_nat j) = nth_error L (Z.to_nat (off + j - lo))) ->
  cagree E b lo L (YP09.mkChunk off (CVal (N.of_nat n) v)).
Proof.
intros E b lo L off n v z Hv Hz H j Hj. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hj |- *.
rewrite nat_N_Z in Hj. unfold YP09.cbyte. rewrite Hv, (tn_bow_le (Z_to_bv 64 z) n j Hj), unsigned_lit_small by exact Hz.
apply H. exact Hj.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Definition tTh (c : tctx) : list byte := DTC.upd (tT c) 384 (Z_to_le_bytes 4 (DTC.n_of (tT c) + 1)).
Definition tTz (c : tctx) : list byte := DTC.upd (tTh c) (48 * DTC.n_of (tT c)) (repeat (Z_to_bv 8 0) 48).
Definition tTm (c : tctx) : list byte := DTC.upd (tTz c) (48 * DTC.n_of (tT c)) (DTC.sub (tG c) 0 6).
Definition tTn (c : tctx) : list byte :=
  DTC.upd (tTh c) (48 * DTC.n_of (tT c)) (RDOC.new_entry (tG c) (tow c) (tnow c)).
Lemma tn_lens : forall c, tpre B c -> 0 <= DTC.n_of (tT c) < 8 ->
  length (tTh c) = 400%nat /\ length (tTz c) = 400%nat /\ length (tTm c) = 400%nat /\ length (tTn c) = 400%nat.
Proof.
intros c HP Hn. pose proof (tp_Tl _ _ HP) as LT. pose proof (tp_Gl _ _ HP) as LG.
destruct (RDO.mf_ne (tG c) (tow c) (tnow c) LG) as (LN & _).
assert (Lh : length (tTh c) = 400%nat) by (unfold tTh; rewrite RDO.upd_len; rewrite ?length_Z_to_le_bytes; lia).
assert (Lz : length (tTz c) = 400%nat) by (unfold tTz; rewrite RDO.upd_len; rewrite ?repeat_length; lia).
assert (Lm : length (tTm c) = 400%nat)
  by (unfold tTm; rewrite RDO.upd_len; rewrite ?length_sub_le; lia).
assert (Ln : length (tTn c) = 400%nat) by (unfold tTn; rewrite RDO.upd_len; lia).
exact (conj Lh (conj Lz (conj Lm Ln))).
Qed.
Lemma tn_out : forall c, tpre B c -> 0 <= DTC.n_of (tT c) < 8 -> forall i, 0 <= i < 400 ->
  ~ (48 * DTC.n_of (tT c) <= i < 48 * DTC.n_of (tT c) + 48) ->
  nth_error (tTz c) (Z.to_nat i) = nth_error (tTh c) (Z.to_nat i) /\
  nth_error (tTm c) (Z.to_nat i) = nth_error (tTh c) (Z.to_nat i) /\
  nth_error (tTn c) (Z.to_nat i) = nth_error (tTh c) (Z.to_nat i).
Proof.
intros c HP Hn i Hi Hni. pose proof (tp_Gl _ _ HP) as LG.
destruct (RDO.mf_ne (tG c) (tow c) (tnow c) LG) as (LN & _).
destruct (tn_lens c HP Hn) as (Lh & Lz & Lm & Ln).
assert (Ez : nth_error (tTz c) (Z.to_nat i) = nth_error (tTh c) (Z.to_nat i))
  by (unfold tTz; rewrite TM.upd_nth_out; rewrite ?repeat_length; try reflexivity; lia).
split; [exact Ez|]. split.
- unfold tTm. rewrite TM.upd_nth_out; rewrite ?length_sub_le; try lia. exact Ez.
- unfold tTn. rewrite TM.upd_nth_out; try reflexivity; lia.
Qed.
Lemma tn_th_out : forall c, tpre B c -> forall i, 0 <= i < 400 -> ~ (384 <= i < 388) ->
  nth_error (tTh c) (Z.to_nat i) = nth_error (tT c) (Z.to_nat i).
Proof.
intros c HP i Hi Hni. pose proof (tp_Tl _ _ HP) as LT.
unfold tTh. rewrite TM.upd_nth_out; rewrite ?length_Z_to_le_bytes; try reflexivity; lia.
Qed.
Lemma tn_th_in : forall c, tpre B c -> forall i, 0 <= i < 4 ->
  nth_error (tTh c) (Z.to_nat (384 + i)) = nth_error (Z_to_le_bytes 4 (DTC.n_of (tT c) + 1)) (Z.to_nat i).
Proof.
intros c HP i Hi. pose proof (tp_Tl _ _ HP) as LT.
unfold tTh. rewrite TM.upd_nth_in; rewrite ?length_Z_to_le_bytes; try lia. f_equal. lia.
Qed.
Lemma tn_ent_m : forall c, tpre B c -> 0 <= DTC.n_of (tT c) < 8 -> forall k, 0 <= k < 48 ->
  nth_error (tTm c) (Z.to_nat (48 * DTC.n_of (tT c) + k)) =
  if k <? 6 then nth_error (tG c) (Z.to_nat k) else Some (Z_to_bv 8 0).
Proof.
intros c HP Hn k Hk. pose proof (tp_Gl _ _ HP) as LG.
destruct (tn_lens c HP Hn) as (Lh & Lz & Lm & Ln).
destruct (Z.ltb_spec k 6) as [Hk6|Hk6].
- unfold tTm. rewrite TM.upd_nth_in; rewrite ?length_sub_le; try lia.
  rewrite nth_error_sub by lia. f_equal. lia.
- unfold tTm. rewrite TM.upd_nth_out; rewrite ?length_sub_le; try lia.
  unfold tTz. rewrite TM.upd_nth_in; rewrite ?repeat_length; try lia.
  apply nth_error_repeat. lia.
Qed.
Lemma tn_ent_n : forall c, tpre B c -> 0 <= DTC.n_of (tT c) < 8 -> forall k, 0 <= k < 48 ->
  nth_error (tTn c) (Z.to_nat (48 * DTC.n_of (tT c) + k)) = nth_error (RDOC.new_entry (tG c) (tow c) (tnow c)) (Z.to_nat k).
Proof.
intros c HP Hn k Hk. pose proof (tp_Gl _ _ HP) as LG.
destruct (RDO.mf_ne (tG c) (tow c) (tnow c) LG) as (LN & _).
destruct (tn_lens c HP Hn) as (Lh & Lz & Lm & Ln).
unfold tTn. rewrite TM.upd_nth_in by lia. f_equal. lia.
Qed.
Lemma tn_ent_agree : forall c, tpre B c -> 0 <= DTC.n_of (tT c) < 8 -> forall k,
  (0 <= k < 8 \/ 17 <= k < 20 \/ 28 <= k < 32) ->
  nth_error (DTC.sub (tTm c) (48 * DTC.n_of (tT c)) 48) (Z.to_nat k) =
  nth_error (RDOC.new_entry (tG c) (tow c) (tnow c)) (Z.to_nat k).
Proof.
intros c HP Hn k Hk. pose proof (tp_Gl _ _ HP) as LG.
destruct (tn_ne_nat (tG c) (tow c) (tnow c) LG) as (N1 & N2 & _).
rewrite nth_error_sub by lia.
replace (Z.to_nat (48 * DTC.n_of (tT c)) + Z.to_nat k)%nat with (Z.to_nat (48 * DTC.n_of (tT c) + k)) by lia.
rewrite (tn_ent_m c HP Hn k ltac:(lia)).
destruct (Z.ltb_spec k 6) as [Hk6|Hk6]; symmetry; [apply N1 | apply N2]; lia.
Qed.
Lemma tn_model : forall c, tpre B c -> tnone c -> DTC.n_of (tT c) < 8 ->
  RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) (DTC.upd (tTn c) 392 (Z_to_le_bytes 4 (DTC.seq_of (tTn c) + 1))) 1.
Proof.
intros c HP Hno Hn8. pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (TM.new_table (tT c) (tG c) (tow c) (tnow c) (tp_Tl _ _ HP) (tp_Gl _ _ HP) ltac:(lia)) as X. cbv zeta in X.
destruct X as (_ & Hseq & Hobs & _).
pose proof (TM.model_new (tT c) (tG c) (tow c) (tnow c) Hno Hn8) as HM. rewrite Hobs in HM. cbn [fst snd] in HM.
unfold tTn, tTh, DTC.seq_of. rewrite Hseq. exact HM.
Qed.
Lemma tn_memset : forall c regsT memT mdT Tc r ret Q,
  tpre B c -> tobs_m B c regsT memT mdT Tc -> 0 <= r < 8 ->
  YK11.getr regsT 10 = w64 (tt c + 48 * r) -> YK11.getr regsT 11 = w64 0 -> YK11.getr regsT 12 = w64 48 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall regs2 mem2 md2, tobs_m B c regs2 mem2 md2 (DTC.upd Tc (48 * r) (repeat (Z_to_bv 8 0) 48)) ->
     aregs_preserved regsT regs2 ->
     SRr SEGS (tW c) (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS (tW c) (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA DS___asan_memset)) memT (YK11.seg_rom SEGS)) mdT) Q.
Proof.
intros c regsT memT mdT Tc r ret Q HP HM Hr H10 H11 H12 H1 Hret0 Hret2 HK.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi. pose proof (tp_al _ _ HP) as Hal.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_tam _ _ HP) as Htam. pose proof (tp_twin _ _ HP) as Htwin.
pose proof (tm_sp _ _ _ _ _ _ HM) as Hsp. pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
pose proof (tm_T _ _ _ _ _ _ HM) as HT.
pose proof (tm_tra _ _ _ _ _ _ HM) as Htra. pose proof (tm_thull _ _ _ _ _ _ HM) as Hthull.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam.
pose proof (Z.div_mod (tsp0 c) 16 ltac:(lia)) as D0. rewrite Hsp0al, Z.add_0_r in D0.
pose proof (Z.div_mod (spZ (tregs c)) 16 ltac:(lia)) as D1. rewrite Hal, Z.add_0_r in D1.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OSet _ (AMEMSET fx) (tW c) regsT memT (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c)
    (tW0 c) (tmem0 c) (tmd0 c) (town c) (tlyc c) (tSc c) mdT (tk c) (tt c + 48 * r) 0 48 (spZ regsT - tsp0 c)
    (Z_to_bv 64 (BASE + ret)) HJ H10 H11 H12).
  - lia. - lia. - lia. - lia.
  - replace (spZ regsT - tsp0 c) with ((spZ (tregs c) / 16 - 6 - tsp0 c / 16) * 16) by lia. apply Z_mod_mult.
  - lia. - rewrite Hes. lia.
  - rewrite (tm_gp _ _ _ _ _ _ HM). exact (tp_gp _ _ HP).
  - rewrite (tm_tp _ _ _ _ _ _ HM). exact (tp_tp _ _ HP).
  - exact H1.
  - apply ret_ok_codeptr_v; lia.
  - intros a Ha. split; [exact (proj1 (tp_tawr _ _ HP a ltac:(lia))) | rewrite Hes; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - eapply range_addressable_sub; [exact Htra | lia | lia].
  - intros _. eapply hull_sub; [exact Hthull | lia | lia | lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpr2).
apply (HK regs2 mem2 md2); [|exact HP2].
apply (tobs_m_step B LAWS c regsT memT mdT Tc regs2 mem2 md2 _ HP HM HJ2).
- intros a Ha Ht Hw. apply Hfr; [exact Ha | lia | rewrite Hes; lia].
- exact Hpr2.
- apply (tn_garr8_upd (w_H (tW c)) memT mem2 (tt c) Tc (repeat (Z_to_bv 8 0) 48) (48 * r) HT);
  rewrite ?repeat_length, ?HTl; try lia.
  + intros i Hi Hni. apply Hfr; [lia | lia | rewrite Hes; lia].
  + intros i Hi. exists (Z_to_bv 8 0). split; [apply nth_error_repeat; lia|].
    rewrite (Hset i ltac:(lia)). reflexivity.
- rewrite RDO.upd_len; rewrite ?repeat_length; lia.
- intros q Hq. apply HP2. unfold acallee_saved. cbn in Hq. lia.
Qed.
Lemma tn_memcpy : forall c regsT memT mdT Tc r ret Q,
  tpre B c -> tobs_m B c regsT memT mdT Tc -> 0 <= r < 8 ->
  YK11.getr regsT 10 = w64 (tt c + 48 * r) -> YK11.getr regsT 11 = w64 (ts c) -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall regs2 mem2 md2, tobs_m B c regs2 mem2 md2 (DTC.upd Tc (48 * r) (DTC.sub (tG c) 0 6)) ->
     aregs_preserved regsT regs2 ->
     SRr SEGS (tW c) (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS (tW c) (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA DS___asan_memcpy)) memT (YK11.seg_rom SEGS)) mdT) Q.
Proof.
intros c regsT memT mdT Tc r ret Q HP HM Hr H10 H11 H12 H1 Hret0 Hret2 HK.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi. pose proof (tp_al _ _ HP) as Hal.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_tam _ _ HP) as Htam. pose proof (tp_twin _ _ HP) as Htwin.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63. pose proof (tp_sam _ _ HP) as Hsam. pose proof (tp_swin _ _ HP) as Hswin.
pose proof (tp_st _ _ HP) as Hst. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tm_sp _ _ _ _ _ _ HM) as Hsp. pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
pose proof (tm_T _ _ _ _ _ _ HM) as HT. pose proof (tm_G _ _ _ _ _ _ HM) as HG.
pose proof (tm_tra _ _ _ _ _ _ HM) as Htra. pose proof (tm_sra _ _ _ _ _ _ HM) as Hsra.
pose proof (tm_thull _ _ _ _ _ _ HM) as Hthull. pose proof (tm_shull _ _ _ _ _ _ HM) as Hshull.
pose proof (tm_spres _ _ _ _ _ _ HM) as Hspres.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin, Hswin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hsam.
pose proof (Z.div_mod (tsp0 c) 16 ltac:(lia)) as D0. rewrite Hsp0al, Z.add_0_r in D0.
pose proof (Z.div_mod (spZ (tregs c)) 16 ltac:(lia)) as D1. rewrite Hal, Z.add_0_r in D1.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy _ (AMEMCPY fx) (tW c) regsT memT (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c)
    (tW0 c) (tmem0 c) (tmd0 c) (town c) (tlyc c) (tSc c) mdT (tk c) (tt c + 48 * r) (ts c) 6 (spZ regsT - tsp0 c)
    (Z_to_bv 64 (BASE + ret)) HJ H10 H11 H12).
  - lia. - lia. - lia. - lia.
  - replace (spZ regsT - tsp0 c) with ((spZ (tregs c) / 16 - 6 - tsp0 c / 16) * 16) by lia. apply Z_mod_mult.
  - lia. - rewrite Hes. lia.
  - rewrite (tm_gp _ _ _ _ _ _ HM). exact (tp_gp _ _ HP).
  - rewrite (tm_tp _ _ _ _ _ _ HM). exact (tp_tp _ _ HP).
  - exact H1.
  - apply ret_ok_codeptr_v; lia.
  - intros a Ha. split; [exact (proj1 (tp_tawr _ _ HP a ltac:(lia))) | rewrite Hes; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - eapply range_addressable_sub; [exact Htra | lia | lia].
  - intros _. eapply hull_sub; [exact Hthull | lia | lia | lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hspres; lia | rewrite Hes; lia]. }
    split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|]. split.
    + eapply range_addressable_sub; [exact Hsra | lia | lia].
    + intros _. eapply hull_sub; [exact Hshull | lia | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy & Hfr & Hpr2).
apply (HK regs2 mem2 md2); [|exact HP2].
apply (tobs_m_step B LAWS c regsT memT mdT Tc regs2 mem2 md2 _ HP HM HJ2).
- intros a Ha Ht Hw. apply Hfr; [exact Ha | lia | rewrite Hes; lia].
- exact Hpr2.
- apply (tn_garr8_upd (w_H (tW c)) memT mem2 (tt c) Tc (DTC.sub (tG c) 0 6) (48 * r) HT);
  rewrite ?length_sub_le, ?HTl; try lia.
  + intros i Hi Hni. apply Hfr; [lia | lia | rewrite Hes; lia].
  + intros i Hi. exists (nth (Z.to_nat i) (tG c) (Z_to_bv 8 0)). split.
    * rewrite nth_error_sub by lia. apply nth_error_nth'. lia.
    * rewrite (Hcpy i ltac:(lia)).
      pose proof (aview_of_garr8 (w_H (tW c)) memT (ts c) (tG c) (Z.to_nat i) HG ltac:(lia)) as Hv.
      rewrite Z2Nat.id in Hv by lia. exact Hv.
- rewrite RDO.upd_len; rewrite ?length_sub_le; lia.
- intros q Hq. apply HP2. unfold acallee_saved. cbn in Hq. lia.
Qed.
Definition NewB (c : tctx) : Prop :=
  forall regs1 m1 md1, tpre B c -> tobs_m B c regs1 m1 md1 (tTz c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * DTC.n_of (tT c)) ->
  tnone c -> 0 <= DTC.n_of (tT c) < 8 ->
  SRr SEGS (tW c) (cfgB 0x5420 regs1 m1 md1) (tpost B c).
Definition NewC (c : tctx) : Prop :=
  forall regs1 m1 md1, tpre B c -> tobs_m B c regs1 m1 md1 (tTm c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * DTC.n_of (tT c)) ->
  tnone c -> 0 <= DTC.n_of (tT c) < 8 ->
  SRr SEGS (tW c) (cfgB 0x5430 regs1 m1 md1) (tpost B c).
Lemma tn_new_c : forall c, SegSeq B c -> NewC c.
Proof.
intros c HK regs1 m1 md1 HP HM H18 H19 Hno Hn.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_Gl _ _ HP) as LG. pose proof (tp_ow _ _ HP) as How. pose proof (tp_now _ _ HP) as Hnow.
destruct (tn_lens c HP Hn) as (_ & _ & _ & Ln).
destruct (tn_ne_nat (tG c) (tow c) (tnow c) LG) as (N1 & N2 & N3 & N4 & N5).
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x ->
  ew (tobs_env c regs1 (tTm c) (DTC.n_of (tT c))) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
assert (B8 : base_val (tobs_env c regs1 (tTm c) (DTC.n_of (tT c))) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (EE 8%nat 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM). apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 (tTm c) (DTC.n_of (tT c))) (Some 19%nat) = tt c + 48 * DTC.n_of (tT c)).
{ cbn [base_val]. rewrite (EE 19%nat 19%bv eq_refl), H19. apply unsigned_lit_small. lia. }
pose proof (tobs_regs_ok c regs1 (tTm c) (DTC.n_of (tT c)) (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM)
  (tm_s6 _ _ _ _ _ _ HM) (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tTm c) (DTC.n_of (tT c))) as HEI.
destruct (tobs_enter B c regs1 m1 md1 (tTm c) 0x5430 true (DTC.n_of (tT c)) 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) (fun _ => conj Hn H19)) as [HS SHOK].
unfold cfgB.
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55d0.
{ exact (tobs_awr B c _ true 0 (DTC.n_of (tT c)) HP B8 (fun _ => conj B19 Hn)). }
pmkst HS.
prreg HS (10%bv : bv 5) QA0. prreg HS (18%bv : bv 5) P18.
rewrite (EE 18%nat 18%bv eq_refl), H18 in P18.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg1. cbn [ms_mem restrict] in Hreg1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as Hreg2. cbn [ms_mem restrict] in Hreg2.
lazymatch type of Hreg2 with region_ok _ ?Ex _ _ =>
  assert (ED : forall d, ed Ex d = tobs_data c (tTm c) (DTC.n_of (tT c)) d) by (intros d; reflexivity);
  assert (EW : forall k, (k < 512)%nat -> ew Ex k = ew (tobs_env c regs1 (tTm c) (DTC.n_of (tT c))) k)
    by (intros k Hk; rewrite !ew_ewset_other by lia; reflexivity);
  assert (B8' : base_val Ex (Some 8%nat) = tt c) by (cbn [base_val]; rewrite EW by lia; exact B8);
  assert (B19' : base_val Ex (Some 19%nat) = tt c + 48 * DTC.n_of (tT c)) by (cbn [base_val]; rewrite EW by lia; exact B19)
end.
assert (RB1 : forall i, 384 <= i < 400 -> mbyte SEGS (mrestrict (w_H (tW c)) (ms_mem ms)) (tt c + i) =
  nth_error (DTC.sub (tTm c) 384 16) (Z.to_nat (i - 384))).
{ apply (region_bytes _ _ _ _ _ _ _ _ (tt c) (DTC.sub (tTm c) 384 16) Hreg1 B8' ltac:(vm_compute; reflexivity)).
  apply Forall_cons; [|apply Forall_nil]. apply cagree_cdata; [lia|]. intros k Hk. rewrite ED. cbn [tobs_data].
  rewrite nth_error_sub by lia. f_equal. lia. }
assert (RB2 : forall k, 0 <= k < 48 ->
  mbyte SEGS (mrestrict (w_H (tW c)) (ms_mem ms)) (tt c + 48 * DTC.n_of (tT c) + k) =
  nth_error (RDOC.new_entry (tG c) (tow c) (tnow c)) (Z.to_nat (k - 0))).
{ apply (region_bytes _ _ _ _ _ _ _ _ (tt c + 48 * DTC.n_of (tT c)) (RDOC.new_entry (tG c) (tow c) (tnow c)) Hreg2 B19'
    ltac:(vm_compute; reflexivity)).
  repeat apply Forall_cons.
  all: first
  [ apply Forall_nil
  | apply tn_cagree_sext4;
    [ lia | rewrite ED; cbn [tobs_data]; lia
    | intros j Hj; rewrite ED; cbn [tobs_data]; rewrite Z.sub_0_r; symmetry; apply N1; lia ]
  | apply (tn_cagree_sdata _ _ _ _ _ _ _ 1%nat);
    [ lia | rewrite ED; cbn [tobs_data]; lia | lia
    | intros j Hj; rewrite ED; cbn [tobs_data]; rewrite Z.sub_0_r; symmetry; apply N1; lia ]
  | apply (tn_cagree_lit _ _ _ _ _ 8 _ (tnow c));
    [ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite EW by lia;
      rewrite (EE 20%nat 20%bv eq_refl), (tm_s4 _ _ _ _ _ _ HM); reflexivity
    | lia
    | intros j Hj; rewrite Z.sub_0_r;
      first [ rewrite <- (N4 (Z.to_nat j)) by lia; f_equal; lia
            | rewrite <- (N5 (Z.to_nat j)) by lia; f_equal; lia ] ]
  | apply (tn_cagree_lit _ _ _ _ _ 4 _ (if tow c =? 0 then 0 else 1));
    [ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite EW by lia;
      rewrite (EE 9%nat 9%bv eq_refl), (tm_s1 _ _ _ _ _ _ HM); unfold w64; apply tn_snez; exact How
    | destruct (tow c =? 0); lia
    | intros j Hj; rewrite Z.sub_0_r; rewrite <- (N3 (Z.to_nat j)) by lia; f_equal; lia ]
  | apply cagree_cdata; [lia|]; intros k Hk; rewrite ED; cbn [tobs_data]; rewrite Z.sub_0_r;
    apply (tn_ent_agree c HP Hn); lia ]. }
assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tTn c)).
{ apply (tobs_exit_run B LAWS c regs1 m1 md1 (tTm c) (tobs_env c regs1 (tTm c) (DTC.n_of (tT c))) true 0
    (DTC.n_of (tT c)) (ms_regs ms) (ms_mem ms) _ (tTn c) HP HM B8 (fun _ => conj B19 Hn) HFr HG HJ Ln).
  - intros i Hi Hh He. destruct (tn_out c HP Hn i Hi (He eq_refl)) as (_ & E1 & E2). rewrite E2, E1. reflexivity.
  - intros i Hi. rewrite (RB1 i Hi), nth_error_sub by lia.
    replace (Z.to_nat 384 + Z.to_nat (i - 384))%nat with (Z.to_nat i) by lia.
    destruct (tn_out c HP Hn i ltac:(lia) ltac:(lia)) as (_ & E1 & E2). rewrite E1, E2. reflexivity.
  - intros _ i Hi.
    replace (tt c + i) with (tt c + 48 * DTC.n_of (tT c) + (i - 48 * DTC.n_of (tT c))) by lia.
    rewrite (RB2 (i - 48 * DTC.n_of (tT c)) ltac:(lia)).
    replace (i - 48 * DTC.n_of (tT c) - 0) with (i - 48 * DTC.n_of (tT c)) by lia.
    rewrite <- (tn_ent_n c HP Hn (i - 48 * DTC.n_of (tT c)) ltac:(lia)). f_equal. lia.
  - intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq];
      [ eapply (tobs_reg_same c regs1 (tTm c) (DTC.n_of (tT c)) _ _ _ _ _ HS HR0);
        [ vm_compute; reflexivity | vm_compute; reflexivity
        | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]).
    destruct Hq. }
apply (HK (ms_regs ms) (ms_mem ms) _ (tTn c) 0 1 HP HM2 ltac:(left; reflexivity)).
- rewrite P18. f_equal. lia.
- exact QA0.
- exact (tn_model c HP Hno ltac:(lia)).
Qed.
Lemma tn_new_b : forall c, NewC c -> NewB c.
Proof.
intros c HNC regs1 m1 md1 HP HM H18 H19 Hno Hn.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (tobs_env c regs1 (tTz c) 0) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
assert (B8 : base_val (tobs_env c regs1 (tTz c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (EE 8%nat 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM). apply unsigned_lit_small. lia. }
pose proof (tobs_regs_ok c regs1 (tTz c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tTz c) 0) as HEI.
destruct (tobs_enter B c regs1 m1 md1 (tTz c) 0x5420 false 0 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
paj_run_tok RUN HS HJ SHOK TBspan.
{ exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
pmkst HS.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2. prreg HS (1%bv : bv 5) QRA.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
rewrite (EE 18%nat 18%bv eq_refl), H18 in P18, QA1. rewrite (EE 19%nat 19%bv eq_refl), H19 in P19, QA0.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tTz c)).
{ apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tTz c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity)
    HFr HG HJ Hreg B8 eq_refl).
  intros q Hq. cbn in Hq.
  repeat (destruct Hq as [<- | Hq];
    [ eapply (tobs_reg_same c regs1 (tTz c) 0 _ _ _ _ _ HS HR0);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]).
  destruct Hq. }
eapply (tn_memcpy c (ms_regs ms) (ms_mem ms) _ (tTz c) (DTC.n_of (tT c)) 0x5430 (tpost B c) HP HM2 Hn).
- exact QA0.
- exact QA1.
- exact QA2.
- exact QRA.
- lia.
- reflexivity.
- intros regs2 mem2 md2 HM3 HP2.
  apply (HNC regs2 mem2 md2 HP HM3).
  + etransitivity; [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18].
  + etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19].
  + exact Hno.
  + exact Hn.
Qed.
Lemma tn_new_a : forall c, NewB c -> SegNew B c.
Proof.
intros c HNB regs1 m1 md1 HP HM H18 H23 Hno Hn8.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
assert (Hn : 0 <= DTC.n_of (tT c) < 8) by lia.
destruct (tn_lens c HP Hn) as (Lh & _ & _ & _).
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (tobs_env c regs1 (tT c) 0) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
assert (B8 : base_val (tobs_env c regs1 (tT c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (EE 8%nat 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM). apply unsigned_lit_small. lia. }
pose proof (tobs_regs_ok c regs1 (tT c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tT c) 0) as HEI.
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x53f0 false 0 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
paj_run_tok RUN HS HJ SHOK TBspan.
{ exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
pmkst HS.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2. prreg HS (1%bv : bv 5) QRA.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
rewrite (EE 18%nat 18%bv eq_refl), H18 in P18.
rewrite (EE 8%nat 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM), (EE 23%nat 23%bv eq_refl), H23 in QA0, P19.
unfold w64 in QA0, P19. rewrite tn_s3 in QA0, P19 by lia.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
assert (RB : forall i, 384 <= i < 400 -> mbyte SEGS (mrestrict (w_H (tW c)) (ms_mem ms)) (tt c + i) =
  nth_error (DTC.sub (tTh c) 384 16) (Z.to_nat (i - 384))).
{ apply (region_bytes _ _ _ _ _ _ _ _ (tt c) (DTC.sub (tTh c) 384 16) Hreg B8 ltac:(vm_compute; reflexivity)).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (tn_cagree_lit _ _ _ _ 384 4 (SOff 23 1) (DTC.n_of (tT c) + 1)); [| lia |].
    + cbn [sv_denot]. rewrite (EE 23%nat 23%bv eq_refl), H23. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + intros j Hj. rewrite nth_error_sub by lia.
      replace (Z.to_nat 384 + Z.to_nat (384 + j - 384))%nat with (Z.to_nat (384 + j)) by lia.
      rewrite (tn_th_in c HP j ltac:(lia)). reflexivity.
  - apply cagree_cdata; [lia|]. intros k Hk. rewrite tobs_env_ed. cbn [tobs_data].
    rewrite nth_error_sub by lia.
    replace (Z.to_nat 384 + Z.to_nat (388 + k - 384))%nat with (Z.to_nat (388 + k)) by lia.
    rewrite (tn_th_out c HP (388 + k) ltac:(lia) ltac:(lia)). reflexivity. }
assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tTh c)).
{ apply (tobs_exit_run B LAWS c regs1 m1 md1 (tT c) (tobs_env c regs1 (tT c) 0) false 0 0 (ms_regs ms) (ms_mem ms) _
    (tTh c) HP HM B8 ltac:(discriminate) HFr HG HJ Lh).
  - intros i Hi Hh _. exact (tn_th_out c HP i Hi ltac:(lia)).
  - intros i Hi. rewrite (RB i Hi), nth_error_sub by lia. f_equal. lia.
  - discriminate.
  - intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq];
      [ eapply (tobs_reg_same c regs1 (tT c) 0 _ _ _ _ _ HS HR0);
        [ vm_compute; reflexivity | vm_compute; reflexivity
        | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]).
    destruct Hq. }
eapply (tn_memset c (ms_regs ms) (ms_mem ms) _ (tTh c) (DTC.n_of (tT c)) 0x5420 (tpost B c) HP HM2 Hn).
- exact QA0.
- exact QA1.
- exact QA2.
- exact QRA.
- lia.
- reflexivity.
- intros regs2 mem2 md2 HM3 HP2.
  apply (HNB regs2 mem2 md2 HP HM3).
  + etransitivity; [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18].
  + etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19].
  + exact Hno.
  + exact Hn.
Qed.
Lemma seg_new : forall c, SegSeq B c -> SegNew B c.
Proof. intros c H. exact (tn_new_a c (tn_new_b c (tn_new_c c H))). Qed.
End h.
End f.
End d.
