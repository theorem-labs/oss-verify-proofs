(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnARiK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0198. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0204. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0281. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKOwner OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKUarF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKUarF2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKFamA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189.PnARel3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunNF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunA1N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnARiK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0198.PnARiPH OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0204.PnARiPX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0198.PnARiPU8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rc3a10_c3a14 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKOwnerT OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0281.PnARi1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0281.PnARiTS.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef Utf8Facts. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQARIT8.
Import L5A L5SAR. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation mown := PNRNA.mown.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation ec_stateA := (NEMA.ec_stateA RSEGS AD).
Abbreviation bvu x := (bv_unsigned x).
Abbreviation Sh a := (a / 8 + 2147450880).

(* [comment removed for export] *)
Ltac fdP P := L5SAR.feed P ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_lt1_eq (a b : Z) : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (a - b) mod 2 ^ 64 < 1 -> a = b.
Proof.
  intros Ha Hb H. destruct (Z_lt_le_dec a b) as [LT|GE].
  - rewrite <- (Z.mod_add (a - b) 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma getr_self (R : bvmap 5 word) i : getr R i = Z_to_bv 64 (bv_unsigned (getr R i)).
Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* [comment removed for export] *)
Lemma aacc_join (M : mem) p n m : aacc M p n -> aacc M (p + n) m -> 0 <= n -> aacc M p (n + m).
Proof. intros A B Hn a Ha. destruct (Z_lt_le_dec a (p + n)) as [X|X]; [apply A; lia| apply B; lia]. Qed.
Lemma defined_grows' (M M' : mem) p k : L5.defined M p k -> mem_grows M M' -> L5.defined M' p k.
Proof. intros D MG i Hi. apply MG. apply D. exact Hi. Qed.
(* [comment removed for export] *)
Lemma b64len_3 n : 0 <= n -> 0 <= PNVA.b64len n /\ 3 * PNVA.b64len n <= 4 * n + 2.
Proof. intros Hn. unfold PNVA.b64len, PNV.b64len. split; [apply Z.div_pos; lia|]. apply (Z.mul_div_le (4 * n + 2) 3). lia. Qed.
(* [comment removed for export] *)
Lemma zbv_add_eq (a b c : Z) : Z_to_bv 64 a = Z_to_bv 64 b -> Z_to_bv 64 (a + c) = Z_to_bv 64 (b + c).
Proof.
  intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64) in *.
  rewrite <- (Zplus_mod_idemp_l a), <- (Zplus_mod_idemp_l b). rewrite E. reflexivity.
Qed.
Lemma wtlb8_inj (w w' : word) : word_to_le_bytes 8 w = word_to_le_bytes 8 w' -> w = w'.
Proof.
  intros X. apply (f_equal bytes_le_to_Z) in X. unfold word_to_le_bytes in X.
  pose proof (bv_unsigned_in_range 64 w) as B. pose proof (bv_unsigned_in_range 64 w') as B'. change (bv_modulus 64) with (2 ^ 64) in B, B'.
  rewrite !bytes_le_to_Z_of_le_bytes in X by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in X.
  rewrite !Z.mod_small in X by lia. apply bv_eq. exact X.
Qed.
Lemma u64_at_det (M : mem) a a' v v' : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M a' v' -> Z_to_bv 64 a = Z_to_bv 64 a' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
  unfold L5.u64_at. intros U U' E Hv Hv'. rewrite <- E in U'. rewrite U in U'.
  assert (X : word_to_le_bytes 8 (Z_to_bv 64 v) = word_to_le_bytes 8 (Z_to_bv 64 v')) by congruence.
  apply wtlb8_inj in X. apply (f_equal bv_unsigned) in X. rewrite !L5.unsigned_lit in X by lia. exact X.
Qed.
(* [comment removed for export] *)
Lemma sec_rng (w : Z) : 0 <= w -> 0 <= (1073741824 * w) mod 2 ^ 64 / 1073741824 < 17179869184.
Proof.
  intros Hw. pose proof (Z.mod_pos_bound (1073741824 * w) (2 ^ 64) ltac:(lia)) as (B1 & B2).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64) with (1073741824 * 17179869184) in B2. lia.
Qed.
Lemma nsec_rng (w : Z) : 0 <= w < 2 ^ 64 -> 0 <= w / 17179869184 < 1073741824.
Proof. intros Hw. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64) with (17179869184 * 1073741824) in Hw. lia. Qed.
(* [comment removed for export] *)
Lemma mul_one_limb (sec lo hi : Z) : 0 <= sec < 17179869184 -> 0 <= lo < 2 ^ 64 -> 0 <= hi -> lo + 2 ^ 64 * hi = sec * 1000000000 -> hi = 0 /\ lo = sec * 1000000000.
Proof. intros Hs Hlo Hhi E. assert (hi = 0) by Lia.nia. subst hi. Lia.lia. Qed.
(* [comment removed for export] *)
Lemma zeros4 (Mx : mem) a : L5.u8_at RSEGS Mx a 0 -> L5.u8_at RSEGS Mx (a + 1) 0 -> L5.u8_at RSEGS Mx (a + 2) 0 -> L5.u8_at RSEGS Mx (a + 3) 0 ->
  7036928 <= a -> a + 4 <= 2 ^ 64 -> L5KA.zeros_at Mx a 4.
Proof.
  intros U0 U1 U2 U3 Ha Ha' i Hi. assert (X : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct X as [->|[->|[->| ->]]];
    [rewrite Z.add_0_r; apply (L5ADHR.byte_of_u8 Mx _ 0 U0); lia| apply (L5ADHR.byte_of_u8 Mx _ 0 U1); lia| apply (L5ADHR.byte_of_u8 Mx _ 0 U2); lia| apply (L5ADHR.byte_of_u8 Mx _ 0 U3); lia].
Qed.
Lemma zeros2 (Mx : mem) a : L5.u8_at RSEGS Mx a 0 -> L5.u8_at RSEGS Mx (a + 1) 0 -> 7036928 <= a -> a + 2 <= 2 ^ 64 -> L5KA.zeros_at Mx a 2.
Proof.
  intros U0 U1 Ha Ha' i Hi. assert (X : i = 0 \/ i = 1) by lia.
  destruct X as [->| ->]; [rewrite Z.add_0_r; apply (L5ADHR.byte_of_u8 Mx _ 0 U0); lia| apply (L5ADHR.byte_of_u8 Mx _ 0 U1); lia].
Qed.
(* [comment removed for export] *)
Lemma binl_keep (Mx My : mem) o fb0 len v0 v1 :
  PQATSS.binl_at RSEGS Mx o fb0 len v0 v1 -> (forall i, o <= i < o + 32 -> My (Z_to_bv 64 i) = Mx (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  PQATSS.binl_at RSEGS My o fb0 len v0 v1.
Proof.
  intros ((U0 & R0 & U8 & TB & U16 & U24 & LEN & RV) & RV0 & RV1) AG Ho Ho'.
  assert (AGo : L5C.agree_on Mx My o 32) by (intros i Hi; apply AG; exact Hi).
  split; [| split; [exact RV0| exact RV1]]. unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
  split; [apply (L5C.u8_at_agree RSEGS Mx My); [eapply (L5C.agree_on_sub Mx My); [exact AGo| lia| lia]| lia| lia| exact U0]|].
  split; [exact R0|].
  split; [apply (L5C.u64_at_agree RSEGS Mx My); [eapply (L5C.agree_on_sub Mx My); [exact AGo| lia| lia]| lia| lia| exact U8]|].
  split; [exact TB|].
  split; [apply (L5C.u64_at_agree RSEGS Mx My); [eapply (L5C.agree_on_sub Mx My); [exact AGo| lia| lia]| lia| lia| exact U16]|].
  split; [apply (L5C.u64_at_agree RSEGS Mx My); [eapply (L5C.agree_on_sub Mx My); [exact AGo| lia| lia]| lia| lia| exact U24]|].
  exact (conj LEN RV).
Qed.
(* [comment removed for export] *)
Lemma odd_mod256 c : 0 <= c -> c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc He. apply Z.testbit_true; [lia|]. change (2 ^ 0) with 1. rewrite Z.div_1_r.
  rewrite <- (Znumtheory.Zmod_div_mod 2 256 (c + 1)); [| lia| lia| exists 128; reflexivity].
  rewrite Z.add_mod, He by lia. reflexivity.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (HIk : list (list Z) -> asan_iface)
          (tsp : list (list Z) -> list Z -> credit) (TSRESA : credit).
Hypothesis LY : PMA.layout L C.
Hypothesis FAMok : HAR.asan_famR_ok L ar C SCFG LR HIk.
Hypothesis ICokF : forall D, aicpt_ok L ar IL SCFG (HIk D).
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis TSPB : forall D RC, PMSP.credit_le PMSP.cr0 (tsp D RC) /\ PMSP.credit_le (tsp D RC) TSRESA.
(* [comment removed for export] *)
Variable tspV : Z -> list (list Z) -> list Z -> credit.      (* [comment removed for export] *)
Hypothesis VSTRF : PNVA.v_string_specF RSEGS AD AQ AAD AE L ar HIk tspV.
Hypothesis TSP_V : forall t D RC RCv, PMSP.credit_le (tspV t D RCv) (tsp D RC)
                   /\ (forall D', incl D D' -> PMSP.credit_le (PM.credit_add (tsp D' RC) (tspV t D RCv)) (PM.credit_add (tsp D RC) (tspV t D' RCv))).
                   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis MULU : forall D, PQATSSa.mulu_spec L ar (HIk D).
Hypothesis ADD64 : forall D, PQATSSa.add64_spec L ar (HIk D).
Hypothesis WS1 : forall D, PQATSSa.ws1_spec L ar (HIk D).
Let LYa := PMA.ly_as0 L C LY.
Let HIokF (D : list (list Z)) := HAR.fr_base L ar C SCFG LR HIk FAMok D.
Local Notation mrun_pre := (PNRNA.mrun_pre RSEGS AD AQ AAD AE L ar).
Local Notation mrun_fin := (PNRNA.mrun_fin RSEGS AD AQ AAD AE L ar).
Local Notation pot_runA := (PNRNA.pot_runA L ar).
Local Notation ae_atA := (NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ)).

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r fb cat n : Z) (D0 : list (list Z)) (s : PQMA.mpst) (sa : NEMA.aest) (str : PM.vstr) (sm : PM.strm) (e eb : bool) (RC0 : list Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 160).
Local Notation op := (fb + 592).
Local Notation oa := (fb + 992).
Local Notation oec := (fb + 1232).
Local Notation ois := (fb + 96).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv (HIk D0) (mown s sa ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 10.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM 10 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PQRA.frame_okM FF fb.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 op.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 oa.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 oec.
Hypothesis RPRE : PNRNA.mrun_pre RSEGS AD AQ AAD AE L ar M fb s sa str sm e eb cat n.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis RCH0 : HAR.rchain L ar M sp (bv_unsigned (getr R (reg 8))) RC0.
Hypothesis ROOM0 : PQRA.bb_room s sm.
Hypothesis INV0 : PQRA.minv_d 0 s.
Hypothesis CRED0 : PMSP.credit_le (PM.credit_add (PM.credit_add (PNRNA.pot_runA L ar s sa) (PMSPA.scA L PNRNA.TSRES_ME)) (tsp D0 RC0)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PQMA.mpst) (st' : NEMA.aest) (sm' : PM.strm) (e' b' : bool) (cr' : credit) (D' : list (list Z)),
    regs_preserved R R' ->
    PNRNA.mrun_post_d RSEGS AD AQ AAD AE L ar 0 PNRNA.mprog_item R' M' fb s s' sa st' str sm sm' e e' eb b' cat n ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 10) (PNRNA.W_mrun AD AQ AE fb) M M' ->
    PMSP.credit_keep cr cr' (PM.credit_add (PNRNA.pot_runA L ar s sa) (tsp D0 RC0)) (PM.credit_add (PNRNA.pot_runA L ar s' st') (tsp D' RC0)) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> incl D0 D' ->
    ri_inv (HIk D') (mown s' st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Lemma sp_facts : 140735332487168 + 176 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof. exact (PQARI1.sp_facts L ar R M V2 cls r Hcls ENT). Qed.
Lemma HSPC : sp - 176 <= spc /\ spc + 160 <= sp /\ spc mod 32 = 0.
Proof. exact (PQARI1.HSPC V2 cls Hcls V32). Qed.
Lemma HOC16 : forall a, sp - 16 <= a < sp -> PQARI1.ocell sp a.
Proof. exact (PQARI1.HOC16 V2 cls). Qed.
Lemma HSPC1 : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof. exact (PQARI1.HSPC1 V2 cls Hcls V32). Qed.
Lemma LCL : hl_b_lin L = 3.
Proof. exact (PQARI1.LCL L C LY). Qed.

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Local Notation OWN := (PQARI1.own sp R).
Local Notation OC := (PQARI1.ocell sp).
Hypothesis G : PQAKUF.gctx L ar HIk D0 LBX FF LK Aw sp (PMSPA.pm_scr 10) spc spc sp OC OWN F fl 4 LK2 M2 model2 cr (mown s sa).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (mown s sa ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 4 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 4 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).

Local Notation MM := (PQARIK.ri_mem L ar HIk D0 M model LBX FF LK Aw sp fb cat s str sm e eb spc OWN F).
Local Notation RIC := (PQARIK.ric L cr (PNRNA.pot_runA L ar s sa) (tsp D0 RC0)).
Local Notation REGS := (PQARI1.REGS R V2 cls fb F).
Local Notation FF' := ((F, 4, spc + 32) :: FF).
Local Notation AT := (PQARI1.AT L ar HIk tsp R M model LBX FF LK Aw cr V2 cls fb cat D0 s sa str sm e eb RC0 F).

Ltac kitp lem H := pose proof (lem L ar C IL LR HIk D0 tsp TSRESA LY FAMok ICokF ILY TSPB K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e eb HH AM K0 ENT FRM FRS FOK RPRE INCS
                              RC0 RCH0 ROOM0 INV0 CRED0 KONT spc OC OWN F fl LK2 M2 model2 G APART HSPC HOC16) as H.
(* [comment removed for export] *)
Ltac p1 lem H := pose proof (lem L ar C IL LR HIk tsp TSRESA LY FAMok ICokF ILY TSPB K R M model LBX FF LK Aw cr V2 cls r fb cat n D0 s sa str sm e eb RC0 Hcls V32 HH AM K0 ENT FRM FRS FOK A10 A11 A12 RPRE INCS
                            RCH0 ROOM0 INV0 CRED0 KONT F fl LK2 M2 model2 G APART) as H.
Ltac regsK KS Q := apply (PQARI1.REGS_of R V2 cls fb F _ _ Q); intros j__ Hj__; apply KS; unfold PQARI1.RL in Hj__; repeat (destruct Hj__ as [<-|Hj__]; [inl|]); destruct Hj__.

(* [comment removed for export] *)
Ltac tailp CONC LM Q fxv Rv Mv Awv modelv :=
  let TF := fresh "TF" in
  pose proof (@PQARI1.tail_facts _ L ar C IL LR HIk tsp TSRESA LY FAMok ICokF ILY TSPB K R M model LBX FF LK Aw cr V2 cls r fb cat n D0 s sa str sm e eb RC0 Hcls V32 HH AM K0 ENT FRM FRS FOK A10 A11 A12 RPRE INCS RCH0 ROOM0 INV0 CRED0 KONT F fl LK2 M2 model2 G APART _ _ _ _ _ _ _ _ _ _ _ _ LM) as TF; cbn zeta in TF;
  destruct TF as (tZ16 & tZ8 & tCUR & tW8 & (tOP1 & tOP8 & tOPB) & (tF1 & tF32 & tFB & tFSW & tDF) & tSHA & (tSP & tFSP & tFBSP));
  pose proof Q as (tQ2 & tQ8 & tQ9 & tQ18 & tQ19 & tQ20 & tQ21 & tQ22 & tQ26 & tQ27 & tQK);
  pose proof (LF2CBN( CONC fxv Rv (mrestrict (ahid Awv modelv) Mv) (fun j => match j with 2%nat => V2 | 33%nat => fb + 592 | 34%nat => fb + 1232 | 36%nat => fb + 992 | 50%nat => F | _ => 0 end) )) as P; fdP P.

(* [comment removed for export] *)
Lemma ts_ascii bs : Forall (fun b => b = 45 \/ 48 <= b <= 57) bs -> utf8_valid bs = true /\ NEM.bytes_ok bs.
Proof.
  induction bs as [|b0 tl IH]; intros FA.
  - split; [apply UTF8F.utf8_valid_nil| constructor].
  - inversion FA as [|b' t' Hb Ht]; subst. destruct (IH Ht) as (V & OK). split; [| constructor; [lia| exact OK]].
    rewrite UTF8F.utf8_valid_cons. pose proof (UTF8F.utf8_trail_spec b0) as (T0 & _). rewrite T0 by lia.
    change (Z.to_nat (0 + 1)) with 1%nat. cbv zeta. change (length (b0 :: tl) <? 1)%nat with false. change (firstn 1 (b0 :: tl)) with [b0]. change (skipn 1 (b0 :: tl)) with tl.
    rewrite V. replace (utf8_legal [b0]) with true; [reflexivity|]. symmetry. apply (proj2 (UTF8F.legal1_iff b0)). unfold UTF8F.lead_ok. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma view_len_eq (Rx : bvmap 5 word) (Mx : mem) (p k k' : Z) :
  getr Rx (reg 11) = Z_to_bv 64 p -> L5.u64_at RSEGS Mx (p + 8) k -> 0 <= k < 2 ^ 26 -> PNVA.view_len RSEGS Rx Mx k' -> k' = k.
Proof.
  intros X11 U Hk (p' & E11 & U' & Hk'). rewrite L5K.rl11, X11 in E11.
  apply (u64_at_det Mx (p' + 8) (p + 8) k' k U' U); [apply zbv_add_eq; symmetry; exact E11| clear - Hk'; lia| clear - Hk; lia].
Qed.

(* [comment removed for export] *)
Definition PREm (x : Z * nat * Z) (Rx : bvmap 5 word) (Mx : mem) (o : Z) : Prop :=
  match x with (fb0, len, v0) =>
    getr Rx (reg 11) = Z_to_bv 64 PQATSS.NANOS /\ PQATSS.binl_at RSEGS Mx o fb0 len v0 0 /\ (len <= 1)%nat /\ (len = 0%nat -> v0 = 0) end.
Definition POSTm (x : Z * nat * Z) (Rx : bvmap 5 word) (Mx : mem) (o : Z) : Prop :=
  match x with (fb0, len, v0) =>
    getr Rx (reg 10) = Z_to_bv 64 o /\ exists lo hi, lo + 2 ^ 64 * hi = v0 * PQATSS.NANOS /\ PQATSS.binl_at RSEGS Mx o (PQATSS.wfb fb0 lo hi) (PQATSS.wlen lo hi) lo hi end.
Lemma mulu_fobj D : PQARIK.fobj_spec L ar (HIk D) PQATSS.MULU_A PQATSS.MULU_H PREm POSTm.
Proof.
  intros [[fb0 len] v0] fx R0 M0 model0 K0' LB FF0 LK0 Aw0 cr0 sp0 r0 o HH0 AM0 HK ENT0 FRM0 FRS0 SP16 X10 AO OM ACC (X11 & BINL & LEN & LEN0) BASE KK.
  pose proof (MULU D) as MU. unfold PQATSSa.mulu_spec, PQATSS.mulu_specG in MU.
  apply (MU fx R0 M0 model0 K0' LB FF0 LK0 Aw0 cr0 sp0 r0 o fb0 len v0 HH0 AM0 HK ENT0 FRM0 FRS0 SP16 X10 X11 AO OM ACC BINL LEN LEN0 BASE).
  intros fx' R' M' model' LK' lo hi RP Y10 EQ BINL' HP MRT INCL AM' HH'.
  apply (KK fx' R' M' model' LK' RP); [| exact HP| exact MRT| exact INCL| exact AM'| exact HH'].
  split; [exact Y10|]. exists lo, hi. split; [exact EQ| exact BINL'].
Qed.
Definition PREa (x : Z * Z * nat * Z) (Rx : bvmap 5 word) (Mx : mem) (o : Z) : Prop :=
  match x with (y, fb0, len, v0) =>
    getr Rx (reg 11) = Z_to_bv 64 y /\ 0 <= y /\ v0 + y < 2 ^ 64 /\ PQATSS.binl_at RSEGS Mx o fb0 len v0 0 /\ (len <= 1)%nat /\ (len = 0%nat -> v0 = 0)
    /\ Z.testbit fb0 1 = false end.
Definition POSTa (x : Z * Z * nat * Z) (Rx : bvmap 5 word) (Mx : mem) (o : Z) : Prop :=
  match x with (y, fb0, len, v0) => getr Rx (reg 10) = Z_to_bv 64 o /\ PQATSS.binl_at RSEGS Mx o fb0 (PQATSS.wlen (v0 + y) 0) (v0 + y) 0 end.
Lemma add64_fobj D : PQARIK.fobj_spec L ar (HIk D) PQATSS.ADDU64_A PQATSS.ADD_H PREa POSTa.
Proof.
  intros [[[y fb0] len] v0] fx R0 M0 model0 K0' LB FF0 LK0 Aw0 cr0 sp0 r0 o HH0 AM0 HK ENT0 FRM0 FRS0 SP16 X10 AO OM ACC (X11 & Hy & SUM & BINL & LEN & LEN0 & SGN) BASE KK.
  pose proof (ADD64 D) as AU. unfold PQATSSa.add64_spec, PQATSS.add64_specG in AU.
  apply (AU fx R0 M0 model0 K0' LB FF0 LK0 Aw0 cr0 sp0 r0 o y fb0 len v0 HH0 AM0 HK ENT0 FRM0 FRS0 SP16 X10 X11 Hy SUM AO OM ACC BINL LEN LEN0 SGN BASE).
  intros fx' R' M' model' LK' RP Y10 BINL' HP MRT INCL AM' HH'.
  apply (KK fx' R' M' model' LK' RP); [| exact HP| exact MRT| exact INCL| exact AM'| exact HH'].
  split; [exact Y10| exact BINL'].
Qed.

(* [comment removed for export] *)
Lemma TS8_arm (fx3 : FPState) (R3 : bvmap 5 word) (RC : list Z) (Dc : list (list Z)) (M3 : mem) (model3 : Model) (LK3 : list fframe) (Aw3 : list (Z * Z))
      (s3 : PQMA.mpst) (sm3 : PM.strm) (e3 : bool) (cr3 : credit) :
  PQARITS.ts_entry L ar HIk tsp K R M model LBX FF LK Aw cr V2 cls fb cat D0 s sa str sm e eb RC0 F 10 8 416 2147450932 R3 RC Dc M3 model3 LK3 Aw3 s3 sm3 e3 cr3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xd11a8 M3 model3) K.
Proof using All.
  intros (LM & Q & X10 & X23 & X24 & X25 & CPL3 & INV3 & STK3 & ROOMK3 & UN3 & UN0 & CR3 & SPL8 & SPL16 & SPL24 & ET255 & SH48 & DEF416 & SH52).
  pose proof Q as (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q26 & Q27 & QK).
  destruct sp_facts as (SP1 & SP2 & SP3 & Hr1 & Hr2). pose proof HSPC as (HS1 & HS2 & HS3). assert (CLS : 0 <= cls <= 16) by (destruct Hcls; lia).
  pose proof ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof RPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AOK0 & _ & ACCT0 & OACCT0 & EB0 & BAL0).
  (* [comment removed for export] *)
  kitp PQARIK.ri_pfacts PFX.
  destruct (PFX RC Dc M3 model3 LK3 Aw3 s3 sa sm3 e3 cr3 eb LM) as (IMG3 & (PF1 & PF2 & PF3 & PF4) & (FDF3 & FLW3 & FSW3 & _) & _ & (_ & _ & FSP3 & _) & (FB1 & FB2 & FB3 & FB4) & (ZOP3 & WOP3 & OVIS3 & _) & OFA3 & (AVSH3 & AVF3 & _)). clear PFX.
  change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
  assert (FR : 7036928 <= F <= 140737488354304) by (clear - PF1 PF2; lia).
  assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF9 : F / 8 <= 17592186044288) by (apply Z.div_le_upper_bound; lia).
  assert (F8 : F / 8 * 8 = F) by (pose proof (Z.div_mod F 8 ltac:(lia)) as X8; pose proof (PQARIK.mod16_8 _ (PQARIK.mod32_16 _ PF3)) as Y8; clear - X8 Y8; lia).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  assert (DEFv : L5.defined MV3 (F + 416) 8) by (apply (proj2 (L5A.defined_vis (ahid Aw3 model3) M3 (F + 416) 8 (L5A.avis_sub _ _ _ (F + 416) 8 AVF3 ltac:(lia) ltac:(lia)))); exact DEF416).
  LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8a0_conc fx3 R3 MV3 (fun j => match j with 2%nat => V2 | 50%nat => F | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y24 & Z59 & Z58 & Z57 & Z56).
  kitp PQARIK.ri_piece RP.
  apply (RP RC Dc M3 model3 LK3 Aw3 s3 sa sm3 e3 cr3 eb fx3 fx4 R3 R4 0xd11a8 0xd1224 M4v
           (fun a => F / 8 + 2147450880 + 56 <= a < F / 8 + 2147450880 + 56 + 4) LM MS4 MG4); clear RP.
  { intros a Ha N. apply FRZ4; [exact Ha| exact N]. }
  { intros a Wa; split; [unfold PQARI1.ocell; unfold PMSPA.pm_scr in FSP3; clear - Wa FSP3 PF1 SP1 CLS DF0; lia|].
    right; right; unfold SB; change (ff_bytes 4 / 8) with 128; clear - Wa; lia. }
  intros M4 model4 LM4 AH4 VIS4 FR4 MG4'.
  assert (Q4 : REGS R4) by (regsK KS4 Q). pose proof Q4 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P26 & P27 & PK).
  set (w := bvu (getr R4 (reg 23))).
  assert (Y23 : getr R4 (reg 23) = Z_to_bv 64 w) by (apply getr_self).
  assert (Hw : 0 <= w < 2 ^ 64) by (apply PQARIK.bvu_rng).
  assert (Hw' : 0 <= w <= 18446744073709551615) by (clear - Hw; lia).
  set (MV4 := mrestrict (ahid Aw3 model4) M4) in *.
  kitp PQARIK.ri_pfacts PFX.
  destruct (PFX RC Dc M4 model4 LK3 Aw3 s3 sa sm3 e3 cr3 eb LM4) as (_ & _ & (_ & FLW4 & _) & _ & _ & _ & _ & _ & (AVSH4 & AVF4 & _)). clear PFX.
  change (ff_bytes 4) with 1024 in FLW4, AVF4. change (1024 / 8) with 128 in AVSH4.
  assert (FLW448 : L5.writable RSEGS MV4 (F + 448) 32) by (apply (L5.writable_sub RSEGS MV4 F 1024); [exact FLW4| lia| lia]).
  LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8a_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 50%nat => F | 57%nat => w | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & U1 & U10 & U11 & C472 & C464 & C456 & C448).
  kitp PQARIK.ri_piece RP.
  apply (RP RC Dc M4 model4 LK3 Aw3 s3 sa sm3 e3 cr3 eb fx4 fx5 R4 R5 0xd1224 PQATSS.MULU_A M5v (fun a => F + 448 <= a < F + 448 + 32) LM4 MS5 MG5); clear RP.
  { intros a Ha N. apply FRZ5; [exact Ha| exact N]. }
  { intros a Wa; split; [unfold PQARI1.ocell; unfold PMSPA.pm_scr in FSP3; clear - Wa FSP3 PF1 SP1 CLS; lia|].
    right; left; change (ff_bytes 4) with 1024; clear - Wa; lia. }
  intros M5 model5 LM5 AH5 VIS5 FR5 MG5'.
  assert (Q5 : REGS R5) by (regsK KS5 Q4). pose proof Q5 as (W2 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W26 & W27 & WK).
  set (sec := (1073741824 * w) mod 2 ^ 64 / 1073741824) in *.
  pose proof (sec_rng w (proj1 Hw)) as Hsec.
  assert (AVF5 : avis (ahid Aw3 model4) F 1024) by (exact AVF4).
  assert (M448 : L5.u8_at RSEGS M5 (F + 448) 0).
  { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M5 (F + 448) 0 (L5A.avis_sub _ _ _ (F + 448) 1 AVF5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS5. exact C448. }
  assert (M456 : L5.u64_at RSEGS M5 (F + 456) (if 0 <? sec then 1 else 0)).
  { apply (proj1 (L5A.u64_at_vis (ahid Aw3 model4) M5 (F + 456) _ (L5A.avis_sub _ _ _ (F + 456) 8 AVF5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS5. exact C456. }
  assert (M464 : L5.u64_at RSEGS M5 (F + 464) sec).
  { apply (proj1 (L5A.u64_at_vis (ahid Aw3 model4) M5 (F + 464) _ (L5A.avis_sub _ _ _ (F + 464) 8 AVF5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS5. exact C464. }
  assert (M472 : L5.u64_at RSEGS M5 (F + 472) 0).
  { apply (proj1 (L5A.u64_at_vis (ahid Aw3 model4) M5 (F + 472) _ (L5A.avis_sub _ _ _ (F + 472) 8 AVF5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS5. exact C472. }
  assert (ZSH5 : L5KA.zeros_at M5 (F / 8 + 448 / 8 + 2147450880) 4).
  { change (448 / 8) with 56. apply (L5KA.zeros_at_agree1 M4 M5); [intros i Hi; apply FR5; [clear - Hi DF0 DF9; lia| clear - Hi DF0 FR PF4; lia]|].
    replace (F / 8 + 56 + 2147450880) with (F / 8 + 2147450880 + 56) by lia.
    apply (proj1 (L5A.zeros_at_vis (ahid Aw3 model3) M4 (F / 8 + 2147450880 + 56) 4 (L5A.avis_sub _ _ _ (F / 8 + 2147450880 + 56) 4 AVSH3 ltac:(unfold SB; lia) ltac:(unfold SB; lia)))).
    rewrite VIS4. apply (zeros4 M4v); [replace (F / 8 + 2147450880 + 56) with (F / 8 + 2147450936) by lia; exact Z56| replace (F / 8 + 2147450880 + 56 + 1) with (F / 8 + 2147450937) by lia; exact Z57
      | replace (F / 8 + 2147450880 + 56 + 2) with (F / 8 + 2147450938) by lia; exact Z58| replace (F / 8 + 2147450880 + 56 + 3) with (F / 8 + 2147450939) by lia; exact Z59| lia| lia]. }
  set (len0 := if 0 <? sec then 1%nat else 0%nat).
  assert (BINL5 : PQATSS.binl_at RSEGS M5 (F + 448) 0 len0 sec 0).
  { unfold PQATSS.binl_at, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    split; [| clear - Hsec; lia]. split; [exact M448|]. split; [lia|].
    split; [replace (F + 448 + 8) with (F + 456) by lia; unfold len0; destruct (0 <? sec); exact M456|].
    split; [reflexivity|]. split; [replace (F + 448 + 16) with (F + 464) by lia; exact M464|]. split; [replace (F + 448 + 24) with (F + 472) by lia; exact M472|].
    split; [unfold len0; destruct (0 <? sec); cbn; lia| clear - Hsec; lia]. }
  (* [comment removed for export] *)
  kitp PQARIK.ri_call_fobj CF.
  apply (CF _ PREm POSTm (0, len0, sec) RC Dc M5 model5 LK3 Aw3 s3 sa sm3 e3 cr3 eb fx5 R5 PQATSS.MULU_A PQATSS.MULU_H 0xd1250 448 (mulu_fobj Dc) ltac:(unfold PQATSS.MULU_H; lia) LM5 U1
           ltac:(split; [lia| reflexivity]) ltac:(rewrite (KS5 2%nat) by inl; exact P2) ltac:(rewrite (KS5 3%nat) by inl; exact (eq_trans (PK 3%nat ltac:(inl)) Rgp))
           ltac:(rewrite (KS5 4%nat) by inl; exact (eq_trans (PK 4%nat ltac:(inl)) Rtp)) U10 ltac:(lia) ltac:(change (ff_bytes 4) with 1024; lia) eq_refl ZSH5); clear CF.
  { cbn. split; [exact U11|]. split; [exact BINL5|]. split; [unfold len0; destruct (0 <? sec); lia|]. unfold len0. destruct (0 <? sec) eqn:E0; [intros X; discriminate X| intros _; apply Z.ltb_ge in E0; clear - E0 Hsec; lia]. }
  intros fx6 R6 M6 model6 LK6 RP6 POST6 LM6 FR6 SHK6 FLK6.
  cbn in POST6. destruct POST6 as (V10 & lo & hi & EQ6 & BINL6).
  pose proof BINL6 as (_ & Hlo & Hhi).
  destruct (mul_one_limb sec lo hi Hsec Hlo (proj1 Hhi) EQ6) as (-> & Elo).
  assert (WFB0 : PQATSS.wfb 0 lo 0 = 0) by (unfold PQATSS.wfb; destruct (_ && _)%bool; reflexivity). rewrite WFB0 in BINL6. clear WFB0.
  assert (Q6 : REGS R6) by (exact (PQARI1.REGS_call R V2 cls fb F R5 R6 Q5 RP6)). pose proof Q6 as (X2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & XK').
  assert (V23 : getr R6 (reg 23) = Z_to_bv 64 w) by (rewrite (L5SAR.cs_of_preserved R5 R6 23%nat RP6 ltac:(inl)), (KS5 23%nat) by inl; exact Y23).
  assert (V24 : getr R6 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (L5SAR.cs_of_preserved R5 R6 24%nat RP6 ltac:(inl)), (KS5 24%nat) by inl; exact Y24).
  set (MV6 := mrestrict (ahid Aw3 model6) M6) in *.
  LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8b_conc fx6 R6 MV6 (fun j => match j with 2%nat => V2 | 50%nat => F | 57%nat => w | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & T1 & T10 & T11).
  p1 PQARI1.ro RO. apply (RO RC Dc M6 model6 LK6 Aw3 s3 sa sm3 e3 cr3 eb fx6 fx7 R6 R7 0xd1250 PQATSS.ADDU64_A M7v LM6 MS7 MG7 FRZ7); clear RO.
  intros model7 LM7 AH7.
  pose proof (nsec_rng w Hw) as Hns.
  assert (ZSH7 : L5KA.zeros_at M6 (F / 8 + 448 / 8 + 2147450880) 4).
  { apply (L5KA.zeros_at_agree1 M5 M6); [| exact ZSH5]. intros i Hi. apply SHK6. change (448 / 8) with 56 in Hi. unfold SB. change (ff_bytes 4 / 8) with 128. clear - Hi. lia. }
  kitp PQARIK.ri_call_fobj CF.
  apply (CF _ PREa POSTa (w / 17179869184, 0, PQATSS.wlen lo 0, lo) RC Dc M6 model7 LK6 Aw3 s3 sa sm3 e3 cr3 eb fx7 R7 PQATSS.ADDU64_A PQATSS.ADD_H 0xd125c 448 (add64_fobj Dc)
           ltac:(unfold PQATSS.ADD_H; lia) LM7 T1 ltac:(split; [lia| reflexivity]) ltac:(rewrite (KS7 2%nat) by inl; exact X2') ltac:(rewrite (KS7 3%nat) by inl; exact (eq_trans (XK' 3%nat ltac:(inl)) Rgp))
           ltac:(rewrite (KS7 4%nat) by inl; exact (eq_trans (XK' 4%nat ltac:(inl)) Rtp)) T10 ltac:(lia) ltac:(change (ff_bytes 4) with 1024; lia) eq_refl ZSH7); clear CF.
  { cbn. split; [exact T11|]. split; [clear - Hns; lia|]. split; [clear - Hns Hsec Elo; Lia.nia|]. split; [exact BINL6|].
    split; [destruct (lo =? 0); cbn; lia|].
    split; [destruct (lo =? 0) eqn:El; [intros _; apply Z.eqb_eq in El; exact El| intros X; discriminate X]| reflexivity]. }
  intros fx8 R8 M8 model8 LK8 RP8 POST8 LM8 FR8 SHK8 FLK8.
  cbn in POST8. destruct POST8 as (V10' & BINL8).
  assert (Q7 : REGS R7) by (regsK KS7 Q6).
  assert (Q8r : REGS R8) by (exact (PQARI1.REGS_call R V2 cls fb F R7 R8 Q7 RP8)). pose proof Q8r as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A26 & A27 & AK).
  assert (B24 : getr R8 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (L5SAR.cs_of_preserved R7 R8 24%nat RP8 ltac:(inl)), (KS7 24%nat) by inl; exact V24).
  set (v8 := lo + w / 17179869184) in *.
  assert (Hv8 : 0 <= v8 < 2 ^ 64) by (unfold v8; clear - Hns Hsec Elo Hlo; lia).
  (* [comment removed for export] *)
  pose proof LM8 as (_ & _ & RP8m & _). pose proof RP8m as (PA8 & _).
  unfold PQRA.o_p, PQRA.o_is, PMSP.o_p, PMSP.o_is in PA8. cbn [pa_off_p pa_off_is PMA.AD PnLayoutA.ADDR_A] in PA8.
  pose proof PA8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB8 & _). unfold PQMA.OFF_TB in TB8.
  kitp PQARIK.ri_pfacts PFX.
  destruct (PFX RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb LM8) as (_ & _ & (_ & FLW8 & _) & _ & _ & _ & (ZOP8 & WOP8 & OVIS8 & _) & _ & (AVSH8 & AVF8 & _)). clear PFX.
  change (ff_bytes 4) with 1024 in FLW8, AVF8. change (1024 / 8) with 128 in AVSH8.
  p1 PQARI1.hd_facts HDX. destruct (HDX RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb LM8) as (_ & (_ & _ & _ & _ & OPR8 & _ & _ & O88 & _) & ZG8). clear HDX.
  p1 PQARI1.tail_facts TFX. pose proof (TFX RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb LM8) as TF8; cbn zeta in TF8. clear TFX.
  destruct TF8 as (_ & _ & _ & _ & (uOP1 & uOP8 & uOPB) & _ & _ & (uSP & uFSP & uFBSP)).
  assert (OSP : V2 - 160 + 160 <= fb + 592 \/ fb + 592 + 504 <= V2 - 160) by (right; clear - uFBSP CLS; lia).
  set (MV8 := mrestrict (ahid Aw3 model8) M8) in *.
  assert (SPR : 140735332487328 <= V2 <= 140737488355328) by (clear - SP1 SP2 CLS; lia).
  assert (AG38 : forall i, V2 - 160 <= i < V2 - 128 -> M8 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
  { intros i Hi. rewrite (FR8 i) by (clear - Hi SPR; lia). rewrite (FR6 i) by (clear - Hi SPR; lia).
    rewrite (FR5 i); [| clear - Hi SPR; lia| clear - Hi uFSP CLS; lia]. apply FR4; [clear - Hi SPR; lia| clear - Hi SPR DF9; lia]. }
  assert (SP16_8 : L5.u64_at RSEGS M8 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
  { apply (L5C.u64_at_agree RSEGS M3 M8); [intros i Hi; apply AG38; clear - Hi; lia| lia| lia| exact SPL16]. }
  assert (SP24_8 : L5.u64_at RSEGS M8 (V2 - 136) (fb + 592 + 8)).
  { apply (L5C.u64_at_agree RSEGS M3 M8); [intros i Hi; apply AG38; clear - Hi; lia| lia| lia| exact SPL24]. }
  assert (ZSH8 : L5KA.zeros_at M8 (F / 8 + 448 / 8 + 2147450880) 4).
  { apply (L5KA.zeros_at_agree1 M6 M8); [| exact ZSH7]. intros i Hi. apply SHK8. change (448 / 8) with 56 in Hi. unfold SB. change (ff_bytes 4 / 8) with 128. clear - Hi. lia. }
  destruct (OFA3 (fb + 592) 504 ltac:(lia) ltac:(lia) ltac:(lia)) as (OFo & _).
  assert (POTe : forall x0, PQMA.pot_textM (PMSPA.HV L ar) x0 = PQMA.pot_textM (PMSPA.HV L ar) (PQMA.p_tb s3) ->
                 PNRNA.pot_runA L ar (PQAKWT.with_tb s3 x0) sa = PNRNA.pot_runA L ar s3 sa).
  { intros x0 Ex. unfold PNRNA.pot_runA, PQMA.pot_mparser. cbn [PQAKWT.with_tb PQMA.p_sk PQMA.p_tb PQMA.p_bb PQMA.p_bg]. rewrite Ex. reflexivity. }
  (* [comment removed for export] *)
  assert (WSC : forall (fx9 : FPState) (R9 : bvmap 5 word) (M9 : mem) (model9 : Model) (x0 : PM.vstr),
            MM RC Dc M9 model9 LK8 Aw3 (PQAKWT.with_tb s3 x0) sa sm3 e3 cr3 eb -> REGS R9 ->
            getr R9 (reg 1) = Z_to_bv 64 859876 -> getr R9 (reg 10) = Z_to_bv 64 (F + 448) -> getr R9 (reg 11) = Z_to_bv 64 (fb + 592 + 328) ->
            getr R9 (reg 23) = Z_to_bv 64 ((fb + 592 + 328) / 8 + 2147450880) -> getr R9 (reg 24) = Z_to_bv 64 (F + 448) -> getr R9 (reg 25) = Z_to_bv 64 (fb + 592 + 328) ->
            PM.vs_size x0 = 0 -> PQMA.pot_textM (PMSPA.HV L ar) x0 = PQMA.pot_textM (PMSPA.HV L ar) (PQMA.p_tb s3) ->
            PQATSS.binl_at RSEGS M9 (F + 448) 0 (PQATSS.wlen v8 0) v8 0 -> L5KA.zeros_at M9 (F / 8 + 448 / 8 + 2147450880) 4 ->
            L5.u64_at RSEGS M9 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880) -> L5.u64_at RSEGS M9 (V2 - 136) (fb + 592 + 8) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 PQATSS.WRS_A M9 model9) K).
  { intros fx9 R9 M9 model9 x0 LM9 QQ G1 G10 G11 G23 G24 G25 SZ0 POT0 BINL9 ZSH9 SP16 SP24.
    pose proof QQ as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B26 & B27 & BK).
    assert (CR9 : RIC cr3 (PNRNA.pot_runA L ar (PQAKWT.with_tb s3 x0) sa) (tsp Dc RC0)) by (rewrite (POTe x0 POT0); exact CR3).
    (* [comment removed for export] *)
    kitp PQARIK.ri_call_ws1 CW.
    apply (CW RC Dc M9 model9 LK8 Aw3 (PQAKWT.with_tb s3 x0) sa sm3 e3 cr3 eb fx9 R9 PQATSS.WRS_A PQATSS.WRS_H 0xd1ee4 448 0 (PQATSS.wlen v8 0) v8 (WS1 Dc)
             ltac:(unfold PQATSS.WRS_H; lia) LM9 G1 ltac:(split; [lia| reflexivity]) B2 (eq_trans (BK 3%nat ltac:(inl)) Rgp) (eq_trans (BK 4%nat ltac:(inl)) Rtp)
             G10 ltac:(lia) ltac:(change (ff_bytes 4) with 1024; lia) eq_refl ZSH9 BINL9 eq_refl G11 SZ0
             (PQARIK.ric_le_run L LCL cr _ _ cr3 _ _ CR9 (proj1 (TSPB Dc RC0)))); clear CW.
    intros fx10 R10 M10 model10 LK10 Aw10 x1 cr10 RP10 TBX1 SZ1 TXT10 POST10 LM10 CK10 FR10 SHK10 FLK10.
    change (PQAKWT.with_tb (PQAKWT.with_tb s3 x0) x1) with (PQAKWT.with_tb s3 x1) in LM10, CK10.
    assert (CR10 : RIC cr10 (PNRNA.pot_runA L ar (PQAKWT.with_tb s3 x1) sa) (tsp Dc RC0)) by (unfold PNRNA.pot_runA; apply (PQARIK.ric_par L LCL cr _ _ cr3 _ _ _ cr10 _ CR9 CK10)).
    assert (Q10 : REGS R10) by (exact (PQARI1.REGS_call R V2 cls fb F R9 R10 QQ RP10)). pose proof Q10 as (C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C26 & C27 & CK).
    assert (D23 : getr R10 (reg 23) = Z_to_bv 64 ((fb + 592 + 328) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R9 R10 23%nat RP10 ltac:(inl)); exact G23).
    assert (D24 : getr R10 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (L5SAR.cs_of_preserved R9 R10 24%nat RP10 ltac:(inl)); exact G24).
    assert (D25 : getr R10 (reg 25) = Z_to_bv 64 (fb + 592 + 328)) by (rewrite (L5SAR.cs_of_preserved R9 R10 25%nat RP10 ltac:(inl)); exact G25).
    assert (BINL10 : PQATSS.binl_at RSEGS M10 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
    { apply (binl_keep M9 M10 _ _ _ _ _ BINL9); [| lia| lia]. intros i Hi. apply FLK10. change (ff_bytes 4) with 1024. clear - Hi. lia. }
    assert (SP16' : L5.u64_at RSEGS M10 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
    { apply (L5C.u64_at_agree RSEGS M9 M10); [intros i Hi; apply FR10; clear - Hi SPR; lia| lia| lia| exact SP16]. }
    assert (SP24' : L5.u64_at RSEGS M10 (V2 - 136) (fb + 592 + 8)).
    { apply (L5C.u64_at_agree RSEGS M9 M10); [intros i Hi; apply FR10; clear - Hi SPR; lia| lia| lia| exact SP24]. }
    assert (UN3' : PM.unread (PQMA.p_src (PQAKWT.with_tb s3 x1)) sm3 + 10 <= PM.unread (PQMA.p_src s) sm) by (exact UN3).
    assert (UN0' : 0 <= PM.unread (PQMA.p_src (PQAKWT.with_tb s3 x1)) sm3) by (exact UN0).
    kitp PQARIK.ri_pfacts PFX.
    destruct (PFX RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb LM10) as (IMG10 & _ & (FDF10 & FLW10 & FSW10 & _) & _ & _ & _ & (ZOP10 & WOP10 & OVIS10 & _) & OFA10 & (AVSH10 & AVF10 & AVO10)). clear PFX.
    change (ff_bytes 4) with 1024 in FDF10, FLW10, AVF10. change (1024 / 8) with 128 in AVSH10. change (PMSPA.pm_scr 10) with 32768 in AVO10.
    p1 PQARI1.hd_facts HDX. destruct (HDX RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb LM10) as (_ & (_ & _ & AVP10 & ZOA10 & _ & _ & OAR & _ & _ & OA8) & ZG10). clear HDX.
    cbn [qa_vp_adaptor PnLayoutQA.QADDR_A] in AVP10.
    p1 PQARI1.slot_shz SZX. pose proof (SZX RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb 112 LM10 ltac:(lia) eq_refl) as ZS10. clear SZX.
    change ((1379720 + 112) / 8 + 2147450880) with 2147623359 in ZS10.
    destruct (OFA10 (fb + 992) 96 ltac:(lia) ltac:(lia) ltac:(lia)) as (OAF & _). destruct (OFA10 (fb + 496) 56 ltac:(lia) ltac:(lia) ltac:(lia)) as (OVF & _). destruct (OFA10 (fb + 432) 24 ltac:(lia) ltac:(lia) ltac:(lia)) as (OKF & _).   (* [comment removed for export] *)
    destruct (OFA10 (fb + 592) 504 ltac:(lia) ltac:(lia) ltac:(lia)) as (OF & _).
    assert (OAB : 2147446784 + 17592186048512 <= fb + 992 \/ fb + 992 + 96 <= 2147446784) by (clear - uOPB; lia).
    assert (SHD : (fb + 992) / 8 + 2147450880 + 12 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 128 <= (fb + 992) / 8 + 2147450880).
    { pose proof (PQARI1.shF_apart (fb + 992) F 96 0 12 OA8 (PQARIK.mod16_8 _ (PQARIK.mod32_16 _ PF3)) OAF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X.
      replace (fb + 992 + 0) with (fb + 992) in X by lia. exact X. }
    assert (SHT : (fb + 592 + 328) / 8 + 2147450880 + 3 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 128 <= (fb + 592 + 328) / 8 + 2147450880).
    { exact (PQARI1.shF_apart (fb + 592) F 504 328 3 O88 (PQARIK.mod16_8 _ (PQARIK.mod32_16 _ PF3)) OF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (FLW512 : L5.writable RSEGS (mrestrict (ahid Aw10 model10) M10) (F + 512) 16) by (apply (L5.writable_sub RSEGS _ F 1024); [exact FLW10| lia| lia]).
    pose proof (ZG10 328 ltac:(lia)) as ZT10. pose proof (ZG10 329 ltac:(lia)) as ZT11. pose proof (ZG10 344 ltac:(lia)) as ZT44. pose proof (ZG10 336 ltac:(lia)) as ZT36.
    pose proof LM10 as (_ & _ & RP10m & _). pose proof RP10m as (PA10 & _ & _ & _ & OACC10 & _).
    unfold PQRA.o_p, PQRA.o_is, PMSP.o_p, PMSP.o_is in PA10, OACC10. cbn [pa_off_p pa_off_is PMA.AD PnLayoutA.ADDR_A] in PA10, OACC10.
    pose proof PA10 as (_ & PDEF10 & _).
    set (MV10 := mrestrict (ahid Aw10 model10) M10) in *.
    (* [comment removed for export] *)
    assert (VSC : forall (fx11 : FPState) (R11 : bvmap 5 word) (M11 : mem) (model11 : Model) (d n1 : Z) (bs : list Z),
              MM RC Dc M11 model11 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb -> REGS R11 ->
              getr R11 (reg 1) = Z_to_bv 64 860040 -> getr R11 (reg 10) = Z_to_bv 64 (fb + 992) -> getr R11 (reg 11) = Z_to_bv 64 (F + 512) ->
              getr R11 (reg 24) = Z_to_bv 64 (F + 448) -> getr R11 (reg 12) = Z_to_bv 64 7 -> getr R11 (reg 14) = Z_to_bv 64 (fb + 1232) ->
              L5.bytes_at RSEGS M11 d bs -> Z.of_nat (length bs) = n1 -> Forall (fun b => b = 45 \/ 48 <= b <= 57) bs ->
              L5.u64_at RSEGS M11 (F + 512) d -> L5.u64_at RSEGS M11 (F + 520) n1 -> 1 <= n1 <= 21 -> L5.defined M11 d n1 -> PMSPA.accA M11 d n1 ->
              (PGS.in_blk (PQMA.mparser_own (PQAKWT.with_tb s3 x1) ++ LBX) d n1 \/ PMSPA.aobjA FF' d n1) -> 0 <= d -> d + n1 <= 2 ^ 47 ->
              (d + n1 <= fb + 992 \/ fb + 992 + PQMA.ASIZE <= d) -> (d + n1 <= fb + 496 \/ fb + 496 + 56 <= d) -> (d + n1 <= fb + 432 \/ fb + 432 + 24 <= d) ->   (* [comment removed for export] *)
              L5.u8_at RSEGS M11 (F / 8 + 2147450944) 0 -> L5.u8_at RSEGS M11 (F / 8 + 2147450945) 0 ->
              PQATSS.binl_at RSEGS M11 (F + 448) 0 (PQATSS.wlen v8 0) v8 0 ->
              L5.u64_at RSEGS M11 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880) -> L5.u64_at RSEGS M11 (V2 - 136) (fb + 592 + 8) ->
              srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx11 R11 0xb4e30 M11 model11) K).
    { intros fx11 R11 M11 model11 d n1 bs LM11 QV Z1 Z10 Z11 Z24 Z12 Z14 BSd LENd CLSd VW1 VW2 Hn1 DEFd ACd LOCd Hd0 Hd47 APo APv APk SH64 SH65 BINL11 SQ16 SQ24.
      destruct (ts_ascii bs CLSd) as [UVd BOKd].
      pose proof QV as (E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27 & EK).
      assert (ACv : PMSPA.accA M11 (F + 512) 16).
      { unfold PMSPA.accA. change 16 with (8 + 8). apply aacc_join; [| | lia].
        - apply (PQAKRF.aacc_local M11 F 512 8 0 F8 eq_refl ltac:(lia) ltac:(lia) ltac:(left; split; reflexivity)).
          unfold byte_at. change (512 / 8) with 64. replace (F / 8 + 64 + 2147450880) with (F / 8 + 2147450944) by lia. apply (L5ADHR.byte_of_u8 M11 _ 0 SH64); [right; lia| lia].
        - replace (F + 512 + 8) with (F + 520) by lia. apply (PQAKRF.aacc_local M11 F 520 8 0 F8 eq_refl ltac:(lia) ltac:(lia) ltac:(left; split; reflexivity)).
          unfold byte_at. change (520 / 8) with 65. replace (F / 8 + 65 + 2147450880) with (F / 8 + 2147450945) by lia. apply (L5ADHR.byte_of_u8 M11 _ 0 SH65); [right; lia| lia]. }
      pose proof VSTRF as VS. unfold PNVA.v_string_specF in VS. cbn [qa_v_string PnLayoutQA.QADDR_A] in VS.
      (* [comment removed for export] *)
      kitp PQARIK.ri_call_slotV CS.
      apply (CS tspV RC Dc M11 model11 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb fx11 R11 0xb4e30 0xd1f88 spc NEM.TAG_ENANO (PNVA.args_str RSEGS) (PNVA.pre_str RSEGS) (PNVA.step_str RSEGS) VS LM11 eq_refl); clear CS.
      * lia.
      * exact (proj2 HSPC1).
      * exact Z1.
      * split; [lia| reflexivity].
      * exact E2.
      * exact (eq_trans (EK 3%nat ltac:(inl)) Rgp).
      * exact (eq_trans (EK 4%nat ltac:(inl)) Rtp).
      * exact E8.
      * exact Z10.
      * unfold NEM.TAG_ENANO; exact Z12.
      * unfold NEM.TAG_ENANO; clear; lia.
      * unfold PNVA.args_str, PNVA.view_ok. exists (F + 512), d, n1, NEM.TAG_ENANO, bs. rewrite L5K.rl11, L5K.rl12, L5K.rl14. split; [exact Z11|].
        split; [exists (F, 4, spc + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia]|].
        split. { split; [exact VW1|]. split; [replace (F + 512 + 8) with (F + 520) by lia; exact VW2|]. split; [clear - Hn1; lia|]. split; [exact DEFd|].
                 split; [exact ACv|]. split; [exact ACd|]. split; [right; exact LOCd|].
                 split; [unfold PQMA.ASIZE; clear - OAF; lia|]. split; [exact APo|]. split; [clear - OVF; lia|]. split; [exact APv|]. split; [clear - OKF; lia|]. split; [exact APk|]. split; [exact Hd0| exact Hd47]. }
        split; [unfold NEM.TAG_ENANO; exact Z12|]. split; [right; reflexivity|]. split; [exact Z14|].
        split; [exact BSd|]. split; [exact LENd|]. split; [exact UVd|]. split; [exact BOKd| clear - Hn1; lia].
      * unfold PNVA.pre_str, PNVA.view_len. exists n1. split; [exists (F + 512); rewrite L5K.rl11; split; [exact Z11|]; split; [replace (F + 512 + 8) with (F + 520) by lia; exact VW2| clear - Hn1; lia]|].
        p1 PQARI1.pre_slack2 PSX. destruct (PSX R11 M11 (PQAKWT.with_tb s3 x1) sm3 10 (n1 + 4) (Z.max (n1 + 5) 15) UN3' UN0' ltac:(clear; lia) ltac:(clear - Hn1; lia) ltac:(clear - Hn1; lia)) as [PKB PZB]; clear PSX.
        split; [clear - PKB; lia|]. unfold PNVA.dphi_str. rewrite L5K.rl12, Z12, L5.unsigned_lit by lia. replace (7 =? NEM.TAG_ENANO) with true by reflexivity. clear - PZB; lia.
      * p1 PQARI1.potp_nonneg PNX. destruct (PNX RC Dc M11 model11 LK10 Aw10 (PQAKWT.with_tb s3 x1) sa sm3 e3 cr10 eb LM11) as (N1 & N2 & _). clear PNX.
        apply (PQARIK.ric_le_slotV L LCL cr _ _ cr10 _ _ _ _ CR10); [exact N1| exact N2| exact (proj1 (TSP_V NEM.TAG_ENANO Dc RC0 RC))].
      * intros fx12 R12 M12 model12 LK12 Aw12 sa12 e12 b12 cr12 D12 RP12 LM12 INCD12 AOK12 EB12 EE12 STEP12 CK12 FR12 SHK12 FLK12.
        destruct (PQARIK.ric_unslotV L LCL cr _ _ cr10 _ _ _ cr12 _ _ _ _ CR10 CK12 (proj2 (TSP_V NEM.TAG_ENANO Dc RC0 RC) D12 INCD12)) as (crx & CRX & CKX).
        destruct STEP12 as (n8 & VL8 & STEPV). pose proof (view_len_eq R11 M11 (F + 512) n1 n8 Z11 ltac:(replace (F + 512 + 8) with (F + 520) by lia; exact VW2) ltac:(clear - Hn1; lia) VL8) as En8. subst n8.
        assert (Q12 : REGS R12) by (exact (PQARI1.REGS_call R V2 cls fb F R11 R12 QV RP12)). pose proof Q12 as (I2 & I8 & I9 & I18 & I19 & I20 & I21 & I22 & I26 & I27 & IK).
        assert (I24 : getr R12 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (L5SAR.cs_of_preserved R11 R12 24%nat RP12 ltac:(inl)); exact Z24).
        change (ff_bytes 4) with 1024 in FLK12, SHK12. change (1024 / 8) with 128 in SHK12.
        assert (BINL12 : PQATSS.binl_at RSEGS M12 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
        { apply (binl_keep M11 M12 _ _ _ _ _ BINL11); [| lia| lia]. intros i Hi. apply FLK12. clear - Hi. lia. }
        pose proof BINL12 as ((FL12 & _) & _). cbn [L5.bo_fb] in FL12.
        kitp PQARIK.ri_pfacts PFX.
        destruct (PFX RC D12 M12 model12 LK12 Aw12 (PQAKWT.with_tb s3 x1) sa12 sm3 e12 cr12 b12 LM12) as (_ & _ & (FDF12 & _) & _ & _ & _ & _ & _ & (_ & AVF12 & AVO12)). clear PFX.
        change (ff_bytes 4) with 1024 in FDF12, AVF12. change (PMSPA.pm_scr 10) with 32768 in AVO12.
        set (MV12 := mrestrict (ahid Aw12 model12) M12) in *.
        assert (FLv : L5.u8_at RSEGS MV12 (F + 448) 0).
        { apply (proj2 (L5A.u8_at_vis (ahid Aw12 model12) M12 (F + 448) 0 (L5A.avis_sub _ _ _ (F + 448) 1 AVF12 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact FL12. }
        assert (B47 : 0 <= 0 <= 255) by (clear; lia). pose proof (Z.testbit_even_0 0) as EV47. change (2 * 0) with 0 in EV47.
        pose proof (L5.defined_sub MV12 F 1024 (F + 456) 24 FDF12 ltac:(lia) ltac:(lia)) as DEF456.
        assert (SQ16v : L5.u64_at RSEGS MV12 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
        { apply (proj2 (L5A.u64_at_vis (ahid Aw12 model12) M12 (V2 - 144) _ (L5A.avis_sub _ _ _ (V2 - 144) 8 AVO12 ltac:(clear - SPR CLS; lia) ltac:(clear - SPR CLS; lia)) ltac:(lia) ltac:(lia))).
          apply (L5C.u64_at_agree RSEGS M11 M12); [intros i Hi; apply FR12; clear - Hi SPR; lia| lia| lia| exact SQ16]. }
        assert (SQ24v : L5.u64_at RSEGS MV12 (V2 - 136) (fb + 592 + 8)).
        { apply (proj2 (L5A.u64_at_vis (ahid Aw12 model12) M12 (V2 - 136) _ (L5A.avis_sub _ _ _ (V2 - 136) 8 AVO12 ltac:(clear - SPR CLS; lia) ltac:(clear - SPR CLS; lia)) ltac:(lia) ltac:(lia))).
          apply (L5C.u64_at_agree RSEGS M11 M12); [intros i Hi; apply FR12; clear - Hi SPR; lia| lia| lia| exact SQ24]. }
        (* [comment removed for export] *)
        tailp PQARIPU8.qriU8q_conc LM12 Q12 fx12 R12 M12 Aw12 model12.
        destruct P as (fx13 & R13 & M13v & MG13 & _ & FRZ13 & MS13 & KS13 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO13 & _ & _).
        assert (ROOMK' : PQRA.room_keep s (PQAKWT.with_tb s3 x1) sm sm3) by (exact ROOMK3).
        p1 PQARI1.TAILV8 TVX.
        apply (TVX 64 65 59 52 56 57 58 48 10 _ _ _ fx12 fx13 R12 R13 RC D12 M12 model12 LK12 Aw12 (PQAKWT.with_tb s3 x1) sa12 sm3 e12 crx cr12 _ _ 0xd1f88 M13v LM12 Q12 CPL3 INV3 STK3 ROOMK' UN3' ltac:(clear; lia) AOK12 STEPV ltac:(clear - Hn1; lia) ltac:(unfold PNVA.dphi_str; rewrite L5K.rl12, Z12, L5.unsigned_lit by lia; replace (7 =? NEM.TAG_ENANO) with true by reflexivity; clear - Hn1; lia) CRX CKX MS13 MG13
                 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) FRZ13);
          [intros j Hj; apply KS13; unfold PQARI1.RL in Hj; repeat (destruct Hj as [<-|Hj]; [inl|]); destruct Hj| exact MO13]. }
    assert (AVF10' : avis (ahid Aw10 model10) F 1024) by (exact AVF10).
    (* [comment removed for export] *)
    destruct x1 as [n1|c1 n1 p1].
    + cbn [PM.vs_size] in SZ1. destruct TBX1 as (TD & TA & Hn1 & TU).
      assert (TUv : L5.u8_at RSEGS MV10 (fb + 592 + 328) (2 * n1)).
      { apply (proj2 (L5A.u8_at_vis (ahid Aw10 model10) M10 (fb + 592 + 328) (2 * n1) (OVIS10 (fb + 592 + 328) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact TU. }
      assert (Hb1 : 0 <= 2 * n1 <= 255) by (clear - Hn1; lia). pose proof (Z.testbit_even_0 n1) as EV1.
      LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8dS_conc fx10 R10 MV10 (fun j => match j with 2%nat => V2 | 33%nat => fb + 592 | 34%nat => fb + 1232 | 36%nat => fb + 992 | 50%nat => F | 58%nat => 2 * n1 | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
      destruct P as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & Z1 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & VW2' & VW1' & SH65' & SH64').
      kitp PQARIK.ri_piece RP.
      apply (RP RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 (PM.VShort n1)) sa sm3 e3 cr10 eb fx10 fx11 R10 R11 0xd1ee4 0xb4e30 M11v
               (fun a => (F + 512 <= a < F + 512 + 16) \/ (F / 8 + 2147450880 + 64 <= a < F / 8 + 2147450880 + 64 + 2)) LM10 MS11 MG11); clear RP.
      { intros a Ha N. apply FRZ11; [exact Ha| clear - N; lia| clear - N; lia]. }
      { intros a [Wa|Wa]; (split; [unfold PQARI1.ocell; clear - Wa uFSP PF1 SP1 CLS DF0 DF9; lia|]);
          [right; left; change (ff_bytes 4) with 1024; split; [clear - Wa; lia| clear - Wa; lia]| right; right; unfold SB; change (ff_bytes 4 / 8) with 128; clear - Wa; lia]. }
      intros M11 model11 LM11 AH11 VIS11 FR11 MG11'.
      assert (Q11 : REGS R11) by (regsK KS11 Q10).
      assert (Z24 : getr R11 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (KS11 24%nat) by inl; exact D24).
      assert (VW1 : L5.u64_at RSEGS M11 (F + 512) (fb + 592 + 329)).
      { apply (proj1 (L5A.u64_at_vis (ahid Aw10 model10) M11 (F + 512) _ (L5A.avis_sub _ _ _ (F + 512) 8 AVF10' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact VW1'. }
      assert (VW2 : L5.u64_at RSEGS M11 (F + 520) n1).
      { apply (proj1 (L5A.u64_at_vis (ahid Aw10 model10) M11 (F + 520) _ (L5A.avis_sub _ _ _ (F + 520) 8 AVF10' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS11.
        replace n1 with (2 * n1 / 2) by (clear - Hn1; lia). exact VW2'. }
      assert (SH64 : L5.u8_at RSEGS M11 (F / 8 + 2147450944) 0).
      { apply (proj1 (L5A.u8_at_vis (ahid Aw10 model10) M11 (F / 8 + 2147450944) 0 (L5A.avis_sub _ _ _ (F / 8 + 2147450944) 1 AVSH10 ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact SH64'. }
      assert (SH65 : L5.u8_at RSEGS M11 (F / 8 + 2147450945) 0).
      { apply (proj1 (L5A.u8_at_vis (ahid Aw10 model10) M11 (F / 8 + 2147450945) 0 (L5A.avis_sub _ _ _ (F / 8 + 2147450945) 1 AVSH10 ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact SH65'. }
      assert (DEFd : L5.defined M11 (fb + 592 + 329) n1) by (exact (defined_grows' M10 M11 _ _ (L5.defined_sub M10 (fb + 592) PQMA.PSIZE (fb + 592 + 329) n1 PDEF10 ltac:(lia) ltac:(unfold PQMA.PSIZE; clear - Hn1 SZ1; lia)) MG11')).
      assert (ACd : PMSPA.accA M11 (fb + 592 + 329) n1).
      { apply (PMFA.accA_agree M10 M11 (fb + 592 + 329) n1); [| unfold PMSPA.accA in OACC10 |- *; exact (L5CBR.aacc_sub M10 (fb + 592) 504 (fb + 592 + 329) n1 OACC10 ltac:(lia) ltac:(clear - SZ1; lia))].
        intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Bx.
        pose proof (Z.div_mod (fb + 592 + 328) 8 ltac:(lia)) as Do. pose proof (Z.mod_pos_bound (fb + 592 + 328) 8 ltac:(lia)) as Bo.
        apply FR11; [unfold S, SB; clear - Hx SZ1 FB1 FB2 SP2 CLS; lia|]. unfold S, SB. unfold SB in SHT. intros [N|N].
        * clear - N Hx SZ1 FB1 FB2 SP2 CLS PF4 FR Dx Bx. lia.
        * clear - N Hx SZ1 SHT Dx Bx Do Bo. lia. }
      assert (BINL11 : PQATSS.binl_at RSEGS M11 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
      { apply (binl_keep M10 M11 _ _ _ _ _ BINL10); [| lia| lia]. intros i Hi. apply FR11; [clear - Hi FR; lia| intros [N|N]; [clear - N Hi; lia| clear - N Hi PF4 FR DF0 DF9; lia]]. }
      assert (SQ16 : L5.u64_at RSEGS M11 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
      { apply (L5C.u64_at_agree RSEGS M10 M11); [| lia| lia| exact SP16']. intros i Hi. apply FR11; [clear - Hi SPR; lia| intros [N|N]; [clear - N Hi uFSP CLS; lia| clear - N Hi SPR DF9; lia]]. }
      assert (SQ24 : L5.u64_at RSEGS M11 (V2 - 136) (fb + 592 + 8)).
      { apply (L5C.u64_at_agree RSEGS M10 M11); [| lia| lia| exact SP24']. intros i Hi. apply FR11; [clear - Hi SPR; lia| intros [N|N]; [clear - N Hi uFSP CLS; lia| clear - N Hi SPR DF9; lia]]. }
      destruct TXT10 as (bs & BS10 & LENbs & CLS10). cbn [PM.vs_data PM.vs_size] in BS10, LENbs.
      assert (BS11 : L5.bytes_at RSEGS M11 (fb + 592 + 329) bs).
      { apply (L5C.bytes_at_agree RSEGS M10 M11 _ bs); [| clear - FB1; lia| rewrite LENbs; clear - SZ1 FB2 uFBSP SPR CLS; lia| replace (fb + 592 + 329) with (fb + 592 + 328 + 1) by lia; exact BS10].
        intros i Hi. rewrite LENbs in Hi. apply FR11; [clear - Hi FB1 FB2 SPR CLS SZ1; lia| intros [N|N]; [clear - N Hi SZ1 OF; lia| clear - N Hi SZ1 FB4 DF0 DF9; lia]]. }
      apply (VSC fx11 R11 M11 model11 (fb + 592 + 329) n1 bs LM11 Q11 Z1 Z10 Z11 Z24 Z12 Z14 BS11 LENbs CLS10 VW1 VW2 SZ1 DEFd ACd); [| clear - FB1; lia| clear - SZ1 FB2 uFBSP SPR CLS; lia| left; clear - SZ1; lia| right; clear - SZ1; lia| right; clear - SZ1; lia| exact SH64| exact SH65| exact BINL11| exact SQ16| exact SQ24].
      right. apply PMAUAR.aobjA_push. apply (PQAKRF.aobj_fbM FF fb (fb + 592 + 329) n1 FOK); clear - SZ1; lia.
    + cbn [PM.vs_size] in SZ1. destruct TBX1 as (TD & TA & U0 & U8 & U16 & Hn1c & Hc1 & Hev & DB & CB).
      kitp PQARIK.oblk_facts OBX.
      destruct (OBX RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 (PM.VLong c1 n1 p1)) sa sm3 e3 cr10 eb p1 c1 LM10 ltac:(apply PQAKO.own_tb; cbn; left; reflexivity)) as (B4096 & Bm & B47 & B16 & BAPP & BIMG & BVIS & BSPC & BFB & BF). clear OBX.
      change (ff_bytes 4) with 1024 in BF. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
      assert (U0v : L5.u64_at RSEGS MV10 (fb + 592 + 328) (c1 + 1)).
      { apply (proj2 (L5A.u64_at_vis (ahid Aw10 model10) M10 (fb + 592 + 328) (c1 + 1) (OVIS10 (fb + 592 + 328) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact U0. }
      assert (U8v : L5.u64_at RSEGS MV10 (fb + 592 + 336) n1).
      { apply (proj2 (L5A.u64_at_vis (ahid Aw10 model10) M10 (fb + 592 + 336) n1 (OVIS10 (fb + 592 + 336) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). replace (fb + 592 + 336) with (fb + 592 + 328 + 8) by lia. exact U8. }
      assert (U16v : L5.u64_at RSEGS MV10 (fb + 592 + 344) p1).
      { apply (proj2 (L5A.u64_at_vis (ahid Aw10 model10) M10 (fb + 592 + 344) p1 (OVIS10 (fb + 592 + 344) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). replace (fb + 592 + 344) with (fb + 592 + 328 + 16) by lia. exact U16. }
      pose proof (PMF.u8_of_u64 RSEGS MV10 (fb + 592 + 328) (c1 + 1) ltac:(clear - Hc1; lia) U0v) as TUv.
      pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)) as Hb1'. assert (Hb1 : 0 <= (c1 + 1) mod 256 <= 255) by (clear - Hb1'; lia).
      pose proof (odd_mod256 c1 ltac:(clear - Hc1; lia) Hev) as OD1.
      assert (Hp1 : 0 <= p1 <= 140737488355328) by (clear - B4096 B47 Bm; lia). assert (Hn1r : 0 <= n1 <= 18446744073709551615) by (clear - Hn1c Hc1; lia).
      LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8dL_conc fx10 R10 MV10 (fun j => match j with 2%nat => V2 | 33%nat => fb + 592 | 34%nat => fb + 1232 | 36%nat => fb + 992 | 48%nat => n1 | 50%nat => F | 58%nat => (c1 + 1) mod 256 | 59%nat => p1 | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
      destruct P as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & Z1 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & VW2' & VW1' & SH65' & SH64').
      kitp PQARIK.ri_piece RP.
      apply (RP RC Dc M10 model10 LK10 Aw10 (PQAKWT.with_tb s3 (PM.VLong c1 n1 p1)) sa sm3 e3 cr10 eb fx10 fx11 R10 R11 0xd1ee4 0xb4e30 M11v
               (fun a => (F + 512 <= a < F + 512 + 16) \/ (F / 8 + 2147450880 + 64 <= a < F / 8 + 2147450880 + 64 + 2)) LM10 MS11 MG11); clear RP.
      { intros a Ha N. apply FRZ11; [exact Ha| clear - N; lia| clear - N; lia]. }
      { intros a [Wa|Wa]; (split; [unfold PQARI1.ocell; clear - Wa uFSP PF1 SP1 CLS DF0 DF9; lia|]);
          [right; left; change (ff_bytes 4) with 1024; split; [clear - Wa; lia| clear - Wa; lia]| right; right; unfold SB; change (ff_bytes 4 / 8) with 128; clear - Wa; lia]. }
      intros M11 model11 LM11 AH11 VIS11 FR11 MG11'.
      assert (Q11 : REGS R11) by (regsK KS11 Q10).
      assert (Z24 : getr R11 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (KS11 24%nat) by inl; exact D24).
      assert (VW1 : L5.u64_at RSEGS M11 (F + 512) p1).
      { apply (proj1 (L5A.u64_at_vis (ahid Aw10 model10) M11 (F + 512) _ (L5A.avis_sub _ _ _ (F + 512) 8 AVF10' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact VW1'. }
      assert (VW2 : L5.u64_at RSEGS M11 (F + 520) n1).
      { apply (proj1 (L5A.u64_at_vis (ahid Aw10 model10) M11 (F + 520) _ (L5A.avis_sub _ _ _ (F + 520) 8 AVF10' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact VW2'. }
      assert (SH64 : L5.u8_at RSEGS M11 (F / 8 + 2147450944) 0).
      { apply (proj1 (L5A.u8_at_vis (ahid Aw10 model10) M11 (F / 8 + 2147450944) 0 (L5A.avis_sub _ _ _ (F / 8 + 2147450944) 1 AVSH10 ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact SH64'. }
      assert (SH65 : L5.u8_at RSEGS M11 (F / 8 + 2147450945) 0).
      { apply (proj1 (L5A.u8_at_vis (ahid Aw10 model10) M11 (F / 8 + 2147450945) 0 (L5A.avis_sub _ _ _ (F / 8 + 2147450945) 1 AVSH10 ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia))). rewrite VIS11. exact SH65'. }
      assert (DEFd : L5.defined M11 p1 n1) by (exact (defined_grows' M10 M11 _ _ (L5.defined_sub M10 p1 c1 p1 n1 DB ltac:(lia) ltac:(clear - Hn1c; lia)) MG11')).
      assert (ACd : PMSPA.accA M11 p1 n1).
      { apply (PMFA.accA_agree M10 M11 p1 n1); [| unfold PMSPA.accA in CB |- *; exact (L5CBR.aacc_sub M10 p1 c1 p1 n1 CB ltac:(lia) ltac:(clear - Hn1c; lia))].
        intros x Hx. unfold S, SB.
        pose proof (Z.div_pos x 8 ltac:(clear - Hx B4096; lia) ltac:(lia)) as X0. pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(clear - Hx Hn1c B47; lia)) as X1.
        assert (XF : x / 8 < F / 8 \/ F / 8 + 128 <= x / 8).
        { destruct BF as [Z0|Z0]; [left| right].
          - apply (Z.div_lt_upper_bound x 8 (F / 8) ltac:(lia)). clear - Z0 Hx Hn1c F8. lia.
          - change 128 with (1024 / 8). rewrite <- (PQARI1.div8_off F 1024 (PQARIK.mod16_8 _ (PQARIK.mod32_16 _ PF3)) ltac:(lia)). apply Z.div_le_mono; [lia| clear - Z0 Hx; lia]. }
        apply FR11; [clear - X0 X1; lia| intros [N|N]; [clear - N X0 X1 PF4 DF0 DF9 FR; lia| clear - N XF; lia]]. }
      assert (BINL11 : PQATSS.binl_at RSEGS M11 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
      { apply (binl_keep M10 M11 _ _ _ _ _ BINL10); [| lia| lia]. intros i Hi. apply FR11; [clear - Hi FR; lia| intros [N|N]; [clear - N Hi; lia| clear - N Hi PF4 FR DF0 DF9; lia]]. }
      assert (SQ16 : L5.u64_at RSEGS M11 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
      { apply (L5C.u64_at_agree RSEGS M10 M11); [| lia| lia| exact SP16']. intros i Hi. apply FR11; [clear - Hi SPR; lia| intros [N|N]; [clear - N Hi uFSP CLS; lia| clear - N Hi SPR DF9; lia]]. }
      assert (SQ24 : L5.u64_at RSEGS M11 (V2 - 136) (fb + 592 + 8)).
      { apply (L5C.u64_at_agree RSEGS M10 M11); [| lia| lia| exact SP24']. intros i Hi. apply FR11; [clear - Hi SPR; lia| intros [N|N]; [clear - N Hi uFSP CLS; lia| clear - N Hi SPR DF9; lia]]. }
      destruct TXT10 as (bs & BS10 & LENbs & CLS10). cbn [PM.vs_data PM.vs_size] in BS10, LENbs.
      assert (BS11 : L5.bytes_at RSEGS M11 p1 bs).
      { apply (L5C.bytes_at_agree RSEGS M10 M11 _ bs); [| clear - B4096; lia| rewrite LENbs; clear - B47 Hn1c; lia| exact BS10].
        intros i Hi. rewrite LENbs in Hi. apply FR11; [clear - Hi B4096 B47 Hn1c; lia| intros [N|N]; [clear - N Hi BF Hn1c; lia| clear - N Hi BAPP Hn1c DF0 DF9; lia]]. }
      apply (VSC fx11 R11 M11 model11 p1 n1 bs LM11 Q11 Z1 Z10 Z11 Z24 Z12 Z14 BS11 LENbs CLS10 VW1 VW2 SZ1 DEFd ACd); [| clear - B4096; lia| clear - B47 Hn1c; lia| unfold PQMA.ASIZE; clear - BFB Hn1c; lia| clear - BFB Hn1c; lia| clear - BFB Hn1c; lia| exact SH64| exact SH65| exact BINL11| exact SQ16| exact SQ24].
      left. exists p1, c1. split; [apply in_or_app; left; apply PQAKO.own_tb; cbn; left; reflexivity| clear - Hn1c; lia]. }
  (* [comment removed for export] *)
  destruct (PQMA.p_tb s3) as [n0|c0 n9 p0] eqn:Etb.
  - (* [comment removed for export] *)
    pose proof TB8 as (TD8 & TA8 & Hn0 & TU8).
    assert (TU8v : L5.u8_at RSEGS MV8 (fb + 592 + 328) (2 * n0)).
    { apply (proj2 (L5A.u8_at_vis (ahid Aw3 model8) M8 (fb + 592 + 328) (2 * n0) (OVIS8 (fb + 592 + 328) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact TU8. }
    assert (Hb0 : 0 <= 2 * n0 <= 255) by (clear - Hn0; lia).
    pose proof (Z.testbit_even_0 n0) as EV0.
    pose proof (ZG8 328 ltac:(lia)) as ZT8. pose proof (ZG8 329 ltac:(lia)) as ZT9.
    assert (WT2 : L5.writable RSEGS MV8 (fb + 592 + 328) 2) by (apply (L5.writable_sub RSEGS MV8 (fb + 592) 504); [exact WOP8| lia| lia]).
    LeanFeed.pfeed ident:(P) (PQARIPU8.qriU8cS_conc fx8 R8 MV8 (fun j => match j with 2%nat => V2 | 33%nat => fb + 592 | 50%nat => F | 58%nat => 2 * n0 | _ => 0 end)) ltac:(first [ assumption
  | lazymatch goal with
    | |- 0 <= bv_unsigned ?x < _ => apply (PQARIK.bvu_rng x)
    | |- PQARIPH.aligned _ _ => unfold PQARIPH.aligned; first [assumption | lia]
    | |- PQARIPX.aligned _ _ => unfold PQARIPX.aligned; first [assumption | lia]
    | |- PQARIPU8.aligned _ _ => unfold PQARIPU8.aligned; first [assumption | lia]
    | |- _ => lia
    end ]).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & T1' & T10' & T11' & T23' & T25' & C328 & C329).
    kitp PQARIK.ri_piece_tb RT.
    apply (RT RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb fx8 fx9 R8 R9 0xd125c PQATSS.WRS_A M9v (fun a => fb + 592 + 328 <= a < fb + 592 + 328 + 2) (PM.VShort 0) LM8 MS9 MG9); clear RT.
    { intros a Ha N. apply FRZ9; [exact Ha| exact N]. }
    { intros a Wa. split; [unfold PQARI1.ocell; clear - Wa uFBSP CLS; lia| right; left; clear - Wa; lia]. }
    { rewrite Etb. reflexivity. }
    { cbn. lia. }
    { intros M9 MG9' FR9 VIS9 OV9 AGS9 AGT9 TBo. rewrite Etb in TBo. destruct TBo as (D8 & A8' & _ & _).
      replace (fb + 592 + 328) with (fb + 920) in * by lia.
      split; [exact (defined_grows' M8 M9 _ _ D8 MG9')|].
      split; [exact (PMFA.accA_agree M8 M9 _ _ (PMFA.agsh_sub M8 M9 (fb + 592) PQMA.PSIZE (fb + 920) 24 AGS9 ltac:(lia) ltac:(unfold PQMA.PSIZE; lia)) A8')|].
      split; [lia|]. apply (proj1 (L5A.u8_at_vis (ahid Aw3 model8) M9 (fb + 920) (2 * 0) (L5A.avis_sub _ _ _ (fb + 920) 1 OV9 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      rewrite VIS9. exact C328. }
    intros M9 model9 LM9 AH9 VIS9 FR9 MG9'.
    assert (Q9s : REGS R9) by (regsK KS9 Q8r).
    assert (G24 : getr R9 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (KS9 24%nat) by inl; exact B24).
    assert (BINL9 : PQATSS.binl_at RSEGS M9 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
    { apply (binl_keep M8 M9 _ _ _ _ _ BINL8); [| lia| lia]. intros i Hi. apply FR9; [clear - Hi FR; lia| clear - Hi OFo; lia]. }
    assert (ZSH9 : L5KA.zeros_at M9 (F / 8 + 448 / 8 + 2147450880) 4).
    { apply (L5KA.zeros_at_agree1 M8 M9); [| exact ZSH8]. intros i Hi. change (448 / 8) with 56 in Hi. apply FR9; [clear - Hi DF0 DF9; lia| clear - Hi uOPB DF0 DF9; lia]. }
    assert (SP16_9 : L5.u64_at RSEGS M9 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
    { apply (L5C.u64_at_agree RSEGS M8 M9); [| lia| lia| exact SP16_8]. intros i Hi. apply FR9; [clear - Hi SPR; lia| clear - Hi uFBSP CLS; lia]. }
    assert (SP24_9 : L5.u64_at RSEGS M9 (V2 - 136) (fb + 592 + 8)).
    { apply (L5C.u64_at_agree RSEGS M8 M9); [| lia| lia| exact SP24_8]. intros i Hi. apply FR9; [clear - Hi SPR; lia| clear - Hi uFBSP CLS; lia]. }
    apply (WSC fx9 R9 M9 model9 (PM.VShort 0) LM9 Q9s T1' T10' T11' T23' G24 T25' eq_refl eq_refl BINL9 ZSH9 SP16_9 SP24_9).
  - (* [comment removed for export] *)
    pose proof TB8 as (TD8 & TA8 & U0 & U8 & U16 & Hn0 & Hc0 & Hev0 & DB & CB).
    kitp PQARIK.oblk_facts OBX.
    destruct (OBX RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb p0 c0 LM8 ltac:(apply PQAKO.own_tb; rewrite Etb; cbn; left; reflexivity)) as (B4096 & Bm & B47 & B16 & BAPP & BIMG & BVIS & BSPC & BFB & BF). clear OBX.
    change (ff_bytes 4) with 1024 in BF. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
    assert (U0v : L5.u64_at RSEGS MV8 (fb + 592 + 328) (c0 + 1)).
    { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model8) M8 (fb + 592 + 328) (c0 + 1) (OVIS8 (fb + 592 + 328) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact U0. }
    assert (U16v : L5.u64_at RSEGS MV8 (fb + 592 + 344) p0).
    { apply (proj2 (L5A.u64_at_vis (ahid Aw3 model8) M8 (fb + 592 + 344) p0 (OVIS8 (fb + 592 + 344) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). replace (fb + 592 + 344) with (fb + 592 + 328 + 16) by lia. exact U16. }
    pose proof (PMF.u8_of_u64 RSEGS MV8 (fb + 592 + 328) (c0 + 1) ltac:(clear - Hc0; lia) U0v) as TU8v.
    pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)) as Hb0'. assert (Hb0 : 0 <= (c0 + 1) mod 256 <= 255) by (clear - Hb0'; lia).
    pose proof (odd_mod256 c0 ltac:(clear - Hc0; lia) Hev0) as OD0.
    pose proof (ZG8 328 ltac:(lia)) as ZT8. pose proof (ZG8 344 ltac:(lia)) as ZT44'. pose proof (ZG8 336 ltac:(lia)) as ZT36'.
    assert (Hp0 : 4096 <= p0 <= 140737488355320) by (clear - B4096 B47 Hc0; lia).
    assert (Hp8 : p0 mod 8 = 0) by (exact (PQARIK.mod16_8 _ B16)).
    assert (HpB : 2147446784 + 17592186048512 <= p0 \/ p0 + 1 <= 2147446784) by (clear - BAPP Bm; lia).
    assert (ZSp : L5KA.zeros_at MV8 (p0 / 8 + 2147450880) 1).
    { unfold PMSPA.accA in CB. pose proof (PMKA.zeros_of_aacc M8 p0 8 (L5CBR.aacc_sub M8 p0 c0 p0 8 CB ltac:(lia) ltac:(clear - Hc0; lia)) Hp8 eq_refl ltac:(lia)) as ZZ.
      change (8 / 8) with 1 in ZZ.
      apply (proj2 (L5A.zeros_at_vis (ahid Aw3 model8) M8 (p0 / 8 + 2147450880) 1 ltac:(intros i Hi; replace (p0 / 8 + 2147450880 + i) with (S p0) by (unfold S, SB; clear - Hi; lia); exact (proj2 (BVIS p0 ltac:(clear - Bm; lia)))))).
      exact ZZ. }
    assert (WRp : L5.writable RSEGS MV8 p0 1).
    { apply (L5C.writable_of_defined RSEGS MV8 p0 1); [| clear - Hp0; lia| clear - Hp0; lia].
      apply (proj2 (L5A.defined_vis (ahid Aw3 model8) M8 p0 1 ltac:(intros i Hi; rewrite Z.add_comm; replace (i + p0) with (p0 + i) by lia; exact (proj1 (BVIS (p0 + i) ltac:(clear - Hi Bm Hc0; lia)))))).
      exact (L5.defined_sub M8 p0 c0 p0 1 DB ltac:(lia) ltac:(clear - Hc0; lia)). }
    assert (DJ1 : V2 - 160 + 160 <= p0 \/ p0 + 1 <= V2 - 160) by (right; clear - BSPC Hc0; lia).
    assert (DJ2 : p0 + 1 <= fb + 592 \/ fb + 592 + 504 <= p0) by (clear - BFB Hc0; lia).
    assert (DJ3 : p0 + 1 <= F \/ F + 1024 <= p0) by (clear - BF Hc0; lia).
    assert (DJ4 : 65536 + 6971392 <= p0 \/ p0 + 1 <= 65536) by (clear - BIMG Hc0; lia).
    assert (WT8 : L5.writable RSEGS MV8 (fb + 592 + 336) 8) by (apply (L5.writable_sub RSEGS MV8 (fb + 592) 504); [exact WOP8| lia| lia]).
    pose proof (LF2CBN( PQARIPU8.qriU8cL_conc fx8 R8 MV8 (fun j => match j with 2%nat => V2 | 33%nat => fb + 592 | 50%nat => F | 58%nat => (c0 + 1) mod 256 | 59%nat => p0 | _ => 0 end) )) as P.
    rewrite Z.add_0_r in P. fdP P.
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & T1' & T10' & T11' & T23' & T25' & C336 & Cp0).
    kitp PQARIK.ri_piece_tb RT.
    apply (RT RC Dc M8 model8 LK8 Aw3 s3 sa sm3 e3 cr3 eb fx8 fx9 R8 R9 0xd125c PQATSS.WRS_A M9v (fun a => (p0 <= a < p0 + 1) \/ (fb + 592 + 336 <= a < fb + 592 + 336 + 8)) (PM.VLong c0 0 p0) LM8 MS9 MG9); clear RT.
    { intros a Ha N. apply FRZ9; [exact Ha| clear - N; lia| clear - N; lia]. }
    { intros a [Wa|Wa]; (split; [unfold PQARI1.ocell; clear - Wa uFBSP BSPC Hc0 CLS; lia|]); [right; right; exists p0, c0; split; [rewrite Etb; left; reflexivity| clear - Wa Hc0; lia]| right; left; clear - Wa; lia]. }
    { rewrite Etb. reflexivity. }
    { cbn. clear - Hc0. lia. }
    { intros M9 MG9' FR9 VIS9 OV9 AGS9 AGT9 TBo. rewrite Etb in TBo. destruct TBo as (D8 & A8' & X0' & X8' & X16' & _ & _ & _ & DBo & CBo).
      replace (fb + 592 + 328) with (fb + 920) in * by lia.
      split; [exact (defined_grows' M8 M9 _ _ D8 MG9')|].
      split; [exact (PMFA.accA_agree M8 M9 _ _ (PMFA.agsh_sub M8 M9 (fb + 592) PQMA.PSIZE (fb + 920) 24 AGS9 ltac:(lia) ltac:(unfold PQMA.PSIZE; lia)) A8')|].
      split; [apply (L5C.u64_at_agree RSEGS M8 M9); [intros i Hi; apply FR9; [clear - Hi FB1 FB2 SP2 CLS; lia| clear - Hi BFB Hc0; lia]| lia| lia| exact X0']|].
      split; [replace (fb + 920 + 8) with (fb + 592 + 336) by lia; apply (proj1 (L5A.u64_at_vis (ahid Aw3 model8) M9 (fb + 592 + 336) 0 (L5A.avis_sub _ _ _ (fb + 592 + 336) 8 OV9 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); rewrite VIS9; exact C336|].
      split; [apply (L5C.u64_at_agree RSEGS M8 M9); [intros i Hi; apply FR9; [clear - Hi FB1 FB2 SP2 CLS; lia| clear - Hi BFB Hc0; lia]| lia| lia| exact X16']|].
      split; [clear - Hc0; lia|]. split; [exact Hc0|]. split; [exact Hev0|]. split; [exact (defined_grows' M8 M9 _ _ DBo MG9')|].
      exact (PMFA.accA_agree M8 M9 _ _ (proj1 (AGT9 p0 c0 ltac:(rewrite Etb; left; reflexivity))) CBo). }
    intros M9 model9 LM9 AH9 VIS9 FR9 MG9'.
    assert (Q9s : REGS R9) by (regsK KS9 Q8r).
    assert (G24 : getr R9 (reg 24) = Z_to_bv 64 (F + 448)) by (rewrite (KS9 24%nat) by inl; exact B24).
    assert (BINL9 : PQATSS.binl_at RSEGS M9 (F + 448) 0 (PQATSS.wlen v8 0) v8 0).
    { apply (binl_keep M8 M9 _ _ _ _ _ BINL8); [| lia| lia]. intros i Hi. apply FR9; [clear - Hi FR; lia| clear - Hi OFo BF Hc0; lia]. }
    assert (ZSH9 : L5KA.zeros_at M9 (F / 8 + 448 / 8 + 2147450880) 4).
    { apply (L5KA.zeros_at_agree1 M8 M9); [| exact ZSH8]. intros i Hi. change (448 / 8) with 56 in Hi. apply FR9; [clear - Hi DF0 DF9; lia| clear - Hi uOPB BAPP Bm DF0 DF9; lia]. }
    assert (SP16_9 : L5.u64_at RSEGS M9 (V2 - 144) ((fb + 592 + 8) / 8 + 2147450880)).
    { apply (L5C.u64_at_agree RSEGS M8 M9); [| lia| lia| exact SP16_8]. intros i Hi. apply FR9; [clear - Hi SPR; lia| clear - Hi uFBSP BSPC Hc0 CLS; lia]. }
    assert (SP24_9 : L5.u64_at RSEGS M9 (V2 - 136) (fb + 592 + 8)).
    { apply (L5C.u64_at_agree RSEGS M8 M9); [| lia| lia| exact SP24_8]. intros i Hi. apply FR9; [clear - Hi SPR; lia| clear - Hi uFBSP BSPC Hc0 CLS; lia]. }
    apply (WSC fx9 R9 M9 model9 (PM.VLong c0 0 p0) LM9 Q9s T1' T10' T11' T23' G24 T25' eq_refl eq_refl BINL9 ZSH9 SP16_9 SP24_9).
Qed.

End Frame.
End Run.
End WithHeap.

(* [comment removed for export] *)
Theorem TS8A_ok {SCFG_P : ScfgP} (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR)
    (HIk : list (list Z) -> asan_iface) (tsp : list (list Z) -> list Z -> credit) (TSRESA : credit) (tspV : Z -> list (list Z) -> list Z -> credit) :
  PNVA.v_string_specF RSEGS AD AQ AAD AE L ar HIk tspV ->
  (forall t D RC RCv, PMSP.credit_le (tspV t D RCv) (tsp D RC)
                      /\ (forall D', incl D D' -> PMSP.credit_le (PM.credit_add (tsp D' RC) (tspV t D RCv)) (PM.credit_add (tsp D RC) (tspV t D' RCv)))) ->
  (forall D, PQATSSa.mulu_spec L ar (HIk D)) -> (forall D, PQATSSa.add64_spec L ar (HIk D)) -> (forall D, PQATSSa.ws1_spec L ar (HIk D)) ->
  PQARITS.TS8A L ar C IL LR HIk tsp TSRESA.
Proof.
  intros VSTRF TSP_V MULU ADD64 WS1. unfold PQARITS.TS8A, PQARITS.in_ctx.
  intros LY FAMok ICokF ILY TSPB K R M model LBX FF LK Aw cr V2 cls r fb cat n D0 s sa str sm e eb RC0 Hcls V32 HH AM K0 ENT FRM FRS FOK A10 A11 A12 RPRE INCS RCH0 ROOM0 INV0 CRED0 KONT
         F fl LK2 M2 model2 G APART fx3 R3 RC Dc M3 model3 LK3 Aw3 s3 sm3 e3 cr3 TE.
  exact (TS8_arm L ar C IL LR HIk tsp TSRESA LY FAMok ICokF ILY TSPB tspV VSTRF TSP_V MULU ADD64 WS1 K R M model LBX FF LK Aw cr V2 cls r fb cat n D0 s sa str sm e eb RC0 Hcls V32 HH AM K0
           ENT FRM FRS FOK A10 A11 A12 RPRE INCS RCH0 ROOM0 INV0 CRED0 KONT F fl LK2 M2 model2 G APART fx3 R3 RC Dc M3 model3 LK3 Aw3 s3 sm3 e3 cr3 TE).
Qed.
End PQARIT8.
