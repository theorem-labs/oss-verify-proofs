(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P8_b PnADec128E_b PnADec128S_b PnADec128G_b PnADec128C1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.


Module PNADC2.
Import L5A. Import L5CA. Import L5SAR. Import PNADK. Import PNADC1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma xagr_stat E sp' scr' D M M' a : PNADC1.xagr L ar E sp' scr' D M M' -> PNST.dep PMA.AD PMA.AN a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros AG Da ND. pose proof (PNADK.depA_img a Da) as DI. apply AG; [clear - DI; lia| exact (PNADC1.dep_client L ar C LY _ _ _ _ a Da)| exact ND].
Qed.
Lemma xagr_ro E sp' scr' D M M' a : PNADC1.xagr L ar E sp' scr' D M M' -> 65536 <= a < 1282048 -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros AG Ha ND. apply AG; [clear - Ha; lia| | exact ND].
  unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - Ha; lia|].
  intros Q. pose proof (L5A.aly_static_lo L C LYa a Q) as Q'. clear - Q' Ha. lia.
Qed.
Lemma xagr_stk E sp' scr' D M M' a : PNADC1.xagr L ar E sp' scr' D M M' -> 0 <= a -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (sp' - scr' <= a < sp') -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros AG H0 Ha Hs ND. apply AG; [clear - Ha H0; lia| apply L5SAR.stack_client; [exact Ha| exact Hs]| exact ND].
Qed.

Lemma base_xagr E sp' scr' (D : Z -> Prop) M M' : base_ok M -> PNADC1.xagr L ar E sp' scr' D M M' -> (forall a, D a -> DX a) -> base_ok M'.
Proof.
  intros BASE AG DD. apply (PNADC1.base_x M M'); [| exact BASE]. intros a Ha.
  assert (ND : ~ D a) by (intros Da; apply DD in Da; unfold DX, DXd, DXa in Da; clear - Da Ha; lia).
  destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - apply (xagr_ro E sp' scr' D M M' a AG Ha ND).
  - apply (xagr_stat E sp' scr' D M M' a AG); [| exact ND]. right; left. cbn [pa_canary PMA.AD ADDR_A]. exact Ha.
  - apply (xagr_stat E sp' scr' D M M' a AG); [| exact ND]. apply PNST.dep_of_j. apply PMST.in_foot_nl. cbn [pa_need_locks PMA.AD ADDR_A]. exact Ha.
  - apply (xagr_stat E sp' scr' D M M' a AG); [| exact ND]. apply PNST.dep_of_j. apply PMST.in_foot_ll. cbn [pa_locale_lock PMA.AD ADDR_A]. exact Ha.
Qed.
(* [comment removed for export] *)
Lemma atx_agree (M M' : mem) (hs : list (Z * Z)) : (length hs <= 3)%nat ->
  (forall i, 6896976 <= i < 6896976 + 544 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  HAJ.atexit_cells RSEGS M 6896976 1148964 619876 1148964 687916 449180 hs -> HAJ.atexit_cells RSEGS M' 6896976 1148964 619876 1148964 687916 449180 hs.
Proof.
  intros LEN AG. unfold HAJ.atexit_cells.
  assert (U8 : forall a v, 6896976 <= a -> a + 8 <= 6896976 + 544 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v H1 H2. apply (L5C.u64_at_agree RSEGS M M'); [| clear - H1; lia| clear - H2; lia]. intros i Hi. apply AG. clear - Hi H1 H2; lia. }
  assert (U4 : forall a v, 6896976 <= a -> a + 4 <= 6896976 + 544 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v H1 H2 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a); [exact H| clear - H1; lia| cbn; clear - H2; lia|]. intros i Hi. apply AG. cbn in Hi. clear - Hi H1 H2; lia. }
  assert (U1 : forall a v, 6896976 <= a -> a + 1 <= 6896976 + 544 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v H1 H2. apply (L5C.u8_at_agree RSEGS M M'); [| clear - H1; lia| clear - H2; lia]. intros i Hi. apply AG. clear - Hi H1 H2; lia. }
  intros (F & LK & SL & HD & NX & F0 & A0 & F1 & A1 & EXTc).
  split; [apply U1; [clear; lia| clear; lia| exact F]|]. split; [apply U4; [clear; lia| clear; lia| exact LK]|]. split; [apply U4; [clear; lia| clear; lia| exact SL]|].
  split; [apply U8; [clear; lia| clear; lia| exact HD]|]. split; [apply U8; [clear; lia| clear; lia| exact NX]|]. split; [apply U8; [clear; lia| clear; lia| exact F0]|].
  split; [apply U8; [clear; lia| clear; lia| exact A0]|]. split; [apply U8; [clear; lia| clear; lia| exact F1]|]. split; [apply U8; [clear; lia| clear; lia| exact A1]|].
  intros i f a Hi. pose proof (nth_error_Some hs i) as [Hs _].
  assert (Hlt : (i < length hs)%nat) by (apply Hs; rewrite Hi; discriminate).
  destruct (EXTc i f a Hi) as (E1 & E2 & E3 & E4).
  split; [apply U8; [clear - Hlt LEN; lia| clear - Hlt LEN; lia| exact E1]|]. split; [apply U8; [clear - Hlt LEN; lia| clear - Hlt LEN; lia| exact E2]|].
  split; [apply U8; [clear - Hlt LEN; lia| clear - Hlt LEN; lia| exact E3]| apply U8; [clear - Hlt LEN; lia| clear - Hlt LEN; lia| exact E4]].
Qed.
(* [comment removed for export] *)
Definition keeps (l : list nat) (R R' : bvmap 5 word) : Prop := forall x, In x l -> getr R' (reg x) = getr R (reg x).
Lemma keeps_trans l R1 R2 R3 : keeps l R1 R2 -> keeps l R2 R3 -> keeps l R1 R3.
Proof. intros K1 K2 x Hx. rewrite (K2 x Hx). exact (K1 x Hx). Qed.
Lemma keeps_sub l l' R R' : keeps l' R R' -> (forall x, In x l -> In x l') -> keeps l R R'.
Proof. intros K1 I x Hx. exact (K1 x (I x Hx)). Qed.
Definition CH : list nat := [3; 4; 23; 24; 26; 27]%nat.
Definition CS : list nat := [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 26; 27]%nat.
Lemma keeps_cs l R R' : regs_preserved R R' -> (forall x, In x l -> In x L5SAR.cs_all) -> keeps l R R'.
Proof. intros RP I x Hx. exact (L5SAR.cs_of_preserved R R' x RP (I x Hx)). Qed.
Lemma CH_cs x : In x CH -> In x L5SAR.cs_all.
Proof. revert x. apply (L5K.incl_b CH). vm_compute. reflexivity. Qed.
Lemma CS_cs x : In x CS -> In x L5SAR.cs_all.
Proof. revert x. apply (L5K.incl_b CS). vm_compute. reflexivity. Qed.
Lemma bvu (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Section Phase.
Variables (pcA pcD pcE lit obj obj1 objn g g1 g8 ra0 raC raD sh K K2 : Z) (KSa KSb KSc KSd : list nat).
Hypothesis PA : forall fx R M (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  PNADP8.aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 -> L5.img_clear M g g8 -> L5.writable RSEGS M g 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 64) -> ~ ((0 + g1) <= bv_unsigned a < (0 + g1) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 64) -> ~ ((0 + g1) <= i < (0 + g1) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R pcA M) (st fx' R' 0x6336c M')
        /\ (forall x, In x KSa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729728
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 320)
        /\ getr R' (reg 8) = Z_to_bv 64 lit
        /\ getr R' (reg 10) = Z_to_bv 64 lit
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 obj
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 2%nat)
        /\ L5.u8_at RSEGS M' g1 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (bv_unsigned (Z_to_bv 64 ((V 2%nat) - 256)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) ra0).

Hypothesis PB : forall fx R M (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 lit -> getr R (reg 10) = Z_to_bv 64 K -> getr R (reg 18) = Z_to_bv 64 obj -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> PNADP8.aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 ->
  L5KA.zeros_at M sh 3 -> L5.writable RSEGS M obj 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + obj) <= bv_unsigned a < (0 + obj) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + obj) <= i < (0 + obj) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2280 M) (st fx' R' 0x78370 M')
        /\ (forall x, In x KSb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729908
        /\ getr R' (reg 9) = Z_to_bv 64 K
        /\ getr R' (reg 10) = Z_to_bv 64 obj1
        /\ getr R' (reg 11) = Z_to_bv 64 lit
        /\ getr R' (reg 12) = Z_to_bv 64 K
        /\ getr R' (reg 19) = Z_to_bv 64 obj1
        /\ L5.u8_at RSEGS M' obj K2).

Hypothesis PC : forall fx R M (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 lit -> getr R (reg 9) = Z_to_bv 64 K -> getr R (reg 18) = Z_to_bv 64 obj -> getr R (reg 19) = Z_to_bv 64 obj1 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  PNADP8.aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> L5KA.zeros_at M sh 3 ->
  L5.writable RSEGS M obj 24 -> 4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> L5.u64_at RSEGS M ((V 2%nat) - 264) ra0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 272) (V 2%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 280) ((V 2%nat) - 256) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 296) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 304) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + objn) <= bv_unsigned a < (0 + objn) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + objn) <= i < (0 + objn) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2334 M) (st fx' R' 0x6da18 M')
        /\ (forall x, In x KSc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 raC
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 10) = Z_to_bv 64 874172
        /\ getr R' (reg 11) = Z_to_bv 64 obj
        /\ getr R' (reg 12) = Z_to_bv 64 1282768
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ L5.u8_at RSEGS M' objn 0).

Hypothesis PD : forall fx R M (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> PNADP8.aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M g 2 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + g) <= bv_unsigned a < (0 + g) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + g) <= i < (0 + g) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R pcD M) (st fx' R' pcE M')
        /\ (forall x, In x KSd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 raD
        /\ getr R' (reg 10) = Z_to_bv 64 g
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' g 1
        /\ L5.u8_at RSEGS M' g1 1).
Variables (buf bs : list byte).
Hypothesis c_g1 : g1 = g + 1.
Hypothesis c_g8 : g8 = g + 8.
Hypothesis c_obj1 : obj1 = obj + 1.
Hypothesis c_objn : objn = obj + 1 + K.
Hypothesis c_sh : sh = obj / 8 + 2147450880.
Hypothesis c_K2 : K2 = 2 * K.
Hypothesis c_g : 6759112 <= g /\ g + 8 <= 6759176.
Hypothesis c_obj : 6759112 <= obj /\ obj + 24 <= 6759176 /\ obj mod 8 = 0.
Hypothesis c_K : 0 < K <= 22.
Hypothesis c_gobj : g + 8 <= obj \/ obj + 24 <= g.
Hypothesis c_lit : In (lit, K + 1) (icl_globals IL) /\ 65536 <= lit /\ lit + Z.of_nat (length buf) <= 1282048.
Hypothesis c_buf : rdn RSEGS (fun _ => None) (Z_to_bv 64 lit) (length buf) = Some buf.
Hypothesis c_wend : (lit + K) / 8 * 8 + 8 <= lit + Z.of_nat (length buf).
Hypothesis c_nul : nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0.
Hypothesis c_nnul : forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0.
Hypothesis c_bs : rdn RSEGS (fun _ => None) (Z_to_bv 64 lit) (Z.to_nat K) = Some bs.
Hypothesis c_raC : raC = pcD /\ raC mod 2 = 0 /\ 0 <= raC < 2 ^ 64.
Hypothesis c_wg : StreamSim.wseg_ok RSEGS (Z_to_bv 64 g) (Z.to_nat 2) = true.
Hypothesis c_wobj : StreamSim.wseg_ok RSEGS (Z_to_bv 64 obj) (Z.to_nat 24) = true.
Hypothesis c_wobj1 : StreamSim.wseg_ok RSEGS (Z_to_bv 64 obj1) (Z.to_nat K) = true.
Hypothesis c_KSa : forall x, In x (9 :: 19 :: 20 :: CH)%nat -> In x KSa.
Hypothesis c_KSb : forall x, In x (2 :: 8 :: 18 :: 20 :: 21 :: CH)%nat -> In x KSb.
Hypothesis c_KSc : forall x, In x CH -> In x KSc.
Hypothesis c_KSd : forall x, In x CS -> In x KSd.

Definition Dph (a : Z) : Prop := g <= a < g + 2 \/ obj <= a < obj + 24 \/ DXa a.
Lemma Dph_DX a : Dph a -> DX a.
Proof. unfold Dph, DX, DXd. clear - c_g c_obj. intros [Y|[Y|Y]]; [left; lia| left; lia| right; exact Y]. Qed.

Lemma phase E (X : dkc L ar HI E) LKc (fx : FPState) R M model A (hs : list (Z * Z)) :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M (vml_of model) -> amodel_ok A model -> astk ar M (vsp E) SCR -> base_ok M ->
  PNADE.rgd E R -> L5.img_clear M g g8 ->
  HAJ.atexit_cells RSEGS M 6896976 1148964 619876 1148964 687916 449180 hs -> (length hs <= 2)%nat ->
  (forall fx' R' M' model' A',
     ri_inv HI (vLB E) (FF' E) LKc (vcr E) A' M' (vml_of model') -> amodel_ok A' model' -> model_rt model model' -> incl A A' ->
     astk ar M' (vsp E) SCR -> base_ok M' -> PNADE.rgd E R' ->
     PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M' -> PNADC1.xdkl L ar E (vsp E - 256) XSCR M M' ->
     L5.u8_at RSEGS M' g 1 -> PNST.sso_lit RSEGS M' obj K ->
     HAJ.atexit_cells RSEGS M' 6896976 1148964 619876 1148964 687916 449180 (hs ++ [(874172, obj)]) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pcE M' model') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pcA M model) (vK E).
Proof.
  intros HH AM ASTK BASE RG GCL ATX HLEN KONT.
  pose proof (PNADC1.xgeo L ar HI E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL).
  dgeom L ar HI E X.
  pose proof RG as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q24). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  assert (RTP : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite Q4; exact (c_Rtp L ar HI E X)).
  destruct c_obj as (O1 & O2 & O8). destruct c_g as (G1 & G2). destruct c_lit as (LIN & L1 & L2). destruct c_raC as (RC1 & RC2 & RC3).
  (* [comment removed for export] *)
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M model HH ASTK) as ((V0 & V1 & V2 & V3 & V4) & VIS & VIMG & ZOBJ).
  assert (V5 : L5.img_clear (mrestrict (ahid A model) M) g g8) by (apply L5A.img_clear_mrestrict; exact GCL).
  remember (mrestrict (ahid A model) M) as MV eqn:EMV.
  assert (V6 : L5.writable RSEGS MV g 2) by (apply PNADC1.writable_img; [exact c_wg| clear - G1; lia| clear; lia| clear - G2; lia]).
  pose proof (bvu (getr R (reg 21))) as HV38. pose proof (bvu (getr R (reg 18))) as HV18.
  assert (Q21 : getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (RF : 4096 <= vF E <= 140737488354816) by (clear - GFF1; lia).
  assert (Rf : 4096 <= vfirst E <= 140737488355280) by (clear - GF1; lia).
  assert (Rv : 4096 <= vvp E <= 140737488355312) by (clear - GV1; lia).
  pose proof (PA fx R MV (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 34%nat => vvp E | 38%nat => bv_unsigned (getr R (reg 21)) | 50%nat => vF E | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(assumption).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1r1 & A1r2 & A1r8 & A1r10 & A1r11 & A1r12 & A1r18 & A1r21 & C312 & C272 & CG1 & C304 & C296 & C288 & C280 & C264).
  rewrite L5.unsigned_lit in C280 by (clear - GSLO GSHI GSPT GCEIL; lia).
  subst MV.
  apply (PNADC1.xpiece L ar C HI LY HIok E X LKc fx fx1 R R1 pcA 406380 M model A M1v
           (fun a => vsp E - 320 <= a < vsp E - 320 + 64 \/ 0 + g1 <= a < 0 + g1 + 1) HH AM ASTK MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros Q; apply N; left; exact Q| intros Q; apply N; right; exact Q]. }
  { intros a [Wa|Wa]; [left; unfold XSCR; clear - Wa; lia| right; unfold DXd; clear - Wa G1 G2 c_g1; lia]. }
  intros M1 model1 HH1 AM1 RT1 ASTK1 HID1 VIS1 MGM1 FR1.
  assert (AG1 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M1).
  { apply (PNADC1.xagr_piece L ar C HI LY HIok E LKc (vcr E) A M (vml_of model) (vsp E - 256) XSCR Dph _ M M1 HH ltac:(clear - GSPT; lia) FR1).
    intros a [Wa|Wa]; [left; unfold XSCR; clear - Wa GSLO; lia| right; left; clear - Wa c_g1; lia]. }
  assert (DK1 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M1) by (intros a _ _ D; apply MGM1; exact D).
  assert (BASE1 : base_ok M1) by (exact (base_xagr E _ _ Dph M M1 BASE AG1 Dph_DX)).
  assert (ATX1 : HAJ.atexit_cells RSEGS M1 6896976 1148964 619876 1148964 687916 449180 hs).
  { apply (atx_agree M M1 hs ltac:(clear - HLEN; lia)); [| exact ATX]. intros i Hi. apply FR1; [clear - Hi; lia|]. intros [Wa|Wa]; [clear - Wa Hi GSLO GCEIL; lia| clear - Wa Hi G1 G2 c_g1; lia]. }
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M1 model1 HH1 ASTK1) as (_ & VIS1' & VIMG1 & _).
  assert (FC1 : forall a v, vsp E - 320 <= a -> a + 8 <= vsp E - 256 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 U. rewrite <- VIS1 in U. rewrite <- HID1 in U.
    exact (proj1 (L5A.u64_at_vis (ahid A model1) M1 a v (VIS1' a 8 ltac:(clear - Ha1 GSLO; lia) ltac:(clear - Ha2 GSHI GSPT; lia)) ltac:(clear - Ha1 GSLO GCEIL; lia) ltac:(clear - Ha2 GSHI GSPT; lia)) U). }
  apply FC1 in C312; [| clear; lia| clear; lia]. apply FC1 in C272; [| clear; lia| clear; lia]. apply FC1 in C304; [| clear; lia| clear; lia]. apply FC1 in C296; [| clear; lia| clear; lia].
  apply FC1 in C288; [| clear; lia| clear; lia]. apply FC1 in C280; [| clear; lia| clear; lia]. apply FC1 in C264; [| clear; lia| clear; lia].
  clear FC1 CG1 FRZ1 MS1 MG1 V0 V1 V2 V3 V4 V5 V6 VIS VIMG ZOBJ.
  (* [comment removed for export] *)
  assert (K1CH : keeps CH R R1) by (intros x Hx; apply KS1; apply c_KSa; do 3 right; exact Hx).
  apply (PNADC1.xstrlen L ar C IL HI LY HIok ICok ILY E X LKc fx1 R1 M1 model1 A 320 lit K 729728 buf HH1 AM1 ASTK1 BASE1 ltac:(clear; lia) ltac:(unfold XSCR; clear; lia) ltac:(reflexivity) A1r10).
  { rewrite (KS1 4%nat) by (apply c_KSa; do 4 right; left; reflexivity). exact RTP. }
  { exact A1r1. }
  { reflexivity. }
  { clear; lia. }
  { exact A1r2. }
  { exact LIN. }
  { exact L1. }
  { exact L2. }
  { clear - c_K; lia. }
  { exact c_buf. }
  { exact c_wend. }
  { exact c_nul. }
  { exact c_nnul. }
  intros R2 M2 model2 A2r10 RP2 HH2 AM2 RT2 ASTK2 AGs2 MGM2.
  assert (AG2 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M2).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M M1 M2 AG1). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M1 M2 AGs2); [unfold XSCR; intros x Hx; clear - Hx; lia| intros a []]. }
  assert (DK2 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M2) by (apply (PNADC1.xdkl_trans L ar E _ _ M M1 M2 DK1); intros a _ _ D; apply MGM2; exact D).
  assert (AGF2 : PNADC1.xagr L ar E (vsp E - 320) 2560 (fun a => obj <= a < obj + 24) M1 M2).
  { apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M1 M2 AGs2); [intros x Hx; clear - Hx; lia| intros a []]. }
  assert (BASE2 : base_ok M2) by (apply (base_xagr E _ _ _ M1 M2 BASE1 AGs2); intros a []).
  assert (K2CH : keeps CH R R2) by (apply (keeps_trans CH R R1 R2 K1CH); apply (keeps_cs CH R1 R2 RP2 CH_cs)).
  (* [comment removed for export] *)
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M2 model2 HH2 ASTK2) as ((_ & _ & _ & W3 & W4) & VIS2 & VIMG2 & ZOBJ2).
  destruct (ZOBJ2 obj 24 O1 O2 ltac:(clear; lia) O8 ltac:(reflexivity)) as (ZO2 & ZV2 & _). change (24 / 8) with 3 in ZO2, ZV2. rewrite <- c_sh in ZO2, ZV2.
  apply (proj2 (L5A.zeros_at_vis (ahid A model2) M2 sh 3 ZV2)) in ZO2.
  remember (mrestrict (ahid A model2) M2) as MV eqn:EMV.
  assert (W5 : L5.writable RSEGS MV obj 24) by (apply PNADC1.writable_img; [exact c_wobj| clear - O1; lia| clear; lia| clear - O2; lia]).
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (vsp E - 320)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact A1r2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 lit) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact A1r8).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 obj) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact A1r18).
  assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 21 RP2) by inl; exact A1r21).
  pose proof (PB fx1 R2 MV (fun j => match j with 2%nat => vsp E | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(assumption).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & A3r1 & A3r9 & A3r10 & A3r11 & A3r12 & A3r19 & CSZ).
  subst MV.
  apply (PNADC1.xpiece L ar C HI LY HIok E X LKc fx1 fx3 R2 R3 729728 0x78370 M2 model2 A M3v (fun a => 0 + obj <= a < 0 + obj + 1) HH2 AM2 ASTK2 MS3 MG3 FRZ3).
  { intros a Wa. right. unfold DXd. clear - Wa O1 O2. lia. }
  intros M3 model3 HH3 AM3 RT3 ASTK3 HID3 VIS3 MGM3 FR3.
  assert (AGp3 : forall sp' scr', PNADC1.xagr L ar E sp' scr' (fun a => obj <= a < obj + 24) M2 M3).
  { intros sp' scr'. apply (PNADC1.xagr_piece L ar C HI LY HIok E LKc (vcr E) A M2 (vml_of model2) sp' scr' _ _ M2 M3 HH2 ltac:(clear - GSPT; lia) FR3).
    intros a Wa. right. clear - Wa. lia. }
  assert (AG3 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M3).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M M2 M3 AG2). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M2 M3 (AGp3 (vsp E - 256) XSCR)); [intros x Hx; exact Hx| intros a Da; right; left; exact Da]. }
  assert (DK3 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M3) by (apply (PNADC1.xdkl_trans L ar E _ _ M M2 M3 DK2); intros a _ _ D; apply MGM3; exact D).
  assert (AGF3 : PNADC1.xagr L ar E (vsp E - 320) 2560 (fun a => obj <= a < obj + 24) M1 M3) by (exact (PNADC1.xagr_trans L ar E _ _ _ M1 M2 M3 AGF2 (AGp3 (vsp E - 320) 2560))).
  assert (BASE3 : base_ok M3).
  { apply (base_xagr E 0 0 _ M2 M3 BASE2 (AGp3 0 0)). intros a Da. left. unfold DXd. clear - Da O1 O2. lia. }
  assert (K3CH : keeps CH R R3) by (apply (keeps_trans CH R R2 R3 K2CH); intros x Hx; apply KS3; apply c_KSb; do 5 right; exact Hx).
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M3 model3 HH3 ASTK3) as (_ & _ & VIMG3 & _).
  assert (CSZ3 : L5.u8_at RSEGS M3 obj K2).
  { rewrite <- VIS3, <- HID3 in CSZ. exact (proj1 (L5A.u8_at_vis (ahid A model3) M3 obj K2 (VIMG3 obj 1 ltac:(clear - O1; lia) ltac:(clear - O2; lia)) ltac:(clear - O1; lia) ltac:(clear - O2; lia)) CSZ). }
  clear CSZ FRZ3 MS3 MG3 W3 W4 W5 ZO2 ZV2 VIS2 VIMG2 ZOBJ2.
  (* [comment removed for export] *)
  assert (C2 : getr R3 (reg 2) = Z_to_bv 64 (vsp E - 320)) by (rewrite (KS3 2%nat) by (apply c_KSb; left; reflexivity); exact B2).
  apply (PNADC1.xmemmove L ar C IL HI LY HIok ICok ILY E X LKc fx3 R3 M3 model3 A 320 obj1 lit K 729908 lit (K + 1) bs HH3 AM3 ASTK3 BASE3
           ltac:(clear; lia) ltac:(unfold XSCR; clear; lia) ltac:(reflexivity) A3r10 A3r11 A3r12).
  { rewrite (K3CH 4%nat) by (right; left; reflexivity). exact RTP. }
  { exact A3r1. }
  { reflexivity. }
  { clear; lia. }
  { exact C2. }
  { clear - O1 c_obj1; lia. }
  { clear - O2 c_obj1 c_K; lia. }
  { clear - c_K; lia. }
  { exact c_wobj1. }
  { exact LIN. }
  { clear; lia. }
  { clear; lia. }
  { exact c_bs. }
  intros R4 M4 model4 A4r10 RP4 HH4 AM4 RT4 ASTK4 AGm4 DKm4 DEF4.
  assert (OBD : forall a, obj1 <= a < obj1 + K -> obj <= a < obj + 24) by (intros a Ha; clear - Ha c_obj1 c_K; lia).
  assert (AG4 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M4).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M M3 M4 AG3). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M3 M4 AGm4); [unfold XSCR; intros x Hx; clear - Hx; lia| intros a Da; right; left; exact (OBD a Da)]. }
  assert (DK4 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M4).
  { apply (PNADC1.xdkl_trans L ar E _ _ M M3 M4 DK3). apply (PNADC1.xdkl_mono L ar E _ _ _ _ M3 M4 DKm4). unfold XSCR; intros x Hx; clear - Hx; lia. }
  assert (AGF4 : PNADC1.xagr L ar E (vsp E - 320) 2560 (fun a => obj <= a < obj + 24) M1 M4).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M1 M3 M4 AGF3). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M3 M4 AGm4); [intros x Hx; exact Hx| exact OBD]. }
  assert (BASE4 : base_ok M4).
  { apply (base_xagr E _ _ _ M3 M4 BASE3 AGm4). intros a Da. left. unfold DXd. apply OBD in Da. clear - Da O1 O2. lia. }
  assert (K4CH : keeps CH R R4) by (apply (keeps_trans CH R R3 R4 K3CH); apply (keeps_cs CH R3 R4 RP4 CH_cs)).
  assert (CSZ4 : L5.u8_at RSEGS M4 obj K2).
  { apply (L5C.u8_at_agree RSEGS M3 M4); [| clear - O1; lia| clear - O2; lia| exact CSZ3]. intros i Hi.
    apply (xagr_stat E _ _ _ M3 M4 i AGm4); [apply DX_dep; left; unfold DXd; clear - Hi O1 O2; lia| clear - Hi c_obj1; lia]. }
  (* [comment removed for export] *)
  assert (FC4 : forall a v, vsp E - 320 <= a -> a + 8 <= vsp E - 256 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid A model4) M4) a v).
  { intros a v Ha1 Ha2 U.
    destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M4 model4 HH4 ASTK4) as (_ & VIS4 & _).
    apply (proj2 (L5A.u64_at_vis (ahid A model4) M4 a v (VIS4 a 8 ltac:(clear - Ha1 GSLO; lia) ltac:(clear - Ha2 GSHI GSPT; lia)) ltac:(clear - Ha1 GSLO GCEIL; lia) ltac:(clear - Ha2 GSHI GSPT; lia))).
    apply (L5C.u64_at_agree RSEGS M1 M4); [| clear - Ha1 GSLO GCEIL; lia| clear - Ha2 GSHI GSPT; lia| exact U]. intros i Hi.
    apply (xagr_stk E _ _ _ M1 M4 i AGF4); [clear - Hi Ha1 GSLO GCEIL; lia| clear - Hi Ha1 Ha2 GSLO GSHI GSPT; lia| clear - Hi Ha1; lia| clear - Hi Ha1 O2 GSLO GCEIL; lia]. }
  apply FC4 in C312; [| clear; lia| clear; lia]. apply FC4 in C272; [| clear; lia| clear; lia]. apply FC4 in C304; [| clear; lia| clear; lia]. apply FC4 in C296; [| clear; lia| clear; lia].
  apply FC4 in C288; [| clear; lia| clear; lia]. apply FC4 in C280; [| clear; lia| clear; lia]. apply FC4 in C264; [| clear; lia| clear; lia].
  clear FC4.
  assert (ATX4 : HAJ.atexit_cells RSEGS M4 6896976 1148964 619876 1148964 687916 449180 hs).
  { apply (atx_agree M1 M4 hs ltac:(clear - HLEN; lia)); [| exact ATX1]. intros i Hi.
    apply (xagr_stat E _ _ _ M1 M4 i AGF4); [apply DX_dep; right; exact Hi| clear - Hi O2; lia]. }
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A M4 model4 HH4 ASTK4) as ((V0 & V1 & V2 & V3 & V4) & VIS4 & VIMG4 & ZOBJ4).
  destruct (ZOBJ4 obj 24 O1 O2 ltac:(clear; lia) O8 ltac:(reflexivity)) as (ZO4 & ZV4 & _). change (24 / 8) with 3 in ZO4, ZV4. rewrite <- c_sh in ZO4, ZV4.
  apply (proj2 (L5A.zeros_at_vis (ahid A model4) M4 sh 3 ZV4)) in ZO4.
  remember (mrestrict (ahid A model4) M4) as MV eqn:EMV.
  assert (W5 : L5.writable RSEGS MV obj 24) by (apply PNADC1.writable_img; [exact c_wobj| clear - O1; lia| clear; lia| clear - O2; lia]).
  assert (D2 : getr R4 (reg 2) = Z_to_bv 64 (vsp E - 320)) by (rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; exact C2).
  assert (D8 : getr R4 (reg 8) = Z_to_bv 64 lit) by (rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; rewrite (KS3 8%nat) by (apply c_KSb; right; left; reflexivity); exact B8).
  assert (D9 : getr R4 (reg 9) = Z_to_bv 64 K) by (rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; exact A3r9).
  assert (D18 : getr R4 (reg 18) = Z_to_bv 64 obj) by (rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; rewrite (KS3 18%nat) by (apply c_KSb; do 2 right; left; reflexivity); exact B18).
  assert (D19 : getr R4 (reg 19) = Z_to_bv 64 obj1) by (rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; exact A3r19).
  assert (D21 : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R3 R4 21 RP4) by inl; rewrite (KS3 21%nat) by (apply c_KSb; do 4 right; left; reflexivity); exact B21).
  pose proof (PC fx3 R4 MV (fun j => match j with 2%nat => vsp E | 18%nat => bv_unsigned (getr R (reg 18)) | 33%nat => vfirst E | 38%nat => bv_unsigned (getr R (reg 21)) | 50%nat => vF E | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(assumption).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & A5r1 & A5r2 & A5r8 & A5r9 & A5r10 & A5r11 & A5r12 & A5r18 & A5r19 & A5r20 & A5r21 & CNUL).
  subst MV.
  apply (PNADC1.xpiece L ar C HI LY HIok E X LKc fx3 fx5 R4 R5 729908 0x6da18 M4 model4 A M5v (fun a => 0 + objn <= a < 0 + objn + 1) HH4 AM4 ASTK4 MS5 MG5 FRZ5).
  { intros a Wa. right. unfold DXd. clear - Wa O1 O2 c_objn c_K. lia. }
  intros M5 model5 HH5 AM5 RT5 ASTK5 HID5 VIS5 MGM5 FR5.
  assert (AGp5 : forall sp' scr', PNADC1.xagr L ar E sp' scr' (fun a => obj <= a < obj + 24) M4 M5).
  { intros sp' scr'. apply (PNADC1.xagr_piece L ar C HI LY HIok E LKc (vcr E) A M4 (vml_of model4) sp' scr' _ _ M4 M5 HH4 ltac:(clear - GSPT; lia) FR5).
    intros a Wa. right. clear - Wa c_objn c_K. lia. }
  assert (AG5 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M5).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M M4 M5 AG4). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M4 M5 (AGp5 (vsp E - 256) XSCR)); [intros x Hx; exact Hx| intros a Da; right; left; exact Da]. }
  assert (DK5 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M5) by (apply (PNADC1.xdkl_trans L ar E _ _ M M4 M5 DK4); intros a _ _ D; apply MGM5; exact D).
  assert (BASE5 : base_ok M5).
  { apply (base_xagr E 0 0 _ M4 M5 BASE4 (AGp5 0 0)). intros a Da. left. unfold DXd. clear - Da O1 O2. lia. }
  assert (K5CH : keeps CH R R5) by (apply (keeps_trans CH R R4 R5 K4CH); intros x Hx; apply KS5; apply c_KSc; exact Hx).
  assert (CSZ5 : L5.u8_at RSEGS M5 obj K2).
  { apply (L5C.u8_at_agree RSEGS M4 M5); [| clear - O1; lia| clear - O2; lia| exact CSZ4]. intros i Hi. apply FR5; [clear - Hi O1 O2; lia| clear - Hi c_objn c_K; lia]. }
  assert (DEF5 : L5.defined M5 obj1 K) by (exact (L5.defined_grows M4 M5 _ _ MGM5 DEF4)).
  assert (ATX5 : HAJ.atexit_cells RSEGS M5 6896976 1148964 619876 1148964 687916 449180 hs).
  { apply (atx_agree M4 M5 hs ltac:(clear - HLEN; lia)); [| exact ATX4]. intros i Hi. apply FR5; [clear - Hi; lia| clear - Hi O2 c_objn c_K; lia]. }
  clear CNUL FRZ5 MS5 MG5 V0 V1 V2 V3 V4 W5 ZO4 ZV4 VIS4 VIMG4 ZOBJ4 C312 C272 C304 C296 C288 C280 C264.
  (* [comment removed for export] *)
  apply (PNADC1.xatexit L ar C HI LY HIok E X EXT LKc fx5 R5 M5 model5 A 874172 obj 1282768 raC hs HH5 AM5 ASTK5 BASE5 A5r10 A5r11 A5r12).
  { rewrite (K5CH 4%nat) by (right; left; reflexivity). exact RTP. }
  { exact A5r1. }
  { exact RC2. }
  { exact RC3. }
  { exact A5r2. }
  { exact HLEN. }
  { exact ATX5. }
  intros fx6 R6 M6 model6 A6 RP6 HH6 AM6 RT6 IA6 ASTK6 AGa6 DKa6 ATX6.
  assert (AG6 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M M6).
  { apply (PNADC1.xagr_trans L ar E _ _ _ M M5 M6 AG5). apply (PNADC1.xagr_mono L ar E _ _ _ _ _ _ M5 M6 AGa6); [unfold XSCR; intros x Hx; clear - Hx; lia| intros a Da; right; right; exact Da]. }
  assert (DK6 : PNADC1.xdkl L ar E (vsp E - 256) XSCR M M6).
  { apply (PNADC1.xdkl_trans L ar E _ _ M M5 M6 DK5). apply (PNADC1.xdkl_mono L ar E _ _ _ _ M5 M6 DKa6). unfold XSCR; intros x Hx; clear - Hx; lia. }
  assert (BASE6 : base_ok M6) by (apply (base_xagr E _ _ _ M5 M6 BASE5 AGa6); intros a Da; right; exact Da).
  assert (CSZ6 : L5.u8_at RSEGS M6 obj K2).
  { apply (L5C.u8_at_agree RSEGS M5 M6); [| clear - O1; lia| clear - O2; lia| exact CSZ5]. intros i Hi.
    apply (xagr_stat E _ _ _ M5 M6 i AGa6); [apply DX_dep; left; unfold DXd; clear - Hi O1 O2; lia| unfold DXa; clear - Hi O2; lia]. }
  assert (DEF6 : L5.defined M6 obj1 K).
  { intros i Hi. apply DKa6; [clear - Hi O1 O2 c_obj1 c_K; lia| | exact (DEF5 i Hi)].
    apply (PNADC1.dep_client L ar C LY). apply DX_dep. left. unfold DXd. clear - Hi O1 O2 c_obj1 c_K. lia. }
  (* [comment removed for export] *)
  rewrite RC1 in *.
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A6 M6 model6 HH6 ASTK6) as ((_ & _ & _ & V3 & _) & VIS6 & VIMG6 & _).
  remember (mrestrict (ahid A6 model6) M6) as MV eqn:EMV.
  assert (V6 : L5.writable RSEGS MV g 2) by (apply PNADC1.writable_img; [exact c_wg| clear - G1; lia| clear; lia| clear - G2; lia]).
  assert (E2 : getr R6 (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite (L5SAR.cs_of_preserved R5 R6 2 RP6) by inl; exact A5r2).
  assert (E8 : getr R6 (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite (L5SAR.cs_of_preserved R5 R6 8 RP6) by inl; exact A5r8).
  assert (E9 : getr R6 (reg 9) = Z_to_bv 64 (vsp E - 256)) by (rewrite (L5SAR.cs_of_preserved R5 R6 9 RP6) by inl; exact A5r9).
  assert (E19 : getr R6 (reg 19) = Z_to_bv 64 PNADD.SBv) by (rewrite (L5SAR.cs_of_preserved R5 R6 19 RP6) by inl; exact A5r19).
  assert (E20 : getr R6 (reg 20) = Z_to_bv 64 (vfirst E)) by (rewrite (L5SAR.cs_of_preserved R5 R6 20 RP6) by inl; exact A5r20).
  assert (E21 : getr R6 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (rewrite (L5SAR.cs_of_preserved R5 R6 21 RP6) by inl; exact A5r21).
  assert (K6CH : keeps CH R R6) by (apply (keeps_trans CH R R5 R6 K5CH); apply (keeps_cs CH R5 R6 RP6 CH_cs)).
  assert (E23 : getr R6 (reg 23) = Z_to_bv 64 (vF E / 8 + PNADD.SBv)) by (rewrite (K6CH 23%nat) by (do 2 right; left; reflexivity); exact Q23).
  assert (E24 : getr R6 (reg 24) = Z_to_bv 64 (vvp E)) by (rewrite (K6CH 24%nat) by (do 3 right; left; reflexivity); exact Q24).
  assert (E26 : getr R6 (reg 26) = Z_to_bv 64 (vF E)) by (rewrite (K6CH 26%nat) by (do 4 right; left; reflexivity); exact Q26).
  assert (E27 : getr R6 (reg 27) = Z_to_bv 64 (vF E)) by (rewrite (K6CH 27%nat) by (do 5 right; left; reflexivity); exact Q27).
  unfold PNADD.SBv in E19, E23.
  pose proof (PD fx6 R6 MV (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 34%nat => vvp E | 38%nat => bv_unsigned (getr R (reg 21)) | 50%nat => vF E | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(assumption).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & A7r1 & A7r10 & A7r11 & CG0 & CG1).
  subst MV.
  apply (PNADC1.xpiece L ar C HI LY HIok E X LKc fx6 fx7 R6 R7 pcD pcE M6 model6 A6 M7v (fun a => 0 + g <= a < 0 + g + 2) HH6 AM6 ASTK6 MS7 MG7 FRZ7).
  { intros a Wa. right. unfold DXd. clear - Wa G1 G2. lia. }
  intros M7 model7 HH7 AM7 RT7 ASTK7 HID7 VIS7 MGM7 FR7.
  assert (AGp7 : PNADC1.xagr L ar E (vsp E - 256) XSCR Dph M6 M7).
  { apply (PNADC1.xagr_piece L ar C HI LY HIok E LKc (vcr E) A6 M6 (vml_of model6) (vsp E - 256) XSCR _ _ M6 M7 HH6 ltac:(clear - GSPT; lia) FR7).
    intros a Wa. right. left. clear - Wa. lia. }
  destruct (PNADC1.xview L ar C IL HI LY HIok ICok ILY E X LKc A6 M7 model7 HH7 ASTK7) as (_ & _ & VIMG7 & _).
  apply (KONT fx7 R7 M7 model7 A6 HH7 AM7).
  - eapply L5LZ.model_rt_trans; [| exact RT7]. eapply L5LZ.model_rt_trans; [| exact RT6]. eapply L5LZ.model_rt_trans; [| exact RT5].
    eapply L5LZ.model_rt_trans; [| exact RT4]. eapply L5LZ.model_rt_trans; [| exact RT3]. eapply L5LZ.model_rt_trans; [exact RT1| exact RT2].
  - exact IA6.
  - exact ASTK7.
  - apply (base_xagr E _ _ _ M6 M7 BASE6 AGp7 Dph_DX).
  - assert (K7 : keeps CS R6 R7) by (intros x Hx; apply KS7; apply c_KSd; exact Hx).
    unfold PNADE.rgd, PNADD.RBA, PNADD.SH, PNADD.SBv.
    rewrite (K7 2%nat), (K7 3%nat), (K7 4%nat), (K7 8%nat), (K7 9%nat), (K7 19%nat), (K7 20%nat), (K7 23%nat), (K7 24%nat), (K7 26%nat), (K7 27%nat) by inl.
    rewrite (K6CH 3%nat) by (left; reflexivity). rewrite (K6CH 4%nat) by (right; left; reflexivity).
    repeat split; assumption.
  - exact (PNADC1.xagr_trans L ar E _ _ _ M M6 M7 AG6 AGp7).
  - apply (PNADC1.xdkl_trans L ar E _ _ M M6 M7 DK6). intros a _ _ D. apply MGM7. exact D.
  - rewrite <- VIS7, <- HID7 in CG0.
    exact (proj1 (L5A.u8_at_vis (ahid A6 model7) M7 g 1 (VIMG7 g 1 ltac:(clear - G1; lia) ltac:(clear - G2; lia)) ltac:(clear - G1; lia) ltac:(clear - G2; lia)) CG0).
  - split.
    + rewrite <- c_K2. apply (L5C.u8_at_agree RSEGS M6 M7); [| clear - O1; lia| clear - O2; lia| exact CSZ6]. intros i Hi. apply FR7; [clear - Hi O1 O2; lia| clear - Hi c_gobj; lia].
    + rewrite <- c_obj1. exact (L5.defined_grows M6 M7 _ _ MGM7 DEF6).
  - apply (atx_agree M6 M7 (hs ++ [(874172, obj)])); [rewrite length_app; cbn [length]; clear - HLEN; lia| | exact ATX6].
    intros i Hi. apply FR7; [clear - Hi; lia| clear - Hi G2; lia].
Qed.

End Phase.

Definition buf_inf : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 145632) 16 with Some l => l | None => [] end).
Definition bs_inf : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 145632) 8 with Some l => l | None => [] end).
Definition buf_nan : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 145664) 8 with Some l => l | None => [] end).
Definition bs_nan : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 145664) 3 with Some l => l | None => [] end).
Lemma buf_inf_ok : rdn RSEGS (fun _ => None) (Z_to_bv 64 145632) (length buf_inf) = Some buf_inf. Proof. vm_compute. reflexivity. Qed.
Lemma bs_inf_ok : rdn RSEGS (fun _ => None) (Z_to_bv 64 145632) (Z.to_nat 8) = Some bs_inf. Proof. vm_compute. reflexivity. Qed.
Lemma buf_nan_ok : rdn RSEGS (fun _ => None) (Z_to_bv 64 145664) (length buf_nan) = Some buf_nan. Proof. vm_compute. reflexivity. Qed.
Lemma bs_nan_ok : rdn RSEGS (fun _ => None) (Z_to_bv 64 145664) (Z.to_nat 3) = Some bs_nan. Proof. vm_compute. reflexivity. Qed.
Lemma buf_inf_len : length buf_inf = 16%nat. Proof. vm_compute. reflexivity. Qed.
Lemma buf_nan_len : length buf_nan = 8%nat. Proof. vm_compute. reflexivity. Qed.
Lemma buf_inf_nul : nth (Z.to_nat 8) buf_inf (Z_to_bv 8 0) = Z_to_bv 8 0. Proof. vm_compute. reflexivity. Qed.
Lemma buf_nan_nul : nth (Z.to_nat 3) buf_nan (Z_to_bv 8 0) = Z_to_bv 8 0. Proof. vm_compute. reflexivity. Qed.
Lemma buf_inf_nn : forall j, (j < Z.to_nat 8)%nat -> nth j buf_inf (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof. intros j Hj. change (Z.to_nat 8) with 8%nat in Hj. do 8 (destruct j as [|j]; [intros Q; apply (f_equal bv_unsigned) in Q; vm_compute in Q; discriminate Q|]). exfalso. clear - Hj. lia. Qed.
Lemma buf_nan_nn : forall j, (j < Z.to_nat 3)%nat -> nth j buf_nan (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof. intros j Hj. change (Z.to_nat 3) with 3%nat in Hj. do 3 (destruct j as [|j]; [intros Q; apply (f_equal bv_unsigned) in Q; vm_compute in Q; discriminate Q|]). exfalso. clear - Hj. lia. Qed.
Lemma wseg_cold : StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759136) (Z.to_nat 2) = true /\ StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759112) (Z.to_nat 24) = true
  /\ StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759113) (Z.to_nat 8) = true /\ StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759168) (Z.to_nat 2) = true
  /\ StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759144) (Z.to_nat 24) = true /\ StreamSim.wseg_ok RSEGS (Z_to_bv 64 6759145) (Z.to_nat 3) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lit_i_in : In (145632, 8 + 1) (icl_globals IL) /\ 65536 <= 145632 /\ 145632 + Z.of_nat (length buf_inf) <= 1282048.
Proof. split; [rewrite (aicl_globals IL ILY); do 20 right; left; reflexivity| rewrite buf_inf_len; clear; lia]. Qed.
Lemma c_i_g : 6759112 <= 6759136 /\ 6759136 + 8 <= 6759176. Proof. clear; lia. Qed.
Lemma c_i_obj : 6759112 <= 6759112 /\ 6759112 + 24 <= 6759176 /\ 6759112 mod 8 = 0. Proof. clear; split; [lia| split; [lia| reflexivity]]. Qed.
Lemma c_i_K : 0 < 8 <= 22. Proof. clear; lia. Qed.
Lemma c_i_gobj : 6759136 + 8 <= 6759112 \/ 6759112 + 24 <= 6759136. Proof. clear; lia. Qed.
Lemma c_i_wend : (145632 + 8) / 8 * 8 + 8 <= 145632 + Z.of_nat (length buf_inf). Proof. rewrite buf_inf_len. vm_compute. discriminate. Qed.
Lemma c_i_raC : 740172 = 0xb4b4c /\ 740172 mod 2 = 0 /\ 0 <= 740172 < 2 ^ 64. Proof. clear; split; [reflexivity| split; [reflexivity| lia]]. Qed.
Lemma c_i_KSa : forall x, In x (9 :: 19 :: 20 :: CH)%nat -> In x PNADP8.KS_adkYIa. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_i_KSb : forall x, In x (2 :: 8 :: 18 :: 20 :: 21 :: CH)%nat -> In x PNADP8.KS_adkYIb. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_i_KSc : forall x, In x CH -> In x PNADP8.KS_adkYIc. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_i_KSd : forall x, In x CS -> In x PNADP8.KS_adkYId. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Definition phase_inf :=
  phase 0xb3fac 0xb4b4c 0xb3fbc 145632 6759112 6759113 6759121 6759136 6759137 6759144 740144 740172 740184 2148295769 8 16
    PNADP8.KS_adkYIa PNADP8.KS_adkYIb PNADP8.KS_adkYIc PNADP8.KS_adkYId
    PNADP8.adkYIa_conc PNADP8.adkYIb_conc PNADP8.adkYIc_conc PNADP8.adkYId_conc buf_inf bs_inf
    eq_refl eq_refl eq_refl eq_refl eq_refl c_i_g c_i_obj c_i_K c_i_gobj
    lit_i_in buf_inf_ok c_i_wend buf_inf_nul buf_inf_nn bs_inf_ok c_i_raC
    (proj1 wseg_cold) (proj1 (proj2 wseg_cold)) (proj1 (proj2 (proj2 wseg_cold)))
    c_i_KSa c_i_KSb c_i_KSc c_i_KSd.
Lemma lit_n_in : In (145664, 3 + 1) (icl_globals IL) /\ 65536 <= 145664 /\ 145664 + Z.of_nat (length buf_nan) <= 1282048.
Proof. split; [rewrite (aicl_globals IL ILY); do 21 right; left; reflexivity| rewrite buf_nan_len; clear; lia]. Qed.
Lemma c_n_g : 6759112 <= 6759168 /\ 6759168 + 8 <= 6759176. Proof. clear; lia. Qed.
Lemma c_n_obj : 6759112 <= 6759144 /\ 6759144 + 24 <= 6759176 /\ 6759144 mod 8 = 0. Proof. clear; split; [lia| split; [lia| reflexivity]]. Qed.
Lemma c_n_K : 0 < 3 <= 22. Proof. clear; lia. Qed.
Lemma c_n_gobj : 6759168 + 8 <= 6759144 \/ 6759144 + 24 <= 6759168. Proof. clear; lia. Qed.
Lemma c_n_wend : (145664 + 3) / 8 * 8 + 8 <= 145664 + Z.of_nat (length buf_nan). Proof. rewrite buf_nan_len. vm_compute. discriminate. Qed.
Lemma c_n_raC : 740256 = 0xb4ba0 /\ 740256 mod 2 = 0 /\ 0 <= 740256 < 2 ^ 64. Proof. clear; split; [reflexivity| split; [reflexivity| lia]]. Qed.
Lemma c_n_KSa : forall x, In x (9 :: 19 :: 20 :: CH)%nat -> In x PNADP8.KS_adkYNa. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_n_KSb : forall x, In x (2 :: 8 :: 18 :: 20 :: 21 :: CH)%nat -> In x PNADP8.KS_adkYNb. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_n_KSc : forall x, In x CH -> In x PNADP8.KS_adkYNc. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Lemma c_n_KSd : forall x, In x CS -> In x PNADP8.KS_adkYNd. Proof. apply L5K.incl_b; vm_compute; reflexivity. Qed.
Definition phase_nan :=
  phase 0xb3fbc 0xb4ba0 0xb3fcc 145664 6759144 6759145 6759148 6759168 6759169 6759176 740228 740256 740268 2148295773 3 6
    PNADP8.KS_adkYNa PNADP8.KS_adkYNb PNADP8.KS_adkYNc PNADP8.KS_adkYNd
    PNADP8.adkYNa_conc PNADP8.adkYNb_conc PNADP8.adkYNc_conc PNADP8.adkYNd_conc buf_nan bs_nan
    eq_refl eq_refl eq_refl eq_refl eq_refl c_n_g c_n_obj c_n_K c_n_gobj
    lit_n_in buf_nan_ok c_n_wend buf_nan_nul buf_nan_nn bs_nan_ok c_n_raC
    (proj1 (proj2 (proj2 (proj2 wseg_cold)))) (proj1 (proj2 (proj2 (proj2 (proj2 wseg_cold))))) (proj2 (proj2 (proj2 (proj2 (proj2 wseg_cold)))))
    c_n_KSa c_n_KSb c_n_KSc c_n_KSd.

End WithHeap.
End SCFG_1.
End PNADC2.
