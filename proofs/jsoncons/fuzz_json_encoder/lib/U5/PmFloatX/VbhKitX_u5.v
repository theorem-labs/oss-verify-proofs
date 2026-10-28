(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncKit2_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBHK.
Import PML. Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation agree := (L5C.agree_on).

Lemma enc_objx_agree_d : forall (M M' : mem) V S2 dI dD dD', 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_STACK -> agree M M' (V + O_INDENT) 8 -> agree M M' (V + O_COLON) (O_DEPTH - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  u32 M' (V + O_DEPTH) dD' ->
  PMES2.enc_objx M V S2 dI dD -> PMES2.enc_objx M' V S2 dI dD'.
Proof.
  intros M M' V S2 dI dD dD' HV HV2 A1 AI A2 Hcol HD H. unfold PMES2.enc_objx, sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT, O_NL_CHARS,
    O_COMMON_VPTR, O_ENABLE, O_MAX_DEPTH, O_INDENT_CHAR, O_FP, O_INDENT, O_COMMA, O_OBRACE, O_CBRACE, O_OBRACKET, O_CBRACKET, O_DEPTH, O_STACK in *.
  assert (X8 : forall a v, V <= a -> a + 8 <= V + 264 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply EK.u64_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X4 : forall a v, V <= a -> a + 4 <= V + 264 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply EK.u32_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X1 : forall a v, V <= a -> a + 1 <= V + 264 -> u8 M a v -> u8 M' a v).
  { intros a v H1 H2. apply EK.u8_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (Y8 : forall a v, V + 304 <= a -> a + 8 <= V + 400 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply EK.u64_agree; [apply (EK.agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
  destruct H as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                 H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & (H29 & H29') & (H30 & H30') & (H31 & H31') & (H32 & H32')).
  split; [replace V with (V + 0) by lia; apply X8; [lia | lia | replace (V + 0) with V by lia; exact H1]|].
  split; [apply X8; [lia | lia | exact H2]|]. split; [apply X8; [lia | lia | exact H3]|].
  split; [exists fl; split; [apply X1; [lia | lia | exact H4] | exact H4']|].
  split; [apply X1; [lia | lia | exact H5]|].
  split; [apply X1; [lia | lia | exact H6]|]. split; [apply X1; [lia | lia | exact H7]|]. split; [apply X1; [lia | lia | exact H8]|].
  split; [apply X1; [lia | lia | exact H9]|]. split; [apply X1; [lia | lia | exact H10]|].
  split; [apply X1; [lia | lia | exact H11]|]. split; [apply X8; [lia | lia | exact H12]|].
  split; [apply X8; [lia | lia | exact H13]|]. split; [apply X8; [lia | lia | exact H14]|]. split; [apply X8; [lia | lia | exact H15]|].
  split; [apply (L5C.defined_agree M M' _ _); [apply (EK.agree_sub M M' _ _ _ _ A1); lia | exact H16]|].
  split; [apply X8; [lia | lia | exact H17]|].
  split; [exists en; split; [apply X1; [lia | lia | exact H18] | split; [exact (proj1 H18') | apply (L5C.defined_agree M M' _ _); [apply (EK.agree_sub M M' _ _ _ _ A1); lia | exact (proj2 H18')]]]|].
  split; [apply X4; [lia | lia | exact H19]|]. split; [apply X1; [lia | lia | exact H20]|].
  split; [apply X1; [lia | lia | exact H21]|]. split; [apply X4; [lia | lia | exact H22]|].
  split; [exists dp; apply X1; [lia | lia | exact H23]|].
  split; [apply (EK.u32_agree M M'); [apply (EK.agree_sub _ _ _ _ _ _ AI); lia | lia | lia | exact H24]|]. split; [exact Hcol|]. split; [exact HD|].
  split; [split; [apply Y8; [lia | lia | exact H27] | apply Y8; [lia | lia | exact H27']]|].
  split; [split; [apply Y8; [lia | lia | exact H28] | apply Y8; [lia | lia | exact H28']]|].
  split; [split; [apply Y8; [lia | lia | exact H29] | apply Y8; [lia | lia | exact H29']]|].
  split; [split; [apply Y8; [lia | lia | exact H30] | apply Y8; [lia | lia | exact H30']]|].
  split; [split; [apply Y8; [lia | lia | exact H31] | apply Y8; [lia | lia | exact H31']]|].
  split; [apply Y8; [lia | lia | exact H32] | apply Y8; [lia | lia | exact H32']].
Qed.

Lemma hpres_mono : forall (L : heap_layout) LB LB' sp scr W W' (M M' : mem),
  (forall b, In b LB' -> In b LB) -> (forall a, L5.outside W' a -> L5.outside W a) ->
  L5C.hpres L LB sp scr W M M' -> L5C.hpres L LB' sp scr W' M M'.
Proof.
  intros L LB LB' sp scr W W' M M' HLB HW (HP1 & HP2 & HP3).
  assert (CL : forall a, client_addr L LB' sp scr a -> client_addr L LB sp scr a).
  { intros a [(b & Hb & Hr)|[C|C]]; [left; exists b; split; [apply HLB; exact Hb | exact Hr] | right; left; exact C | right; right; exact C]. }
  split; [|split; [exact HP2|]].
  - intros a (K1 & K2 & K3 & K4). apply HP1. split; [exact K1|]. split; [apply CL; exact K2|]. split; [exact K3 | apply HW; exact K4].
  - intros a Ha HC HE Hd. apply (HP3 a Ha (CL a HC) HE Hd).
Qed.

Lemma kv_st_nonneg : forall capb, 0 <= kv_st capb.
Proof. intros capb. unfold kv_st. destruct (capb =? 0); [lia | apply Z.log2_nonneg]. Qed.

(* [comment removed for export] *)
Lemma stack_at_setnla : forall (M M' : mem) V c r b capb, 0 <= b -> b + capb <= 2 ^ 64 -> 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' (V + O_STACK) 24 ->
  (forall a n, b <= a -> a + n <= b + capb -> (a + n <= b + 32 * depth r + 6 \/ b + 32 * depth r + 7 <= a) -> agree M M' a n) ->
  u8 M' (b + 32 * depth r + 6) 1 -> L5.defined M' (b + 32 * depth r + 6) 1 ->
  stack_at M V (c :: r) b capb -> stack_at M' V (set_nla c :: r) b capb.
Proof.
  intros M M' V c r b capb HB HBC HV HVE AP AB N6 D6 (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, ENC_SIZE, O_STACK in *.
  assert (DEQ : depth (set_nla c :: r) = depth (c :: r)) by reflexivity. rewrite DEQ.
  pose proof (EK2.depth_cons c r) as DC. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [apply (EK.u64_agree M M'); [apply (EK.agree_sub M M' _ _ _ _ AP); lia | lia | lia | exact S1]|].
  split; [apply (EK.u64_agree M M'); [apply (EK.agree_sub M M' _ _ _ _ AP); lia | lia | lia | exact S2]|].
  split; [apply (EK.u64_agree M M'); [apply (EK.agree_sub M M' _ _ _ _ AP); lia | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *. specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (S (length r) - 1 - length r)%nat with 0%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (EA : b + 32 * Z.of_nat (length r) = b + 32 * depth r) by (unfold depth; lia). rewrite EA in S6 |- *.
    destruct S6 as (C1 & C2 & C3 & C4 & C5 & C6). unfold ctx_at. cbn [ec_arr ec_nla ec_count set_nla].
    assert (ROOM : b + 32 * depth r + 32 <= b + capb) by (rewrite DC in S4; lia).
    split; [apply (EK.u32_agree M M'); [apply AB; lia | lia | lia | exact C1]|].
    split; [apply (EK.u8_agree M M'); [apply AB; lia | lia | lia | exact C2]|].
    split; [exact N6|].
    split; [apply (EK.u64_agree M M'); [apply AB; lia | lia | lia | exact C4]|].
    split; [exact C5|].
    intros j Hj. destruct (Z.eq_dec j 6) as [->|Hj6].
    + replace (b + 32 * depth r + 6) with (b + 32 * depth r + 6 + 0) by lia. apply D6. lia.
    + rewrite (AB (b + 32 * depth r + j) 1 ltac:(lia) ltac:(lia) ltac:(lia) (b + 32 * depth r + j) ltac:(lia)). apply C6. exact Hj.
  - assert (Hlt : (i < length r)%nat) by lia. assert (HiR : Z.of_nat i + 1 <= depth r) by (unfold depth; lia). rewrite DC in S4.
    replace (nth (S (length r) - 1 - i) (set_nla c :: r) ctx0) with (nth (S (length r) - 1 - i) (c :: r) ctx0).
    2: { replace (S (length r) - 1 - i)%nat with (S (length r - 1 - i))%nat by lia. reflexivity. }
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | | exact S6].
    apply AB; [lia | lia | left; lia].
Qed.

(* [comment removed for export] *)
Lemma stack_at_top_cells : forall (M M' : mem) V c c' r b capb,
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * depth (c :: r)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  (forall i, (i < length r)%nat -> ctx_at M' (b + 32 * Z.of_nat i) (nth (length r - 1 - i) r ctx0)) ->
  ctx_at M' (b + 32 * depth r) c' ->
  stack_at M V (c :: r) b capb -> stack_at M' V (c' :: r) b capb.
Proof.
  intros M M' V c c' r b capb P1 P2 P3 LOW TOP (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at.
  assert (DEQ : depth (c' :: r) = depth (c :: r)) by reflexivity. rewrite DEQ.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact S4|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *. destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. replace (32 * Z.of_nat (length r)) with (32 * depth r) by (unfold depth; lia). exact TOP.
  - replace (S (length r) - 1 - i)%nat with (S (length r - 1 - i))%nat by lia. cbn [nth]. apply LOW. lia.
Qed.

(* [comment removed for export] *)
Lemma hpres_rebase : forall (L : heap_layout) LBk sp k scr W (M M' : mem),
  0 <= k -> 0 <= scr -> L5.defined M (sp - k) k -> 0 <= sp - k - scr -> hl_errno L + 4 <= sp - k - scr -> hl_ceil L <= sp - k - scr -> sp < 2 ^ 64 ->
  L5C.hpres L LBk (sp - k) scr W M M' -> L5C.hpres L LBk sp (k + scr) W M M'.
Proof.
  intros L LBk sp k scr W M M' Hk Hs Hdef H0 He Hc Hsp HP. apply L5C.hpres_intro.
  - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). split; [exact K1|]. split; [|split; assumption].
    destruct K2 as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C].
  - intros j Hj. destruct (Z_lt_dec j scr) as [Hlo|Hhi].
    + replace (sp - (k + scr) + j) with (sp - k - scr + j) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP). lia.
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - (k + scr) + j) HP); [lia | right; left; split; lia | unfold in_errno; lia |].
      replace (sp - (k + scr) + j) with (sp - k + (j - scr)) by lia. apply Hdef. lia.
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [|exact HE | exact Hd].
    destruct HC as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C].
Qed.

Lemma model_ok_but_vm : forall m m', model_ok m -> model_but_vm m m' -> model_ok m'.
Proof.
  intros m m' (A & B & C) H. unfold model_ok. rewrite (L5C.halted_but_vm _ _ H), (L5C.lazy_but_vm _ _ H), (L5C.materialized_but_vm _ _ H). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma lb_drop_mid : forall LBo rep X, List.NoDup (map fst (LBo ++ srep_blocks rep ++ X)) -> lb_drop rep (LBo ++ srep_blocks rep ++ X) = LBo ++ X.
Proof.
  intros LBo rep X Hnd. destruct rep as [s|cap p s]; cbn [lb_drop srep_blocks app] in *; [reflexivity|].
  rewrite EK.lb_remove_app.
  - cbn [lb_remove app fst]. rewrite Z.eqb_refl. reflexivity.
  - rewrite map_app in Hnd. intros Hin. apply (EK.nodup_app_l _ _ p Hnd); [|exact Hin]. cbn [map app fst]. left. reflexivity.
Qed.

End VBHK.
