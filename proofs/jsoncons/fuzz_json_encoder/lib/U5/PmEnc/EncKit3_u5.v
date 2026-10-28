(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSound LibSym. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncKit2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmEncSpecs2_u5.
Import ListNotations.
Import PML.
Import PMES.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module EK3.
Abbreviation mem := (word -> option byte).
Abbreviation agree := (L5C.agree_on).

(* [comment removed for export] *)
Definition inv_d (M : mem) (V S2 : Z) (g : eghost) (d : Z) : Prop :=
  enc_obj M V S2 d /\ stack_at M V (g_es g) (g_sb g) (g_scap g) /\ sink_at M S2 (g_rep g) /\ len (srep_chars (g_rep g)) = g_len g /\ depth (g_es g) <= MAX_DEPTH.
Lemma inv_d_of : forall (M : mem) V S2 g, enc_inv M V S2 g -> inv_d M V S2 g (depth (g_es g)).
Proof. intros M V S2 g H. exact H. Qed.
Lemma inv_of_d : forall (M : mem) V S2 g, inv_d M V S2 g (depth (g_es g)) -> enc_inv M V S2 g.
Proof. intros M V S2 g H. exact H. Qed.

(* [comment removed for export] *)
Lemma enc_obj_agree_d : forall (M M' : mem) V S2 d d', 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_STACK -> agree M M' (V + O_COLON) (O_DEPTH - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  u32 M' (V + O_INDENT) (4 * d') -> u32 M' (V + O_DEPTH) d' ->
  enc_obj M V S2 d -> enc_obj M' V S2 d'.
Proof.
  intros M M' V S2 d d' HV HV2 A1 A2 Hcol HI HD H. unfold enc_obj, sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT, O_NL_CHARS,
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
  split; [exact HI|]. split; [exact Hcol|]. split; [exact HD|].
  repeat split; apply Y8; try lia; assumption.
Qed.

(* [comment removed for export] *)
Lemma stack_at_frame : forall (M M' : mem) V es es' b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * depth es') -> u64 M' (V + O_STACK + 16) (b + capb) ->
  (exists top, es = top ++ es') -> agree M M' b (32 * depth es') ->
  stack_at M V es b capb -> stack_at M' V es' b capb.
Proof.
  intros M M' V es es' b capb HV HV2 HB HB2 P1 P2 P3 (top & ->) AG (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at.
  assert (DL : depth (top ++ es') = depth top + depth es') by (unfold depth; rewrite length_app, Nat2Z.inj_add; reflexivity).
  assert (D0 : 0 <= depth top) by (unfold depth; lia). assert (D1 : 0 <= depth es') by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. specialize (S6 i ltac:(rewrite length_app; lia)).
  rewrite length_app in S6. replace (length top + length es' - 1 - i)%nat with (length top + (length es' - 1 - i))%nat in S6 by lia. rewrite app_nth2_plus in S6.
  apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | unfold depth in *; lia | | exact S6].
  apply (EK.agree_sub M M' _ _ _ _ AG); unfold depth in *; lia.
Qed.

(* [comment removed for export] *)
Lemma stack_head : forall (M : mem) V c r b capb, stack_at M V (c :: r) b capb -> ctx_at M (b + 32 * depth r) c.
Proof.
  intros M V c r b capb (_ & _ & _ & _ & _ & S6). pose proof (S6 (length r) ltac:(cbn [length]; lia)) as HC. cbn [length] in HC.
  replace (S (length r) - 1 - length r)%nat with 0%nat in HC by lia. cbn [nth] in HC. exact HC.
Qed.
(* [comment removed for export] *)
Lemma stack_second : forall (M : mem) V c c2 r b capb, stack_at M V (c :: c2 :: r) b capb -> ctx_at M (b + 32 * depth r) c2.
Proof.
  intros M V c c2 r b capb (_ & _ & _ & _ & _ & S6). pose proof (S6 (length r) ltac:(cbn [length]; lia)) as HC. cbn [length] in HC.
  replace (S (S (length r)) - 1 - length r)%nat with 1%nat in HC by lia. cbn [nth] in HC. exact HC.
Qed.
(* [comment removed for export] *)
Lemma stack_at_pop1 : forall (M M' : mem) V c c2 c2' r b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 1)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> ctx_at M' (b + 32 * depth r) c2' ->
  stack_at M V (c :: c2 :: r) b capb -> stack_at M' V (c2' :: r) b capb.
Proof.
  intros M M' V c c2 c2' r b capb HV HV2 HB HB2 P1 P2 P3 AG Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, ENC_SIZE, O_STACK in *.
  rewrite !EK2.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (S (S (length r)) - 1 - i)%nat with (S (S (length r - 1 - i)))%nat in S6 by lia. cbn [nth] in S6.
    replace (S (length r) - 1 - i)%nat with (S (length r - 1 - i))%nat by lia. cbn [nth].
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma stack_at_pop0 : forall (M M' : mem) V c b capb,
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) b -> u64 M' (V + O_STACK + 16) (b + capb) ->
  stack_at M V [c] b capb -> stack_at M' V [] b capb.
Proof.
  intros M M' V c b capb P1 P2 P3 (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at. unfold depth in *. cbn [length Z.of_nat] in *.
  split; [exact P1|]. split; [rewrite Z.mul_0_r, Z.add_0_r; exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi. lia.
Qed.
(* [comment removed for export] *)
Lemma stack_at_mid : forall (M M' : mem) V c c2 c2' r b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 2)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> ctx_at M' (b + 32 * depth r) c2' -> agree M M' (b + 32 * (depth r + 1)) 32 ->
  stack_at M V (c :: c2 :: r) b capb -> stack_at M' V (c :: c2' :: r) b capb.
Proof.
  intros M M' V c c2 c2' r b capb HV HV2 HB HB2 P1 P2 P3 AG Hmid AGH (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, ENC_SIZE, O_STACK in *.
  rewrite !EK2.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [replace (depth r + 1 + 1) with (depth r + 2) by lia; exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (S (length r))) as [->|Hne1]; [|destruct (Nat.eq_dec i (length r)) as [->|Hne2]].
  - specialize (S6 (S (length r)) ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (S (S (length r)) - 1 - S (length r))%nat with 0%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat (S (length r)))); [lia | unfold depth in *; lia | | exact S6].
    apply (EK.agree_sub M M' _ _ _ _ AGH); unfold depth in *; lia.
  - replace (S (S (length r)) - 1 - length r)%nat with 1%nat by lia. cbn [nth]. exact Hmid.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (S (S (length r)) - 1 - i)%nat with (S (S (length r - 1 - i)))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma stack_at_head2 : forall (M M' : mem) V c c' r b capb, 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 1)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> ctx_at M' (b + 32 * depth r) c' ->
  stack_at M V (c :: r) b capb -> stack_at M' V (c' :: r) b capb.
Proof.
  intros M M' V c c' r b capb HB HB2 P1 P2 P3 AG Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, O_STACK in *.
  rewrite !EK2.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (S (length r) - 1 - i)%nat with (S (length r - 1 - i))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma stack_at_nil : forall (M M' : mem) V b capb,
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) b -> u64 M' (V + O_STACK + 16) (b + capb) ->
  stack_at M V [] b capb -> stack_at M' V [] b capb.
Proof.
  intros M M' V b capb P1 P2 P3 (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at. unfold depth in *. cbn [length Z.of_nat] in *.
  split; [exact P1|]. split; [rewrite Z.mul_0_r, Z.add_0_r; exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi. lia.
Qed.
(* [comment removed for export] *)
Lemma enc_objx_agree : forall (M M' : mem) V S2 dI dD, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_STACK -> agree M M' (V + O_INDENT) 8 -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  PMES2.enc_objx M V S2 dI dD -> PMES2.enc_objx M' V S2 dI dD.
Proof.
  intros M M' V S2 dI dD HV HV2 A1 AI A2 Hcol H. unfold PMES2.enc_objx, sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT, O_NL_CHARS,
    O_COMMON_VPTR, O_ENABLE, O_MAX_DEPTH, O_INDENT_CHAR, O_FP, O_INDENT, O_COMMA, O_OBRACE, O_CBRACE, O_OBRACKET, O_CBRACKET, O_DEPTH, O_STACK in *.
  assert (X8 : forall a v, V <= a -> a + 8 <= V + 264 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply EK.u64_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X4 : forall a v, V <= a -> a + 4 <= V + 264 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply EK.u32_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X1 : forall a v, V <= a -> a + 1 <= V + 264 -> u8 M a v -> u8 M' a v).
  { intros a v H1 H2. apply EK.u8_agree; [apply (EK.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (Y8 : forall a v, V + 304 <= a -> a + 8 <= V + 408 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply EK.u64_agree; [apply (EK.agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
  assert (Y4 : forall a v, V + 304 <= a -> a + 4 <= V + 408 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply EK.u32_agree; [apply (EK.agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
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
  split; [apply (EK.u32_agree M M'); [apply (EK.agree_sub _ _ _ _ _ _ AI); lia | lia | lia | exact H24]|]. split; [exact Hcol|]. split; [apply Y4; [lia | lia | exact H26]|].
  repeat split; apply Y8; try lia; assumption.
Qed.
(* [comment removed for export] *)
Lemma enc_objx_agree_d : forall (M M' : mem) V S2 dI dD dI' dD', 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_STACK -> agree M M' (V + O_COLON) (O_DEPTH - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  u32 M' (V + O_INDENT) (4 * dI') -> u32 M' (V + O_DEPTH) dD' ->
  PMES2.enc_objx M V S2 dI dD -> PMES2.enc_objx M' V S2 dI' dD'.
Proof.
  intros M M' V S2 dI dD dI' dD' HV HV2 A1 A2 Hcol HI HD H. unfold PMES2.enc_objx, sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT, O_NL_CHARS,
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
  split; [exact HI|]. split; [exact Hcol|]. split; [exact HD|].
  repeat split; apply Y8; try lia; assumption.
Qed.

(* [comment removed for export] *)
Lemma stack_at_recell : forall (M M' : mem) V es b capb, 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * depth es) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b capb -> stack_at M V es b capb -> stack_at M' V es b capb.
Proof.
  intros M M' V es b capb HB HB2 P1 P2 P3 AG (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact S4|]. split; [exact S5|].
  intros i Hi. specialize (S6 i Hi). assert (Hd : Z.of_nat i < depth es) by (unfold depth; lia).
  apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma stack_mid_cons : forall (M M' : mem) V es c0 b capb, 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth es + 1)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b capb -> PMES2.stack_mid M V es c0 b capb -> stack_at M' V (c0 :: es) b capb.
Proof.
  intros M M' V es c0 b capb HB HB2 P1 P2 P3 AG (S1 & S3 & S4 & S5 & S6 & SC). unfold stack_at. rewrite EK2.depth_cons.
  assert (D0 : 0 <= depth es) by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [right; exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (length es)) as [->|Hne].
  - replace (S (length es) - 1 - length es)%nat with 0%nat by lia. cbn [nth]. fold (depth es).
    apply (EK.ctx_at_agree M M' (b + 32 * depth es)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | unfold depth; exact SC].
  - specialize (S6 i ltac:(lia)). replace (S (length es) - 1 - i)%nat with (S (length es - 1 - i))%nat by lia. cbn [nth].
    assert (Hd : Z.of_nat i < depth es) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma defined_of_u32 : forall (M : mem) a v, L5.u32_at RSEGS M a v -> 0xfe000 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4.
Proof.
  intros M a v Hu Ha H4 i Hi. unfold L5.u32_at in Hu.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) 4 _ Hu).
  - rewrite !u64_of_Z by lia. cbn. lia.
  - rewrite u64_of_Z by lia. unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
End EK3.
