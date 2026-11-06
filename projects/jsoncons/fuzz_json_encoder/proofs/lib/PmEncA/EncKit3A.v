(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core AxSymExec3 AxSymExec3Sound AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EK3A.
Import PMES.
Abbreviation mem := (word -> option byte).
Abbreviation agree := (L5C.agree_on).

Section K.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Abbreviation u64 := (PMSA.u64 L).
Abbreviation u32 := (PMSA.u32 L).
Abbreviation u8 := (PMSA.u8 L).

(* [comment removed for export] *)
Lemma enc_objA_agree_d : forall (M M' : mem) V S2 d d', 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_STACK -> agree M M' (V + O_COLON) (O_DEPTH - O_COLON) -> L5.defined M' V ENC_SIZE ->
  u32 M' (V + O_INDENT) (4 * d') -> u32 M' (V + O_DEPTH) d' ->
  PMESA.enc_objA L IC EC M V S2 d -> PMESA.enc_objA L IC EC M' V S2 d'.
Proof.
  intros M M' V S2 d d' HV HV2 A1 A2 DEF HI HD H. unfold PMESA.enc_objA, PMESA.sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT,
    O_NL_CHARS, O_COMMON_VPTR, O_ENABLE, O_MAX_DEPTH, O_INDENT_CHAR, O_FP, O_INDENT, O_COMMA, O_OBRACE, O_CBRACE, O_OBRACKET, O_CBRACKET, O_DEPTH, O_STACK in *.
  assert (X8 : forall a v, V <= a -> a + 8 <= V + 264 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply (EKA.u64_agree L M M'); [apply (EKA.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X4 : forall a v, V <= a -> a + 4 <= V + 264 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply (EKA.u32_agree L M M'); [apply (EKA.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X1 : forall a v, V <= a -> a + 1 <= V + 264 -> u8 M a v -> u8 M' a v).
  { intros a v H1 H2. apply (EKA.u8_agree L M M'); [apply (EKA.agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (Y8 : forall a v, V + 304 <= a -> a + 8 <= V + 400 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply (EKA.u64_agree L M M'); [apply (EKA.agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
  destruct H as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                 H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & (H29 & H29') & (H30 & H30') & (H31 & H31') & (H32 & H32') & HD').
  split; [replace V with (V + 0) by lia; apply X8; [lia | lia | replace (V + 0) with V by lia; exact H1]|].
  split; [apply X8; [lia | lia | exact H2]|]. split; [apply X8; [lia | lia | exact H3]|].
  split; [exists fl; split; [apply X1; [lia | lia | exact H4] | exact H4']|].
  split; [apply X1; [lia | lia | exact H5]|].
  split; [apply X1; [lia | lia | exact H6]|]. split; [apply X1; [lia | lia | exact H7]|]. split; [apply X1; [lia | lia | exact H8]|].
  split; [apply X1; [lia | lia | exact H9]|]. split; [apply X1; [lia | lia | exact H10]|].
  split; [apply X1; [lia | lia | exact H11]|]. split; [apply X8; [lia | lia | exact H12]|].
  split; [apply X8; [lia | lia | exact H13]|]. split; [apply X8; [lia | lia | exact H14]|]. split; [apply X8; [lia | lia | exact H15]|].
  split; [apply (L5C.defined_agree M M' _ _); [apply (EKA.agree_sub M M' _ _ _ _ A1); lia | exact H16]|].
  split; [apply X8; [lia | lia | exact H17]|].
  split; [exists en; split; [apply X1; [lia | lia | exact H18] | split; [exact (proj1 H18') | apply (L5C.defined_agree M M' _ _); [apply (EKA.agree_sub M M' _ _ _ _ A1); lia | exact (proj2 H18')]]]|].
  split; [apply X4; [lia | lia | exact H19]|]. split; [apply X1; [lia | lia | exact H20]|].
  split; [apply X1; [lia | lia | exact H21]|]. split; [apply X4; [lia | lia | exact H22]|].
  split; [exists dp; apply X1; [lia | lia | exact H23]|].
  split; [exact HI|]. split; [intros i Hi; replace (V + 296 + i) with (V + (296 + i)) by lia; apply DEF; lia|]. split; [exact HD|].
  split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|].
  split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|].
  exact DEF.
Qed.

(* [comment removed for export] *)
Lemma stack_second : forall (M : mem) V c c2 r b capb, PMESA.stack_at L M V (c :: c2 :: r) b capb -> PMESA.ctx_at L M (b + 32 * depth r) c2.
Proof.
  intros M V c c2 r b capb (_ & _ & _ & _ & _ & S6). pose proof (S6 (length r) ltac:(cbn [length]; lia)) as HC. cbn [length] in HC.
  replace (Datatypes.S (Datatypes.S (length r)) - 1 - length r)%nat with 1%nat in HC by lia. cbn [nth] in HC. exact HC.
Qed.
Lemma stack_head : forall (M : mem) V c r b capb, PMESA.stack_at L M V (c :: r) b capb -> PMESA.ctx_at L M (b + 32 * depth r) c.
Proof.
  intros M V c r b capb (_ & _ & _ & _ & _ & S6). pose proof (S6 (length r) ltac:(cbn [length]; lia)) as HC. cbn [length] in HC.
  replace (Datatypes.S (length r) - 1 - length r)%nat with 0%nat in HC by lia. cbn [nth] in HC. exact HC.
Qed.

(* [comment removed for export] *)
Lemma stack_at_pop1 : forall (M M' : mem) V c c2 c2' r b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 1)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> PMESA.ctx_at L M' (b + 32 * depth r) c2' ->
  PMESA.stack_at L M V (c :: c2 :: r) b capb -> PMESA.stack_at L M' V (c2' :: r) b capb.
Proof.
  intros M M' V c c2 c2' r b capb HV HV2 HB HB2 P1 P2 P3 AG Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold PMESA.stack_at, ENC_SIZE, O_STACK in *.
  rewrite !EKA.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (Datatypes.S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (Datatypes.S (Datatypes.S (length r)) - 1 - i)%nat with (Datatypes.S (Datatypes.S (length r - 1 - i)))%nat in S6 by lia. cbn [nth] in S6.
    replace (Datatypes.S (length r) - 1 - i)%nat with (Datatypes.S (length r - 1 - i))%nat by lia. cbn [nth].
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EKA.ctx_at_agree L M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EKA.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.

(* [comment removed for export] *)
Lemma stack_at_mid : forall (M M' : mem) V c c2 c2' r b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 2)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> PMESA.ctx_at L M' (b + 32 * depth r) c2' -> agree M M' (b + 32 * (depth r + 1)) 32 ->
  PMESA.stack_at L M V (c :: c2 :: r) b capb -> PMESA.stack_at L M' V (c :: c2' :: r) b capb.
Proof.
  intros M M' V c c2 c2' r b capb HV HV2 HB HB2 P1 P2 P3 AG Hmid AGH (S1 & S2 & S3 & S4 & S5 & S6). unfold PMESA.stack_at, ENC_SIZE, O_STACK in *.
  rewrite !EKA.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [replace (depth r + 1 + 1) with (depth r + 2) by lia; exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (Datatypes.S (length r))) as [->|Hne1]; [|destruct (Nat.eq_dec i (length r)) as [->|Hne2]].
  - specialize (S6 (Datatypes.S (length r)) ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (Datatypes.S (Datatypes.S (length r)) - 1 - Datatypes.S (length r))%nat with 0%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    apply (EKA.ctx_at_agree L M M' (b + 32 * Z.of_nat (Datatypes.S (length r)))); [lia | unfold depth in *; lia | | exact S6].
    apply (EKA.agree_sub M M' _ _ _ _ AGH); unfold depth in *; lia.
  - replace (Datatypes.S (Datatypes.S (length r)) - 1 - length r)%nat with 1%nat by lia. cbn [nth]. exact Hmid.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (Datatypes.S (Datatypes.S (length r)) - 1 - i)%nat with (Datatypes.S (Datatypes.S (length r - 1 - i)))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EKA.ctx_at_agree L M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EKA.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma stack_at_head2 : forall (M M' : mem) V c c' r b capb, 0 <= b -> b + capb <= 2 ^ 64 ->
  u64 M' (V + O_STACK) b -> u64 M' (V + O_STACK + 8) (b + 32 * (depth r + 1)) -> u64 M' (V + O_STACK + 16) (b + capb) ->
  agree M M' b (32 * depth r) -> PMESA.ctx_at L M' (b + 32 * depth r) c' ->
  PMESA.stack_at L M V (c :: r) b capb -> PMESA.stack_at L M' V (c' :: r) b capb.
Proof.
  intros M M' V c c' r b capb HB HB2 P1 P2 P3 AG Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold PMESA.stack_at, O_STACK in *.
  rewrite !EKA.depth_cons in *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *.
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (Datatypes.S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (Datatypes.S (length r) - 1 - i)%nat with (Datatypes.S (length r - 1 - i))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EKA.ctx_at_agree L M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EKA.agree_sub M M' _ _ _ _ AG); lia | exact S6].
Qed.
End K.
End EK3A.
