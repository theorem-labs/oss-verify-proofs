(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg RelocSpan.
Import ListNotations.
Local Open Scope Z_scope.

Definition canon_spans : list cspan := [
  mkSpan 1000%positive SK_RO 0x13084 0x130a0 4; mkSpan 1001%positive SK_RO 0x130a0 0x130cc 4; mkSpan 1002%positive SK_RO 0x130cc 0x13140 4;
  mkSpan 1003%positive SK_RO 0x13140 0x131d0 4; mkSpan 1004%positive SK_RO 0x131d0 0x13494 4; mkSpan 1005%positive SK_RO 0x13494 0x13498 4;
  mkSpan 1006%positive SK_RO 0x13498 0x134a0 4; mkSpan 1007%positive SK_RO 0x134a0 0x135ac 4; mkSpan 1008%positive SK_RO 0x135ac 0x135f4 4;
  mkSpan 1009%positive SK_RO 0x1365c 0x13660 4; mkSpan 1010%positive SK_RO 0x13660 0x13694 4; mkSpan 1011%positive SK_RO 0x13694 0x13730 4;
  mkSpan 1012%positive SK_RO 0x13730 0x13764 4; mkSpan 1013%positive SK_RO 0x13764 0x1377c 4; mkSpan 1014%positive SK_RO 0x1377c 0x13794 4;
  mkSpan 1015%positive SK_RO 0x14d1c 0x14d20 4; mkSpan 1016%positive SK_RO 0x1516c 0x15170 4; mkSpan 1017%positive SK_RO 0x15170 0x1539c 4;
  mkSpan 1018%positive SK_RO 0x1539c 0x153e8 4; mkSpan 1019%positive SK_RO 0x153e8 0x15448 4; mkSpan 1020%positive SK_RO 0x15448 0x15490 4;
  mkSpan 1021%positive SK_RO 0x15490 0x15740 4; mkSpan 1022%positive SK_RO 0x1574c 0x15758 4; mkSpan 1023%positive SK_RO 0x15758 0x15794 4;
  mkSpan 1024%positive SK_RO 0x15794 0x157b0 4; mkSpan 1025%positive SK_RO 0x157b0 0x157b4 4; mkSpan 1026%positive SK_RO 0x157b4 0x15800 4;
  mkSpan 1027%positive SK_RO 0x15800 0x15874 4; mkSpan 1028%positive SK_RO 0x15874 0x15958 4; mkSpan 1029%positive SK_RO 0x15958 0x159b8 4;
  mkSpan 1030%positive SK_RO 0x159b8 0x159c0 4; mkSpan 1031%positive SK_RO 0x159c0 0x159f8 4; mkSpan 1032%positive SK_RO 0x159f8 0x159fc 4;
  mkSpan 1033%positive SK_RO 0x159fc 0x15a00 4; mkSpan 1034%positive SK_RO 0x15a00 0x15b38 4; mkSpan 1035%positive SK_RO 0x15b38 0x15b3c 4;
  mkSpan 1036%positive SK_RO 0x15b3c 0x15b40 4; mkSpan 1037%positive SK_RO 0x15b40 0x15d0c 4; mkSpan 1038%positive SK_RO 0x15d0c 0x15e1c 4;
  mkSpan 1039%positive SK_RO 0x15e1c 0x161f4 4; mkSpan 1040%positive SK_RO 0x161f4 0x164cc 4; mkSpan 1041%positive SK_RO 0x164cc 0x1683c 4;
  mkSpan 1042%positive SK_RO 0x1683c 0x170e0 4; mkSpan 1043%positive SK_RO 0x170e0 0x17230 4; mkSpan 1044%positive SK_RO 0x17230 0x173a8 4;
  mkSpan 1045%positive SK_RO 0x173a8 0x17440 4; mkSpan 1046%positive SK_RO 0x17440 0x17444 4; mkSpan 1047%positive SK_RO 0x17444 0x17530 4;
  mkSpan 1048%positive SK_RO 0x17530 0x17578 4; mkSpan 1049%positive SK_RO 0x17578 0x175c0 4; mkSpan 1050%positive SK_RO 0x175c0 0x176bc 4;
  mkSpan 1051%positive SK_RO 0x176bc 0x1771c 4; mkSpan 1052%positive SK_RO 0x1771c 0x178c0 4; mkSpan 1053%positive SK_RO 0x178c0 0x17a50 4;
  mkSpan 1054%positive SK_RO 0x17a50 0x17a58 4; mkSpan 1055%positive SK_RO 0x17a58 0x17a5c 4; mkSpan 1056%positive SK_RO 0x17a5c 0x17a88 4;
  mkSpan 1057%positive SK_RO 0x17a88 0x17aec 4; mkSpan 1058%positive SK_RO 0x17aec 0x17b40 4; mkSpan 1059%positive SK_RO 0x17b40 0x17b9c 4;
  mkSpan 1060%positive SK_RO 0x17b9c 0x17cd4 4; mkSpan 1061%positive SK_RO 0x17cd4 0x17d8c 4; mkSpan 1062%positive SK_RO 0x17d8c 0x17dbc 4;
  mkSpan 1063%positive SK_RO 0x17dbc 0x17f6c 4; mkSpan 1064%positive SK_RO 0x17f6c 0x18d9c 4; mkSpan 1065%positive SK_RO 0x18d9c 0x18ed0 4;
  mkSpan 1066%positive SK_RO 0x18ed0 0x18fa4 4; mkSpan 1067%positive SK_RO 0x18fa4 0x1a66c 4; mkSpan 1068%positive SK_RO 0x1a66c 0x1a690 4;
  mkSpan 1069%positive SK_RO 0x1a690 0x1a7bc 4; mkSpan 1070%positive SK_RO 0x1a7bc 0x1a94c 4; mkSpan 1071%positive SK_RO 0x1a94c 0x1a954 4;
  mkSpan 1072%positive SK_RO 0x1a954 0x1a998 4; mkSpan 1073%positive SK_RO 0x1a998 0x1aa70 4; mkSpan 1074%positive SK_RO 0x1aa70 0x1ab38 4;
  mkSpan 1075%positive SK_RO 0x1ab38 0x1b238 4; mkSpan 1076%positive SK_RO 0x1b238 0x1b340 4; mkSpan 1077%positive SK_RO 0x1b340 0x1b350 4;
  mkSpan 1078%positive SK_RO 0x1b350 0x1bb1c 4; mkSpan 1079%positive SK_RO 0x1bb1c 0x1bb4c 4; mkSpan 1080%positive SK_RO 0x1bb4c 0x1bb58 4;
  mkSpan 1081%positive SK_RO 0x1bb58 0x1bbec 4; mkSpan 1082%positive SK_RO 0x1bbec 0x1bcd8 4; mkSpan 1083%positive SK_RO 0x1bcd8 0x1bd80 4;
  mkSpan 1084%positive SK_RO 0x1bd80 0x1c684 4; mkSpan 1085%positive SK_RO 0x1c684 0x1c6a0 4; mkSpan 1086%positive SK_RO 0x1c6a0 0x1c740 4;
  mkSpan 1087%positive SK_RO 0x1c740 0x1c80c 4; mkSpan 1088%positive SK_RO 0x1c80c 0x1c8e8 4; mkSpan 1089%positive SK_RO 0x1c8e8 0x1c9b4 4;
  mkSpan 1090%positive SK_RO 0x1c9b4 0x1cdb8 4; mkSpan 1091%positive SK_RO 0x1cdb8 0x1ceb0 4; mkSpan 1092%positive SK_RO 0x1ceb0 0x1cf40 4;
  mkSpan 1093%positive SK_RO 0x1cf40 0x1cf84 4; mkSpan 1094%positive SK_RO 0x1cf84 0x1d20c 4; mkSpan 1095%positive SK_RO 0x1d20c 0x1d280 4;
  mkSpan 1096%positive SK_RO 0x1d280 0x1d2a4 4; mkSpan 1097%positive SK_RO 0x1d2a4 0x1d2a8 4; mkSpan 1098%positive SK_RO 0x1d2a8 0x1d2b4 4;
  mkSpan 1099%positive SK_RO 0x1d2b4 0x1d308 4; mkSpan 1100%positive SK_RO 0x1d308 0x1d314 4; mkSpan 1101%positive SK_RO 0x1d314 0x1d348 4;
  mkSpan 4000%positive SK_RO 0x102e7 0x102f1 1; mkSpan 4001%positive SK_RO 0x103fc 0x1040f 1; mkSpan 4002%positive SK_RO 0x10445 0x10459 1;
  mkSpan 4003%positive SK_RO 0x10459 0x1045d 1; mkSpan 4004%positive SK_RO 0x1045d 0x1045e 1; mkSpan 4005%positive SK_RO 0x1045e 0x10460 1;
  mkSpan 4006%positive SK_RO 0x10492 0x104a3 1; mkSpan 4007%positive SK_RO 0x104a3 0x104c3 1; mkSpan 4008%positive SK_RO 0x10563 0x10567 1;
  mkSpan 4009%positive SK_RO 0x106e4 0x106e8 1; mkSpan 4010%positive SK_RO 0x106e8 0x10709 1; mkSpan 4011%positive SK_RO 0x108b7 0x108cc 1;
  mkSpan 4012%positive SK_RO 0x108cc 0x108e3 1; mkSpan 4013%positive SK_RO 0x1097c 0x10980 1; mkSpan 4014%positive SK_RO 0x109b4 0x109b8 1;
  mkSpan 4015%positive SK_RO 0x109eb 0x10a0b 1; mkSpan 4016%positive SK_RO 0x10a13 0x10a24 1; mkSpan 4017%positive SK_RO 0x10a6d 0x10a77 1;
  mkSpan 4018%positive SK_RO 0x10a77 0x10a7e 1; mkSpan 5000%positive SK_RO 0x10b04 0x113b4 2; mkSpan 5001%positive SK_RO 0x113b4 0x113d4 4;
  mkSpan 5002%positive SK_RO 0x1144f 0x11454 1; mkSpan 5003%positive SK_RO 0x11458 0x11460 4; mkSpan 5004%positive SK_RO 0x11460 0x11468 4;
  mkSpan 5005%positive SK_RO 0x11468 0x11470 4; mkSpan 5006%positive SK_RO 0x11480 0x11488 4; mkSpan 5007%positive SK_RO 0x114a0 0x114a8 4;
  mkSpan 5008%positive SK_RO 0x114a8 0x117c0 4; mkSpan 5009%positive SK_RO 0x117c0 0x117d0 4; mkSpan 5010%positive SK_RO 0x117d0 0x117dc 4;
  mkSpan 5011%positive SK_RO 0x11968 0x12084 4; mkSpan 5012%positive SK_RELRO 0x1e368 0x1e3a0 8; mkSpan 5013%positive SK_DATA 0x1f3f8 0x1f430 8;
  mkSpan 5015%positive SK_DATA 0x1f630 0x2f6b0 8; mkSpan 5016%positive SK_RELRO 0x1e348 0x1e368 8; mkSpan 5018%positive SK_RO 0x10a80 0x10b04 4;
  mkSpan 5019%positive SK_DATA 0x1f440 0x1f624 8; mkSpan 5020%positive SK_RO 0x113d4 0x1144f 2; mkSpan 5021%positive SK_RO 0x11470 0x11478 4;
  mkSpan 5022%positive SK_RO 0x11478 0x11480 4; mkSpan 5023%positive SK_RO 0x11488 0x11490 4; mkSpan 5024%positive SK_RO 0x11490 0x11498 4;
  mkSpan 5025%positive SK_RO 0x11498 0x114a0 4; mkSpan 5026%positive SK_RELRO 0x1e3b0 0x1e3b8 8; mkSpan 5034%positive SK_RELRO 0x1e3a0 0x1e3b0 8; mkSpan 5027%positive SK_RELRO 0x1e3b8 0x1e3f8 8;
  mkSpan 5028%positive SK_DATA 0x1f430 0x1f440 8; mkSpan 5029%positive SK_DATA 0x2f6f0 0x2f840 8; mkSpan 5035%positive SK_DATA 0x2f6b0 0x2f6b8 8;
  mkSpan 5036%positive SK_DATA 0x2f6b8 0x2f6f0 8; mkSpan 5030%positive SK_DATA 0x2f840 0x2f844 4;
  mkSpan 5031%positive SK_DATA 0x2f848 0x2fc88 8; mkSpan 5032%positive SK_DATA 0x2fc88 0x2fcb0 8; mkSpan 5033%positive SK_DATA 0x2fcb0 0x300b0 4].

(* [comment removed for export] *)
Definition canon_order : list (positive * positive) := [(5013%positive, 5028%positive); (5013%positive, 5019%positive); (5013%positive, 5015%positive); (5013%positive, 5035%positive); (5013%positive, 5029%positive); (5013%positive, 5036%positive); (5013%positive, 5030%positive); (5013%positive, 5031%positive); (5013%positive, 5032%positive); (5013%positive, 5033%positive); (5028%positive, 5019%positive); (5028%positive, 5015%positive); (5028%positive, 5035%positive); (5028%positive, 5029%positive); (5028%positive, 5036%positive); (5028%positive, 5030%positive); (5028%positive, 5031%positive); (5028%positive, 5032%positive); (5028%positive, 5033%positive); (5019%positive, 5015%positive); (5019%positive, 5035%positive); (5019%positive, 5029%positive); (5019%positive, 5036%positive); (5019%positive, 5030%positive); (5019%positive, 5031%positive); (5019%positive, 5032%positive); (5019%positive, 5033%positive); (5015%positive, 5035%positive); (5015%positive, 5029%positive); (5015%positive, 5036%positive); (5015%positive, 5030%positive); (5015%positive, 5031%positive); (5015%positive, 5032%positive); (5015%positive, 5033%positive); (5035%positive, 5029%positive); (5035%positive, 5036%positive); (5035%positive, 5030%positive); (5035%positive, 5031%positive); (5035%positive, 5032%positive); (5035%positive, 5033%positive); (5029%positive, 5036%positive); (5029%positive, 5030%positive); (5029%positive, 5031%positive); (5029%positive, 5032%positive); (5029%positive, 5033%positive); (5036%positive, 5030%positive); (5036%positive, 5031%positive); (5036%positive, 5032%positive); (5036%positive, 5033%positive); (5030%positive, 5031%positive); (5030%positive, 5032%positive); (5030%positive, 5033%positive); (5031%positive, 5032%positive); (5031%positive, 5033%positive); (5032%positive, 5033%positive); (5016%positive, 5012%positive); (5016%positive, 5026%positive); (5016%positive, 5027%positive); (5012%positive, 5026%positive); (5012%positive, 5027%positive); (5026%positive, 5027%positive)].

Class RelocSpans (RL : Reloc) (RD : RelocData RL) := {
  rl_hull_ok : hull_okb = true;
  rl_spans_ok : spans_check canon_spans = true;
  rl_orders_ok : orders_check canon_spans canon_order = true }.

(* [comment removed for export] *)
Lemma rdn_wbytes_out_xblk : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} segs bs m b1 b2 ca cb (n : nat),
  xblk_apartb canon_spans canon_order b1 b2 ca n cb (length bs) = true ->
  rdn segs (wbytes m (rl (rl_delta b2) cb) bs) (rl (rl_delta b1) ca) n = rdn segs m (rl (rl_delta b1) ca) n.
Proof.
  intros RL RD RSP segs bs m b1 b2 ca cb n H.
  destruct (xblk_apart canon_spans canon_order rl_spans_ok rl_orders_ok rl_hull_ok b1 b2 ca n cb (length bs) H) as (A1 & A2 & A3 & A4 & A5).
  assert (E1 : bv_unsigned (rl (rl_delta b1) ca) = ca + rl_delta b1) by (apply rl_u; pose proof (Zle_0_nat n); lia).
  assert (E2 : bv_unsigned (rl (rl_delta b2) cb) = cb + rl_delta b2) by (apply rl_u; pose proof (Zle_0_nat (length bs)); lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; lia.
Qed.

(* [comment removed for export] *)
Lemma rl_hull : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD},
  2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo /\ rl_data_lo <= rl_img_hi /\ rl_img_hi <= 2^31.
Proof. intros RL RD RSP. destruct (hull_fact rl_hull_ok) as (A & B & C & D & E & _). auto. Qed.
Lemma rl_hull_al : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD}, rl_img_hi mod 8 = 0.
Proof. intros RL RD RSP. destruct (hull_fact rl_hull_ok) as (_ & _ & _ & _ & _ & F). exact F. Qed.

Lemma rl_span : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} b s, span_find canon_spans b = Some s -> span_P s.
Proof. intros RL RD RSP b s H. exact (span_fact canon_spans rl_spans_ok b s H). Qed.

(* [comment removed for export] *)
Definition span_mark (b : positive) : Prop := True.
Ltac rl_span_of b :=
  lazymatch goal with
  | _ : span_mark b |- _ => fail
  | _ =>
      let r := eval vm_compute in (span_find canon_spans b) in
      lazymatch r with
      | Some ?s =>
          let P := eval cbv [span_P sp_blk sp_kind sp_lo sp_hi sp_al] in (span_P s) in
          lazymatch P with
          | ?R /\ _ =>
              let h := fresh "Hspan" in let m := fresh "Hspanm" in
              pose proof (proj1 (rl_span b s (@eq_refl _ (Some s)) : P) : R) as h; pose proof (I : span_mark b) as m
          end
      | None => fail
      end
  end.
(* [comment removed for export] *)
Ltac rl_span_al b :=
  let r := eval vm_compute in (span_find canon_spans b) in
  lazymatch r with
  | Some ?s =>
      let P := eval cbv [span_P sp_blk sp_kind sp_lo sp_hi sp_al] in (span_P s) in
      lazymatch P with
      | _ /\ ?A =>
          let h := fresh "Hspanal" in pose proof (proj2 (rl_span b s (@eq_refl _ (Some s)) : P) : A) as h
      end
  end.

(* [comment removed for export] *)
Ltac rl_hull_ctx :=
  lazymatch goal with
  | _ : 2^16 <= rl_img_lo /\ _ |- _ => idtac
  | _ => let h := fresh "Hhull" in pose proof rl_hull as h
  end.
Ltac rl_spans_ctx :=
  rl_hull_ctx;
  repeat match goal with
         | |- context [@rl_delta _ ?b] => rl_span_of b
         | H : context [@rl_delta _ ?b] |- _ => rl_span_of b
         end.

(* [comment removed for export] *)
Lemma rl_order : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} b1 b2 s1 s2,
  pair_inb canon_order b1 b2 = true -> span_find canon_spans b1 = Some s1 -> span_find canon_spans b2 = Some s2 ->
  sp_hi s1 + rl_delta b1 <= sp_lo s2 + rl_delta b2.
Proof. intros RL RD RSP b1 b2 s1 s2. exact (order_fact canon_spans canon_order rl_orders_ok b1 b2 s1 s2). Qed.
Ltac rl_order_of b1 b2 :=
  let r1 := eval vm_compute in (span_find canon_spans b1) in
  let r2 := eval vm_compute in (span_find canon_spans b2) in
  lazymatch r1 with
  | Some ?s1 =>
      lazymatch r2 with
      | Some ?s2 =>
          let P := eval cbv [sp_blk sp_kind sp_lo sp_hi sp_al] in (sp_hi s1 + rl_delta b1 <= sp_lo s2 + rl_delta b2) in
          let h := fresh "Hord" in
          pose proof (rl_order b1 b2 s1 s2 (@eq_refl bool true) (@eq_refl _ (Some s1)) (@eq_refl _ (Some s2)) : P) as h
      end
  end.
Ltac rl_data_chain :=
  rl_order_of 5013%positive 5028%positive;
  rl_order_of 5028%positive 5019%positive;
  rl_order_of 5019%positive 5015%positive;
  rl_order_of 5015%positive 5035%positive;
  rl_order_of 5035%positive 5029%positive;
  rl_order_of 5029%positive 5036%positive;
  rl_order_of 5036%positive 5030%positive;
  rl_order_of 5030%positive 5031%positive;
  rl_order_of 5031%positive 5032%positive;
  rl_order_of 5032%positive 5033%positive.
Ltac rl_relro_chain :=
  rl_order_of 5016%positive 5012%positive;
  rl_order_of 5012%positive 5026%positive;
  rl_order_of 5026%positive 5027%positive.
(* [comment removed for export] *)
Ltac rl_ndata l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | cons (@rl_delta _ ?b) ?t =>
      let n := rl_ndata t in
      lazymatch b with
      | 5013%positive => constr:(S n)
      | 5028%positive => constr:(S n)
      | 5019%positive => constr:(S n)
      | 5015%positive => constr:(S n)
      | 5029%positive => constr:(S n)
      | 5035%positive => constr:(S n)
      | 5036%positive => constr:(S n)
      | 5030%positive => constr:(S n)
      | 5031%positive => constr:(S n)
      | 5032%positive => constr:(S n)
      | 5033%positive => constr:(S n)
      | _ => n
      end
  | cons _ ?t => rl_ndata t
  end.
Ltac rl_nrelro l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | cons (@rl_delta _ ?b) ?t =>
      let n := rl_nrelro t in
      lazymatch b with
      | 5016%positive => constr:(S n)
      | 5012%positive => constr:(S n)
      | 5026%positive => constr:(S n)
      | 5027%positive => constr:(S n)
      | _ => n
      end
  | cons _ ?t => rl_nrelro t
  end.
Ltac rl_chains l :=
  (let n := rl_ndata l in lazymatch n with S (S _) => try rl_data_chain | _ => idtac end);
  (let n := rl_nrelro l in lazymatch n with S (S _) => try rl_relro_chain | _ => idtac end).

(* [comment removed for export] *)
Ltac rl_spans_data :=
  rl_hull_ctx;
  try rl_span_of 5000%positive;
  try rl_span_of 5001%positive;
  try rl_span_of 5002%positive;
  try rl_span_of 5003%positive;
  try rl_span_of 5004%positive;
  try rl_span_of 5005%positive;
  try rl_span_of 5006%positive;
  try rl_span_of 5007%positive;
  try rl_span_of 5008%positive;
  try rl_span_of 5009%positive;
  try rl_span_of 5010%positive;
  try rl_span_of 5011%positive;
  try rl_span_of 5012%positive;
  try rl_span_of 5013%positive;
  try rl_span_of 5015%positive;
  try rl_span_of 5016%positive;
  try rl_span_of 5018%positive;
  try rl_span_of 5019%positive;
  try rl_span_of 5020%positive;
  try rl_span_of 5021%positive;
  try rl_span_of 5022%positive;
  try rl_span_of 5023%positive;
  try rl_span_of 5024%positive;
  try rl_span_of 5025%positive;
  try rl_span_of 5026%positive;
  try rl_span_of 5027%positive;
  try rl_span_of 5028%positive;
  try rl_span_of 5029%positive;
  try rl_span_of 5030%positive;
  try rl_span_of 5031%positive;
  try rl_span_of 5032%positive;
  try rl_span_of 5033%positive;
  try rl_span_of 5035%positive;
  try rl_span_of 5036%positive.
