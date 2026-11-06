(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
  intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). Local Ltac2 Set LiaHints.tbl := fun () => "0060=1091967795.6 13313130211.526981515745.641415986323.551794599906.564252374674.600000100500900:00>00ASS2HaS2HaSS2HkS1H".
rewrite Z.mod_small by lia.
  apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Hn Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0090>14062844781.1114064710771.7 26981912057.1144204549936.7 61889706092.118734382278.8  8740432102.11 9666804367.11 9668754063.11 00000400800?00F00S00W00[00n01=S2HbS2HbS2Ha2A0S2Ha2HbS2Hb2Ha2A02B0S2HaS2HaS2Ha2Hb2NN2A02B02NES2Ha2Hb2A02B01E".
pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
  - apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
  intros Ha Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0040=26981515745.741415986323.651794599906.664252374674.700000400500900<S2HaSS2HkS1H".
rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition clz_pow (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
  let v2 := Z.lor v1 (Z.shiftr v1 2) in
  let v3 := Z.lor v2 (Z.shiftr v2 4) in
  let v4 := Z.lor v3 (Z.shiftr v3 8) in
  Z.land (v4 + 1) (Z.lxor v4 18446744073709551615).
Definition clz_notv (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
  let v2 := Z.lor v1 (Z.shiftr v1 2) in
  let v3 := Z.lor v2 (Z.shiftr v2 4) in
  let v4 := Z.lor v3 (Z.shiftr v3 8) in
  Z.lxor v4 18446744073709551615.
Definition clz_fn (x : Z) : bool := (clz_pow x =? 2 ^ Z.log2 x) && (0 <=? clz_notv x) && (clz_notv x <? 2^64).
#[using="Type"] Lemma clz_check_true : forallb clz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma clz_pow_eq x : 11 <= x < 8192 -> clz_pow x = 2 ^ Z.log2 x /\ 0 <= clz_notv x < 2^64.
Proof.
  intros Hx. pose proof (forallb_zseq clz_fn 11 8181 x clz_check_true ltac:(lia) ltac:(lia)) as X. unfold clz_fn in X.
  apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. split; [exact X1| split; [exact X2| exact X3]].
Qed.

(* [comment removed for export] *)
Definition stc_q (q : Z) : Z :=
  if q <? 10 then q else
    let x := q + 1 in
    let i := 4 * Z.log2 x - 4 in
    let i := if size_class (i + 1) <? x then i + 2 else i in
    if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
  let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
                    && ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
#[using="Type"] Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
  intros Hn. unfold size_to_class, stc_q, IB, clz32.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=25230619975.340825277104.37015158863.4 000001002003SSS".
replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  set (q := (n + 3) / 16). cbv zeta.
  replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma size_to_class_props n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + 4 <= 16 * size_class (size_to_class n)
  /\ (10 <= (n + 3) / 16 -> 3 <= Z.log2 ((n + 3) / 16 + 1) <= 12).
Proof.
  intros Hn. unfold MMAP_THRESHOLD in Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0080>15043147681.4 2424960062.3  32185819564.1032185819564.9 50312752925.4 51283537973.3 59976777223.8 68555949424.8 00000100500<00C00F00J00Q00USS2HnS2X52X6S2X42HQS1QS2HnS2X12X2S2X3".
rewrite size_to_class_q by lia.
  assert (Q : 0 <= (n + 3) / 16 < 8191) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
  apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
  split; [lia|]. split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
  intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
  apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC1.
