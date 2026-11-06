(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraMainPhaseA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarFam OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibInit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraMainPhaseA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.PnTopAL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition art_IL : icpt_layout :=      (* [comment removed for export] *)
  ICL 0x6a294
      2304
      0x103d0
      0x103f0
      [(0x23a40, 7); (0x23a60, 53); (0x23ae0, 13); (0x23b00, 39); (0x23b60, 6); (0x23b80, 21); (0x23c20, 6); (0x23c40, 6); (0x23c60, 5496); (0x25720, 2748); (0x26480, 11); (0x264a0, 74); (0x26520, 6); (0x26540, 11); (0x26560, 5); (0x26580, 5); (0x265a0, 6); (0x26660, 1); (0x267e0, 17); (0x26820, 23); (0x26860, 13); (0x26880, 38); (0x268e0, 42); (0x26940, 43); (0x269a0, 59); (0x26a00, 58); (0x26a60, 43); (0x26ac0, 77); (0x26b40, 18); (0x26b80, 22); (0x26bc0, 33); (0x26c20, 45); (0x26c80, 60); (0x26ce0, 42); (0x26d40, 37); (0x26da0, 51); (0x26e00, 13); (0x26f40, 3); (0x26f60, 10); (0x26f80, 13); (0x26fa0, 14); (0x27020, 54); (0x27080, 440); (0x151520, 88)]
      [(0x23a40, 0x272a0); (0x151520, 0x1515a0); (0x15b8a0, 0x15c3a0)]
      0x7ebb8
      0x7ebb4
      0x6b4fb8
      0x6a30c
      4320
      [(0x693ad0, 8, 0x6b3dc8); (0x6b3df0, 8, 0)]
      0x10000
      0x158000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 38.
Lemma BUDGET0_lo : 2 ^ 36 + 2 ^ 20 + PRIMCAP <= BUDGET0.  Proof. vm_compute. discriminate. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition RES_ok (RES : credit) : Prop := 0 <= fst RES <= 700 /\ 0 <= snd RES <= 3 * 2 ^ 30.      (* [comment removed for export] *)

Section R.
Variable RES : credit.
Hypothesis ROK : RES_ok RES.

Lemma pm_lib_layout : drv_lib_layoutA (PQHAS.LayA RES art_L) art_L.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - change (lla_stack (PQHAS.LayA RES art_L)) with 36864. lia.
  - reflexivity.
  - intros iv Hin.
    change (lla_foot (PQHAS.LayA RES art_L)) with [(6889728, 6889730); (6890288, 6890290); (6890290, 6892144); (6893976, 6894064); (7027536, 7028080)] in Hin.
    change LIB_HOLES with [(6889728, 6889736); (6890288, 6894064); (7027536, 7028080); (6896220, 6896224)].   (* [comment removed for export] *)
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
      first [ (exists 6889728, 6889736; split; [cbn [In]; left; reflexivity | lia])
            | (exists 6890288, 6894064; split; [cbn [In]; right; left; reflexivity | lia])
            | (exists 7027536, 7028080; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
  - intros iv Hin. change (lla_junk (PQHAS.LayA RES art_L)) with [(6896220, 6896224)] in Hin.   (* [comment removed for export] *)
    change LIB_HOLES with [(6889728, 6889736); (6890288, 6894064); (7027536, 7028080); (6896220, 6896224)].
    destruct Hin as [<-|[]]. cbn [fst snd]. exists 6896220, 6896224; split; [cbn [In]; do 3 right; left; reflexivity | lia].
  - intros n Hn. change (lla_credit (PQHAS.LayA RES art_L) n) with (1320 + fst RES, 12 * 2 ^ 30 + 8 * n + snd RES). cbn [fst snd].
    destruct ROK as [[? ?] [? ?]]. lia.
  - intros k Hk. change (lla_leak (PQHAS.LayA RES art_L) k) with 0. change (lla_frames (PQHAS.LayA RES art_L) k) with 14.
    cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; split; discriminate.
Qed.

Lemma pm_lib_cells : drv_lib_cellsA (PQHAS.LayA RES art_L).
Proof.
  constructor; try reflexivity.
  - intros iv Hin.
    change (lla_init_img (PQHAS.LayA RES art_L)) with [(65536, 1409024); (1422544, 1422712); (6889685, 6896176)] in Hin.
    change LIBINIT_IMG with [(65536, 1409024); (6889681, 6889684); (6889685, 6896176); (1422544, 1422712); (7028168, 7028216)].
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd];
      first [ (exists 65536, 1409024; split; [cbn [In]; left; reflexivity | lia])
            | (exists 1422544, 1422712; split; [cbn [In]; right; right; right; left; reflexivity | lia])
            | (exists 6889685, 6896176; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
  - change (lla_rw_lo (PQHAS.LayA RES art_L)) with 1409024. lia.
  - intros iv Hin.
    change (lla_initc (PQHAS.LayA RES art_L)) with [(6896184, 6896384); (7027520, 7027528); (7028120, 7028128); (7028168, 7028216); (7028115, 7028116); (7028336, 7028340)] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.

Lemma pm_lib_budget : drv_budgetA art_L (PQHAS.LayA RES art_L).
Proof.
  intros n Hn. unfold credA, CAPk, adebit.
  change (lla_credit (PQHAS.LayA RES art_L) n) with (1320 + fst RES, 12 * 2 ^ 30 + 8 * n + snd RES).
  change (hl_k_per_malloc art_L) with 8. change (hl_b_lin art_L) with 3. change (hl_b_overhead art_L) with 2097152.
  cbn [fst snd]. destruct ROK as [[? ?] [? ?]]. lia.
Qed.
End R.
