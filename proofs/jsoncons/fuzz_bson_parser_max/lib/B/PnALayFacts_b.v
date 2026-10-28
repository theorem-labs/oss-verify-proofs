(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatIfaceInst_b
     Ba0DrvLibL_b Ba0DrvLibInit_b Ba0DrvG_b Ba0DrvMain_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnTopS. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnTopAL_b PnAHarnessStmts_b PnAHarness_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x6336c 2304 0x103b0 0x103d0
      [(0x231c0, 13); (0x23220, 7); (0x23240, 54); (0x23300, 14); (0x23320, 23); (0x23360, 13); (0x23380, 38); (0x233e0, 43); (0x23440, 66); (0x234c0, 62); (0x23520, 22);
       (0x23560, 17); (0x235a0, 26); (0x235e0, 19); (0x23620, 19); (0x23660, 23); (0x236a0, 21); (0x236e0, 48); (0x23740, 26); (0x23880, 54); (0x238e0, 9); (0x23900, 4);
       (0x23920, 39)]
      [(0x231c0, 0x23980); (0x13bfc0, 0x13c580)]
      0x77c90 0x77c8c 0x6951b8 0x633e4 4320 [(0x673cd0, 8, 0x693fc8); (0x693ff0, 8, 0)] 0x10000 0x139000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 34.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0.  Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. unfold BUDGET0. lia. Qed.

(* [comment removed for export] *)
Lemma pm_lib_layout : drv_lib_layoutA (PNHA.LayA art_L) art_L.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn. unfold PNHAS.STK. lia.
  - reflexivity.
  - intros iv Hin. cbn [PNHA.LayA PNTAL.TopLayA_a lla_foot] in Hin. rewrite PNTAL.foot_a_eq in Hin. unfold LIB_HOLES.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd];
      first [ (exists 0x6722c0, 0x672308; split; [cbn [In]; left; reflexivity | lia])
            | (exists 0x672530, 0x6733f0; split; [cbn [In]; right; left; reflexivity | lia])
            | (exists 0x693d50, 0x693f70; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
  - intros iv Hin. cbn in Hin. destruct Hin.
  - intros n Hn. cbn. unfold PNTS.TOPK. lia.
  - intros k Hk. cbn [PNHA.LayA PNTAL.TopLayA_a lla_leak lla_frames]. unfold PNHAS.LEAK, PNHAS.FRAMES, ff_cap, ff_bytes.
    cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; split; discriminate.
Qed.

Lemma pm_lib_cells : drv_lib_cellsA (PNHA.LayA art_L).
Proof.
  constructor; try reflexivity.
  - intros iv Hin. cbn [PNHA.LayA PNTAL.TopLayA_a lla_init_img] in Hin. unfold LIBINIT_IMG.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd];
      first [ (exists 65536, 1282048; split; [cbn [In]; left; reflexivity | lia])
            | (exists 1293304, 1293472; split; [cbn [In]; right; right; right; left; reflexivity | lia])
            | (exists 6759061, 6765616; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
  - cbn. lia.
  - intros iv Hin. cbn [PNHA.LayA PNTAL.TopLayA_a lla_initc] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.

Lemma pm_lib_budget : drv_budgetA art_L (PNHA.LayA art_L).
Proof.
  intros n Hn. unfold credA, CAPk, adebit. cbn [PNHA.LayA PNTAL.TopLayA_a lla_credit PNHAS.CREDIT PNTS.TOPK fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead].
  unfold PNTS.TOPK. lia.
Qed.
