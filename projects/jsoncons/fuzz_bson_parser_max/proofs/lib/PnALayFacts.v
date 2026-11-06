(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAB BatIfaceInst
     Ba0DrvLibL Ba0DrvLibInit Ba0DrvG Ba0DrvMain PnTopS PnTopAL PnAHarnessStmts PnAHarness.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x62fa4 2304 0x103a8 0x103c8
      [(0x231a0, 13); (0x23200, 7); (0x23220, 54); (0x232e0, 14); (0x23300, 23); (0x23340, 13); (0x23360, 38); (0x233c0, 43); (0x23420, 66); (0x234a0, 62); (0x23500, 22);
       (0x23540, 17); (0x23580, 26); (0x235c0, 19); (0x23600, 19); (0x23640, 23); (0x23680, 21); (0x236c0, 48); (0x23720, 26); (0x23860, 54); (0x238c0, 9); (0x238e0, 4);
       (0x23900, 39); (0x12f740, 112)]
      [(0x231a0, 0x23960); (0x12f740, 0x12f7e0); (0x139ae0, 0x13a0e0)]
      0x778c8 0x778c4 0x692d38 0x6301c 4320 [(0x671850, 8, 0x691b48); (0x691b70, 8, 0)] 0x10000 0x136000.
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
      first [ (exists 0x66fe40, 0x66fe88; split; [cbn [In]; left; reflexivity | lia])
            | (exists 0x6700b0, 0x670f70; split; [cbn [In]; right; left; reflexivity | lia])
            | (exists 0x6918d0, 0x691af0; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
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
      first [ (exists 65536, 1269760; split; [cbn [In]; left; reflexivity | lia])
            | (exists 1283856, 1284024; split; [cbn [In]; right; right; right; left; reflexivity | lia])
            | (exists 6749717, 6756272; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
  - cbn. lia.
  - intros iv Hin. cbn [PNHA.LayA PNTAL.TopLayA_a lla_initc] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.

Lemma pm_lib_budget : drv_budgetA art_L (PNHA.LayA art_L).
Proof.
  intros n Hn. unfold credA, CAPk, adebit. cbn [PNHA.LayA PNTAL.TopLayA_a lla_credit PNHAS.CREDIT PNTS.TOPK fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead].
  unfold PNTS.TOPK. lia.
Qed.
