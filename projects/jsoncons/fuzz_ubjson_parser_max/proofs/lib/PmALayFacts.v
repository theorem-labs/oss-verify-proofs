(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAJ JatIfaceInst
Ja0DrvLibL Ja0DrvLibInit Ja0DrvG Ja0DrvMain PmTopAL PmAHarnessStmts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition art_IL : icpt_layout :=
ICL 0x62a14 2304 0x10390 0x103b0
[(0x23100, 13); (0x23160, 7); (0x23180, 54); (0x23340, 16); (0x23360, 23); (0x233a0, 13); (0x233c0, 60); (0x23420, 77); (0x234a0, 73);
(0x23520, 13); (0x23540, 38); (0x235a0, 70); (0x23620, 69); (0x236a0, 37); (0x23700, 43); (0x23760, 34); (0x237c0, 71); (0x23840, 28);
(0x23880, 52); (0x12cda0, 104)]
[(0x23100, 0x238e0); (0x12cda0, 0x12ce40); (0x137140, 0x137640)]
0x77338 0x77334 0x690238 0x62a8c 4320 [(0x66ed50, 8, 0x68f048); (0x68f070, 8, 0)] 0x10000 0x134000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.
Definition BUDGET0 : Z := 2 ^ 34.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0. Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35. Proof. unfold BUDGET0. lia. Qed.
Lemma pm_lib_layout : drv_lib_layoutA (PMHAS.Lay art_L) art_L.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn. unfold PMHAS.STK. lia.
- reflexivity.
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_a lla_foot PMTAL.foot_a app] in Hin. unfold PMTAL.ATEXIT_a in Hin. unfold LIB_HOLES.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
first [ (exists 0x66d380, 0x66d382; split; [cbn [In]; left; reflexivity | lia])
| (exists 0x66d5b0, 0x66e470; split; [cbn [In]; right; left; reflexivity | lia])
| (exists 0x68edd0, 0x68eff0; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
- intros iv Hin. cbn in Hin. destruct Hin.
- intros n Hn. cbn. lia.
- intros k Hk. cbn [PMHAS.Lay PMTAL.TopLayA_a lla_leak lla_frames]. unfold PMHAS.LEAK, PMHAS.FRAMES, ff_cap, ff_bytes.
cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; vm_compute; split; discriminate.
Qed.
Lemma pm_lib_cells : drv_lib_cellsA (PMHAS.Lay art_L).
Proof.
constructor; try reflexivity.
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_a lla_init_img] in Hin. unfold LIBINIT_IMG.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd];
first [ (exists 65536, 1261568; split; [cbn [In]; left; reflexivity | lia])
| (exists 1273200, 1273368; split; [cbn [In]; right; right; right; left; reflexivity | lia])
| (exists 6738769, 6738772; split; [cbn [In]; right; left; reflexivity | lia])
| (exists 6738773, 6745264; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
- cbn. lia.
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_a lla_initc] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.
Lemma pm_lib_budget : drv_budgetA art_L (PMHAS.Lay art_L).
Proof.
intros n Hn. unfold credA, CAPk, adebit. cbn [PMHAS.Lay PMTAL.TopLayA_a lla_credit PMHAS.CREDIT fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead].
lia.
Qed.
