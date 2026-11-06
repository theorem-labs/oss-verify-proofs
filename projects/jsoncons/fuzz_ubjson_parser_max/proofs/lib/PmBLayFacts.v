(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAJ JbtIfaceInst
Jb0DrvLibL Jb0DrvLibInit Jb0DrvG Jb0DrvMain PmTopAL PmBHarnessStmts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition art_IL : icpt_layout :=
ICL 0x62ce4 2304 0x10390 0x103b0
[(0x23160, 13); (0x231c0, 7); (0x231e0, 54); (0x233a0, 16); (0x233c0, 23); (0x23400, 13); (0x23420, 60); (0x23480, 77); (0x23500, 73);
(0x23580, 13); (0x235a0, 38); (0x23600, 70); (0x23680, 69); (0x23700, 37); (0x23760, 43); (0x237c0, 34); (0x23820, 71); (0x238a0, 28);
(0x238e0, 52)]
[(0x23160, 0x23940); (0x138ea0, 0x139360)]
0x77608 0x77604 0x691f78 0x62d5c 4320 [(0x670a90, 8, 0x690d88); (0x690db0, 8, 0)] 0x10000 0x136000.
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
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_b lla_foot PMTAL.foot_b app] in Hin. unfold PMTAL.ATEXIT_b in Hin. unfold LIB_HOLES.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
first [ (exists 0x66f0c0, 0x66f0c2; split; [cbn [In]; left; reflexivity | lia])
| (exists 0x66f2f0, 0x6701b0; split; [cbn [In]; right; left; reflexivity | lia])
| (exists 0x690b10, 0x690d30; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
- intros iv Hin. cbn in Hin. destruct Hin.
- intros n Hn. cbn. lia.
- intros k Hk. cbn [PMHAS.Lay PMTAL.TopLayA_b lla_leak lla_frames]. unfold PMHAS.LEAK, PMHAS.FRAMES, ff_cap, ff_bytes.
cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; vm_compute; split; discriminate.
Qed.
Lemma pm_lib_cells : drv_lib_cellsA (PMHAS.Lay art_L).
Proof.
constructor; try reflexivity.
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_b lla_init_img] in Hin. unfold LIBINIT_IMG.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd];
first [ (exists 65536, 1269760; split; [cbn [In]; left; reflexivity | lia])
| (exists 1280728, 1280896; split; [cbn [In]; right; right; right; left; reflexivity | lia])
| (exists 6746257, 6746260; split; [cbn [In]; right; left; reflexivity | lia])
| (exists 6746261, 6752752; split; [cbn [In]; right; right; left; reflexivity | lia]) ].
- cbn. lia.
- intros iv Hin. cbn [PMHAS.Lay PMTAL.TopLayA_b lla_initc] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.
Lemma pm_lib_budget : drv_budgetA art_L (PMHAS.Lay art_L).
Proof.
intros n Hn. unfold credA, CAPk, adebit. cbn [PMHAS.Lay PMTAL.TopLayA_b lla_credit PMHAS.CREDIT fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead].
lia.
Qed.
