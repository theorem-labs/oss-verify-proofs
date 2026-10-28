(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_rt_facts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"].


Lemma alloc_ceiling_top47 {L : heap_layout} : alloc_ceiling + 8 <= 2^47.
Proof. pose proof (@alloc_ceiling_hi L). cbn. lia. Qed.

(* [comment removed for export] *)
Lemma blk_top47 : ltac2:(CDefT.buildp (gd_tbl_A_rt_facts ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PB,$8.Pk,$8.P,(9.R9.R8.R7.R6.R5.R4.R3.)P,(:.(;.$8.$8.)(<.$8.$8.R3.R2.)R6.)(=.(>.(>.R4.R3.)+8.)(?.+2.+2?.))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m B k HH HIN. destruct (hm_apart segs R HIA h LB LF m HH) as [HF _].
  rewrite Forall_forall in HF. ddestruct (HF (B, k) ltac:(apply in_app_iff; left; exact HIN)) as (_ & _ & HC & _). cbn in HC.
  pose proof (@alloc_ceiling_top47 (arl_L R)). clear - H HC. lia.
Qed.

(* [comment removed for export] *)
Lemma cw_top47 : ltac2:(CDefT.buildp (gd_tbl_A_rt_facts ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PSP,$8.PA,$8.Pn,$8.P,(9.R:.R9.R8.R7.R6.R5.R4.)P,(10.(11.R:.)(12.$5.R7.(13.R6.))R4.(14.R;.R:.R9.R8.)R3.R2.)P,(15.=R3.)(=.(>.(>.R5.R4.)+8.)(?.+2.+2?.))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m SP A n HH CW Hn.
  pose proof (hm_top16 segs R HIA h LB LF m HH) as T16. pose proof (art_data_lo segs R HIA) as DLO. pose proof (@alloc_ceiling_top47 (arl_L R)) as C47.
  destruct (hm_apart segs R HIA h LB LF m HH) as [HF _]. rewrite Forall_forall in HF.
  destruct (CW (A + n - 1) ltac:(clear - Hn; lia)) as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]].
  - clear - Hs T16. lia.
  - clear - Hd1 DLO C47. lia.
  - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    + ddestruct (HF b ltac:(apply in_app_iff; left; exact Hb)) as (_ & _ & HC & _). clear - HC Hr C47. lia.
    + ddestruct (in_fdata_hull LF b (A + n - 1) Hb Hr) as (fb & Hfb & Hr2).
      ddestruct (HF fb ltac:(apply in_app_iff; right; exact Hfb)) as (_ & _ & HC & _). clear - HC Hr2 C47. lia.
Qed.

(* [comment removed for export] *)
Lemma cw_top47_or : ltac2:(CDefT.buildp (gd_tbl_A_rt_facts ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PSP,$8.PA,$8.Pn,$8.P,(9.R:.R9.R8.R7.R6.R5.R4.)P,(10.(11.R:.)(12.$5.R7.(13.R6.))R4.(14.R;.R:.R9.R8.)R3.R2.)P,(=.=R3.)(16.(17.$8.R4.=)(=.(>.(>.R5.R4.)+8.)(?.+2.+2?.)))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m SP A n HH CW Hn. destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
  eapply cw_top47; [exact HH| exact CW| clear - Hn NE; lia].
Qed.

Lemma blk_top47_sub : ltac2:(CDefT.buildp (gd_tbl_A_rt_facts ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PB,$8.Pk,$8.PA,$8.Pn,$8.P,(9.R;.R:.R9.R8.R7.R6.R5.)P,(:.(;.$8.$8.)(<.$8.$8.R5.R4.)R8.)P,(=.(>.R4.R3.)(>.R6.R5.))(16.(17.$8.R4.=)(=.(>.(>.R5.R4.)+8.)(?.+2.+2?.)))")
(* [comment removed for export] *).
Proof. intros segs R HIA h LB LF m B k A n HH HIN HS. right. pose proof (blk_top47 segs R HIA h LB LF m B k HH HIN). clear - H HS. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cw_top47_in : ltac2:(CDefT.buildp (gd_tbl_A_rt_facts ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PSP,$8.PA,$8.Pn,$8.PB,$8.Pk,$8.P,(9.R<.R;.R:.R9.R8.R7.R6.)P,(10.(11.R<.)(12.$5.R9.(13.R8.))R6.(14.R=.R<.R;.R:.)R5.R4.)P,(=.R6.R4.)P,(=.(>.R5.R4.)(>.R7.R6.))P,(=.=R5.)(16.(17.$8.R6.=)(=.(>.(>.R7.R6.)+8.)(?.+2.+2?.)))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m SP A n B k HH CW H1 H2 H3. destruct (Z.eq_dec k 0) as [E|NE]; [left; exact E| right].
  pose proof (cw_top47 segs R HIA h LB LF m SP A n HH CW ltac:(clear - H1 H2 H3 NE; lia)). clear - H H1 H2. lia.
Qed.
