(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc EdBridge EdEvNode.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QiVh.
Import ListNotations.

From Stdlib Require NArith FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QwNp Qnhz Qpox QsV0 QsRG Qrxj QSjk Qn1e QBxa Q9ox QMz4 Q6q3 QSpR QuJV.

Module Mm.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QJyS QwNp Qnhz.Mq1 Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3 QBxa.Mq0 Q9ox.Mq0 QSpR.Mq2 QMz4 QSpR.Mq0 QSpR.Mq1.
Import QuJV.Mq1.
Import ListNotations.
Open Scope bv_scope.
Import Q6q3.

Lemma mmap_outcome_ekept (segs : list Segment) : forall ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  ekept (sys_input segs ms x8) model o <->
  (mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
   /\ exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
  \/ (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ o = Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
               (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros ms x8 model o Hno Ha.
  refine (ekept_arm (sys_input segs ms x8) model
    (mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
    (fun o => exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    (fun o => exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ o = Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
               (mmap_model a (page_round_up (ms_gpr ms 1)) model) [])
    _ _ _ _ _ o).
  - right. left. exact Hno.
  - intros o'. exact (mmap_outcome_si segs ms x8 model o' Hno Ha).
  - intros o' (e & He & ->). do 3 eexists. split; [reflexivity |]. destruct He as [<- | []]. reflexivity.
  - intros o' (a & Hg & ->). do 3 eexists. split; [reflexivity |]. change (a <> errno_ret ENOMEM).
    unfold grant_ok in Hg. rewrite !andb_true_iff in Hg. destruct Hg as [[[[_ _] G3] _] _].
    apply (ed_below_top_ne_enomem a (m_vmmaps model) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
      [apply ed_nZ_nonneg | apply Z.leb_le; exact G3].
  - apply ekept_bool. split.
    + intros HR. destruct Ha as (_ & _ & H3 & _ & _). rewrite H3 in HR.
      destruct (not_refusable_grant_ok (ms_gpr ms 0) model _ HR) as [a Hg].
      eexists. exists a. split; [exact Hg | reflexivity].
    + intros (o' & a & Hg & _). exact (grant_ok_not_refusable _ _ _ _ _ Hg).
Qed.

Lemma mmap_outcome_live (segs : list Segment) : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> m_halted model = None ->
  forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None.
Proof.
  intros ms x8 model Hno Ha Hh eff m' evs Hs.
  apply (mmap_outcome_si segs ms x8 model _ Hno Ha) in Hs.
  destruct Hs as [(e & _ & E) | (a & _ & E)]; injection E as _ E2 _; rewrite E2; exact Hh.
Qed.

End Mm.

Module Ms.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QJyS QwNp QMz4 Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3 QBxa.Mq0 Q9ox.Mq0.
Import QSpR.Mq2.
Import Q6q3.
Import ListNotations.
Open Scope bv_scope.

Lemma mmap_noaccess_outcome_ekept (segs : list Segment) : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  forall o, ekept (sys_input segs ms x8) model o <->
  (mmap_reserve_refusable model n = true
   /\ exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
  \/ (exists a, grant_ok_na (ms_gpr ms 0) model a n = true
      /\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (noaccess_model a (Z_to_bv 64 n) model) []).
Proof.
  intros ms x8 model Hno Ha n o.
  refine (ekept_arm (sys_input segs ms x8) model (mmap_reserve_refusable model n = true)
    (fun o => exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    (fun o => exists a, grant_ok_na (ms_gpr ms 0) model a n = true
      /\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (noaccess_model a (Z_to_bv 64 n) model) [])
    _ _ _ _ _ o).
  - right. left. exact Hno.
  - intros o'. exact (mmap_noaccess_outcome_si segs ms x8 model Hno Ha o').
  - intros o' (e & He & ->). do 3 eexists. split; [reflexivity |]. destruct He as [<- | []]. reflexivity.
  - intros o' (a & Hg & ->). do 3 eexists. split; [reflexivity |]. change (a <> errno_ret ENOMEM).
    unfold grant_ok_na in Hg. rewrite !andb_true_iff in Hg. destruct Hg as [[[_ _] G3] _].
    apply (ed_below_top_ne_enomem a (m_vmmaps model) n); [apply ed_nZ_nonneg | apply Z.leb_le; exact G3].
  - apply ekept_bool. split.
    + intros HR. destruct (not_refusable_grant_ok_na (ms_gpr ms 0) model n HR) as [a Hg].
      eexists. exists a. split; [exact Hg | reflexivity].
    + intros (o' & a & Hg & _). exact (grant_ok_na_not_refusable _ _ _ _ Hg).
Qed.

Lemma mmap_noaccess_outcome_live (segs : list Segment) : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms -> m_halted model = None ->
  forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None.
Proof.
  intros ms x8 model Hno Ha Hh eff m' evs Hs.
  apply (mmap_noaccess_outcome_si segs ms x8 model Hno Ha) in Hs.
  destruct Hs as [(e & _ & E) | (a & _ & E)]; injection E as _ E2 _; rewrite E2; exact Hh.
Qed.

Lemma mprotect_outcome_ekept (segs : list Segment) : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  m_halted model = None ->
  (forall o, ekept (sys_input segs ms x8) model o <->
    (mprotect_refusable model addr n = true
     /\ exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []))
  /\ (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None).
Proof.
  intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma Hh.
  pose proof (mprotect_outcome_si segs ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  split.
  - intros o.
    refine (ekept_arm (sys_input segs ms x8) model (mprotect_refusable model addr n = true)
      (fun o => exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
      (fun o => mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) [])
      _ Hchk _ _ _ o).
    + right. right. exact Hno.
    + intros o' (e & He & ->). do 3 eexists. split; [reflexivity |]. destruct He as [<- | []]. reflexivity.
    + intros o' (Hb & ->). do 3 eexists. split; [reflexivity |].
      change (Z_to_bv 64 0 <> errno_ret ENOMEM). exact ed_zero_ne_enomem.
    + apply ekept_bool. rewrite mprotect_refusable_budget. split.
      * intros HR. apply Bool.negb_false_iff in HR. eexists. split; [exact HR | reflexivity].
      * intros (o' & Hb & _). rewrite Hb. reflexivity.
  - intros eff m' evs Hs. apply Hchk in Hs.
    destruct Hs as [(e & _ & E) | (_ & E)]; injection E as _ E2 _; rewrite E2; exact Hh.
Qed.

Section RCF.
Context {RC__ : Q6q3.RunConsts}.

Lemma mmap_fixed_outcome_ekept (segs : list Segment) : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
  alloc_top (m_vmmaps model) = alloc_ceiling ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  m_halted model = None ->
  (forall o, ekept (sys_input segs ms x8) model o <->
    o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) [])
  /\ (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None).
Proof.
  intros ms x8 model addr len Hno Ha H0 Hal Hpos H1 Hlen Hce Hceil n Hrf Hmc Hh.
  pose proof (mmap_fixed_outcome_si segs ms x8 model addr len Hno Ha H0 Hal Hpos H1 Hlen Hce Hceil Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Hne : addr <> errno_ret ENOMEM).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)) as B.
    apply (ed_below_top_ne_enomem addr (m_vmmaps model) (page_round_up_Z len)); [lia | rewrite Hceil; exact Hce]. }
  assert (Hk : forall o, ekept (sys_input segs ms x8) model o <->
    (False /\ ((exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
               \/ (exists e, In e mmap_errnos /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                     (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) [])))
    \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) []).
  { intros o.
    refine (ekept_arm (sys_input segs ms x8) model False
      (fun o => (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
                \/ (exists e, In e mmap_errnos /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                      (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []))
      (fun o => o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) [])
      _ _ _ _ _ o).
    - right. left. exact Hno.
    - intros o'. rewrite (Hchk o'). tauto.
    - intros o' [(e & He & ->) | (e & He & ->)]; do 3 eexists; (split; [reflexivity |]);
        destruct He as [<- | []]; reflexivity.
    - intros o' ->. do 3 eexists. split; [reflexivity |]. change (addr <> errno_ret ENOMEM). exact Hne.
    - split; [intros [] | intros HN; apply HN; eexists; reflexivity]. }
  split.
  - intros o. rewrite (Hk o). tauto.
  - intros eff m' evs Hs. apply Hchk in Hs.
    destruct Hs as [E | [(e & _ & E) | (e & _ & E)]]; injection E as _ E2 _; rewrite E2; exact Hh.
Qed.

End RCF.

End Ms.
