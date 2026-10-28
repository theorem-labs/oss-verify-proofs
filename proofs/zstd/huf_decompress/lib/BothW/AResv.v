(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl BothHandoff.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AsanPlan MainExport MainFactsBoth.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase AMalloc_iface ARepInit_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AResv () := "C46Stdlib5Lists4List2InC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7resv_ofC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport2zvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff5iv_ofC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List;in_flat_mapK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib5Lists4List7map_appK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface4pcovC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06I5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth;asan_ledgerI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC46Stdlib5Lists4List8nil_consI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff4uns2C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_indC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic7and_indK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff=reserved_evalI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okI47Corelib5Lists7ListDef6Forall00K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact01C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff:pfact_findc5ARocqVerifyHarness?AgentSubmission5BothW5AResv8resv_imgK5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry02C47Corelib4Init5Logic5proj1c5ARocqVerifyHarness?AgentSubmission5BothW5AResv8resv_litC47Corelib4Init5Logic5proj2c5ARocqVerifyHarness?AgentSubmission5BothW5AResv:resv_namedC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit2LVK5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8aresv_okC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9pfact_eqbC46Stdlib5Lists4List7existsbC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_VI5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_factsK6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind01K6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind02K6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind04".
Import ListNotations. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma resv_named : forall V k n kd lo hi,
  In (LMap (ZMul (ZLit 4096) (ZV k)) n kd) asan_ledger ->
  0 <= V k <= 34359738368 -> 0 <= n < 2^62 ->
  4096 * V k <= lo -> hi <= 4096 * V k + n ->
  pcov (resv_of V) lo hi.
Proof using Type.
  intros V k n kd lo hi HIN HV HN LO HI x Hx.
  exists (4096 * V k, 4096 * V k + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZMul (ZLit 4096) (ZV k))), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZMul (ZLit 4096) (ZV k)) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma resv_lit : forall V b n kd lo hi,
  In (LMap (ZLit b) n kd) asan_ledger ->
  0 <= b < 2^62 -> 0 <= n < 2^62 ->
  b <= lo -> hi <= b + n ->
  pcov (resv_of V) lo hi.
Proof using Type.
  intros V b n kd lo hi HIN HB HN LO HI x Hx.
  exists (b, b + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZLit b)), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZLit b) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma resv_img : forall V, pcov (resv_of V) 0x10000 AIMG_HI.
Proof using Type.
  intros V x Hx. unfold AIMG_HI in Hx.
  assert (SEG : forall b n, In (b, n) (map uns2 (segments_reserved bsegs)) -> In (b, b + n) (resv_of V)).
  { intros b n Hin. apply in_map_iff in Hin. destruct Hin as ([a m] & E & Hin). unfold uns2 in E. cbn [fst snd] in E. injection E as <- <-.
    unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. right. apply in_map_iff. exists (a, m). split; [reflexivity| exact Hin]. }
  rewrite reserved_eval in SEG.
  destruct (Z_lt_le_dec x 196608); [| destruct (Z_lt_le_dec x 724992); [| destruct (Z_lt_le_dec x 733184)]].
  - exists (65536, 65536 + 131072). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (196608, 196608 + 528384). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (724992, 724992 + 8192). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (733184, 733184 + 5619712). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
Qed.

End CANSEC1.
Local Ltac inled := cbn; repeat (first [left; reflexivity | right]).
(* [comment removed for export] *)
Local Ltac pv PF k lo hi :=
  let H := fresh in pose proof (pfact_find _ (PVar k lo hi) PF ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok] in H.

Section CANSEC2. Context {rc : runConstT}.
Theorem aresv_ok_handoff : forall V (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts ->
  aresv_ok (mkALayout (LV V) w U) (resv_of V).
Proof.
  intros V w U PF.
  pv PF 78%nat 1551 34359736304. pv PF 207%nat 1551 34359735410. pv PF 208%nat 4295491576 34326181871.
  pv PF 226%nat 1551 34359734272. pv PF 227%nat 1 34359736319. pv PF 228%nat 1551 34359736304.
  pv PF 245%nat 1 34359736319. pv PF 310%nat 1 34359736319. pv PF 377%nat 1551 34359733495.
  pv PF 453%nat 1551 34359736064. pv PF 454%nat 1551 34359734272. pv PF 471%nat 1 34359736319.
  unfold aresv_ok, al_space_beg, al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake. cbv [al_V LV Nat.eqb].
  split; [apply resv_img|].
  split.
  {
    intros x Hx.
    destruct (Z_lt_le_dec x 0x8fff7000); [| destruct (Z_lt_le_dec x 0x2008fff7000)].
    - eapply (resv_lit V 2147446784 268435456 KRWLAZY); [inled| lia| lia| | | exact (conj (proj1 Hx) l)]; cbn; lia.
    - eapply (resv_lit V 2415882240 2199023255552 KNONELAZY); [inled| lia| lia| | | exact (conj l l0)]; cbn; lia.
    - eapply (resv_lit V 2201439137792 15392894357504 KRWLAZY); [inled| lia| lia| | | exact (conj l0 (proj2 Hx))]; cbn; lia. }
  split; [eapply (resv_named V 208 137439023104 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 226 8388608 KNONELAZY); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 227 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 228 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 453 1048576 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 454 8388608 KRWLAZY); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 377 11571200 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 310 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 78 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 207 3727360 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 245 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia].
Qed.
End CANSEC2.
