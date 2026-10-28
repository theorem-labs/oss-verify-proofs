(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmSpecs PgSrc PgV8 PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAPAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma aobj_fbB FF fb a n : PNRA.frame_okB FF fb -> fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof.
  intros ((rs & Hf) & _) X1 X2. exists (fb, 5, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
Qed.
Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  rewrite Dm. replace (2048 * (fb / 2048) + 8 * k) with ((256 * (fb / 2048) + k) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma op_visB LB FF LK cr Aw M model fb ois s :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PNRA.frame_okB FF fb ->
  PNM.bparser_at RSEGS PMA.AD accA annA (pa_vp_parser PMA.AD) M (fb + 464) ois s -> accA M (fb + 464) 424 ->
  let op := fb + 464 in let MV := mrestrict (ahid Aw model) M in
  (6905856 <= op <= 140737488354904 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 424 <= 2147446784))
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 53
  /\ L5.writable RSEGS MV op 424 /\ op + 424 <= ahl_ceil ar
  /\ (forall a n, op <= a -> a + n <= op + 424 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF op 424.
Proof.
  intros HH FOK PA OACC op MV.
  pose proof FOK as ((rs & Hf) & F2048).
  assert (AO : PMSPA.aobjA FF op 424) by (apply (aobj_fbB FF fb op 424 FOK); unfold op; lia).
  assert (O8 : op mod 8 = 0) by (unfold op; replace 464 with (8 * 58) by reflexivity; apply fb_mod8; exact F2048).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model op 424 0 0 HH (PMKA.aobj_of_aobjA FF op 424 AO O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  assert (Zop : L5KA.zeros_at MV (op / 8 + SB) (424 / 8)).
  { apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model op 424 HH AO O8); [lia| reflexivity| exact OACC]. }
  change (424 / 8) with 53 in Zop. unfold SB in Zop.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zop|].
  split; [apply (proj2 (L5A.writable_vis _ M op 424 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]| exact AO].
Qed.

(* [comment removed for export] *)
Lemma ov_visB LB FF LK cr Aw M model fb :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PNRA.frame_okB FF fb -> PMSPA.visitor_at RSEGS PMA.AD M (fb + 432) ->
  let ov := fb + 432 in let MV := mrestrict (ahid Aw model) M in
  (6905856 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784))
  /\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ov + 8 <= ahl_ceil ar
  /\ L5.u64_at RSEGS MV ov (pa_vp_visitor PMA.AD) /\ PMSPA.aobjA FF ov 8.
Proof.
  intros HH FOK (VU & VC) ov MV.
  pose proof FOK as ((rs & Hf) & F2048).
  assert (AO : PMSPA.aobjA FF ov 8) by (apply (aobj_fbB FF fb ov 8 FOK); unfold ov; lia).
  assert (O8 : ov mod 8 = 0) by (unfold ov; replace 432 with (8 * 54) by reflexivity; apply fb_mod8; exact F2048).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 0 0 HH (PMKA.aobj_of_aobjA FF ov 8 AO O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  assert (Zov : L5KA.zeros_at MV (ov / 8 + SB) (8 / 8)) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 HH AO O8 ltac:(lia) ltac:(reflexivity) VC).
  change (8 / 8) with 1 in Zov. unfold SB in Zov.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis _ M ov 8 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|].
  split; [apply (proj2 (L5A.u64_at_vis _ M ov _ OVIS ltac:(lia) ltac:(lia))); exact VU| exact AO].
Qed.

(* [comment removed for export] *)
Lemma oec_visB LB FF LK cr Aw M model fb v c :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PNRA.frame_okB FF fb -> PMSPA.ec_at RSEGS M (fb + 1024) v c ->
  let oec := fb + 1024 in let MV := mrestrict (ahid Aw model) M in
  (6905856 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784))
  /\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ oec + 16 <= ahl_ceil ar
  /\ L5.u32_at RSEGS MV oec v /\ L5.u64_at RSEGS MV (oec + 8) c /\ PMSPA.aobjA FF oec 16.
Proof.
  intros HH FOK (EU & EU8 & ED & EC) oec MV.
  pose proof FOK as ((rs & Hf) & F2048).
  assert (AO : PMSPA.aobjA FF oec 16) by (apply (aobj_fbB FF fb oec 16 FOK); unfold oec; lia).
  assert (O8 : oec mod 8 = 0) by (unfold oec; replace 1024 with (8 * 128) by reflexivity; apply fb_mod8; exact F2048).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 0 0 HH (PMKA.aobj_of_aobjA FF oec 16 AO O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  assert (Zo : L5KA.zeros_at MV (oec / 8 + SB) (16 / 8)) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 HH AO O8 ltac:(lia) ltac:(reflexivity) EC).
  change (16 / 8) with 2 in Zo. unfold SB in Zo.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zo|].
  split; [apply (proj2 (L5A.writable_vis _ M oec 16 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|].
  split; [apply (proj2 (L5A.u32_at_vis _ M oec v (L5A.avis_sub _ oec 16 oec 4 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EU|].
  split; [apply (proj2 (L5A.u64_at_vis _ M (oec + 8) c (L5A.avis_sub _ oec 16 (oec + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EU8| exact AO].
Qed.

(* [comment removed for export] *)
Lemma bparser_keepA LB FF LK cr Aw V W sp scr M M' op ois s :
  ri_inv HI LB FF LK cr Aw M V -> L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W ->
  PMSPA.aobjA FF op PNM.PSIZE -> incl (PNM.bparser_own s) LB ->
  (forall i, op <= i < op + PNM.PSIZE -> L5.outside W i) ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> PMKA.blk_out W B m) ->
  PNM.bparser_at RSEGS PMA.AD accA annA (pa_vp_parser PMA.AD) M op ois s -> PNM.bparser_at RSEGS PMA.AD accA annA (pa_vp_parser PMA.AD) M' op ois s.
Proof.
  intros HH EK WAPP AO INC OW OB PA.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  destruct (PMKA.aobjA_bounds FF FRB op PNM.PSIZE AO) as [O0 O1].
  apply (PNBOA.bparser_keepS RSEGS PMA.AD (pa_vp_parser PMA.AD) M M' op ois s); [exact O0| unfold PNM.PSIZE in *; lia| | | exact PA].
  - exact (PMKA.agA_obj L ar LB FF sp scr W M M' EK WAPP FRB op PNM.PSIZE AO OW).
  - intros B m Hi. destruct (BRB _ (INC _ Hi)) as [B0 B1]. cbn [fst snd] in B0, B1.
    split; [exact B0|]. split; [lia|]. exact (PMKA.agA_blk L ar LB FF sp scr W M M' EK WAPP BRB B m (INC _ Hi) (OB B m Hi)).
Qed.

End WithHeap.
End PNAPAR.
