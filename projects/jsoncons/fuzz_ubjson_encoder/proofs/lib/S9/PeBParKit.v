(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmSpecs PmParKit PeBSrcKitJ LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBPAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma parser_pop_updA (M M' : word -> option byte) op ois s :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 8 -> PMFA.agA M M' (op + 9) 3 -> PMFA.agA M M' (op + 16) 344 -> PMFA.agsh M M' op 384 -> L5.defined M' op 384 ->
  L5.u8_at RSEGS M' (op + 8) 1 -> L5.u32_at RSEGS M' (op + 12) (PM.p_depth s - 1) -> 0 <= PM.p_depth s - 1 ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA M' (op + 360) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s)) ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agA M M' p c) ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M' op ois
    (PM.PST 1 (PM.p_done s) (PM.p_depth s - 1) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s))).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 _] [AG9 _] AG2 SH D' C8 C12 Hd VEC' Hq Hq' AGQ AGT.
  pose proof AG2 as [AG2d _].
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 360 -> PMFA.agA M M' a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG1| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [exact C8|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
  split; [exact C12|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PeCLayoutB.CADDR_B M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [exact VEC'|].
  split; [right; reflexivity|]. split; [exact B2|]. unfold PM.MAX_DEPTH in *. lia.
Qed.

Lemma src_step_transA src1 src2 src3 sm1 sm2 sm3 :
  PMSPA.src_step src1 src2 sm1 sm2 -> PMSPA.src_step src2 src3 sm2 sm3 -> PMSPA.src_step src1 src3 sm1 sm3.
Proof.
  unfold PMSPA.src_step. intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply B4; apply A4; exact X| lia].
Qed.

Lemma parser_more_updA (M M' : word -> option byte) op ois s v :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 8 -> PMFA.agA M M' (op + 9) 375 -> PMFA.agsh M M' op 384 -> L5.defined M' op 384 ->
  L5.u8_at RSEGS M' (op + 8) v -> (v = 0 \/ v = 1) ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agA M M' p c) ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M' op ois (PMPK.set_more s v).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 _] AG2 SH D' C8 Hv Hq Hq' AGQ Hb Hb' AGV AGT.
  pose proof AG2 as [AG2d _].
  unfold PMPK.set_more, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 9 <= a -> a + n <= op + 384 -> PMFA.agA M M' a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG1| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [exact C8|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 9) 1); lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PeCLayoutB.CADDR_B M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
  split; [exact Hv|]. split; [exact B2| exact B3].
Qed.

Lemma src_accJ (M : word -> option byte) (op ois : Z) (s : PM.pst) :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> PMSPA.accA M (op + 32) 288.
Proof.
  intros PA. destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & NI & SF & _).
  destruct NI as (_ & _ & NC & _ & _ & IOS). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC).
  destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  intros a Ha. destruct (Z_lt_le_dec a (op + 32 + 80)) as [X|X]; [apply NC; lia|].
  destruct (Z_lt_le_dec a (op + 32 + 80 + 152)) as [Y|Y]; [apply IC; lia|]. apply SC; lia.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma op_vis LB FF LK cr Aw M model fb ois s :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M (PMSPA.o_p PeCLayoutB.CADDR_B fb) ois s ->
  let op := PMSPA.o_p PeCLayoutB.CADDR_B fb in let MV := mrestrict (ahid Aw model) M in
  (6930432 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784))
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44
  /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
  /\ L5.writable RSEGS MV op 384 /\ op + 384 <= ahl_ceil ar
  /\ (forall a n, op <= a -> a + n <= op + 384 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF op 384 /\ op = fb + 592.
Proof.
  intros HH FOK PA op MV.
  assert (Eop : op = fb + 592) by reflexivity.
  pose proof FOK as ((rs & Hf) & F1024).
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n).
  { intros a n X1 X2. exists (fb, 5, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (O8 : op mod 8 = 0).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model op 384 0 0 HH (PMKB.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  pose proof PA as (_ & _ & PC0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PC320 & _).
  pose proof (src_accJ M op ois s PA) as CS.
  assert (C32 : PMSPA.accA M (op + 32) 352).
  { intros a Ha. destruct (Z_lt_le_dec a (op + 320)) as [Y|Y]; [apply CS; lia| apply PC320; lia]. }
  assert (Zop : L5KA.zeros_at MV (op / 8 + SB) (24 / 8)).
  { apply (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model op 24 HH (AOF op 24 ltac:(lia) ltac:(lia)) O8); [lia| reflexivity| exact PC0]. }
  assert (Z32 : L5KA.zeros_at MV ((op + 32) / 8 + SB) (352 / 8)).
  { apply (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (op + 32) 352 HH (AOF (op + 32) 352 ltac:(lia) ltac:(lia))); [| lia| reflexivity| exact C32].
    replace (op + 32) with (op + 4 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
  change (24 / 8) with 3 in Zop. change (352 / 8) with 44 in Z32. unfold SB in Zop, Z32.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zop|]. split; [exact Z32|].
  split.
  { assert (E20 : (op + 20) / 8 = op / 8 + 2).
    { replace (op + 20) with (4 + (op / 8 + 2) * 8) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
    rewrite E20. intros i Hi. replace (op / 8 + 2 + 2147450880 + i) with (op / 8 + 2147450880 + (2 + i)) by lia. apply Zop. lia. }
  split; [apply (proj2 (L5A.writable_vis _ M op 384 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [apply AOF; lia| exact Eop].
Qed.

Lemma ov_vis LB FF LK cr Aw M model fb :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb -> PMSPA.visitor_at RSEGS PeCLayoutB.CADDR_B M (PMSPA.o_v PeCLayoutB.CADDR_B fb) ->
  let ov := PMSPA.o_v PeCLayoutB.CADDR_B fb in let MV := mrestrict (ahid Aw model) M in
  (6930432 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784))
  /\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ov + 8 <= ahl_ceil ar
  /\ L5.u64_at RSEGS MV ov 1277312 /\ PMSPA.aobjA FF ov 8 /\ ov = fb + 496.
Proof.
  intros HH FOK (VU & VC) ov MV.
  assert (Eov : ov = fb + 496) by reflexivity.
  pose proof FOK as ((rs & Hf) & F1024).
  assert (AO : PMSPA.aobjA FF ov 8).
  { exists (fb, 5, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (O8 : ov mod 8 = 0).
  { rewrite Eov. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (2048 * (fb / 2048) + 496) with ((256 * (fb / 2048) + 62) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 0 0 HH (PMKB.aobj_of_aobjA FF ov 8 AO O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  assert (Zov : L5KA.zeros_at MV (ov / 8 + SB) (8 / 8)) by exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 HH AO O8 ltac:(lia) ltac:(reflexivity) VC).
  change (8 / 8) with 1 in Zov. unfold SB in Zov.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zov|].
  split; [apply (proj2 (L5A.writable_vis _ M ov 8 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|].
  split; [apply (proj2 (L5A.u64_at_vis _ M ov 1277312 OVIS ltac:(lia) ltac:(lia))); exact VU|].
  split; [exact AO| exact Eov].
Qed.

Lemma base_keepW LB FF sp scr W M M' :
  L5SAR.ek L ar LB FF sp scr W M M' ->
  (forall a, 65536 <= a < 0x13f000 -> L5.outside W a) -> (forall a, 0x69a1c0 <= a < 0x69a1c8 -> L5.outside W a) ->
  L5.outside W 0x69a413 -> (forall a, 0x69a4f0 <= a < 0x69a4f4 -> L5.outside W a) ->
  PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M -> PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M'.
Proof.
  intros E O1 O2 O3 O4 (RO0 & (can & Hcan & CAN) & NL & LL).
  assert (AGD : forall a, 0 <= a < 2 ^ 64 -> PMST.dep PeCLayoutB.CADDR_B a -> L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha D Ho. apply E. split; [exact Ha|]. split; [|exact Ho]. unfold aclient, aclient_g. right; right; left.
    pose proof (PMBSKJ.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))]. }
  cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PeCLayoutB.CADDR_B ADDR_A] in *.
  split; [|split; [|split]].
  - intros i Hi. cbn [pa_rw_lo PeCLayoutB.CADDR_B ADDR_A] in Hi. rewrite E; [apply RO0; cbn [pa_rw_lo PeCLayoutB.CADDR_B ADDR_A]; exact Hi|]. split; [lia|]. split; [| apply O1; lia]. unfold aclient, aclient_g. right; right; left.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| intros X; pose proof (L5A.aly_static_lo L C LYa _ X); lia].
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [|cbn [pa_canary PeCLayoutB.CADDR_B ADDR_A]; lia|cbn [pa_canary PeCLayoutB.CADDR_B ADDR_A]; lia| exact CAN]. intros i Hi. cbn [pa_canary PeCLayoutB.CADDR_B ADDR_A] in Hi. apply AGD; [lia| right; left; cbn [pa_canary PeCLayoutB.CADDR_B ADDR_A]; lia| apply O2; lia].
  - cbn [pa_need_locks PeCLayoutB.CADDR_B ADDR_A] in NL |- *. apply (L5C.u8_at_agree RSEGS M M'); [|lia|lia| exact NL]. intros i Hi.
    apply AGD; [lia| apply PMST.in_foot_nl; cbn [pa_need_locks PeCLayoutB.CADDR_B ADDR_A]; lia| replace i with 0x69a413 by lia; exact O3].
  - cbn [pa_locale_lock PeCLayoutB.CADDR_B ADDR_A] in LL |- *. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat 0x69a4f0); [exact LL| lia| cbn; lia|].
    intros i Hi. cbn in Hi. apply AGD; [lia| apply PMST.in_foot_ll; cbn [pa_locale_lock PeCLayoutB.CADDR_B ADDR_A]; lia| apply O4; lia].
Qed.

Lemma oec_vis LB FF LK cr Aw M model fb v c :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb -> PMSPA.ec_at RSEGS M (PMSPA.o_ec PeCLayoutB.CADDR_B fb) v c ->
  let oec := PMSPA.o_ec PeCLayoutB.CADDR_B fb in let MV := mrestrict (ahid Aw model) M in
  (6930432 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784))
  /\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ oec + 16 <= ahl_ceil ar
  /\ L5.u32_at RSEGS MV oec v /\ PMSPA.aobjA FF oec 16 /\ oec = fb + 1120.
Proof.
  intros HH FOK (EU & EU8 & ED & EC) oec MV.
  assert (Eo : oec = fb + 1120) by reflexivity.
  pose proof FOK as ((rs & Hf) & F1024).
  assert (AO : PMSPA.aobjA FF oec 16).
  { exists (fb, 5, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (O8 : oec mod 8 = 0).
  { rewrite Eo. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (2048 * (fb / 2048) + 1120) with ((256 * (fb / 2048) + 140) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 0 0 HH (PMKB.aobj_of_aobjA FF oec 16 AO O8)
                ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
  assert (Zo : L5KA.zeros_at MV (oec / 8 + SB) (16 / 8)) by exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 HH AO O8 ltac:(lia) ltac:(reflexivity) EC).
  change (16 / 8) with 2 in Zo. unfold SB in Zo.
  split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
  split; [exact Zo|].
  split; [apply (proj2 (L5A.writable_vis _ M oec 16 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|].
  split; [apply (proj2 (L5A.u32_at_vis _ M oec v (L5A.avis_sub _ oec 16 oec 4 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EU|].
  split; [exact AO| exact Eo].
Qed.

Lemma pot_text_le_parserA s cr : 0 <= PM.p_k s <= 11 ->
  PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) cr -> PMSPA.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))) cr.
Proof.
  intros Hk CR. pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
  pose proof (PMPK.pot_text_le_parser (PMSPA.HV L ar) s (PM.pot_parser (PMSPA.HV L ar) s)) as X.
  unfold PMSP.credit_le in X. cbn [PMSPA.HV LibIfaceAB.heap_view HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in X.
  rewrite K8, BO in X. specialize (X ltac:(lia) ltac:(lia) Hk ltac:(split; lia)). destruct X as (X1 & X2).
  unfold PMSPA.credit_le, PMSPA.scA in *. cbn [fst snd] in *. rewrite B3 in *. destruct CR as (C1 & C2). split; lia.
Qed.
Lemma credit_le_keepA cr cr1 p p1 : PMSPA.credit_le p cr -> PMSPA.credit_keep cr cr1 p p1 -> PMSPA.credit_le p1 cr1.
Proof. unfold PMSPA.credit_le, PMSPA.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.

Lemma credit_keep_transA cr1 cr2 cr3 p1 p2 p3 : PMSPA.credit_keep cr1 cr2 p1 p2 -> PMSPA.credit_keep cr2 cr3 p2 p3 -> PMSPA.credit_keep cr1 cr3 p1 p3.
Proof. unfold PMSPA.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.

Lemma credit_keep_textA s s' cr cr' :
  PMSPA.credit_keep cr cr' (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))) (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s') (PM.p_tg s'))) ->
  PM.p_k s' = PM.p_k s ->
  PMSPA.credit_keep cr cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')).
Proof.
  intros CK Ek. pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
  unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_parser, PM.credit_add in *. rewrite Ek. cbn [fst snd] in *. rewrite B3 in *. destruct CK as (C1 & C2). split; lia.
Qed.

End WithHeap.
End PMBPAR.
