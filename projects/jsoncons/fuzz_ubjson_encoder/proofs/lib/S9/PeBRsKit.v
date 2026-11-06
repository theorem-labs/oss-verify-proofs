(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmTxtKit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBRSK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma parser_tb_setA (M M' : word -> option byte) op ois s tb tg :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 336 -> PMFA.agA M M' (op + 360) 24 -> PMFA.agsh M M' (op + 336) 24 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  PM.vstr_at RSEGS PMSPA.accA M' (op + 336) tb -> L5.defined M' op 384 ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M' op ois (PMTK2.with_tb s tb tg).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 SH1] [AG2 SH2] SH3 Hq Hq' AGQ Hb Hb' AGB TB' D'.
  unfold PMTK2.with_tb, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
  assert (U64 : forall a v, op <= a -> a + 8 <= op + 336 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, op <= a -> a + 4 <= op + 336 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, op <= a -> a + 1 <= op + 336 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  split; [apply U64; [lia|lia|exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PeCLayoutB.CADDR_B M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'
            | split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact AGQ| exact SRC]|].
  split; [apply U32; [lia|lia|exact H320]|].
  split; [apply U64; [lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; destruct (Z_lt_le_dec x (op + 336)) as [X|X]; [apply SH1; lia|];
            destruct (Z_lt_le_dec x (op + 360)) as [Y|Y]; [apply SH3; lia| apply SH2; lia]| exact C320]|].
  split; [exact TB'|].
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG2; lia| exact AGB| exact VEC]|].
  split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma ffroom_incl h h' FF LK LK' : PMSPA.ffroomA h FF LK -> incl LK' LK -> NoDup (map ff_addr (FF ++ LK')) -> h' <= h -> PMSPA.ffroomA h' FF LK'.
Proof.
  intros FR I ND Hh k Hk. specialize (FR k Hk).
  assert (CI : (ff_count k (FF ++ LK') <= ff_count k (FF ++ LK))%nat).
  { apply L5SAR.ff_count_incl.
    - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [X|X]; [left; exact X| right; apply I; exact X].
    - apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. }
  lia.
Qed.

Lemma tb_vis LB FF LK cr Aw M model fb ois s :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M (PMSPA.o_p PeCLayoutB.CADDR_B fb) ois s ->
  let tb := PMSPA.o_tb PeCLayoutB.CADDR_B fb in let MV := mrestrict (ahid Aw model) M in
  (6930432 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ tb + 24 <= ahl_ceil ar
  /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF tb 24 /\ ar_fs ar <= tb /\ tb + 24 <= ar_fs ar + FS_BYTES.
Proof.
  intros HH FOK PA tb MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
  assert (AO : PMSPA.aobjA FF tb 24).
  { exists (fb, 5, rs). split; [exact Hf|]. unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [ff_addr ff_class ff_bytes pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B].
    unfold ff_bytes. cbn. lia. }
  assert (O8 : tb mod 8 = 0).
  { unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (2048 * (fb / 2048) + 592 + 336) with ((256 * (fb / 2048) + 116) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model tb 24 0 0 HH (PMKB.aobj_of_aobjA FF tb 24 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  assert (ACC : PMSPA.accA M tb 24).
  { pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & _). destruct TB as (_ & TC & _). exact TC. }
  split; [split; [lia| split; [exact O8| exact OBIG]]|].
  split.
  { change 3 with (24 / 8). apply (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model tb 24 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  split.
  { apply (proj2 (L5A.writable_vis _ M tb 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
  destruct (WF _ Hf) as (W1 & W2 & _). unfold ff_addr, ff_class in W1, W2. cbn in W1, W2. unfold ff_bytes in W2. change (64 * 2 ^ 4) with 1024 in W2.
  unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold FS_BYTES in *. split; lia.
Qed.

Lemma tbd_vis LB FF LK cr Aw M model p c :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> In (p, c) LB -> 26 <= c -> PMSPA.accA M p c ->
  let MV := mrestrict (ahid Aw model) M in
  (4096 <= p /\ p + c <= 2 ^ 47 /\ p mod 16 = 0 /\ (2147446784 + 17592186048512 <= p \/ p + c <= 2147446784))
  /\ L5KA.zeros_at MV (p / 8 + 2147450880) 1 /\ L5.writable RSEGS MV p 1 /\ L5A.avis (ahid Aw model) p 1 /\ p + c <= ahl_ceil ar.
Proof.
  intros HH Hin Hc CC MV.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ Hin) as ((B0 & B1 & B2 & B3 & B4 & B5) & _). cbn [fst snd] in B0, B1, B2, B3, B4, B5.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & VBLK & _).
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
  assert (P8 : p mod 8 = 0) by (apply PMKB.mod16_8'; exact B2).
  assert (VP : L5A.avis (ahid Aw model) p 1) by (apply (VBLK p c p 1 Hin); lia).
  split; [split; [lia| split; [lia| split; [exact B2| destruct B5 as (_ & [X|X] & _); [right| left]; lia]]]|].
  split.
  { change 1 with (8 / 8). apply (PMKB.blk_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model p c p 8 HH Hin ltac:(lia) ltac:(lia) P8 ltac:(lia) ltac:(reflexivity)).
    intros x Hx. apply CC. lia. }
  split.
  { apply (proj2 (L5A.writable_vis _ M p 1 VP ltac:(lia) ltac:(lia))).
    destruct (WB _ Hin) as (_ & DEF & _). apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M p c p 1 DEF); lia| lia| lia]. }
  split; [exact VP|]. lia.
Qed.
End WithHeap.
End PMBRSK.
