(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2 ARep AHeapP FsKit AFake_iface AFake_relP AInstance AInstanceM AInstanceU AInstanceUF AInstanceU2 AInstanceU2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARealloc_x AInstanceA16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require APristLaw AInstancePrist.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section FakeLaw.
Context {rc : runConstT}.

Hypothesis EXHW : exh_first_stmt.
Local Notation AIu2 := (AInstanceU2.AIu2 EXHW).

Definition FLGu (L : alayout) (b : ablock) : Z := match ab_kind b with ABFake c => fflag L c (ab_addr b) | ABHeap _ => 0 end.

Lemma AIu_fk_facts : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b ->
  ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0 /\ ab_size b mod 8 = 0 /\ 64 <= ab_size b
  /\ wr_at asegs m (ab_addr b) (ab_size b) /\ wr_at asegs m (shad (ab_addr b)) (shlen (ab_size b)).
Proof.
  intros L RNG st LBa m b (ov & [g AH] & SUP) Hb [c Hc]. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (afakeU_block (ov:=ov) g L RNG st LBa m c F n AH Hb) as (C0 & EN & F64 & BK & TOP & N64 & WR & WRS).
  assert (N8 : n mod 8 = 0).
  { subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64.
    replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia. }
  split; [exact BK|]. split; [exact TOP|]. split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [exact N8|]. split; [exact N64|]. split; assumption.
Qed.

Lemma AIu_fk_area : forall L RNG st LBa m c F n, AHEAP AIu2 L RNG st LBa m -> In (mkABlock (ABFake c) F n) LBa ->
  al_fake L <= F /\ F + n <= al_fake L + 11571200 /\ F mod 8 = 0 /\ n mod 8 = 0 /\ ablk F (F + n).
Proof.
  intros L RNG st LBa m c F n AH2 Hb.
  destruct (AIu_fk_facts L RNG st LBa m (mkABlock (ABFake c) F n) AH2 Hb ltac:(exists c; reflexivity)) as (BK & _ & F8 & N8 & _). cbn [ab_addr ab_size] in *.
  destruct AH2 as (ov & [g AH] & SUP). destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LBa m c F n HFK Hb) as (_ & _ & _ & _ & FLO & FHI & _). unfold FAKESZ in FHI.
  split; [lia|]. split; [exact FHI|]. split; [exact F8|]. split; [exact N8| exact BK].
Qed.

Lemma AIu_fk_class : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b ->
  exists c, ab_kind b = ABFake c /\ 0 <= c /\ ab_size b = 64 * 2 ^ c.
Proof.
  intros L RNG st LBa m b (ov & AH & SUP) Hb [c Hc]. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & _ & EN & C0). exists c. split; [reflexivity|]. split; [exact C0|].
  subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma AIu_fk_law : forall L b, is_fake b -> flag_law AIu2 L b (FLGu L b).
Proof.
  intros L b [c Hc] RNG st LBa m AH2 Hb. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k. unfold FLGu. cbn [ab_kind ab_addr].
  pose proof AH2 as (ov & AH & SUP).
  destruct (fflagU_facts (ov:=ov) L RNG st LBa m c F n AH Hb) as (FR & FLO & WR).
  pose proof (fakeU_obj (ov:=ov) L RNG st LBa m AH) as OBJ. pose proof atop_range as ATR.
  split; [| split; [exact WR| split; [| split]]].
  -
    replace (lb_del (mkABlock (ABFake c) F n) LBa) with (fk_rel c F LBa); [exact (AHU2_fake_release L RNG st LBa m c F n AH2 Hb)|].
    unfold fk_rel, lb_del. apply filter_ext_in. intros x Hx.
    destruct (ablock_eq_dec x (mkABlock (ABFake c) F n)) as [->|NE].
    + unfold fk_is. cbn [ab_kind ab_addr]. rewrite !Z.eqb_refl. reflexivity.
    + destruct (fk_is c F x) eqn:FK; [| reflexivity]. exfalso. apply NE. unfold fk_is in FK.
      destruct x as [[p|c'] F' n']; cbn [ab_kind ab_addr] in FK; [discriminate|]. apply andb_prop in FK as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' F'.
      destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n' AH Hx) as (_ & _ & EN' & _). destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & _ & EN & _).
      subst n n'. reflexivity.
  - unfold ablk, AIMG_HI, KLS in *. lia.
  - intros b' Hb' IN. destruct b' as [[p|c'] F' n']; cbn [ab_addr ab_size] in IN.
    + destruct (heapU_off_fake (ov:=ov) L RNG st LBa m p F' n' AH Hb') as [D|D]; lia.
    + destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c' F' n' AH Hb') as (LO' & _). lia.
  -   unfold FAKESZ in *. lia.
Qed.

Lemma AIu_fk_rng : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b -> afake_rng L RNG ->
  rng RNG (ab_addr b) (ab_size b) /\ rng RNG (shad (ab_addr b)) (shlen (ab_size b)) /\ rng RNG (FLGu L b) 1.
Proof.
  intros L RNG st LBa m b AH2 Hb [c Hc] (R1 & R2 & _). destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k. unfold FLGu. cbn [ab_kind ab_addr].
  pose proof AH2 as (ov & AH & SUP).
  destruct (fflagU_facts (ov:=ov) L RNG st LBa m c F n AH Hb) as (FR & FLO & _).
  destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & FHI & EN & C0).
  destruct (AIu_fk_facts L RNG st LBa m (mkABlock (ABFake c) F n) AH2 Hb ltac:(exists c; reflexivity)) as (_ & _ & A8 & N8 & N64 & _). cbn [ab_addr ab_size] in A8, N8, N64.
  pose proof (fakeU_obj (ov:=ov) L RNG st LBa m AH) as OBJ. unfold ablk, AIMG_HI in OBJ. unfold FAKESZ in *.
  split; [apply (rng_sub RNG _ _ F n R1); lia|]. split; [| apply (rng_sub RNG _ _ (fflag L c F) 1 R1); lia].
  apply (rng_sub RNG _ _ (shad F) (shlen n) R2); unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia.
Qed.

Definition AIu_fake : AI_fake_law AIu2 :=
  {| FLG := FLGu; FRNG := afake_rng; fk_facts := AIu_fk_facts; fk_class := AIu_fk_class; fk_law := AIu_fk_law; fk_rng := AIu_fk_rng; fk_area := fun L RNG FR => proj1 FR |}.

Lemma last_cell_bytes : forall (m : amem) F (j0 j1 j2 w : word) k junk,
  rw_cells asegs m F [C8 j0; C8 j1; C8 j2; CB k junk; C8 w] -> bytes_at asegs m (F + 24 + Z.of_nat k) (le8 w).
Proof.
  intros m F j0 j1 j2 w k junk [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & _ & LJ & _).
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA].
  rewrite !length_le8, LJ in BA. replace (F + 24 + Z.of_nat k) with (F + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat k) by lia. exact BA.
Qed.
Lemma frame_in_flag : forall L (m' : amem) c F n (j0 j1 j2 : word) junk, 32 <= n ->
  rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))] ->
  exists flg, bytes_at asegs m' (F + n - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AIu2 L (mkABlock (ABFake c) F n) flg.
Proof.
  intros L m' c F n j0 j1 j2 junk N32 RW. exists (fflag L c F). split.
  - pose proof (last_cell_bytes m' F j0 j1 j2 _ _ junk RW) as BA. rewrite Z2Nat.id in BA by lia. replace (F + n - 8) with (F + 24 + (n - 32)) by lia. exact BA.
  - exact (AIu_fk_law L (mkABlock (ABFake c) F n) ltac:(exists c; reflexivity)).
Qed.

Lemma IMGSH_aci_u : forall v a, In v Op.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros v a Hv R. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
  change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, in_ranges, ASHOFF.
  unfold Op.SHLIT, Actr.ActrA.IMGSH, Op.STGSH, Op.PUBSH in Hv. cbn [In app] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in R.
  - destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x22c60) as [LT|GE].
    + exists (0x10000, 0x22c60). split; [cbn [In]; tauto| cbn [fst snd]; lia].
    + exists (0x22c60, 0x23360). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  -
    destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x5fc110) as [LT|GE].
    + exists (0x5fc100, 0x5fc110). split; [cbn [In]; tauto| cbn [fst snd]; lia].
    + exists (0x5fc110, 0x60cc28). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x5fc110, 0x60cc28). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x60ccb0, 0x62cf40). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x62cf48, 0x62dc18). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x62dc20, 0x62e028). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x62e030, 0x62e560). split; [cbn [In]; tauto| cbn [fst snd]; lia].
Qed.

Lemma AIu_realloc : AInstanceU2F.arealloc_stmt2x (aci AIu2) (AHEAP AIu2).
Proof. exact (AHU2_realloc EXHW). Qed.

Lemma AIu_aligned16 : AInstanceU2F.aaligned16_stmt2x (aci AIu2) (AHEAP AIu2).
Proof. exact (AHU2_aligned16 EXHW). Qed.

Lemma AIu_errno : forall LB SP, aclient_range (aci AIu2) LB SP AERRNO 4.
Proof. exact ARealloc_x.errno_client. Qed.

Lemma AIu_prist : APristLaw.prist_det_law (AHEAP AIu2).
Proof. exact AInstancePrist.AHU2_prist. Qed.

Lemma AIu_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2 ^ 47 -> m' (wa a) = m (wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Proof. exact AInstanceU2.AIu2_frame_top. Qed.

End FakeLaw.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB ARep.TwinB AHeapP.TwinB FsKit.TwinB AFake_iface.TwinB AFake_relP.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceU.TwinB AInstanceUF.TwinB AInstanceU2.TwinB AInstanceU2F.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import AEmbRep.TwinB.
Import Actr.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section FakeLaw.
Context {rc : runConstT}.

Hypothesis EXHW : exh_first_stmt.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 EXHW).

Definition FLGu (L : alayout) (b : ablock) : Z := match ab_kind b with ABFake c => fflag L c (ab_addr b) | ABHeap _ => 0 end.

Lemma AIu_fk_facts : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b ->
  ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 8 = 0 /\ ab_size b mod 8 = 0 /\ 64 <= ab_size b
  /\ wr_at bsegs m (ab_addr b) (ab_size b) /\ wr_at bsegs m (shad (ab_addr b)) (shlen (ab_size b)).
Proof.
  intros L RNG st LBa m b (ov & [g AH] & SUP) Hb [c Hc]. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (afakeU_block (ov:=ov) g L RNG st LBa m c F n AH Hb) as (C0 & EN & F64 & BK & TOP & N64 & WR & WRS).
  assert (N8 : n mod 8 = 0).
  { subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64.
    replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia. }
  split; [exact BK|]. split; [exact TOP|]. split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [exact N8|]. split; [exact N64|]. split; assumption.
Qed.

Lemma AIu_fk_area : forall L RNG st LBa m c F n, AHEAP AIu2 L RNG st LBa m -> In (mkABlock (ABFake c) F n) LBa ->
  al_fake L <= F /\ F + n <= al_fake L + 11571200 /\ F mod 8 = 0 /\ n mod 8 = 0 /\ ablk F (F + n).
Proof.
  intros L RNG st LBa m c F n AH2 Hb.
  destruct (AIu_fk_facts L RNG st LBa m (mkABlock (ABFake c) F n) AH2 Hb ltac:(exists c; reflexivity)) as (BK & _ & F8 & N8 & _). cbn [ab_addr ab_size] in *.
  destruct AH2 as (ov & [g AH] & SUP). destruct AH as (_ & _ & _ & HFK). cbn [AHI ah_fake] in HFK.
  destruct (afake_lb (gb:=g) L LBa m c F n HFK Hb) as (_ & _ & _ & _ & FLO & FHI & _). unfold FAKESZ in FHI.
  split; [lia|]. split; [exact FHI|]. split; [exact F8|]. split; [exact N8| exact BK].
Qed.

Lemma AIu_fk_class : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b ->
  exists c, ab_kind b = ABFake c /\ 0 <= c /\ ab_size b = 64 * 2 ^ c.
Proof.
  intros L RNG st LBa m b (ov & AH & SUP) Hb [c Hc]. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k.
  destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & _ & EN & C0). exists c. split; [reflexivity|]. split; [exact C0|].
  subst n. unfold fk_fsize. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma AIu_fk_law : forall L b, is_fake b -> flag_law AIu2 L b (FLGu L b).
Proof.
  intros L b [c Hc] RNG st LBa m AH2 Hb. destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k. unfold FLGu. cbn [ab_kind ab_addr].
  pose proof AH2 as (ov & AH & SUP).
  destruct (fflagU_facts (ov:=ov) L RNG st LBa m c F n AH Hb) as (FR & FLO & WR).
  pose proof (fakeU_obj (ov:=ov) L RNG st LBa m AH) as OBJ. pose proof atop_range as ATR.
  split; [| split; [exact WR| split; [| split]]].
  -
    replace (lb_del (mkABlock (ABFake c) F n) LBa) with (fk_rel c F LBa); [exact (AHU2_fake_release L RNG st LBa m c F n AH2 Hb)|].
    unfold fk_rel, lb_del. apply filter_ext_in. intros x Hx.
    destruct (ablock_eq_dec x (mkABlock (ABFake c) F n)) as [->|NE].
    + unfold fk_is. cbn [ab_kind ab_addr]. rewrite !Z.eqb_refl. reflexivity.
    + destruct (fk_is c F x) eqn:FK; [| reflexivity]. exfalso. apply NE. unfold fk_is in FK.
      destruct x as [[p|c'] F' n']; cbn [ab_kind ab_addr] in FK; [discriminate|]. apply andb_prop in FK as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' F'.
      destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n' AH Hx) as (_ & _ & EN' & _). destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & _ & EN & _).
      subst n n'. reflexivity.
  - unfold ablk, AIMG_HI, KLS in *. lia.
  - intros b' Hb' IN. destruct b' as [[p|c'] F' n']; cbn [ab_addr ab_size] in IN.
    + destruct (heapU_off_fake (ov:=ov) L RNG st LBa m p F' n' AH Hb') as [D|D]; lia.
    + destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c' F' n' AH Hb') as (LO' & _). lia.
  -   unfold FAKESZ in *. lia.
Qed.

Lemma AIu_fk_rng : forall L RNG st LBa m b, AHEAP AIu2 L RNG st LBa m -> In b LBa -> is_fake b -> afake_rng L RNG ->
  rng RNG (ab_addr b) (ab_size b) /\ rng RNG (shad (ab_addr b)) (shlen (ab_size b)) /\ rng RNG (FLGu L b) 1.
Proof.
  intros L RNG st LBa m b AH2 Hb [c Hc] (R1 & R2 & _). destruct b as [k F n]. cbn [ab_kind ab_addr ab_size] in *. subst k. unfold FLGu. cbn [ab_kind ab_addr].
  pose proof AH2 as (ov & AH & SUP).
  destruct (fflagU_facts (ov:=ov) L RNG st LBa m c F n AH Hb) as (FR & FLO & _).
  destruct (fakeU_frame_lo (ov:=ov) L RNG st LBa m c F n AH Hb) as (_ & FHI & EN & C0).
  destruct (AIu_fk_facts L RNG st LBa m (mkABlock (ABFake c) F n) AH2 Hb ltac:(exists c; reflexivity)) as (_ & _ & A8 & N8 & N64 & _). cbn [ab_addr ab_size] in A8, N8, N64.
  pose proof (fakeU_obj (ov:=ov) L RNG st LBa m AH) as OBJ. unfold ablk, AIMG_HI in OBJ. unfold FAKESZ in *.
  split; [apply (rng_sub RNG _ _ F n R1); lia|]. split; [| apply (rng_sub RNG _ _ (fflag L c F) 1 R1); lia].
  apply (rng_sub RNG _ _ (shad F) (shlen n) R2); unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia.
Qed.

Definition AIu_fake : AI_fake_law AIu2 :=
  {| FLG := FLGu; FRNG := afake_rng; fk_facts := AIu_fk_facts; fk_class := AIu_fk_class; fk_law := AIu_fk_law; fk_rng := AIu_fk_rng; fk_area := fun L RNG FR => proj1 FR |}.

Lemma last_cell_bytes : forall (m : amem) F (j0 j1 j2 w : word) k junk,
  rw_cells bsegs m F [C8 j0; C8 j1; C8 j2; CB k junk; C8 w] -> bytes_at bsegs m (F + 24 + Z.of_nat k) (le8 w).
Proof.
  intros m F j0 j1 j2 w k junk [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & _ & LJ & _).
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA]. apply bytes_at_app in BA as [_ BA].
  rewrite !length_le8, LJ in BA. replace (F + 24 + Z.of_nat k) with (F + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat k) by lia. exact BA.
Qed.
Lemma frame_in_flag : forall L (m' : amem) c F n (j0 j1 j2 : word) junk, 32 <= n ->
  rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (fflag L c F))] ->
  exists flg, bytes_at bsegs m' (F + n - 8) (le8 (Z_to_bv 64 flg)) /\ flag_law AIu2 L (mkABlock (ABFake c) F n) flg.
Proof.
  intros L m' c F n j0 j1 j2 junk N32 RW. exists (fflag L c F). split.
  - pose proof (last_cell_bytes m' F j0 j1 j2 _ _ junk RW) as BA. rewrite Z2Nat.id in BA by lia. replace (F + n - 8) with (F + 24 + (n - 32)) by lia. exact BA.
  - exact (AIu_fk_law L (mkABlock (ABFake c) F n) ltac:(exists c; reflexivity)).
Qed.

Lemma IMGSH_aci_u : forall v a, In v Op.TwinB.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros v a Hv R. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
  change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges, ASHOFF.
  unfold Op.TwinB.SHLIT, Actr.TwinB.ActrA.IMGSH, Op.TwinB.STGSH, Op.TwinB.PUBSH in Hv. cbn [In app] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in R.
  - destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x22d00) as [LT|GE].
    + exists (0x10000, 0x22d00). split; [cbn [In]; tauto| cbn [fst snd]; lia].
    + exists (0x22d00, 0x23500). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  -
    destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x5fe2d0) as [LT|GE].
    + exists (0x5fe2c0, 0x5fe2d0). split; [cbn [In]; tauto| cbn [fst snd]; lia].
    + exists (0x5fe2d0, 0x60ede8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x5fe2d0, 0x60ede8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x60ee70, 0x62f100). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x62f108, 0x62fdd8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x62fde0, 0x6301e8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x6301f0, 0x630720). split; [cbn [In]; tauto| cbn [fst snd]; lia].
Qed.

Lemma AIu_realloc : AInstanceU2F.TwinB.arealloc_stmt2x (aci AIu2) (AHEAP AIu2).
Proof. exact (AHU2_realloc EXHW). Qed.

Lemma AIu_aligned16 : AInstanceU2F.TwinB.aaligned16_stmt2x (aci AIu2) (AHEAP AIu2).
Proof. exact (AHU2_aligned16 EXHW). Qed.

Lemma AIu_errno : forall LB SP, aclient_range (aci AIu2) LB SP AERRNO 4.
Proof. exact ARealloc_x.TwinB.errno_client. Qed.

Lemma AIu_prist : APristLaw.TwinB.prist_det_law (AHEAP AIu2).
Proof. exact AInstancePrist.TwinB.AHU2_prist. Qed.

Lemma AIu_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2 ^ 47 -> m' (wa a) = m (wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m'.
Proof. exact AInstanceU2.TwinB.AIu2_frame_top. Qed.

End FakeLaw.
End TwinB.
