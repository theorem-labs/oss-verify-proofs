(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops CtrSys.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib Layout OpsBridge RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw RtLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre RoLitA AsanRun.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout.
Module UB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge.UB.

Lemma rdZ_of_rb : forall (m : word -> option byte) n a (bs : list byte), length bs = n -> 0 <= a -> a + Z.of_nat n <= two64 ->
  (forall t, (t < n)%nat -> rb asegs m (a + Z.of_nat t) = Some (nth t bs (Z_to_bv 8 0))) ->
  UL.rdZ (UB.bmem_of asegs m) a n = Some (bytes_le_to_Z bs).
Proof.
  intros m n. induction n as [|n IH]; intros a bs L A0 A1 H.
  - destruct bs; [reflexivity| discriminate L].
  - destruct bs as [|b bs]; [discriminate L|]. cbn [UL.rdZ].
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0.
    rewrite (UB.bmem_of_some asegs m a b ltac:(lia) H0).
    rewrite (IH (a + 1) bs ltac:(cbn in L; lia) ltac:(lia) ltac:(lia)).
    + rewrite MemP.bytes_le_to_Z_cons. reflexivity.
    + intros t Ht. specialize (H (S t) ltac:(lia)). cbn [nth] in H. rewrite <- H. f_equal. lia.
Qed.

Section Inst.
Context {rc : runConstT}.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.
Variables p1 file : list byte.

Notation OPSA := (AsanRun.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file).
Notation AWAx := (AWA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake).
Notation CHSA := (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user asegs IMGX AWAx OPSA).

Lemma img_chg : forall os m mo z, (exists seg, find_segment asegs z 1 = Some seg) -> CHSA os m mo z.
Proof.
  intros os m mo z S. left. left.
  exact (AsanRun.OPSA_cov0_img IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file z S).
Qed.

Lemma cell_rb : forall (m : amem) A c, AS.rw_cells asegs m A [c] -> forall t, (t < length (cbytes c))%nat ->
  rb asegs m (A + Z.of_nat t) = Some (nth t (cbytes c) (Z_to_bv 8 0)).
Proof.
  intros m A c [[_ BY] _] t Ht. cbn [cells_bytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
  transitivity (nth_error (cbytes c) t); [exact (BY t Ht)| apply nth_error_nth'; exact Ht].
Qed.

Theorem OPSA_rolit_HR : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a n : int) (v : w64),
  (forall id, In id RoLitA.RoLitA.VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_ASAN asegs a n = Some v -> wt v = false ->
  UL.rdZ (UB.bmem_of asegs m) (to_Z a) (Z.to_nat (to_Z n)) = Some (to_Z (wl v)) /\
  (forall j, 0 <= j < to_Z n -> CHSA os m mo (to_Z a + j)).
Proof.
  intros os m mo a n v V RVE WT.
  destruct (V 1%uint63 ltac:(left; reflexivity)) as (hargs & _ & HH).
  assert (HX : heap_holds asegs IMGX AWAx Cw hargs m mo) by exact HH.
  pose proof (RtLaw.heap_holds_rt AIu2 ACCT UNIV Cw hargs m mo
                (Op.heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw hargs m mo HX)) as [RELRO ART].
  assert (WV : w2Z v = to_Z (wl v)) by (unfold w2Z; rewrite WT; reflexivity).
  unfold RoLitA.RoLitA.RV in RVE. cbn [RoLitA.RoLitA.relro_lo RoLitA.RoLitA.relro_hi RoLitA.RoLitA.shbase_addr RoLitA.RoLitA.flag_addr RoLitA.RoLitA.CFG_ASAN] in RVE.
  destruct (RoLitA.RoLitA.wok_b n && PrimInt63.leb 839680 a && PrimInt63.leb (PrimInt63.add a n) 864256)%bool eqn:C1.
  -
    apply andb_prop in C1 as [C1 LE2]. apply andb_prop in C1 as [WOK LE1].
    apply Uint63.leb_spec in LE1. apply Uint63.leb_spec in LE2. change (to_Z 839680%uint63) with 0xcd000 in LE1. change (to_Z 864256%uint63) with 0xd3000 in LE2.
    assert (N8 : to_Z n = 1 \/ to_Z n = 2 \/ to_Z n = 4 \/ to_Z n = 8).
    { unfold RoLitA.RoLitA.wok_b in WOK. rewrite !orb_true_iff in WOK. destruct WOK as [[[W|W]|W]|W]; apply Uint63.eqb_correct in W; subst n; cbn; tauto. }
    destruct (Mem.img_bytes asegs (to_Z a) (Z.to_nat (to_Z n))) as [bs|] eqn:IB; [|discriminate RVE]. injection RVE as <-.
    destruct (MemP.img_bytes_spec asegs _ _ _ IB) as [LEN BY].
    pose proof (to_Z_bounded a) as RA. rewrite wB_two63 in RA. unfold two63 in RA.

    assert (SEG0 : exists seg, find_segment asegs (to_Z a) 1 = Some seg).
    { destruct (BY 0%nat ltac:(lia)) as [rest M]. rewrite Z.add_0_r in M. apply (MemP.memory_read_find_segment asegs (to_Z a) _ ltac:(unfold two64; lia) M). }
    assert (AHI : to_Z a < 0x62f000).
    { destruct (Z.lt_ge_cases (to_Z a) 0x62f000) as [X|X]; [exact X|]. destruct SEG0 as [seg S]. rewrite (UnreggPre.no_seg_above (to_Z a) X) in S. discriminate S. }
    rewrite Uint63.add_spec, wB_two63, Z.mod_small in LE2 by (unfold two63; lia).
    assert (INR : forall t, (t < Z.to_nat (to_Z n))%nat -> rb asegs m (to_Z a + Z.of_nat t) = Some (nth t bs (Z_to_bv 8 0))).
    { intros t Ht. destruct (BY t Ht) as [rest M].
      pose proof (RELRO (to_Z a + Z.of_nat t) ltac:(unfold ARELRO_LO, ARELRO_HI; lia)) as X. unfold AM.wa in X.
      unfold rb. rewrite X. unfold rom_of. rewrite M. reflexivity. }
    split.
    + rewrite (rdZ_of_rb m _ (to_Z a) bs LEN ltac:(lia) ltac:(unfold two64; lia) INR).
      rewrite <- WV, (MemP.bytes_to_w64_ok bs ltac:(lia)). reflexivity.
    + intros j Hj. apply img_chg.
      destruct (BY (Z.to_nat j) ltac:(lia)) as [rest M]. rewrite Z2Nat.id in M by lia.
      apply (MemP.memory_read_find_segment asegs (to_Z a + j) _ ltac:(unfold two64; lia) M).
  - unfold artcells in ART. destruct ART as (_ & _ & _ & _ & SHB & FLG & _).
    destruct (PrimInt63.eqb a 891576 && PrimInt63.eqb n 8)%bool eqn:C2.
    +
      apply andb_prop in C2 as [EA EN]. apply Uint63.eqb_correct in EA. apply Uint63.eqb_correct in EN. subst a n. injection RVE as <-.
      change (to_Z 891576%uint63) with 0xd9ab8. change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
      split.
      * rewrite (rdZ_of_rb m 8 0xd9ab8 (cbytes (C8 (Z_to_bv 64 0x7fff8000))) ltac:(reflexivity) ltac:(lia) ltac:(unfold two64; lia) (cell_rb m 0xd9ab8 _ SHB)).
        vm_compute. reflexivity.
      * intros j Hj. apply img_chg. apply (AsanRun.seg_cover asegs 0xd9ab8 0xd9ac8 ltac:(vm_compute; reflexivity)). lia.
    + destruct (PrimInt63.eqb a 891584 && PrimInt63.eqb n 4)%bool eqn:C3; [|discriminate RVE].
      apply andb_prop in C3 as [EA EN]. apply Uint63.eqb_correct in EA. apply Uint63.eqb_correct in EN. subst a n. injection RVE as <-.
      change (to_Z 891584%uint63) with 0xd9ac0. change (Z.to_nat (to_Z 4%uint63)) with 4%nat. change (to_Z 4%uint63) with 4.
      split.
      * rewrite (rdZ_of_rb m 4 0xd9ac0 (cbytes (C4 (Z_to_bv 64 1))) ltac:(reflexivity) ltac:(lia) ltac:(unfold two64; lia) (cell_rb m 0xd9ac0 _ FLG)).
        vm_compute. reflexivity.
      * intros j Hj. apply img_chg. apply (AsanRun.seg_cover asegs 0xd9ab8 0xd9ac8 ltac:(vm_compute; reflexivity)). lia.
Qed.

Theorem arolit_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop),
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  forall pc, PlanSound.PlanS.contract_sound asegs OPSA MP PB (RoLit.RoLit.rolit_c asegs RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_ASAN asegs) pc).
Proof.
  intros MP PB HMPA pc.
  exact (RoLit.RoLit.rolit_sound asegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_ASAN asegs) CHSA
           (AsanRun.OPSA_acc_user_law IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)
           OPSA_rolit_HR MP PB HMPA pc).
Qed.
End Inst.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.
Import Ledger.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout.
Module UB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge.UB.

Lemma rdZ_of_rb : forall (m : word -> option byte) n a (bs : list byte), length bs = n -> 0 <= a -> a + Z.of_nat n <= two64 ->
  (forall t, (t < n)%nat -> rb bsegs m (a + Z.of_nat t) = Some (nth t bs (Z_to_bv 8 0))) ->
  UL.rdZ (UB.bmem_of bsegs m) a n = Some (bytes_le_to_Z bs).
Proof.
  intros m n. induction n as [|n IH]; intros a bs L A0 A1 H.
  - destruct bs; [reflexivity| discriminate L].
  - destruct bs as [|b bs]; [discriminate L|]. cbn [UL.rdZ].
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0.
    rewrite (UB.bmem_of_some bsegs m a b ltac:(lia) H0).
    rewrite (IH (a + 1) bs ltac:(cbn in L; lia) ltac:(lia) ltac:(lia)).
    + rewrite MemP.bytes_le_to_Z_cons. reflexivity.
    + intros t Ht. specialize (H (S t) ltac:(lia)). cbn [nth] in H. rewrite <- H. f_equal. lia.
Qed.

Section Inst.
Context {rc : runConstT}.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.
Variables p1 file : list byte.

Notation OPSA := (AsanRun.TwinB.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file).
Notation AWAx := (AWA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake).
Notation CHSA := (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user bsegs IMGX AWAx OPSA).

Lemma img_chg : forall os m mo z, (exists seg, find_segment bsegs z 1 = Some seg) -> CHSA os m mo z.
Proof.
  intros os m mo z S. left. left.
  exact (AsanRun.TwinB.OPSA_cov0_img IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file z S).
Qed.

Lemma cell_rb : forall (m : amem) A c, AS.rw_cells bsegs m A [c] -> forall t, (t < length (cbytes c))%nat ->
  rb bsegs m (A + Z.of_nat t) = Some (nth t (cbytes c) (Z_to_bv 8 0)).
Proof.
  intros m A c [[_ BY] _] t Ht. cbn [cells_bytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
  transitivity (nth_error (cbytes c) t); [exact (BY t Ht)| apply nth_error_nth'; exact Ht].
Qed.

Theorem OPSA_rolit_HR : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a n : int) (v : w64),
  (forall id, In id RoLitA.RoLitA.VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH bsegs a n = Some v -> wt v = false ->
  UL.rdZ (UB.bmem_of bsegs m) (to_Z a) (Z.to_nat (to_Z n)) = Some (to_Z (wl v)) /\
  (forall j, 0 <= j < to_Z n -> CHSA os m mo (to_Z a + j)).
Proof.
  intros os m mo a n v V RVE WT.
  destruct (V 1%uint63 ltac:(left; reflexivity)) as (hargs & _ & HH).
  assert (HX : heap_holds bsegs IMGX AWAx Cw hargs m mo) by exact HH.
  pose proof (RtLaw.TwinB.heap_holds_rt AIu2 ACCT UNIV Cw hargs m mo
                (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge.Op.TwinB.heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw hargs m mo HX)) as [RELRO ART].
  assert (WV : w2Z v = to_Z (wl v)) by (unfold w2Z; rewrite WT; reflexivity).
  unfold RoLitA.RoLitA.RV in RVE. cbn [RoLitA.RoLitA.relro_lo RoLitA.RoLitA.relro_hi RoLitA.RoLitA.shbase_addr RoLitA.RoLitA.flag_addr RoLitA.RoLitA.CFG_BOTH] in RVE.
  destruct (RoLitA.RoLitA.wok_b n && PrimInt63.leb 847872 a && PrimInt63.leb (PrimInt63.add a n) 872448)%bool eqn:C1.
  -
    apply andb_prop in C1 as [C1 LE2]. apply andb_prop in C1 as [WOK LE1].
    apply Uint63.leb_spec in LE1. apply Uint63.leb_spec in LE2. change (to_Z 847872%uint63) with 0xcf000 in LE1. change (to_Z 872448%uint63) with 0xd5000 in LE2.
    assert (N8 : to_Z n = 1 \/ to_Z n = 2 \/ to_Z n = 4 \/ to_Z n = 8).
    { unfold RoLitA.RoLitA.wok_b in WOK. rewrite !orb_true_iff in WOK. destruct WOK as [[[W|W]|W]|W]; apply Uint63.eqb_correct in W; subst n; cbn; tauto. }
    destruct (Mem.img_bytes bsegs (to_Z a) (Z.to_nat (to_Z n))) as [bs|] eqn:IB; [|discriminate RVE]. injection RVE as <-.
    destruct (MemP.img_bytes_spec bsegs _ _ _ IB) as [LEN BY].
    pose proof (to_Z_bounded a) as RA. rewrite wB_two63 in RA. unfold two63 in RA.

    assert (SEG0 : exists seg, find_segment bsegs (to_Z a) 1 = Some seg).
    { destruct (BY 0%nat ltac:(lia)) as [rest M]. rewrite Z.add_0_r in M. apply (MemP.memory_read_find_segment bsegs (to_Z a) _ ltac:(unfold two64; lia) M). }
    assert (AHI : to_Z a < 0x631000).
    { destruct (Z.lt_ge_cases (to_Z a) 0x631000) as [X|X]; [exact X|]. destruct SEG0 as [seg S]. rewrite (UnreggPre.TwinB.no_seg_above (to_Z a) X) in S. discriminate S. }
    rewrite Uint63.add_spec, wB_two63, Z.mod_small in LE2 by (unfold two63; lia).
    assert (INR : forall t, (t < Z.to_nat (to_Z n))%nat -> rb bsegs m (to_Z a + Z.of_nat t) = Some (nth t bs (Z_to_bv 8 0))).
    { intros t Ht. destruct (BY t Ht) as [rest M].
      pose proof (RELRO (to_Z a + Z.of_nat t) ltac:(unfold ARELRO_LO, ARELRO_HI; lia)) as X. unfold AM.wa in X.
      unfold rb. rewrite X. unfold rom_of. rewrite M. reflexivity. }
    split.
    + rewrite (rdZ_of_rb m _ (to_Z a) bs LEN ltac:(lia) ltac:(unfold two64; lia) INR).
      rewrite <- WV, (MemP.bytes_to_w64_ok bs ltac:(lia)). reflexivity.
    + intros j Hj. apply img_chg.
      destruct (BY (Z.to_nat j) ltac:(lia)) as [rest M]. rewrite Z2Nat.id in M by lia.
      apply (MemP.memory_read_find_segment bsegs (to_Z a + j) _ ltac:(unfold two64; lia) M).
  - unfold artcells in ART. destruct ART as (_ & _ & _ & _ & SHB & FLG & _).
    destruct (PrimInt63.eqb a 900216 && PrimInt63.eqb n 8)%bool eqn:C2.
    +
      apply andb_prop in C2 as [EA EN]. apply Uint63.eqb_correct in EA. apply Uint63.eqb_correct in EN. subst a n. injection RVE as <-.
      change (to_Z 900216%uint63) with 0xdbc78. change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
      split.
      * rewrite (rdZ_of_rb m 8 0xdbc78 (cbytes (C8 (Z_to_bv 64 0x7fff8000))) ltac:(reflexivity) ltac:(lia) ltac:(unfold two64; lia) (cell_rb m 0xdbc78 _ SHB)).
        vm_compute. reflexivity.
      * intros j Hj. apply img_chg. apply (AsanRun.TwinB.seg_cover bsegs 0xdbc78 0xdbc88 ltac:(vm_compute; reflexivity)). lia.
    + destruct (PrimInt63.eqb a 900224 && PrimInt63.eqb n 4)%bool eqn:C3; [|discriminate RVE].
      apply andb_prop in C3 as [EA EN]. apply Uint63.eqb_correct in EA. apply Uint63.eqb_correct in EN. subst a n. injection RVE as <-.
      change (to_Z 900224%uint63) with 0xdbc80. change (Z.to_nat (to_Z 4%uint63)) with 4%nat. change (to_Z 4%uint63) with 4.
      split.
      * rewrite (rdZ_of_rb m 4 0xdbc80 (cbytes (C4 (Z_to_bv 64 1))) ltac:(reflexivity) ltac:(lia) ltac:(unfold two64; lia) (cell_rb m 0xdbc80 _ FLG)).
        vm_compute. reflexivity.
      * intros j Hj. apply img_chg. apply (AsanRun.TwinB.seg_cover bsegs 0xdbc78 0xdbc88 ltac:(vm_compute; reflexivity)). lia.
Qed.

Theorem arolit_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop),
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  forall pc, PlanSound.PlanS.contract_sound bsegs OPSA MP PB (RoLit.RoLit.rolit_c bsegs RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH bsegs) pc).
Proof.
  intros MP PB HMPA pc.
  exact (RoLit.RoLit.rolit_sound bsegs OPSA RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH bsegs) CHSA
           (AsanRun.TwinB.OPSA_acc_user_law IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file)
           OPSA_rolit_HR MP PB HMPA pc).
Qed.
End Inst.
End TwinB.
