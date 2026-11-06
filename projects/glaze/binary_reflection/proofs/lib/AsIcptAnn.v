(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptAnnM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation U := bv_unsigned.

Lemma hid_off_pw : forall (Hd : word -> bool) lo n,
  (forall z, lo <= z < lo + n -> 0 <= z < 2 ^ 64 /\ Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n.
Proof. intros Hd lo n F x Hx. destruct (F (U x) Hx) as [R E]. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Section M.
  Context {fx : FPState}.
  Variables (base : word) (M : word -> option byte) (oldw neww raw spw : word) (R : bvmap 5 word).
  (* [comment removed for export] *)
  Variables (beg n om nm : Z).
  Hypothesis Hom : Ao oldw = om.  Hypothesis Hnm : An neww = nm.
  Hypothesis Hbeg : 0 <= beg. Hypothesis HO : beg <= om <= beg + n. Hypothesis HN : beg <= nm <= beg + n.
  Hypothesis E47 : beg + n < 140737488355328.
  Hypothesis Hsp : 17594333495296 + 2192 <= U spw.
  Hypothesis HB : (U base mod 2 = 0)%Z /\ (4096 <= U base)%Z /\ (U base + 4096 < 2 ^ 64)%Z.

  #[local] Abbreviation M' := (ann_mem base M oldw neww raw spw R).
  #[local] Abbreviation SB := 2147450880.

  Lemma dn8s : dn8 om <= om < dn8 om + 8 /\ om <= dn8 (om + 7) < om + 8 /\ dn8 nm <= nm < dn8 nm + 8 /\ nm <= dn8 (nm + 7) < nm + 8
               /\ 0 <= dn8 om /\ 0 <= dn8 nm /\ dn8 (om + 7) <= 140737488355328 /\ dn8 (nm + 7) <= 140737488355328
               /\ dn8 om / 8 = om / 8 /\ dn8 nm / 8 = nm / 8 /\ dn8 (om + 7) / 8 = (om + 7) / 8 /\ dn8 (nm + 7) / 8 = (nm + 7) / 8
               /\ (dn8 nm - dn8 om) / 8 = nm / 8 - om / 8 /\ (dn8 (om + 7) - dn8 (nm + 7)) / 8 = (om + 7) / 8 - (nm + 7) / 8.
  Proof using HB E47 HN HO Hbeg n beg base.
    pose proof (dn8_le om). pose proof (dn8_le (om + 7)). pose proof (dn8_le nm). pose proof (dn8_le (nm + 7)).
    pose proof (dn8_nonneg om ltac:(lia)). pose proof (dn8_nonneg nm ltac:(lia)).
    unfold dn8 in *. rewrite !Z.div_mul by lia. rewrite <- !Z.mul_sub_distr_r. rewrite !Z.div_mul by lia.
    pose proof (Z.div_le_mono (om + 7) 140737488355334 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_le_mono (nm + 7) 140737488355334 8 ltac:(lia) ltac:(lia)) as D2.
    change (140737488355334 / 8) with 17592186044416 in D1, D2.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PZ_in : forall m lo hi v (a : word),
    0 <= lo -> lo <= hi -> hi <= 140737488355328 -> lo mod 8 = 0 -> hi mod 8 = 0 ->
    SB + lo / 8 <= U a < SB + hi / 8 ->
    PZ base oldw neww spw m lo hi v a = Some (cbyte (Z_to_bv 64 v)).
  Proof using HB.
    intros m lo hi v a L0 L1 L2 L8 H8 Ha. (lazymatch goal with |- ?G => let G' := eval unfold PZ, shad, shlen in G in change_no_check G' end).
    pose proof (Z.div_pos lo 8 L0 ltac:(lia)). pose proof (Z.div_le_mono hi 140737488355328 8 ltac:(lia) L2) as DH.
    change (140737488355328 / 8) with 17592186044416 in DH.
    pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
    assert (EQ : (hi - lo) / 8 = hi / 8 - lo / 8).
    { replace (hi - lo) with ((hi / 8 - lo / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite (AsRtIMemmove.wbytes_get_g) by (rewrite repeat_length, Z2Nat.id; wd_ulia).
    rewrite repeat_length, Z2Nat.id by (wd_ulia). unorm.
    replace (inrng (lo / 8 + SB) ((hi - lo) / 8) (U a)) with true by (symmetry; apply inrng_true; lia).
    rewrite nth_repeat_lt by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma M1_same : forall a : word, (U a < U spw - 2192 \/ U spw <= U a) -> M1 M raw spw R a = M a.
  Proof using Hsp oldw base. intros a Ha. apply (M1_out base M oldw raw spw Hsp R a). lia. Qed.

  (* [comment removed for export] *)
  Section Out.
    Variable a : word.
    Hypothesis OFF : U a < U spw - 2192 \/ U spw <= U a.

    Lemma ann_mem_eq : om = nm -> M' a = M a.
    Proof using OFF Hsp Hnm Hom. intros E. (lazymatch goal with |- ?G => let G' := eval unfold ann_mem in G in change_no_check G' end). rewrite Hom, Hnm. rewrite (proj2 (Z.eqb_eq om nm) E). apply M1_same. exact OFF. Qed.

    (* [comment removed for export] *)
    Lemma ann_mem_out :
      (U a < SB + Z.min om nm / 8 \/ SB + (Z.max om nm + 7) / 8 <= U a) -> M' a = M a.
    Proof using OFF HB Hsp E47 HN HO Hbeg Hnm Hom n beg.
      intros W. pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
      assert (FR : U a < U spw - 2192 \/ U spw - 2128 <= U a) by (clear - OFF; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold ann_mem, ann_M3, ann_M2 in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold ga, gb1, gb2, gc, SBADDR in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold gb1 in G in change_no_check G' end). rewrite Hnm.
      destruct (Z.eqb_spec om nm) as [E|NE]; [apply M1_same; exact OFF|].
      pose proof (Z.div_pos nm 8 ltac:(clear - HN Hbeg; lia) ltac:(lia)) as NM0.
      pose proof (Z.div_le_mono nm 140737488355328 8 ltac:(lia) ltac:(clear - HN E47; lia)) as NM1. change (140737488355328 / 8) with 17592186044416 in NM1.
      destruct (Z.ltb_spec om nm) as [LT | GE].
      - (* [comment removed for export] *)
        rewrite Z.min_l in W by lia. rewrite Z.max_r in W by lia.
        pose proof (Z.div_le_mono om nm 8 ltac:(lia) ltac:(lia)) as LE1.
        assert (BYTE : forall m, (nm mod 8 <> 0) -> wbytes m (Z_to_bv 64 (dn8 nm / 8 + SB)) [Z_to_bv 8 (nm mod 8)] a = m a).
        { intros m NZ. rewrite D10. pose proof (dn8_up7 nm) as [[X1 X2] | [X1 X2]]; [exfalso; exact (NZ X2)|]. unfold dn8 in X1.
          assert (E1 : (nm + 7) / 8 = nm / 8 + 1) by (clear - X1; lia).
          apply wbytes_outside; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); change (Z.of_nat 1) with 1%Z; [clear - NM0 NM1; lia | clear - W LE1 E1; lia]. }
        assert (P : (if dn8 om <? dn8 nm then PZ base oldw neww spw (M1 M raw spw R) (dn8 om) (dn8 nm) 0 else M1 M raw spw R) a = M a).
        { destruct (Z.ltb_spec (dn8 om) (dn8 nm)) as [C|C]; [|apply M1_same; exact OFF].
          rewrite (PZ_same base HB oldw oldw neww spw Hsp _ (dn8 om) (dn8 nm) 0 a ltac:(clear - D5; lia) ltac:(clear - C; lia) ltac:(clear - D3 HN E47; lia) FR).
          - apply M1_same; exact OFF.
          - rewrite D13, D9. pose proof (Z.div_le_mono nm (nm + 7) 8 ltac:(lia) ltac:(lia)). clear - W H. lia. }
        destruct (Z.eqb_spec (nm mod 8) 0) as [Z0|NZ]; [exact P|]. rewrite BYTE by exact NZ. exact P.
      - (* [comment removed for export] *)
        assert (LT : nm < om) by (clear - GE NE; lia).
        rewrite Z.min_r in W by lia. rewrite Z.max_l in W by lia.
        pose proof (Z.div_le_mono (nm + 7) (om + 7) 8 ltac:(lia) ltac:(lia)) as LE1.
        assert (BYTE : forall m, (nm mod 8 <> 0) -> wbytes m (Z_to_bv 64 (dn8 nm / 8 + SB)) [Z_to_bv 8 (nm mod 8)] a = m a).
        { intros m NZ. rewrite D10. pose proof (dn8_up7 nm) as [[X1 X2] | [X1 X2]]; [exfalso; exact (NZ X2)|]. unfold dn8 in X1.
          assert (E1 : (nm + 7) / 8 = nm / 8 + 1) by (clear - X1; lia).
          apply wbytes_outside; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); change (Z.of_nat 1) with 1%Z; [clear - NM0 NM1; lia | clear - W LE1 E1; lia]. }
        assert (P : (if dn8 (nm + 7) <? dn8 (om + 7) then PZ base oldw neww spw (M1 M raw spw R) (dn8 (nm + 7)) (dn8 (om + 7)) 252 else M1 M raw spw R) a = M a).
        { destruct (Z.ltb_spec (dn8 (nm + 7)) (dn8 (om + 7))) as [C|C]; [|apply M1_same; exact OFF].
          rewrite (PZ_same base HB oldw oldw neww spw Hsp _ (dn8 (nm + 7)) (dn8 (om + 7)) 252 a ltac:(clear - D4 HN Hbeg; lia) ltac:(clear - C; lia) ltac:(clear - D7; lia) FR).
          - apply M1_same; exact OFF.
          - rewrite D14, D12. pose proof (Z.div_le_mono nm (nm + 7) 8 ltac:(lia) ltac:(lia)). clear - W H. lia. }
        destruct (Z.eqb_spec (nm mod 8) 0) as [Z0|NZ]; [exact P|]. rewrite BYTE by exact NZ. exact P.
    Qed.
  End Out.

  (* [comment removed for export] *)
  Lemma wbyte_hit : forall m (d : word) (b : byte), wbytes m d [b] d = Some b.
  Proof using base.
    intros m d b. pose proof (u64_range d). rewrite AsRtIMemmove.wbytes_get_g by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). change (Z.of_nat 1) with 1.
    replace (inrng (U d) 1 (U d)) with true by (symmetry; apply inrng_true; lia). rewrite Z.sub_diag. reflexivity.
  Qed.
  Lemma wbyte_miss : forall m (d a : word) (b : byte), U a <> U d -> wbytes m d [b] a = m a.
  Proof using base.
    intros m d a b NE. pose proof (u64_range d). rewrite AsRtIMemmove.wbytes_get_g by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). change (Z.of_nat 1) with 1.
    replace (inrng (U d) 1 (U a)) with false by (symmetry; apply inrng_false; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_ne : om <> nm ->
    ann_mem base M oldw neww raw spw R =
      (if (nm mod 8 =? 0) then (fun m => m) else (fun m => wbytes m (Z_to_bv 64 (nm / 8 + SB)) [Z_to_bv 8 (nm mod 8)]))
        (if om <? nm then (if dn8 om <? dn8 nm then PZ base oldw neww spw (M1 M raw spw R) (dn8 om) (dn8 nm) 0 else M1 M raw spw R)
         else (if dn8 (nm + 7) <? dn8 (om + 7) then PZ base oldw neww spw (M1 M raw spw R) (dn8 (nm + 7)) (dn8 (om + 7)) 252 else M1 M raw spw R)).
  Proof using HB E47 HN HO Hbeg Hnm Hom n beg.
    intros NE. pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    (lazymatch goal with |- ?G => let G' := eval unfold ann_mem, ann_M3, ann_M2 in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold ga, gb1, gb2, gc, SBADDR in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold gb1 in G in change_no_check G' end). rewrite Hnm.
    rewrite (proj2 (Z.eqb_neq om nm) NE). rewrite D10. destruct (nm mod 8 =? 0); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_zero : forall a : word, om < nm -> SB + om / 8 <= U a < SB + nm / 8 -> M' a = Some (Z_to_bv 8 0).
  Proof using HB E47 HN HO Hbeg Hnm Hom n beg.
    intros a LT Ha. pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    rewrite (ann_mem_ne ltac:(lia)). rewrite (proj2 (Z.ltb_lt om nm) LT).
    pose proof (Z.div_pos nm 8 ltac:(clear - HN Hbeg; lia) ltac:(lia)) as NM0.
    pose proof (Z.div_le_mono nm 140737488355328 8 ltac:(lia) ltac:(clear - HN E47; lia)) as NM1. change (140737488355328 / 8) with 17592186044416 in NM1.
    assert (C : dn8 om < dn8 nm) by (clear - Ha D9 D10 D1 D3; unfold dn8 in *; lia).
    rewrite (proj2 (Z.ltb_lt _ _) C).
    assert (P : PZ base oldw neww spw (M1 M raw spw R) (dn8 om) (dn8 nm) 0 a = Some (Z_to_bv 8 0)).
    { rewrite (PZ_in (M1 M raw spw R) (dn8 om) (dn8 nm) 0 a ltac:(clear - D5; lia) ltac:(clear - C; lia) ltac:(clear - D3 HN E47; lia)
                (dn8_mod om) (dn8_mod nm) ltac:(rewrite D9, D10; exact Ha)). reflexivity. }
    destruct (Z.eqb_spec (nm mod 8) 0) as [Z0|NZ]; [exact P|].
    rewrite wbyte_miss; [exact P|]. unorm. clear - Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_fc : forall a : word, nm < om -> SB + (nm + 7) / 8 <= U a < SB + (om + 7) / 8 -> M' a = Some (Z_to_bv 8 252).
  Proof using HB E47 HN HO Hbeg Hnm Hom n beg.
    intros a LT Ha. pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    rewrite (ann_mem_ne ltac:(lia)). replace (om <? nm) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (Z.div_pos nm 8 ltac:(clear - HN Hbeg; lia) ltac:(lia)) as NM0.
    pose proof (Z.div_le_mono nm 140737488355328 8 ltac:(lia) ltac:(clear - HN E47; lia)) as NM1. change (140737488355328 / 8) with 17592186044416 in NM1.
    assert (C : dn8 (nm + 7) < dn8 (om + 7)) by (clear - Ha D11 D12 D2 D4; unfold dn8 in *; lia).
    rewrite (proj2 (Z.ltb_lt _ _) C).
    assert (P : PZ base oldw neww spw (M1 M raw spw R) (dn8 (nm + 7)) (dn8 (om + 7)) 252 a = Some (Z_to_bv 8 252)).
    { rewrite (PZ_in (M1 M raw spw R) (dn8 (nm + 7)) (dn8 (om + 7)) 252 a ltac:(clear - D4 HN Hbeg; lia) ltac:(clear - C; lia) ltac:(clear - D7; lia)
                (dn8_mod (nm + 7)) (dn8_mod (om + 7)) ltac:(rewrite D11, D12; exact Ha)). reflexivity. }
    destruct (Z.eqb_spec (nm mod 8) 0) as [Z0|NZ]; [exact P|].
    rewrite wbyte_miss; [exact P|]. unorm.
    pose proof (dn8_up7 nm) as [[X1 X2] | [X1 X2]]; [exfalso; exact (NZ X2)|]. unfold dn8 in X1. clear - Ha X1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_byte : om <> nm -> nm mod 8 <> 0 -> M' (Z_to_bv 64 (SB + nm / 8)) = Some (Z_to_bv 8 (nm mod 8)).
  Proof using HB E47 HN HO Hbeg Hnm Hom n beg.
    intros NE NZ. rewrite (ann_mem_ne NE). rewrite (proj2 (Z.eqb_neq (nm mod 8) 0) NZ).
    replace (SB + nm / 8) with (nm / 8 + SB) by lia. apply wbyte_hit.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_grows : mem_grows M M'.
  Proof using.
    assert (GPZ : forall lo hi v, mem_grows M (PZ base oldw neww spw (M1 M raw spw R) lo hi v)).
    { intros lo hi v. eapply mem_grows_trans; [apply M1_grows | apply PZ_grows]. }
    (lazymatch goal with |- ?G => let G' := eval unfold ann_mem, ann_M3, ann_M2 in G in change_no_check G' end).
    destruct (Ao oldw =? An neww); [apply M1_grows|].
    set (m2 := if Ao oldw <? An neww then _ else _).
    assert (G2 : mem_grows M m2).
    { subst m2. destruct (Ao oldw <? An neww); [destruct (ga oldw <? gb1 neww) | destruct (gb2 neww <? gc oldw)];
        [apply GPZ | apply M1_grows | apply GPZ | apply M1_grows]. }
    destruct (An neww mod 8 =? 0); [exact G2 | eapply mem_grows_trans; [exact G2 | apply wbytes_grows]].
  Qed.

  Lemma wbytes_some_or_same : forall m (d : word) bs (a : word),
    (U d + Z.of_nat (length bs) <= 2 ^ 64)%Z -> wbytes m d bs a = m a \/ exists b, wbytes m d bs a = Some b.
  Proof using.
    intros m d bs a Hb. rewrite AsRtIMemmove.wbytes_get_g by exact Hb. destruct (inrng _ _ _); [right; wd_eexists; reflexivity | left; reflexivity].
  Qed.

  Lemma ann_mem_some : forall a : word, M' a <> M a -> M' a <> None.
  Proof using HB Hsp E47 HN HO Hbeg Hnm Hom nm om n beg.
    intros a NE. pose proof (u64_range spw) as Hs. pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    assert (PSF : forall m (s r0 s0 s1 s2 s3 s4 s5 : word), (64 <= U s)%Z ->
              ps_frame m s r0 s0 s1 s2 s3 s4 s5 a = m a \/ exists b, ps_frame m s r0 s0 s1 s2 s3 s4 s5 a = Some b).
    { intros m s r0 s0 s1 s2 s3 s4 s5 Hs64. pose proof (u64_range s). (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end).
      repeat match goal with |- wbytes ?mm ?dd ?bb a = _ \/ _ =>
        destruct (wbytes_some_or_same mm dd bb a ltac:(rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as [-> | [bx ->]]; [|right; wd_eexists; reflexivity] end.
      left; reflexivity. }
    assert (PZS : forall m lo hi v, 0 <= lo -> lo <= hi -> hi <= 140737488355328 ->
              PZ base oldw neww spw m lo hi v a = m a \/ exists b, PZ base oldw neww spw m lo hi v a = Some b).
    { intros m lo hi v L0 L1 L2. (lazymatch goal with |- ?G => let G' := eval unfold PZ, shad, shlen in G in change_no_check G' end).
      pose proof (Z.div_pos lo 8 L0 ltac:(lia)). pose proof (Z.div_pos (hi - lo) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound lo 8 17592186044416 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (hi - lo) 8 17592186044416 ltac:(lia) ltac:(lia)).
      destruct (wbytes_some_or_same (ps_frame m (sp2 spw) (at_ base 584) spw (Z_to_bv 64 (gb1 neww)) (Z_to_bv 64 (gb2 neww)) (Z_to_bv 64 0) oldw neww)
                 (Z_to_bv 64 (U (Z_to_bv 64 lo) / 8 + SB)) (repeat (cbyte (Z_to_bv 64 v)) (Z.to_nat (U (Z_to_bv 64 (hi - lo)) / 8))) a
                 ltac:(rewrite repeat_length, Z2Nat.id by (wd_ulia); wd_ulia)) as [-> | [bx ->]]; [|right; wd_eexists; reflexivity].
      apply PSF. (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_u by lia. lia. }
    assert (M1S : M1 M raw spw R a = M a \/ exists b, M1 M raw spw R a = Some b) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply PSF; lia).
    Ltac fin H := destruct H as [E | [bx E]]; rewrite E in *; [exfalso; congruence | discriminate].
    unfold ann_mem, ann_M3, ann_M2 in *. rewrite Hom, Hnm in *. unfold ga, gb1, gb2, gc, SBADDR in *. rewrite Hom, Hnm in *. unfold gb1 in *. rewrite Hnm in *.
    destruct (om =? nm). { fin M1S. }
    set (m2 := if om <? nm then _ else _) in *.
    assert (M2S : m2 a = M a \/ exists b, m2 a = Some b).
    { subst m2. destruct (Z.ltb_spec om nm); [destruct (Z.ltb_spec (dn8 om) (dn8 nm)) | destruct (Z.ltb_spec (dn8 (nm + 7)) (dn8 (om + 7)))].
      - destruct (PZS (M1 M raw spw R) (dn8 om) (dn8 nm) 0 ltac:(lia) ltac:(lia) ltac:(lia)) as [-> | [bx ->]]; [exact M1S | right; wd_eexists; reflexivity].
      - exact M1S.
      - destruct (PZS (M1 M raw spw R) (dn8 (nm + 7)) (dn8 (om + 7)) 252 ltac:(lia) ltac:(lia) ltac:(lia)) as [-> | [bx ->]]; [exact M1S | right; wd_eexists; reflexivity].
      - exact M1S. }
    destruct (nm mod 8 =? 0). { fin M2S. }
    pose proof (Z.div_pos nm 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono nm 140737488355328 8 ltac:(lia) ltac:(lia)) as NM1. change (140737488355328 / 8) with 17592186044416 in NM1.
    destruct (wbytes_some_or_same m2 (Z_to_bv 64 (dn8 nm / 8 + SB)) [Z_to_bv 8 (nm mod 8)] a ltac:(rewrite D10; wd_ulia_c)) as [E3 | [bx3 E3]]; rewrite E3 in *; [|discriminate].
    fin M2S.
  Qed.

  (* [comment removed for export] *)
  Lemma ann_mem_mrestrict : forall (Hd : word -> bool),
    beg mod 8 = 0 ->
    hid_off Hd (U spw - 2192) 2192 ->
    (forall z, SB + beg / 8 <= z < SB + (beg + n + 7) / 8 -> Hd (Z_to_bv 64 z) = false) ->
    ann_mem base (mrestrict Hd M) oldw neww raw spw R = mrestrict Hd (ann_mem base M oldw neww raw spw R).
  Proof using HB Hsp E47 HN HO Hbeg Hnm Hom nm om.
    intros Hd B8 FRH NSHD. pose proof (u64_range spw) as Hs.
    pose proof dn8s as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (Z.div_pos beg 8 Hbeg ltac:(lia)) as B0.
    pose proof (Z.div_le_mono (beg + n + 7) 140737488355334 8 ltac:(lia) ltac:(lia)) as BH. change (140737488355334 / 8) with 17592186044416 in BH.
    assert (SHR : forall lo hi, beg <= lo -> lo <= hi -> hi <= beg + n + 7 -> lo mod 8 = 0 -> hid_off Hd (lo / 8 + SB) ((hi - lo) / 8)).
    { clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14. intros lo hi L1 L2 L3 L8. apply hid_off_pw. intros zz Hzz.
      pose proof (Z.div_le_mono beg lo 8 ltac:(lia) L1). pose proof (Z.div_mod lo 8 ltac:(lia)).
      assert ((hi - lo) / 8 <= (beg + n + 7) / 8 - lo / 8).
      { pose proof (Z.div_le_mono (hi - lo) (beg + n + 7 - lo) 8 ltac:(lia) ltac:(lia)) as X.
        replace (beg + n + 7 - lo) with ((beg + n + 7) + (- (lo / 8)) * 8) in X by lia. rewrite Z.div_add in X by lia. lia. }
      split; [lia|]. apply NSHD. lia. }
    assert (PSR : forall m, ps_frame (mrestrict Hd m) spw raw (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)
                            = mrestrict Hd (ps_frame m spw raw (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21))).
    { clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14. intros m. apply ps_frame_mrestrict; [lia|]. eapply hid_off_sub; [exact FRH | lia | lia]. }
    assert (PSR2 : forall m, ps_frame (mrestrict Hd m) (sp2 spw) (at_ base 584) spw (Z_to_bv 64 (dn8 nm)) (Z_to_bv 64 (dn8 (nm + 7))) (Z_to_bv 64 0) oldw neww
                             = mrestrict Hd (ps_frame m (sp2 spw) (at_ base 584) spw (Z_to_bv 64 (dn8 nm)) (Z_to_bv 64 (dn8 (nm + 7))) (Z_to_bv 64 0) oldw neww)).
    { clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14. intros m. apply ps_frame_mrestrict; (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end); rewrite at_u by lia; [lia|]. eapply hid_off_sub; [exact FRH | lia | lia]. }
    assert (PZR : forall m lo hi v, beg <= lo -> lo <= hi -> hi <= beg + n + 7 -> lo mod 8 = 0 ->
              wbytes (ps_frame (mrestrict Hd m) (sp2 spw) (at_ base 584) spw (Z_to_bv 64 (dn8 nm)) (Z_to_bv 64 (dn8 (nm + 7))) (Z_to_bv 64 0) oldw neww)
                     (Z_to_bv 64 (U (Z_to_bv 64 lo) / 8 + SB)) (repeat (cbyte (Z_to_bv 64 v)) (Z.to_nat (U (Z_to_bv 64 (hi - lo)) / 8)))
              = mrestrict Hd (wbytes (ps_frame m (sp2 spw) (at_ base 584) spw (Z_to_bv 64 (dn8 nm)) (Z_to_bv 64 (dn8 (nm + 7))) (Z_to_bv 64 0) oldw neww)
                     (Z_to_bv 64 (U (Z_to_bv 64 lo) / 8 + SB)) (repeat (cbyte (Z_to_bv 64 v)) (Z.to_nat (U (Z_to_bv 64 (hi - lo)) / 8))))).
    { clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14. intros m lo hi v L1 L2 L3 L8. rewrite PSR2.
      pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (hi - lo) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono lo 140737488355334 8 ltac:(lia) ltac:(lia)) as U1. change (140737488355334 / 8) with 17592186044416 in U1.
      pose proof (Z.div_le_mono (hi - lo) 140737488355334 8 ltac:(lia) ltac:(lia)) as U2. change (140737488355334 / 8) with 17592186044416 in U2.
      unorm. apply (wbytes_mrestrict_at Hd _ _ _ ((hi - lo) / 8)); [apply repeat_length | lia | wd_ulia |].
      unorm. apply SHR; assumption. }
    pose proof (dn8_mono beg om ltac:(lia)) as GA. rewrite (dn8_id beg B8) in GA.
    pose proof (dn8_mono (nm + 7) (beg + n + 7) ltac:(lia)) as GB. pose proof (dn8_le (beg + n + 7)) as GE.
    pose proof (dn8_mono (om + 7) (beg + n + 7) ltac:(lia)) as GC.
    (lazymatch goal with |- ?G => let G' := eval unfold ann_mem, ann_M3, ann_M2, PZ, M1 in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold ga, gb1, gb2, gc, SBADDR, shad, shlen in G in change_no_check G' end). rewrite Hom, Hnm. (lazymatch goal with |- ?G => let G' := eval unfold gb1 in G in change_no_check G' end). rewrite Hnm.
    rewrite PSR. set (F1 := ps_frame M spw raw (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).
    destruct (om =? nm); [reflexivity|].
    match goal with |- (if _ then ?X else _) = mrestrict Hd (if _ then ?Y else _) =>
      assert (A2 : X = mrestrict Hd Y) end.
    { destruct (Z.ltb_spec om nm) as [LT|GEo]; [destruct (Z.ltb_spec (dn8 om) (dn8 nm)) as [C|C] | destruct (Z.ltb_spec (dn8 (nm + 7)) (dn8 (om + 7))) as [C|C]].
      - apply PZR; [exact GA | lia | clear - GB GE C HN D3; lia | apply dn8_mod].
      - reflexivity.
      - apply PZR; [lia | lia | clear - GC GE; lia | apply dn8_mod].
      - reflexivity. }
    rewrite A2. destruct (Z.eqb_spec (nm mod 8) 0) as [Z0 | NZ]; [reflexivity|].
    pose proof (Z.div_pos nm 8 ltac:(lia) ltac:(lia)) as NM0. pose proof (Z.div_le_mono nm (beg + n) 8 ltac:(lia) ltac:(lia)) as NMB.
    pose proof (dn8_up7 nm) as [[X1 X2] | [X1 X2]]; [exfalso; exact (NZ X2)|]. unfold dn8 in X1.
    pose proof (Z.div_le_mono (nm + 7) (beg + n + 7) 8 ltac:(lia) ltac:(lia)) as NM7. pose proof (Z.div_le_mono (beg + n) (beg + n + 7) 8 ltac:(lia) ltac:(lia)) as BN.
    pose proof (Z.div_le_mono beg nm 8 ltac:(lia) ltac:(lia)) as BM.
    rewrite D10. clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14. apply wbytes_mrestrict; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); change (Z.of_nat 1) with 1; [clear - NM0 NMB BN BH; lia|].
    apply hid_off_pw. intros zz Hzz. split; [clear -Hzz NM0 NMB BN BH; lia|]. apply NSHD. clear - Hzz X1 NM7 BM. lia.
  Qed.
End M.
End AsIcptAnnM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsRtAccess.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

Definition boxP (P : Prop) : Prop := P.
(* [comment removed for export] *)
Tactic Notation "liac" ne_hyp_list(l) := clear - l; lia.
Ltac lia0 := clear; lia.

Lemma bv_signed_small8 : forall z, 0 <= z < 128 -> bv_signed (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold bv_signed, bv_swrap in G in change_no_check G' end). rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_half_modulus, bv_modulus in G in change_no_check G' end).
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Section CONTRACT.
  Context {fx0 : FPState}.
  Context {RC : run_ceil}.
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  (* [comment removed for export] *)
  Hypothesis HNM : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> n <= NMAX.
  (* [comment removed for export] *)
  Variables (abase : word) (pt : poison_tab) (mt : m2s_tab) (g_flags p_flags g_verb p_verb g_shoff p_shoff : Z).
  Hypothesis ACODE : code_ato SEGS abase 0 anncc_words.
  Hypothesis PTOK : forall fx : FPState, @poison_tab_ok fx SEGS pt.
  Hypothesis PTB : pt_base pt = at_ abase (-3908).
  Hypothesis MTOK : forall fx : FPState, @m2s_tab_ok fx SEGS mt.
  Hypothesis MTB : mt_base mt = at_ abase (-2632).
  Hypothesis G44 : forall fx : FPState, @gload fx SEGS abase 44 11 g_flags.
  Hypothesis G72 : forall fx : FPState, @gload fx SEGS abase 72 10 g_verb.
  Hypothesis G404 : forall fx : FPState, @gload fx SEGS abase 404 11 g_shoff.
  Hypothesis HBASE : (U abase mod 2 = 0)%Z /\ (4096 <= U abase)%Z /\ (U abase + 4096 < 2 ^ 64)%Z.
  Hypothesis MSET_NZ : U (pt_mset pt) <> 0.
  Hypothesis MSET_RET : ret_ok (pt_mset pt).
  Hypothesis T_entry : abase = Z_to_bv 64 (as_annot IA).
  (* [comment removed for export] *)
  Definition ann_cellsL : list (Z * nat * Z) :=
    [(g_flags, 8%nat, p_flags); (p_flags + 96, 1%nat, 1); (g_verb, 8%nat, p_verb); (p_verb, 4%nat, 0); (g_shoff, 8%nat, p_shoff); (p_shoff, 8%nat, SB);
     (pt_g_shoff pt, 8%nat, pt_p_shoff pt); (pt_p_shoff pt, 8%nat, SB);
     (pt_g_midbeg pt, 8%nat, pt_p_midbeg pt); (pt_p_midbeg pt, 8%nat, 0);
     (pt_g_midend pt, 8%nat, pt_p_midend pt); (pt_p_midend pt, 8%nat, 0);
     (pt_g_hiend pt, 8%nat, pt_p_hiend pt); (pt_p_hiend pt, 8%nat, 0x7fffffffffff);
     (pt_g_rms pt, 8%nat, pt_p_rms pt); (pt_p_rms pt, 8%nat, U (pt_mset pt));
     (pt_c_cpm pt, 1%nat, 1); (pt_g_cfl pt, 8%nat, pt_p_cfl pt); (pt_p_cfl pt + 120, 8%nat, 18446744073709551615);
     (mt_g_shoff mt, 8%nat, mt_p_shoff mt); (mt_p_shoff mt, 8%nat, SB);
     (mt_g_midbeg mt, 8%nat, mt_p_midbeg mt); (mt_p_midbeg mt, 8%nat, 0);
     (mt_g_midend mt, 8%nat, mt_p_midend mt); (mt_p_midend mt, 8%nat, 0);
     (mt_g_hiend mt, 8%nat, mt_p_hiend mt); (mt_p_hiend mt, 8%nat, 0x7fffffffffff)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) ann_cellsL.
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) ann_cellsL.
  Hypothesis PFL_img : 0 <= p_flags /\ 0 <= pt_p_cfl pt.

  #[local] Abbreviation cfg := (AsIface3.cfg SEGS).

  (* [comment removed for export] *)

  Theorem C_annotate : ANNOTATE_AT SEGS FXOK IA AAINVH (as_annot IA).
  Proof using PFL_img CELLS_img CELLS T_entry MSET_RET MSET_NZ HBASE G404 G72 G44 MTB MTOK PTB PTOK ACODE p_shoff g_shoff p_verb g_verb p_flags g_flags mt pt abase HNM IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold ANNOTATE_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF B C K ret sp beg n om nm HFX HH AI CP HIN Ha0 Ha1 Ha2 Ha3 HOM HNMID ACC LG.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF; fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    pose proof (aap_zone _ _ _ _ HPh _ _ _ _ _ _ _ beg n AI HIN) as ((Z1 & Z2 & Z3 & Z4) & Zn & Z16).
    pose proof (HNM _ _ _ _ _ _ _ _ _ _ AI HIN) as NMX.
    pose proof (aap_cells _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (BLK & _ & _ & _).
    unfold AS_HEAPLO, PTRHI, PTRLO, SB, AS_LO, MSTK_C, NMAX in *.
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false)
      by (intros z Hz Hr; apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz); tauto).
    (* [comment removed for export] *)
    assert (NSHD : forall z, sh_lo beg <= z < sh_hi beg n -> Hd (Z_to_bv 64 z) = false)
      by (intros z Hz; exact (HL_allowed_page mdl AA (sh_lo beg) (sh_hi beg n) z (Z_to_bv 64 z) (BLKok beg n HIN) Hz eq_refl)).
    (* [comment removed for export] *)
    set (begw := getr R 10) in *; set (endw := getr R 11) in *; set (oldw := getr R 12) in *; set (neww := getr R 13) in *;
    set (spw := getr R 2) in *.
    pose proof (u64_range begw) as Hbr; pose proof (u64_range endw) as Her; pose proof (u64_range oldw) as Hor;
    pose proof (u64_range neww) as Hnr; pose proof (u64_range spw) as Hsr.
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    set (raw := Z_to_bv 64 ret) in *.
    set (Mr := mrestrict Hd M).
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE; pose proof CELLS_img as CI; unfold ann_cellsL in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 CE]. apply Forall_cons_iff in CE; destruct CE as [C3 CE]. apply Forall_cons_iff in CE; destruct CE as [C4 CE]. apply Forall_cons_iff in CE; destruct CE as [C5 CE]. apply Forall_cons_iff in CE; destruct CE as [C6 CE]. apply Forall_cons_iff in CE; destruct CE as [C7 CE]. apply Forall_cons_iff in CE; destruct CE as [C8 CE]. apply Forall_cons_iff in CE; destruct CE as [C9 CE]. apply Forall_cons_iff in CE; destruct CE as [C10 CE]. apply Forall_cons_iff in CE; destruct CE as [C11 CE]. apply Forall_cons_iff in CE; destruct CE as [C12 CE]. apply Forall_cons_iff in CE; destruct CE as [C13 CE]. apply Forall_cons_iff in CE; destruct CE as [C14 CE]. apply Forall_cons_iff in CE; destruct CE as [C15 CE]. apply Forall_cons_iff in CE; destruct CE as [C16 CE]. apply Forall_cons_iff in CE; destruct CE as [C17 CE]. apply Forall_cons_iff in CE; destruct CE as [C18 CE]. apply Forall_cons_iff in CE; destruct CE as [C19 CE]. apply Forall_cons_iff in CE; destruct CE as [C20 CE]. apply Forall_cons_iff in CE; destruct CE as [C21 CE]. apply Forall_cons_iff in CE; destruct CE as [C22 CE]. apply Forall_cons_iff in CE; destruct CE as [C23 CE]. apply Forall_cons_iff in CE; destruct CE as [C24 CE]. apply Forall_cons_iff in CE; destruct CE as [C25 CE]. apply Forall_cons_iff in CE; destruct CE as [C26 CE]. apply Forall_cons_iff in CE; destruct CE as [C27 CE].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 CI]. apply Forall_cons_iff in CI; destruct CI as [D3 CI]. apply Forall_cons_iff in CI; destruct CI as [D4 CI]. apply Forall_cons_iff in CI; destruct CI as [D5 CI]. apply Forall_cons_iff in CI; destruct CI as [D6 CI]. apply Forall_cons_iff in CI; destruct CI as [D7 CI]. apply Forall_cons_iff in CI; destruct CI as [D8 CI]. apply Forall_cons_iff in CI; destruct CI as [D9 CI]. apply Forall_cons_iff in CI; destruct CI as [D10 CI]. apply Forall_cons_iff in CI; destruct CI as [D11 CI]. apply Forall_cons_iff in CI; destruct CI as [D12 CI]. apply Forall_cons_iff in CI; destruct CI as [D13 CI]. apply Forall_cons_iff in CI; destruct CI as [D14 CI]. apply Forall_cons_iff in CI; destruct CI as [D15 CI]. apply Forall_cons_iff in CI; destruct CI as [D16 CI]. apply Forall_cons_iff in CI; destruct CI as [D17 CI]. apply Forall_cons_iff in CI; destruct CI as [D18 CI]. apply Forall_cons_iff in CI; destruct CI as [D19 CI]. apply Forall_cons_iff in CI; destruct CI as [D20 CI]. apply Forall_cons_iff in CI; destruct CI as [D21 CI]. apply Forall_cons_iff in CI; destruct CI as [D22 CI]. apply Forall_cons_iff in CI; destruct CI as [D23 CI]. apply Forall_cons_iff in CI; destruct CI as [D24 CI]. apply Forall_cons_iff in CI; destruct CI as [D25 CI]. apply Forall_cons_iff in CI; destruct CI as [D26 CI]. apply Forall_cons_iff in CI; destruct CI as [D27 CI].
    cbn [fst snd] in *.
    assert (HCELLS : Forall (fun c => 0 <= c /\ c + 8 <= U spw - 2192 /\ c + 8 <= 2147450880)
                       (AsRtAnn.ann_cells pt mt g_flags p_flags g_verb p_verb g_shoff p_shoff)).
    { destruct PFL_img as [PF1 PF2].
      clear - D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 D18 D19 D20 D21 D22 D23 D24 D25 D26 D27 PF1 PF2 IMG_HI IMG_LO CPlo CP2 CR.
      (lazymatch goal with |- ?G => let G' := eval unfold AsRtAnn.ann_cells, poison_cells, m2s_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end).
      repeat apply Forall_cons; try apply Forall_nil; lia. }
    Ltac hoz NZ := apply hid_off_pointwise; intros zz Hzz; split; [lia | apply NZ; lia].
    Ltac konst NZ MM C := apply (cellN_mrestrict SEGS _ MM _ _ _ C); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); hoz NZ].
    assert (K1 : rdn SEGS Mr (Z_to_bv 64 (g_flags)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p_flags)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C1).
    assert (K3 : rdn SEGS Mr (Z_to_bv 64 (g_verb)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p_verb)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C3).
    assert (K5 : rdn SEGS Mr (Z_to_bv 64 (g_shoff)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p_shoff)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C5).
    assert (K6 : rdn SEGS Mr (Z_to_bv 64 (p_shoff)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2147450880)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C6).
    assert (K7 : rdn SEGS Mr (Z_to_bv 64 (pt_g_shoff pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_shoff pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C7).
    assert (K8 : rdn SEGS Mr (Z_to_bv 64 (pt_p_shoff pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2147450880)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C8).
    assert (K9 : rdn SEGS Mr (Z_to_bv 64 (pt_g_midbeg pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_midbeg pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C9).
    assert (K10 : rdn SEGS Mr (Z_to_bv 64 (pt_p_midbeg pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C10).
    assert (K11 : rdn SEGS Mr (Z_to_bv 64 (pt_g_midend pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_midend pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C11).
    assert (K12 : rdn SEGS Mr (Z_to_bv 64 (pt_p_midend pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C12).
    assert (K13 : rdn SEGS Mr (Z_to_bv 64 (pt_g_hiend pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_hiend pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C13).
    assert (K14 : rdn SEGS Mr (Z_to_bv 64 (pt_p_hiend pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x7fffffffffff)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C14).
    assert (K15 : rdn SEGS Mr (Z_to_bv 64 (pt_g_rms pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_rms pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C15).
    assert (K18 : rdn SEGS Mr (Z_to_bv 64 (pt_g_cfl pt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_cfl pt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C18).
    assert (K19 : rdn SEGS Mr (Z_to_bv 64 (pt_p_cfl pt + 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (18446744073709551615)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C19).
    assert (K20 : rdn SEGS Mr (Z_to_bv 64 (mt_g_shoff mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff mt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C20).
    assert (K21 : rdn SEGS Mr (Z_to_bv 64 (mt_p_shoff mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2147450880)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C21).
    assert (K22 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midbeg mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg mt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C22).
    assert (K23 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midbeg mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C23).
    assert (K24 : rdn SEGS Mr (Z_to_bv 64 (mt_g_midend mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend mt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C24).
    assert (K25 : rdn SEGS Mr (Z_to_bv 64 (mt_p_midend mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C25).
    assert (K26 : rdn SEGS Mr (Z_to_bv 64 (mt_g_hiend mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend mt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C26).
    assert (K27 : rdn SEGS Mr (Z_to_bv 64 (mt_p_hiend mt)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x7fffffffffff)))) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); konst NZ M C27).
    assert (K2 : rdn SEGS Mr (Z_to_bv 64 (p_flags + 96)) 1 = Some [Z_to_bv 8 1])
      by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite (cellN_mrestrict SEGS Hd M _ _ _ C2); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]).
    assert (K17 : rdn SEGS Mr (Z_to_bv 64 (pt_c_cpm pt)) 1 = Some [Z_to_bv 8 1])
      by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite (cellN_mrestrict SEGS Hd M _ _ _ C17); [vm_compute; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]).
    assert (K4 : rdn SEGS Mr (Z_to_bv 64 p_verb) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)))
      by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite (cellN_mrestrict SEGS Hd M _ _ _ C4); [reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]).
    assert (K16 : rdn SEGS Mr (Z_to_bv 64 (pt_p_rms pt)) 8 = Some (word_to_le_bytes 8 (pt_mset pt)))
      by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite (cellN_mrestrict SEGS Hd M _ _ _ C16); [rewrite Z_to_bv_bv_unsigned; reflexivity | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoz NZ]).
    (* [comment removed for export] *)
    assert (Rb : begw = Z_to_bv 64 beg) by (apply bv_eq; rewrite u_Z2bv by lia; exact Ha0).
    assert (Re : endw = Z_to_bv 64 (beg + n)) by (apply bv_eq; rewrite u_Z2bv by lia; exact Ha1).
    assert (Ro : oldw = Z_to_bv 64 om) by (apply bv_eq; rewrite u_Z2bv by lia; exact Ha2).
    assert (Rn : neww = Z_to_bv 64 nm) by (apply bv_eq; rewrite u_Z2bv by lia; exact Ha3).
    assert (UAb : Ab begw = beg) by exact Ha0. assert (UAe : Ae endw = beg + n) by exact Ha1.
    assert (UAo : Ao oldw = om) by exact Ha2. assert (UAn : An neww = nm) by exact Ha3.
    assert (E47 : beg + n < 140737488355328) by lia.
    assert (HSP' : 17594333497488 <= U spw /\ U spw + 16 <= 140737488355328) by lia.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (ebz := 2147450880 + (beg + n) / 8).
    set (eb := match M (Z_to_bv 64 ebz) with Some b => b | None => Z_to_bv 8 0 end).
    assert (REB : RebH SEGS g_shoff p_shoff Mr endw eb).
    { (lazymatch goal with |- ?G => let G' := eval unfold RebH in G in change_no_check G' end). rewrite UAe. intros NE8.
      assert (SHZ : sh_lo beg <= ebz < sh_hi beg n).
      { clear - NE8 Zn Z1. (lazymatch goal with |- ?G => let G' := eval unfold ebz, sh_lo, sh_hi in G in change_no_check G' end). pose proof (Z.div_le_mono beg (beg + n) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_mod (beg + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n) 8 ltac:(lia)).
        pose proof (Z.div_mod (beg + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n + 7) 8 ltac:(lia)). (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). lia. }
      assert (EBR : 0 <= ebz < 17594333495296).
      { pose proof SHZ as X. unfold sh_lo, sh_hi, SB in X. clear - X E47 Z1 Zn.
        pose proof (Z.div_pos beg 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_le_mono (beg + n + 7) 140737488355334 8 ltac:(lia) ltac:(lia)) as DM.
        change (140737488355334 / 8) with 17592186044416 in DM. lia. }
      assert (DEF : M (Z_to_bv 64 ebz) <> None).
      { apply (aap_shdef _ _ _ _ HPh _ _ _ _ _ _ _ ebz AI). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ebz in G in change_no_check G' end).
        pose proof (Z.div_le_mono (beg + n) 140737488355327 8 ltac:(lia) ltac:(lia)). change (140737488355327 / 8) with 17592186044415 in *.
        destruct Z4 as [LOW | HIGH].
        - left. pose proof (Z.div_le_mono (beg + n) 2147446784 8 ltac:(lia) ltac:(lia)). change (2147446784 / 8) with 268430848 in *.
          pose proof (Z.div_pos (beg + n) 8 ltac:(lia) ltac:(lia)). lia.
        - right. pose proof (Z.div_le_mono 17594333495296 (beg + n) 8 ltac:(lia) ltac:(lia)). change (17594333495296 / 8) with 2199291686912 in *. lia. }
      destruct (M (Z_to_bv 64 ebz)) as [b|] eqn:EM; [|exfalso; exact (DEF eq_refl)]. subst eb.
      unfold last_gran_ok, sbyte in LG. replace (n mod 8) with ((beg + n) mod 8) in LG.
      2:{ rewrite <- Zplus_mod_idemp_l. replace (beg mod 8) with 0; [reflexivity|]. symmetry.
          pose proof (Z.div_mod beg 16 ltac:(lia0)) as DM16. rewrite Z16 in DM16. replace beg with (beg / 16 * 2 * 8) by (clear - DM16; lia). apply Z_mod_mult. }
      unfold SB in LG. fold ebz in LG. rewrite EM in LG. destruct (LG NE8) as [L1 L2].
      split; [exact K5|]. split; [exact K6|]. split; [|split; [exact L1 | exact L2]].
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [| clear - EBR; wd_ulia_c |].
      - (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). fold ebz. rewrite EM. reflexivity.
      - clear - EBR NSHD SHZ. unorm. intros x Hx. cbn in Hx. replace x with (Z_to_bv 64 ebz) by (apply bv_eq; wd_ulia). apply NSHD. exact SHZ. }
    (* [comment removed for export] *)
    assert (DCO : U (Z_to_bv 8 1) <> 0) by (cbv; discriminate).
    assert (PCPM : PcpmH SEGS pt Mr oldw neww (Z_to_bv 8 1)).
    { (lazymatch goal with |- ?G => let G' := eval unfold PcpmH in G in change_no_check G' end). intros _. split; [exact K17 | exact DCO]. }
    assert (PCFL : PcflH SEGS pt Mr oldw neww 18446744073709551615).
    { (lazymatch goal with |- ?G => let G' := eval unfold PcflH in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ga, gb1 in G in change_no_check G' end). rewrite UAo, UAn. intros LT CALL. split; [exact K18|]. split; [exact K19|]. split; [|lia].
      clear - LT CALL HOM HNMID E47 Z1. apply Z.div_lt_upper_bound; [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end).
      pose proof (Z.div_mod nm 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound nm 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod om 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound om 8 ltac:(lia)) as D4. lia. }
    assert (HB8 : Ab begw mod 8 = 0).
    { rewrite UAb. pose proof (Z.div_mod beg 16 ltac:(lia)) as DM. rewrite Z16 in DM. replace beg with (beg / 16 * 2 * 8) by lia. apply Z_mod_mult. }
    assert (HB8' : beg mod 8 = 0) by (rewrite <- UAb; exact HB8).
    assert (HO1 : Ab begw <= Ao oldw) by (rewrite UAb, UAo; lia). assert (HO2 : Ao oldw <= Ae endw) by (rewrite UAo, UAe; lia).
    assert (HN1 : Ab begw <= An neww) by (rewrite UAb, UAn; lia). assert (HN2 : An neww <= Ae endw) by (rewrite UAn, UAe; lia).
    assert (HN40 : Ae endw - Ab begw <= 1099511627776) by (rewrite UAe, UAb; lia).
    assert (HRNG : rngH begw endw).
    { (lazymatch goal with |- ?G => let G' := eval unfold rngH in G in change_no_check G' end). rewrite UAb, UAe. destruct Z4 as [LOW | HIGH]; [right; lia | left; lia]. }
    assert (HSP : 17594333495296 + 2192 <= U spw) by lia.
    assert (WV : forall (m : mem) (x : word), store_ok SEGS m x 1%nat = true -> wview SEGS m x <> None).
    { intros m x Hx. cbn [store_ok] in Hx. destruct (wview SEGS m x); [discriminate | discriminate Hx]. }
    assert (FRH : hid_off Hd (U spw - 2192) 2192).
    { apply hid_off_pointwise. intros zz Hzz. split; [clear - Hzz Hsr CPlo CP2 CR; lia | apply NZ; [clear - Hzz Hsr CPlo CP2 CR; lia | right; clear - Hzz CPlo CP2 CR; lia]]. }
    assert (HSTK : store_ok SEGS Mr (at_ spw (-2192)) 2192 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u by (clear - Hsr HSP; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsr HSP; lia | rewrite at_u by (clear - Hsr HSP; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact FRH].
      apply store_ok_of_all; [rewrite at_u by (clear - Hsr HSP; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsr HSP; lia|]. intros x Hx. rewrite at_u in Hx by (clear - Hsr HSP; lia).
      apply WV. apply CPstk. cbn in Hx. clear - Hx CP2. lia. }
    assert (HSHW : forall a : word, 2147450880 + Ab begw / 8 <= U a < 2147450880 + (Ae endw + 7) / 8 -> store_ok SEGS Mr a 1%nat = true).
    { intros a Ha. rewrite UAb, UAe in Ha. pose proof (u64_range a). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      - destruct (BLK beg n (U a) HIN) as [_ OK]; [right; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); lia|]. rewrite Z_to_bv_bv_unsigned in OK. exact OK.
      - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros x Hx. replace x with (Z_to_bv 64 (U a)) by (apply bv_eq; wd_ulia). apply NSHD. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    destruct (anncc_run0 SEGS abase pt mt g_flags p_flags g_verb p_verb g_shoff p_shoff ACODE (PTOK fx) PTB (MTOK fx) MTB
                (G44 fx) (G72 fx) (G404 fx) HBASE Mr (seg_rom SEGS) begw endw oldw neww raw spw
                (Z_to_bv 8 1) eb (Z_to_bv 8 1) (Z_to_bv 64 0) (Z_to_bv 64 0) 18446744073709551615
                K1 K2 DCO K3 K4 REB K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 MSET_NZ MSET_RET PCPM PCFL
                K20 K21 K22 K23 K24 K25 K26 K27 HCELLS HB8 HO1 HO2 HN1 HN2 HN40 HRNG HSP HSTK HSHW RET
                R CP1 eq_refl eq_refl eq_refl eq_refl eq_refl) as (r & RUN & R2f & AG).
    (* [comment removed for export] *)
    clear K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
    clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 CE.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 D18 D19 D20 D21 D22 D23 D24 D25 D26 D27 CI.
    clear HCELLS HSTK HSHW PCPM PCFL REB HRNG DCO.
    try clear Rb Re Ro Rn. try clear Hbr Her Hor Hnr. try clear CPr CP16 CP4. try clear Z3 Z4. try clear SHCok HSP'.
    try (clearbody eb ebz; clear eb ebz).
    (* [comment removed for export] *)
    set (M' := ann_mem abase M oldw neww raw spw R).
    assert (MEMr : ann_mem abase Mr oldw neww raw spw R = mrestrict Hd M').
    { subst M'. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply (ann_mem_mrestrict abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HSP HBASE Hd).
      - exact HB8'.
      - exact FRH.
      - intros z Hz. apply NSHD. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). exact Hz. }
    rewrite MEMr in RUN.
    (* [comment removed for export] *)
    set (mn := Z.min om nm). set (mx := Z.max om nm).
    assert (MNX : beg <= mn /\ mn <= om /\ mn <= nm /\ om <= mx /\ nm <= mx /\ mx <= beg + n).
    { subst mn mx. destruct (Z_lt_le_dec om nm); [rewrite Z.min_l, Z.max_r by lia | rewrite Z.min_r, Z.max_l by lia]; lia. }
    assert (MNlt : boxP (om < nm -> mn = om /\ mx = nm)) by ((lazymatch goal with |- ?G => let G' := eval unfold boxP in G in change_no_check G' end); intros; subst mn mx; rewrite Z.min_l, Z.max_r by lia; lia).
    assert (MNge : boxP (nm <= om -> mn = nm /\ mx = om)) by ((lazymatch goal with |- ?G => let G' := eval unfold boxP in G in change_no_check G' end); intros; subst mn mx; rewrite Z.min_r, Z.max_l by lia; lia).
    assert (MNeq : boxP (mn = Z.min om nm /\ mx = Z.max om nm)) by ((lazymatch goal with |- ?G => let G' := eval unfold boxP in G in change_no_check G' end); subst mn mx; split; reflexivity).
    assert (OUT : forall a : word, (U a < U spw - 2192 \/ U spw <= U a) ->
                  (U a < 2147450880 + mn / 8 \/ 2147450880 + (mx + 7) / 8 <= U a) -> M' a = M a).
    { intros a H1' H2'. exact (ann_mem_out abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HSP HBASE a H1' H2'). }
    clearbody mn mx. destruct MNX as (MN1 & MN2 & MN3 & MN4 & MN5 & MN6).
    assert (GRW : mem_grows M M') by (apply ann_mem_grows).
    assert (SOME : forall a : word, M' a <> M a -> M' a <> None).
    { intros a. exact (ann_mem_some abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HSP HBASE a). }
    pose proof (Z.div_le_mono beg mn 8 ltac:(lia0) MN1) as W1. pose proof (Z.div_le_mono (mx + 7) (beg + n + 7) 8 ltac:(lia0) ltac:(liac MN6)) as W2.
    pose proof (Z.div_pos beg 8 ltac:(liac Z1) ltac:(lia0)) as W0.
    pose proof (Z.div_le_mono (beg + n + 7) 140737488355334 8 ltac:(lia0) ltac:(liac E47)) as W3. change (140737488355334 / 8) with 17592186044416 in W3.
    assert (CHG : forall a : word, M' a <> M a ->
              (U spw - 2192 <= U a < U spw) \/ (2147450880 + mn / 8 <= U a < 2147450880 + (mx + 7) / 8)).
    { intros a NEQ.
      destruct (Z_lt_le_dec (U a) (U spw - 2192)) as [L1|G1]; [| destruct (Z_lt_le_dec (U a) (U spw)) as [L2|G2]; [left; liac G1 L2|]].
      - right. destruct (Z_lt_le_dec (U a) (2147450880 + mn / 8)) as [L3|G3]; [exfalso; apply NEQ; apply OUT; [left; exact L1 | left; exact L3]|].
        destruct (Z_lt_le_dec (U a) (2147450880 + (mx + 7) / 8)) as [L4|G4]; [liac G3 L4 | exfalso; apply NEQ; apply OUT; [left; exact L1 | right; exact G4]].
      - right. destruct (Z_lt_le_dec (U a) (2147450880 + mn / 8)) as [L3|G3]; [exfalso; apply NEQ; apply OUT; [right; exact G2 | left; exact L3]|].
        destruct (Z_lt_le_dec (U a) (2147450880 + (mx + 7) / 8)) as [L4|G4]; [liac G3 L4 | exfalso; apply NEQ; apply OUT; [right; exact G2 | right; exact G4]]. }
    assert (SHWn : forall a : word, 2147450880 + mn / 8 <= U a < 2147450880 + (mx + 7) / 8 -> sh_lo beg <= U a < sh_hi beg n).
    { intros a Ha. clear - Ha W1 W2. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). lia. }
    assert (NH' : forall a : word, Hd a = true -> M' a = M a).
    { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. pose proof (u64_range a) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. destruct (CHG a NE) as [X|X].
      - rewrite (NZ (U a)) in Ha; [discriminate Ha | exact Ra | right; liac X CPlo CP2 CR].
      - rewrite (NSHD (U a) (SHWn a X)) in Ha. discriminate Ha. }
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:FSE; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite FSE; discriminate)) as SH. clear - Ha SH IMG_HI CR. lia. }
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end). rewrite <- T_entry. rewrite (at_0 abase) in RUN.
    apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R abase M (seg_rom SEGS))
             (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
    { rewrite restrict_mkst'. exact RUN. }
    intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
    rewrite (munrestrict_mrestrict_same Hd M M' NH').
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold annot_post in G in change_no_check G' end). exists fx, r, M', mdl'.
    assert (LZ : m_vm_lazy mdl' = m_vm_lazy mdl) by (rewrite SBM; destruct mdl; reflexivity).
    assert (HALT : m_halted mdl' = None) by (rewrite SBM; destruct mdl; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HH).
    split; [reflexivity|]. split; [exact HFX|].
    split. { apply regs_kept_of_list. intros x Hx. apply AG. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clob in G in change_no_check G' end). unfold saved_regs in Hx. cbn [In] in Hx |- *.
             intros Hc. repeat (destruct Hx as [<- | Hx]; [repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]); exact Hc |]). exact Hx. }
    (* [comment removed for export] *)
    assert (ZRUN : forall a : word, om < nm -> 2147450880 + om / 8 <= U a < 2147450880 + nm / 8 -> M' a = Some (Z_to_bv 8 0)).
    { intros a. exact (ann_mem_zero abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HBASE a). }
    assert (FRUN : forall a : word, nm < om -> 2147450880 + (nm + 7) / 8 <= U a < 2147450880 + (om + 7) / 8 -> M' a = Some (Z_to_bv 8 252)).
    { intros a. exact (ann_mem_fc abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HBASE a). }
    assert (BRUN : om <> nm -> nm mod 8 <> 0 -> M' (Z_to_bv 64 (2147450880 + nm / 8)) = Some (Z_to_bv 8 (nm mod 8))).
    { exact (ann_mem_byte abase M oldw neww raw spw R beg n om nm UAo UAn ltac:(liac Z1) HOM HNMID E47 HBASE). }
    assert (ERUN : om = nm -> forall a : word, (U a < U spw - 2192 \/ U spw <= U a) -> M' a = M a).
    { intros E a Ha. exact (ann_mem_eq abase M oldw neww raw spw R om nm UAo UAn HSP a Ha E). }
    (* [comment removed for export] *)
    pose proof (Z.div_mod nm 8 ltac:(lia)) as NMd. pose proof (Z.mod_pos_bound nm 8 ltac:(lia)) as NMm.
    pose proof (Z.div_mod (beg + n) 8 ltac:(lia)) as ENd. pose proof (Z.mod_pos_bound (beg + n) 8 ltac:(lia)) as ENm.
    assert (NMe : nm / 8 <= (beg + n) / 8) by (apply Z.div_le_mono; liac HNMID).
    assert (NMb : beg / 8 <= nm / 8) by (apply Z.div_le_mono; liac HNMID).
    assert (OMe : om / 8 <= (beg + n) / 8) by (apply Z.div_le_mono; liac HOM).
    assert (MNo : mn / 8 <= om / 8) by (apply Z.div_le_mono; liac MN2).
    assert (MNn : mn / 8 <= nm / 8) by (apply Z.div_le_mono; liac MN3).
    assert (SPB : U spw - 2192 >= 17594333495296) by (liac HSP).
    assert (ENB : 0 <= (beg + n) / 8 /\ (beg + n) / 8 < 17592186044416).
    { split; [apply Z.div_pos; liac Z1 Zn | apply Z.div_lt_upper_bound; liac E47]. }
    split.
    { (* [comment removed for export] *)
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold sbyte, sh_lo, SB in G in change_no_check G' end).
      pose proof (Z.div_mod a 8 ltac:(lia)) as Ad. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Am.
      assert (Ab' : beg / 8 <= a / 8) by (apply Z.div_le_mono; liac Ha).
      assert (An' : a / 8 <= nm / 8) by (apply Z.div_le_mono; liac Ha).
      assert (SA : 0 <= a / 8 /\ a / 8 < 17592186044416) by (split; [apply Z.div_pos; liac Ha Z1 | apply Z.div_lt_upper_bound; liac Ha HNMID E47]).
      set (Xa := Z_to_bv 64 (2147450880 + a / 8)).
      assert (UXa : U Xa = 2147450880 + a / 8) by (subst Xa; rewrite u_Z2bv by (liac SA); reflexivity).
      assert (FXa : U Xa < U spw - 2192 \/ U spw <= U Xa) by (left; liac UXa SA SPB).
      destruct (Z.eq_dec om nm) as [E | NE].
      - rewrite (ERUN E Xa FXa). pose proof (ACC a ltac:(liac Ha E)) as X. unfold sbyte, sh_lo, SB in X. exact X.
      - destruct (Z_lt_le_dec (a / 8) (mn / 8)) as [B1 | B2].
        + rewrite (OUT Xa FXa ltac:(left; liac UXa B1)).
          assert (a < om) by (destruct (Z_lt_le_dec a om) as [?|GEa]; [assumption|]; pose proof (Z.div_le_mono om a 8 ltac:(lia) GEa); liac B1 MNo H).
          pose proof (ACC a ltac:(liac Ha H)) as X. unfold sbyte, sh_lo, SB in X. exact X.
        + destruct (Z_lt_le_dec om nm) as [LT | GE].
          * unfold boxP in MNlt; destruct (MNlt LT) as [Emn Emx]; clear MNlt MNge; subst mn mx.
            destruct (Z_lt_le_dec (a / 8) (nm / 8)) as [C1' | C2'].
            -- rewrite (ZRUN Xa LT ltac:(rewrite UXa; liac B2 C1')). left. reflexivity.
            -- assert (EQ8 : a / 8 = nm / 8) by (liac C2' An').
               assert (NZ8 : nm mod 8 <> 0) by (liac EQ8 Ha Ad Am NMd NMm).
               replace Xa with (Z_to_bv 64 (2147450880 + nm / 8)) by (subst Xa; rewrite EQ8; reflexivity).
               rewrite (BRUN NE NZ8). right. rewrite bv_signed_small8 by (liac NMm). liac EQ8 Ha Ad Am NMd NMm.
          * unfold boxP in MNge; destruct (MNge GE) as [Emn Emx]; clear MNlt MNge; subst mn mx.
            assert (EQ8 : a / 8 = nm / 8) by (liac B2 An').
            assert (NZ8 : nm mod 8 <> 0) by (liac EQ8 Ha Ad Am NMd NMm).
            replace Xa with (Z_to_bv 64 (2147450880 + nm / 8)) by (subst Xa; rewrite EQ8; reflexivity).
            rewrite (BRUN NE NZ8). right. rewrite bv_signed_small8 by (liac NMm). liac EQ8 Ha Ad Am NMd NMm. }
    split.
    { (* [comment removed for export] *)
      intros NZn. (lazymatch goal with |- ?G => let G' := eval unfold sbyte, SB in G in change_no_check G' end).
      assert (NZe : (beg + n) mod 8 <> 0).
      { rewrite <- Zplus_mod_idemp_l. rewrite HB8'. exact NZn. }
      pose proof LG as LG0. unfold last_gran_ok in LG0. specialize (LG0 NZn). unfold sbyte, SB in LG0.
      set (Xe := Z_to_bv 64 (2147450880 + (beg + n) / 8)) in *.
      assert (UXe : U Xe = 2147450880 + (beg + n) / 8) by (subst Xe; rewrite u_Z2bv by (liac ENB); reflexivity).
      assert (FXe : U Xe < U spw - 2192 \/ U spw <= U Xe) by (left; liac UXe ENB SPB).
      destruct (Z.eq_dec om nm) as [E | NE].
      - rewrite (ERUN E Xe FXe). exact LG0.
      - assert (LOWe : (nm mod 8 <> 0 /\ nm / 8 = (beg + n) / 8) \/ (nm + 7) / 8 <= (beg + n) / 8).
        { pose proof (dn8_up7 nm) as [[X1 X2] | [X1 X2]]; unfold dn8 in X1.
          - right. liac X1 NMe.
          - destruct (Z.eq_dec (nm / 8) ((beg + n) / 8)) as [SG | DG]; [left; split; [exact X2 | exact SG] | right; liac X1 DG NMe]. }
        destruct LOWe as [[NZ8 SAMEG] | LOW7].
        + replace Xe with (Z_to_bv 64 (2147450880 + nm / 8)) by (subst Xe; rewrite SAMEG; reflexivity).
          rewrite (BRUN NE NZ8). rewrite bv_signed_small8 by (liac NMm). liac NZ8 SAMEG HNMID NMd NMm ENd ENm.
        + destruct (Z_lt_le_dec om nm) as [LT | GE].
          * unfold boxP in MNlt; destruct (MNlt LT) as [Emn Emx]; clear MNlt MNge; subst mn mx.
            rewrite (OUT Xe FXe); [exact LG0|]. rewrite UXe. right. liac LOW7.
          * unfold boxP in MNge; destruct (MNge GE) as [Emn Emx]; clear MNlt MNge; subst mn mx.
            destruct (Z_lt_le_dec ((beg + n) / 8) ((om + 7) / 8)) as [IN | ABOVE].
            -- rewrite (FRUN Xe ltac:(liac GE NE) ltac:(rewrite UXe; liac LOW7 IN)).
               change (bv_signed (Z_to_bv 8 252)) with (-4). liac ENm.
            -- rewrite (OUT Xe FXe); [exact LG0|]. rewrite UXe. right. liac ABOVE. }
    split. { intros a Ha. destruct (CHG a Ha) as [X | X]; [right; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_C in G in change_no_check G' end); liac X CP2 | left]. unfold boxP in MNeq. destruct MNeq as [Em Ex].
             rewrite <- Em. (lazymatch goal with |- ?G => let G' := eval unfold sh_hi, SB in G in change_no_check G' end). clear - X W2. split; lia. }
    split. { exact SOME. }
    split. { intros a Ha. unfold MSTK_C in Ha. split.
             - apply GRW. apply (store_ok1_defined SEGS M a); [apply SEGnone; liac Ha CPlo | apply CPstk; liac Ha].
             - eapply store_ok_mono; [exact GRW | apply CPstk; liac Ha]. }
    split. { apply (aap_frame _ _ _ _ HPh [] Lc FF B C K M M' mdl').
             - intros a (lo & hi & Hin & _). destruct Hin.
             - exact (PRES mdl' MI' SBM).
             - intros a Ha. split; [|exact (SOME a Ha)]. destruct (CHG a Ha) as [X | X].
               + right. right. left. liac X CPlo CP2.
               + right. right. right. right. left. exists beg, n. split; [exact HIN | exact (SHWn a X)]. }
    split. { exact (same_except_vm_of_materialized _ _ SBM). }
    split. { intros a _. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite LZ. reflexivity. }
    exact HALT.
  Qed.
End CONTRACT.
