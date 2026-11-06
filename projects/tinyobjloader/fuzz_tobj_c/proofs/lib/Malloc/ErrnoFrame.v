(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "of_nat"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_errno"; "holds"; "mc_ctx"; "mc_img_hi"; "mc_img_lo"; "mc_lock"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "CTX_SIZE"; "LCtx"; "LMem"; "footprint"; "le_byte"; "@Corelib.Init.Datatypes"; "bool"; "Some"; "length"; "option"; "nat"; "pair"; "prod"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame"; "lev"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv"; "MA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "astate"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "static_addr"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocLayout MallocFooter MallocIface FpLaws MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma footprint_entry_cases' : ltac2:(tb__ "0|0|
S27S12S0S2cS1eS12S0A2S1dS12S0R2R1A4S16R3A1A3S5S1S2S12R3S14Z0A1A3S2S0R2S13A3A2S3S25S25S2S12R4S15R1A1A3Lp;A2A2F_;Fn;Fl;Fs;").
Proof.
  intros s l n Hin. unfold footprint in Hin. destruct Hin as [E | Hin].
  - left. injection E as <- <-. auto.
  - right. apply in_app_iff in Hin as [Hin | Hin].
    + apply in_map_iff in Hin as (a & E & _). injection E as <- _. exists a. reflexivity.
    + apply in_flat_map in Hin as (k & _ & Hin).
      destruct (region_of s k) as [rg|]; [|destruct Hin].
      destruct (rg_kind rg); try (destruct Hin; fail).
      destruct (rg_live rg); [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- _. eexists. reflexivity.
Qed.

Definition errno_frame_stmt (C : mconsts) : Prop := ltac2:(tb__ "0|7|
S24S28Q40M0A1M1S1bS28Q8A1M2A1M3F_;G1S18F_;S2aG1G3Fx;G1S18Fx;S23VC;R6R5R4R3A5S0S1S6Z0R1A2S7R1S9Z2Z40A2A2A2S4S1S6ScVC;A1M4R2A2S7R2S8G4Z4A2M5A2A2A1S1S2G3R6S29G0R3A2M6A1R9G6A1A3S2S18R5G6A1R8G6A1A3A2F_;F_;Fa;S0S1S6G4R1A2S7R1G5A2A2S3G2G2S2G3R7G6A1S19G2R1A2A3Lb;A2F_;Fa;S23VC;R9R5R4R6A5F_;F_;F_;Fwok';Frd';Fvm;Fwok;Frd;FA;").

Fixpoint lev (bs : list Z) : Z := match bs with [] => 0 | b :: t => b + 256 * lev t end.
Lemma lev_nonneg l : ltac2:(tb__ "0|1|
S1fS0S0S1S6Z0M0R1A2S7R1Z100A2A2Lb;Vl;A3S6G0S21Vl;A1A2F_;").
Proof. induction l as [|b t IH]; intros H; cbn [lev]; [lia|]. apply Forall_cons_iff in H as [Hb Ht]. specialize (IH Ht). lia. Qed.
Lemma lev_lt l : ltac2:(tb__ "0|1|
S1fS0S0S1S6Z0R1A2S7R1Z100M0A2A2Lb;Vl;A3S7S21Vl;A1S9G0SaS1aS0Vl;A2A1A2A2F_;").
Proof.
  induction l as [|b t IH]; intros H; cbn [lev length]; [lia|].
  apply Forall_cons_iff in H as [Hb Ht]. specialize (IH Ht). pose proof (lev_nonneg t Ht).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma pow256 n : ltac2:(tb__ "0|1|
S2S0S9Z100SaVn;A1M0A2S9Z2SbZ8G0A2A2A3").
Proof. change 256 with (2 ^ 8). rewrite <- Z.pow_mul_r by lia. reflexivity. Qed.

Lemma le_byte_lev l k : ltac2:(tb__ "0|2|
S1fS0S0S1S6Z0M0R1A2S7R1Z100A2A2Lb;Vl;A3S22Vk;S1aS0Vl;A2M1A2S2S0S17S21Vl;A1G1Vk;A3S20S0Vk;Vl;G0A4A3F_;F_;").
Proof.
  revert k. induction l as [|b t IH]; intros k H Hk; cbn [length] in Hk; [lia|].
  pose proof H as HBT. apply Forall_cons_iff in H as [Hb Ht]. pose proof (lev_nonneg t Ht) as NT. pose proof (lev_lt t Ht) as LT.
  pose proof (lev_lt (b :: t) HBT) as LBT. cbn [length] in LBT. rewrite pow256 in LT, LBT.
  pose proof (lev_nonneg (b :: t) HBT) as NBT.
  unfold le_byte. rewrite (Z.mod_small (lev (b :: t))) by (cbn [length]; lia).
  cbn [lev].
  destruct k as [|k].
  - cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. Z.to_euclidean_division_equations; nia.
  - cbn [nth]. specialize (IH k Ht ltac:(lia)). unfold le_byte in IH. rewrite (Z.mod_small (lev t)) in IH by lia.
    rewrite <- IH. f_equal. rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite <- Z.shiftr_shiftr by lia. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    Z.to_euclidean_division_equations; nia.
Qed.

Lemma holds_of_readable (m : byteview) a w : ltac2:(tb__ "0|0|
S1cS22R1Vw;A2S3S0S0S1S2S1bS0A1Vm;S8Va;SaR3A1A2A1S19S0R1A2A3S1S6Z0R1A2S7R1Z100A2A2A2Lb;A2F_;Fk;S3S0S0SdVm;Va;Vw;R1A4Lv;A2F_;").
Proof.
  intros H.
  set (f := fun k => match m (a + Z.of_nat k) with Some b => b | None => 0 end).
  set (l := map f (seq 0 w)).
  assert (Hl : length l = w) by (subst l; rewrite length_map, length_seq; reflexivity).
  assert (Fl : Forall (fun b => 0 <= b < 256) l).
  { subst l. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). apply in_seq in Hk.
    destruct (H k ltac:(lia)) as (bb & E & R). unfold f. rewrite E. exact R. }
  assert (NTH : forall k, (k < w)%nat -> nth k l 0 = f k).
  { intros k Hk. subst l. rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
    rewrite map_nth, seq_nth by exact Hk. reflexivity. }
  exists (lev l). intros k Hk. rewrite <- Hl at 1. rewrite (le_byte_lev l k Fl) by lia. rewrite (NTH k Hk).
  destruct (H k Hk) as (bb & E & R). unfold f. rewrite E. reflexivity.
Qed.

Section ErrnoFrame.
  Variable C : mconsts.

  Hypothesis E_img : ltac2:(tb__ "0|1|
S0S1S6ScVC;A1M0R1A2S7R1S8G0Z4A2A2A2S1S6S10VC;A1R2A2S7R2SfVC;A1A2A2F_;Fa;").
  Hypothesis E_static : ltac2:(tb__ "0|1|
S0S1S6ScVC;A1M0R1A2S7R1S8G0Z4A2A2A2S4S2bVC;R2A2A1F_;Fa;").
  Hypothesis E_ctx : ltac2:(tb__ "0|2|
S0S1S6ScVC;A1M0R1A2S7R1S8G0Z4A2A2A2S4S1S6SeVC;A1M1R2A2S7R2S8G1S13A2A2A2A1F_;Fa;").
  Hypothesis E_lock : ltac2:(tb__ "0|3|
S0S1S6ScVC;A1M0R1A2S7R1S8G0Z4M1A2A2A2S4S1S6S11VC;A1M2R2A2S7R2S8G2G1A2A2A2A1F_;Fa;").
  Hypothesis E_low : ltac2:(tb__ "0|1|
S0S1S6ScVC;A1M0R1A2S7R1S8G0Z4A2A2A2S1S6S26R2A2S7R2Z7fff7f800000A2A2F_;Fa;").

  Theorem minv_errno_frame : errno_frame_stmt C.
  Proof using E_ctx E_img E_lock E_low E_static.
    intros [s L] rd wok vm rd' wok' HM AG RD.
    pose proof HM as (HW & HB & HC & ((HL & HI & HO) & HF) & HV & HS & HA & HLG & HIMG). cbn [ma_s ma_L] in *.
    assert (E_dec : forall a, (mc_errno C <= a < mc_errno C + 4) \/ ~ (mc_errno C <= a < mc_errno C + 4)) by (intros a; lia).
    assert (NO : forall a, 0 <= a < 2 ^ 64 -> owned C L s a \/ static_addr C a -> ~ (mc_errno C <= a < mc_errno C + 4)).
    { intros a Ha [Ho|Hs] He; [|exact (E_static a He Hs)].
      destruct Ho as [Ho|Ho].
      - destruct Ho as [([l n] & Hrg & Hx) _]. cbn [fst snd] in Hx.
        destruct (footprint_entry_cases' s l n Hrg) as [[-> ->] | [p ->]].
        + unfold loc_addr in Hx. rewrite HC in Hx. apply (E_ctx a He). lia.
        + pose proof (fp_mem_range C L s vm p n HV HLG Hrg ltac:(lia)) as (R1 & R2 & R3).
          change (loc_addr L (LMem p)) with (addr_of L p) in Hx. pose proof (E_img a He). clear - Hx R3 H. lia.
      - exact (E_lock a He Ho). }
    assert (AG' : forall a, 0 <= a < 2 ^ 64 -> owned C L s a \/ static_addr C a ->
              rd' (Z_to_bv 64 a) = rd (Z_to_bv 64 a) /\ wok' (Z_to_bv 64 a) = wok (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (AG a Ha). exact (NO a Ha Ho). }
    pose proof (bv_agree C s L rd rd' wok wok' AG') as BA.
    unfold MInv. cbn [ma_s ma_L].
    split; [exact HW|]. split; [exact HB|]. split; [exact HC|].
    split.
    { split; [split; [exact HL|split]|].
      - apply Forall_forall. intros c Hc. apply (cell_holds_agree C s L rd rd' wok wok' AG' HW HL c (or_introl Hc)).
        exact (proj1 (Forall_forall _ _) HI c Hc).
      - intros x Hx. rewrite (proj1 (BA x (fun _ => or_introl (or_introl Hx)))). exact (HO x Hx).
      - apply Forall_forall. intros c Hc. apply (cell_holds_agree C s L rd rd' wok wok' AG' HW HL c (or_intror Hc)).
        exact (proj1 (Forall_forall _ _) HF c Hc). }
    split; [exact HV|].
    assert (RV : forall a, static_addr C a -> byteview_of rd' (fun _ => true) a = byteview_of rd (fun _ => true) a).
    { intros a Ha. exact (proj2 (BA a (fun _ => or_intror Ha))). }
    pose proof (topL_range L) as TR.
    assert (RHI : forall a, topL L <= a -> byteview_of rd' (fun _ => true) a = byteview_of rd (fun _ => true) a).
    { intros a Ha. unfold byteview_of. destruct ((0 <=? a) && (a <? 2 ^ 64))%bool eqn:E; [|reflexivity].
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [andb].
      rewrite (proj1 (AG a ltac:(lia) ltac:(intros He; pose proof (E_low a He); lia))). reflexivity. }
    assert (RD' : forall a v, byteview_of rd (fun _ => true) a = Some v -> exists v', byteview_of rd' (fun _ => true) a = Some v' /\ 0 <= v' < 256).
    { intros a v Hv. unfold byteview_of in *. destruct ((0 <=? a) && (a <? 2 ^ 64))%bool eqn:E; [|discriminate].
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [andb] in *.
      destruct (E_dec a) as [He|He].
      - destruct (RD a He) as [b Hb]. rewrite Hb. exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as U. change (bv_modulus 8%N) with 256 in U. lia.
      - rewrite (proj1 (AG a ltac:(lia) He)). destruct (rd (Z_to_bv 64 a)) as [b|]; [|discriminate].
        exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as U. change (bv_modulus 8%N) with 256 in U. lia. }
    split.
    { destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (gd & S9 & S10)).
      unfold statics_ok, mc_need_locks, mc_page_size, mc_auxv in *.
      split; [eapply holds_agree; [|exact S1]; intros k Hk; apply RV; unfold static_addr; lia|].
      split; [eapply holds_agree; [|exact S2]; intros k Hk; apply RV; unfold static_addr; lia|].
      split; [eapply holds_agree; [|exact S3]; intros k Hk; apply RV; unfold static_addr; lia|].
      split. { eapply holds_agree; [|exact S4]. intros k Hk. refine (proj1 (BA _ _)). intros _. left. right. lia. }
      split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S5 k Hk). }
      split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S6 k Hk). }
      split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S7 k Hk). }
      split. { intros k Hk. rewrite RV by (unfold static_addr; lia). exact (S8 k Hk). }
      exists gd. split.
      - eapply holds_agree; [|exact S9]. intros k Hk; apply RV; unfold static_addr; lia.
      - eapply holds_agree; [|exact S10]. intros k Hk; apply RV; unfold static_addr; lia. }
    split.
    {   intros Hf. destruct (HA Hf) as (av & q & n & A1 & A2 & A3 & A4 & A5 & A6 & Aav & Aq & Aq2 & Hn).
      exists av, q, n. unfold mc_auxv in *.
      assert (AGH : forall b z, topL L <= b -> holds (byteview_of rd (fun _ => true)) b 8 z -> holds (byteview_of rd' (fun _ => true)) b 8 z).
      { intros b z Hb Hh. eapply holds_agree; [|exact Hh]. intros k Hk. apply RHI. lia. }
      split; [eapply holds_agree; [|exact A1]; intros k Hk; apply RV; unfold static_addr; lia|].
      split; [apply AGH; [lia | exact A2]|]. split; [apply AGH; [lia | exact A3]|]. split; [apply AGH; [lia | exact A4]|].
      split.
      { intros i Hi. destruct (A5 i Hi) as (k & v & B1 & B2 & B3 & B4). exists k, v.
        split; [apply AGH; [lia | exact B1]|]. split; [exact B2|]. split; [apply AGH; [lia | exact B3]|].
        intros Hk. destruct (B4 Hk) as [w Hw]. apply (holds_of_readable _ (v + 8) 8).
        intros j Hj. destruct (RD' _ _ (Hw j Hj)) as (v' & E' & R'). exists v'. auto. }
      split.
      { destruct A6 as (t & Hnt & T0 & T1). exists t. split; [exact Hnt|]. split; [apply AGH; [lia | exact T0]|].
        intros i Hi. destruct (T1 i Hi) as (k & K1 & K2 & K3). exists k. split; [apply AGH; [lia | exact K1] | auto]. }
      repeat split; assumption. }
    split; [exact HLG | exact HIMG].
  Qed.
End ErrnoFrame.

Lemma errno_frame_P : errno_frame_stmt C_P.
Proof. apply minv_errno_frame; intros a Ha; unfold mc_errno, static_addr in *; cbn in *; unfold CTX_SIZE, PGSZ; lia. Qed.
Lemma errno_frame_U : errno_frame_stmt C_U.
Proof. apply minv_errno_frame; intros a Ha; unfold mc_errno, static_addr in *; cbn in *; unfold CTX_SIZE, PGSZ; lia. Qed.
