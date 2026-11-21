(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Br/MemcpyCtr.v: the memcpy contract's soundness (memcpy_rr_sound) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (a0's kept value read across the library's copies of the register read by conversion instead of rewriting, as Br/MemcpyCtr.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Omono.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG MemcpyG CtrFX MemFX CopyFX HeapCtr MemcpyCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB RegsEqvB MemStrGB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX PlanSB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module MemcpyCtrW.
Section OPS.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma kept_or_clobbered : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> In (reg_of_r5 x) kept_regs.
Proof.
  intros x N0 N10 H. destruct x; try discriminate H; try congruence;
  unfold kept_regs; cbn [In];
  repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end.
Qed.

Lemma ms_shape : forall E st ms mo, St.st_ok rsegs OPS E st ms mo -> s_resv st = RNone ->
  ms = MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs).
Proof.
  intros E st ms mo HS RV. rewrite (MS_eta ms) at 1 by exact (so_svc _ _ _ _ _ _ HS). f_equal.
  - exact (so_pc _ _ _ _ _ _ HS).
  - pose proof (so_resv _ _ _ _ _ _ HS) as X. rewrite RV in X. exact X.
  - exact (so_rom _ _ _ _ _ _ HS).
Qed.

Lemma call_sound : forall E st ms mo r, St.st_ok rsegs OPS E st ms mo -> call_pre st = Some r -> callP E st ms r.
Proof.
  intros E st ms mo r HS CP.
  pose proof (call_pre_resv st r CP) as RV.
  destruct (call_pre_inv st r CP) as (FR & ra & Hra & Twt & Tlt & ->).
  destruct (fresh_ok_inv st FR) as (SVB & POS & B62).
  pose proof (MemFX.getr_R rsegs OPS E st ms mo HS) as GR.
  pose proof (int_range (wl ra)) as Rr. rewrite two63_eq in Rr.
  assert (EVEN : to_Z (wl ra) mod 2 = 0).
  { pose proof (call_pre_even st _ CP) as Hev.
    pose proof (land_mk (wl ra) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite Hev in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  constructor; try assumption.
  - rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt). apply ret_pc_even; [lia| exact EVEN].
  - rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt). reflexivity.
  - exact (MemFX.mem_inv_of_st_ok rsegs OPS E st ms mo HS).
Qed.

Lemma minv_of_mem_inv : forall M, Lib.Mem.mem_inv rsegs M ->
  forall x b, M x = Some b -> forall seg, find_segment rsegs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros M MI x b Hx seg Hs. pose proof (MI x b Hx) as X. unfold ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Lemma memcpy_mono : forall (m M' : word -> option byte) (D nZ : Z) (src : list byte),
  munch [(D, D + nZ)] m M' -> rw_cells rsegs M' D [CB (Z.to_nat nZ) src] -> 0 <= nZ ->
  (forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None) ->
  forall x, m x <> None -> M' x <> None.
Proof.
  intros m M' D nZ src MU RW Hn NS x Hx.
  pose proof (bv_unsigned_in_range 64 x) as XR. rewrite bv_modulus_64 in XR.
  destruct (Z_lt_le_dec (bv_unsigned x) D) as [L|G]; [| destruct (Z_lt_le_dec (bv_unsigned x) (D + nZ)) as [L2|G2]].
  - rewrite (MU x); [exact Hx|]. cbn. split; [lia| exact I].
  - destruct RW as [_ (_ & _ & WR)]. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in WR.
    pose proof (WR (bv_unsigned x - D) ltac:(lia)) as W. replace (D + (bv_unsigned x - D)) with (bv_unsigned x) in W by lia.
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. unfold wview in W. rewrite (NS (bv_unsigned x)) in W by lia.
    destruct (M' x); [discriminate| exact W].
  - rewrite (MU x); [exact Hx|]. cbn. split; [lia| exact I].
Qed.

Lemma memcpy_frame : forall (m M' : word -> option byte) (D nZ : Z),
  munch [(D, D + nZ)] m M' -> forall a, 0 <= a < W64.two64 -> ~ (D <= a < D + nZ) -> M' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m M' D nZ MU a Ha NI. apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia).
  split; [exact NI| exact I].
Qed.

Lemma based_sep : forall (D S hd hs n : Z),
  (forall a, ~ (D <= a < D + hd /\ S <= a < S + hs)) -> 0 <= n -> n <= hd -> n <= hs -> S + n <= D \/ D + n <= S.
Proof.
  intros D S hd hs n DISJ Hn Nd Ns.
  destruct (Z_lt_le_dec D (S + n)) as [L1|G1]; [| left; lia].
  destruct (Z_lt_le_dec S (D + n)) as [L2|G2]; [| right; lia].
  exfalso. destruct (Z_le_gt_dec S D) as [L|G].
  - apply (DISJ D). lia.
  - apply (DISJ S). lia.
Qed.

Lemma zones_apart : forall E st ms mo ks kd a,
  St.st_ok rsegs OPS E st ms mo -> ks <> kd ->
  CopyFX.zone rsegs (s_regs st) (s_priv st) E ks a -> CopyFX.zoneW rsegs (s_regs st) (s_priv st) E kd a -> False.
Proof.
  intros E st ms mo ks kd a HS NE ZS [ZD WD]. unfold CopyFX.zone in *.
  destruct (PrimInt63.eqb ks 0%uint63) eqn:KS0; destruct (PrimInt63.eqb kd 0%uint63) eqn:KD0.
  - apply Uint63.eqb_correct in KS0. apply Uint63.eqb_correct in KD0. congruence.
  - destruct ZS as [[seg Hs] _]. destruct ZD as (rd & Hkd & RG).
    rewrite (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) kd rd a (so_reg _ _ _ _ _ _ HS kd rd Hkd) KD0 RG) in Hs. discriminate Hs.
  - destruct ZD as [[seg Hs] _]. destruct ZS as (rs & Hks & RG).
    rewrite (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) ks rs a (so_reg _ _ _ _ _ _ HS ks rs Hks) KS0 RG) in Hs. discriminate Hs.
  - destruct ZS as (rs & Hks & RGs). destruct ZD as (rd & Hkd & RGd). destruct (WD eq_refl) as (rd' & Hkd' & W). rewrite Hkd in Hkd'. injection Hkd' as <-.
    exact (so_disj _ _ _ _ _ _ HS ks rs kd rd Hks Hkd NE KS0 KD0 (or_intror W) a (conj RGs RGd)).
Qed.

Lemma zoneW_not_fp : forall E st ms mo kd a o,
  St.st_ok rsegs OPS E st ms mo -> CopyFX.zoneW rsegs (s_regs st) (s_priv st) E kd a -> In o (s_ops st) ->
  ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))).
Proof.
  intros E st ms mo kd a o HS [ZD WD] Ho FP.
  destruct (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) o Ho a FP) as [NB PR].
  unfold CopyFX.zone in ZD. destruct (PrimInt63.eqb kd 0%uint63) eqn:KD0.
  - destruct ZD as [SEG NP]. exact (NP (PR SEG)).
  - destruct ZD as (rd & Hkd & RG). apply NB. exists kd, rd. auto.
Qed.

Lemma wadd_lit0 : forall o, wadd o (wlit (of_Z 0)) = o.
Proof. intros o. apply w2Z_inj. rewrite wadd_ok, wlit_ok. change (to_Z (of_Z 0)) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply w2Z_range. Qed.

Theorem memcpy_rr_sound_b : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound_b rsegs OPS MP PB (CtrM.memcpy_rr_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrM.memcpy_rr_c] in Happ. unfold CtrM.memcpy_rr_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X12) as [nw| | | | | | | | | |] eqn:HX12; try discriminate.
  destruct (wt nw || negb (Z.leb (to_Z (wl nw)) CtrM.MEMCPY_MAX) || negb (PrimInt63.eqb (wl nw) 0%uint63 || CtrM.rr_separated st (wl nw))) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C SEPB]. apply orb_false_iff in C as [T LE]. apply negb_false_iff in LE. apply Z.leb_le in LE.
  apply negb_false_iff in SEPB. unfold CtrM.MEMCPY_MAX in LE.
  destruct (CtrM.copy_bytes rsegs (Z.to_nat (to_Z (wl nw))) 0%uint63 (getr st X11) (getr st X10) st) as [stn|] eqn:CB; [|discriminate].
  destruct (havoc_errno rsegs ERRNO (clobber stn)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrM.memcpy_rr_c] in MSE. rewrite Hpc in MSE.
  set (n := to_Z (wl nw)) in *. pose proof (int_range (wl nw)) as Rn. fold n in Rn.
  set (src := getr st X11) in *. set (dst := getr st X10) in *.
  set (S := bv_unsigned (den E src)). set (D := bv_unsigned (den E dst)).
  pose proof (bv_unsigned_in_range 64 (den E src)) as RS. rewrite bv_modulus_64 in RS. fold S in RS.
  pose proof (bv_unsigned_in_range 64 (den E dst)) as RD. rewrite bv_modulus_64 in RD. fold D in RD.
  assert (HS0 : St.st_ok rsegs OPS E st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo)
    by (rewrite <- MSE; exact HS).

  destruct (CopyFX.copy_bytes_ind rsegs OPS E (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              (Z.to_nat n) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(lia) eq_refl
              (CopyFX.CINV0 rsegs OPS E _ _ _ _ _ mo src dst st (ms_mem ms) RV HS0) CB) as (mn & bs & CI).
  rewrite Z.add_0_l, Z2Nat.id in CI by lia.
  destruct CI as [OKn SHn SRn LEN FRn WRn RDn SRCn DSTn].
  assert (XS : forall j, 0 <= j < n -> bv_unsigned (CopyFX.saddr E src j) = S + j).
  { apply CopyFX.addr_exact. intros j Hj. destruct (SRCn j Hj) as (k & _ & _ & B & _). exact B. }
  assert (XD : forall j, 0 <= j < n -> bv_unsigned (CopyFX.daddr E dst j) = D + j).
  { apply CopyFX.addr_exact. intros j Hj. destruct (DSTn j Hj) as (k & o & key & _ & _ & _ & _ & B & _). exact B. }
  assert (SN : S + n <= two64).
  { destruct (Z.eq_dec n 0) as [->|N0]; [lia|]. destruct (SRCn (n - 1) ltac:(lia)) as (k & _ & _ & B & _). rewrite (XS (n - 1)) in B by lia. lia. }
  assert (DN : D + n <= two64).
  { destruct (Z.eq_dec n 0) as [->|N0]; [lia|]. destruct (DSTn (n - 1) ltac:(lia)) as (k & o & key & _ & _ & _ & _ & B & _). rewrite (XD (n - 1)) in B by lia. lia. }

  assert (SEP : S + n <= D \/ D + n <= S).
  { destruct (Z.eq_dec n 0) as [N0|N0]; [lia|].
    apply orb_prop in SEPB. destruct SEPB as [Z0|SEPB]; [apply Uint63.eqb_correct in Z0; exfalso; apply N0; subst n; rewrite Z0; reflexivity|].
    unfold CtrM.rr_separated in SEPB. fold src dst in SEPB.
    destruct (addr_of dst) as [[kd0 od0]|] eqn:ADST; [|discriminate].

    assert (KS0 : exists ks0, CopyFX.keyof (s_regs st) src = Some ks0 /\
              (ks0 <> kd0 \/ exists os0 a b, addr_of src = Some (kd0, os0) /\ Mem.okey od0 = Some a /\ Mem.okey os0 = Some b /\
                                 (keyZ a + n <= keyZ b \/ keyZ b + n <= keyZ a))).
    { unfold CopyFX.keyof. destruct (addr_of src) as [[ks0 os0]|] eqn:ASRC.
      - exists ks0. split; [reflexivity|]. destruct (Uint63.eqb ks0 kd0) eqn:Q; cbn [negb orb] in SEPB.
        + apply Uint63.eqb_correct in Q. subst ks0. right. exists os0.
          destruct (Mem.okey od0) as [a|]; [|discriminate]. destruct (Mem.okey os0) as [b|]; [|discriminate].
          exists a, b. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          apply orb_prop in SEPB. destruct SEPB as [L|L]; apply Z.leb_le in L; fold n in L; [left| right]; exact L.
        + apply Uint63.eqb_false_spec in Q. left. exact Q.
      - destruct (sym_addr_of (s_regs st) src) as [[[ks0 rs0] off0]|]; [|discriminate]. exists ks0. split; [reflexivity|].
        left. apply Uint63.eqb_false_spec. apply negb_true_iff. exact SEPB. }
    destruct KS0 as (ks0 & KS0 & CASES).
    apply (CopyFX.sep_of_pointwise S D n ltac:(lia)). intros j j' Hj Hj' EQ.
    destruct (SRCn j Hj) as (ks & KS & ZS & _ & XAS). destruct (DSTn j' Hj') as (kd & od & keyd & AD & OKD & XAD & ZD & _ & _ & _).
    rewrite (CopyFX.keyof_add_lit (s_regs st) src ks0 _ KS0) in KS. injection KS as <-.
    rewrite (CopyFX.addr_of_add_lit dst kd0 od0 _ ADST) in AD. injection AD as <- <-.
    rewrite (XS j Hj) in ZS, XAS. rewrite (XD j' Hj') in XAD, ZD.
    destruct CASES as [NEK|(os0 & a & b & ASRC & OKa & OKb & FAR)].
    - exact (zones_apart E st ms mo ks0 kd0 (S + j) HS NEK ZS ltac:(rewrite EQ; exact ZD)).
    -
      destruct (SRCn 0 ltac:(lia)) as (ks1 & _ & _ & _ & XAS0). destruct (DSTn 0 ltac:(lia)) as (kd1 & od1 & keyd1 & AD1 & OKD1 & XAD1 & _).
      rewrite (XS 0) in XAS0 by lia. rewrite (XD 0) in XAD1 by lia. rewrite Z.add_0_r in XAS0, XAD1.
      rewrite (CopyFX.addr_of_add_lit dst kd0 od0 _ ADST), wadd_lit0 in AD1. injection AD1 as <- <-. rewrite OKa in OKD1. injection OKD1 as <-.
      destruct (XAS0 kd0 os0 ltac:(rewrite (CopyFX.addr_of_add_lit src kd0 os0 _ ASRC), wadd_lit0; reflexivity)) as (b0 & OKb0 & ES0).
      rewrite OKb in OKb0. injection OKb0 as <-.
      destruct (XAS kd0 (wadd os0 (wlit (of_Z j))) (CopyFX.addr_of_add_lit src kd0 os0 _ ASRC)) as (bj & OKbj & ESj).

      lia. }

  assert (DISJ : forall j j', 0 <= j < n -> 0 <= j' < n -> CopyFX.saddr E src j <> CopyFX.daddr E dst j').
  { intros j j' Hj Hj' EQW. apply (f_equal bv_unsigned) in EQW. rewrite XS, XD in EQW by lia. lia. }
  assert (RDall : forall j, 0 <= j < n -> rb rsegs (ms_mem ms) (S + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (XS j Hj). apply RDn; [exact Hj|]. intros j' Hj'. apply DISJ; lia. }
  assert (SRCB : bytes_at rsegs (ms_mem ms) S bs).
  { apply CopyFX.bytes_at_of_rb; rewrite ?LEN, ?Z2Nat.id; try lia. intros j Hj. apply RDall. lia. }
  destruct (CopyFX.rw_cells_of_views rsegs (ms_mem ms) D (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id; lia)) as (junk & LJ & DSTC).
  { intros j Hj. rewrite Z2Nat.id in Hj by lia. destruct (DSTn j Hj) as (k & o & key & _ & _ & _ & _ & _ & WB & RB). rewrite (XD j Hj) in WB, RB. auto. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR. subst D dst. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S).
  { rewrite <- reg_of_X11, GR. subst S src. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 n).
  { rewrite <- reg_of_X12, GR, HX12. rewrite <- (Z_to_bv_bv_unsigned (den E (VL nw))), unsigned_VL, (w2Z_nowt nw T). reflexivity. }
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G_b (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S n bs junk K A0 A1 A2
           ltac:(rewrite <- T64; exact RD) ltac:(rewrite <- T64; exact RS) ltac:(lia) RA1 SRCB LEN DSTC SEP MI
           (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (NXn : s_next stn = s_next st) by (rewrite SHn; reflexivity).
  assert (RVn : s_resv stn = RNone) by (rewrite SHn; reflexivity).
  assert (OPSn : s_ops stn = s_ops st) by (rewrite SHn; reflexivity).
  set (E' := MemFX.cenv rsegs E stn R' M' ERRNO).
  assert (EXT : env_ext (s_next st) E E') by (rewrite <- NXn; apply MemFX.cenv_ext).
  assert (HS0' : St.st_ok rsegs OPS E' st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo)
    by (exact (st_ok_reval rsegs OPS (s_next st) E E' EXT st _ mo POS SVB HS0)).
  destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _ & _ & _ & _ & P6).
  assert (DS : den E' src = den E src) by (apply (den_reval (s_next st) E E' EXT); exact (rf_allb_get _ _ _ P1 X11)).
  assert (DD : den E' dst = den E dst) by (apply (den_reval (s_next st) E E' EXT); exact (rf_allb_get _ _ _ P1 X10)).
  destruct (CopyFX.copy_bytes_ind rsegs OPS E' (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              (Z.to_nat n) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(lia) eq_refl
              (CopyFX.CINV0 rsegs OPS E' _ _ _ _ _ mo src dst st (ms_mem ms) RV HS0') CB) as (mn' & bs' & CI').
  rewrite Z.add_0_l, Z2Nat.id in CI' by lia.
  destruct CI' as [OKn' _ _ LEN' FRn' WRn' RDn' _ _].
  assert (SD' : forall j, CopyFX.saddr E' src j = CopyFX.saddr E src j) by (intros j; unfold CopyFX.saddr; rewrite DS; reflexivity).
  assert (DD' : forall j, CopyFX.daddr E' dst j = CopyFX.daddr E dst j) by (intros j; unfold CopyFX.daddr; rewrite DD; reflexivity).
  assert (BSEQ : forall j, 0 <= j < n -> nth (Z.to_nat j) bs' (Z_to_bv 8 0) = nth (Z.to_nat j) bs (Z_to_bv 8 0)).
  { intros j Hj. pose proof (RDn' j Hj ltac:(intros j' Hj'; rewrite SD', DD'; apply DISJ; lia)) as X. rewrite SD', (XS j Hj), (RDall j Hj) in X.
    injection X as X. symmetry. exact X. }
  assert (DW : forall j, 0 <= j < n -> CopyFX.daddr E dst j = Z_to_bv 64 (D + j)).
  { intros j Hj. rewrite <- (XD j Hj). symmetry. apply Z_to_bv_bv_unsigned. }
  destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
  destruct BY as (_ & _ & BY). rewrite LEN in BY. rewrite (Z2Nat.id n) in WR by lia.
  assert (HSn' : St.st_ok rsegs OPS E' stn (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { apply (MemFX.st_ok_view_ext rsegs OPS E' stn _ _ _ _ None mn' M' _ mo OKn').
    - intros a Ha. destruct (Z_lt_le_dec a D) as [L|G]; [| destruct (Z_lt_le_dec a (D + n)) as [L2|G2]].
      + unfold rb. rewrite (memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
        intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia.
      + rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) at 1 by lia. rewrite BY by lia.
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite LEN; lia).
        unfold rb. replace (Z_to_bv 64 a) with (CopyFX.daddr E' dst (a - D)) by (rewrite DD', DW by lia; f_equal; lia).
        rewrite (WRn' (a - D)) by lia. rewrite BSEQ by lia. reflexivity.
      + unfold rb. rewrite (memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
        intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia.
    - intros a Ha W. destruct (Z_lt_le_dec a D) as [L|G]; [| destruct (Z_lt_le_dec a (D + n)) as [L2|G2]].
      + assert (EQM : mn' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
        { apply FRn'. intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia. }
        assert (W0 : wb rsegs (ms_mem ms) a = true) by (unfold wb, wview in W |- *; rewrite <- EQM; exact W).
        apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact W0.
      + apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + assert (EQM : mn' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
        { apply FRn'. intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia. }
        assert (W0 : wb rsegs (ms_mem ms) a = true) by (unfold wb, wview in W |- *; rewrite <- EQM; exact W).
        apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact W0.
    -
      rewrite OPSn. apply Forall_forall. intros o Ho.
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS0') o Ho) as OH. cbn [ms_mem MS] in OH.
      apply (St.op_frame OPS _ _ (ms_mem ms) M' mo); [| intros a _ Hm; exact (OM _ Hm)| exact OH].
      intros a Ha FP. symmetry. apply (memcpy_frame _ _ D n MU a Ha). intros IN.
      assert (FP0 : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
      { replace (map (den E) (op_args o)) with (map (den E') (op_args o)); [exact FP|].
        apply map_ext_in. intros u Hu. apply (den_reval (s_next st) E E' EXT). exact (forallb_In _ _ _ u (forallb_In _ _ _ _ P6 Ho) Hu). }
      destruct (DSTn (a - D) ltac:(lia)) as (k & o' & key & _ & _ & _ & ZD & _). rewrite (XD (a - D)) in ZD by lia.
      replace (D + (a - D)) with a in ZD by lia. exact (zoneW_not_fp E st ms mo k a o HS ZD Ho FP0).
    - exact (minv_of_mem_inv M' MI'). }

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10. etransitivity; [exact A0'|]. symmetry. exact A0.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  pose proof POS as POSn. pose proof B62 as B62n. rewrite <- NXn in POSn, B62n.
  destruct (MemFX.ccall_frame_above rsegs OPS E stn ERRNO r st2 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo
              HSn' RVn POSn B62n HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ EXT HMP ST).
Qed.

Hypothesis PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).

Lemma dst_offset_sound : forall E R a k off, CtrM.dst_offset R a = Some (k, off) -> den E a = (ev E k + den E off)%bv.
Proof.
  intros E R a k off H. unfold CtrM.dst_offset in H.
  destruct a as [|k1 o1| | | | | | | | |]; try (destruct (sym_addr_of R _) as [[[k2 r2] off2]|] eqn:SA; [| discriminate H]; injection H as <- <-;
    exact (proj2 (sym_addr_of_sound E R _ _ _ _ SA))).
  destruct (weqb o1 wzero) eqn:W; injection H as <- <-.
  - apply weqb_eq in W. subst o1. reflexivity.
  - reflexivity.
Qed.

Lemma sym_offset_sound : forall E R a k off, CtrA.sym_offset R a = Some (k, off) -> den E a = (ev E k + den E off)%bv.
Proof.
  intros E R a k off H. unfold CtrA.sym_offset in H.
  destruct a as [|k1 o1| | | | | | | | |]; try (destruct (sym_addr_of R _) as [[[k2 r2] off2]|] eqn:SA; [| discriminate H]; injection H as <- <-;
    exact (proj2 (sym_addr_of_sound E R _ _ _ _ SA))).
  destruct (weqb o1 wzero) eqn:W; injection H as <- <-.
  - apply weqb_eq in W. subst o1. reflexivity.
  - reflexivity.
Qed.

End OPS.
End MemcpyCtrW.
