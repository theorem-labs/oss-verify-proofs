(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM DefsW.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG MemcpyG CtrFX MemFX CopyFX CopyFXW HeapCtr MemcpyCtr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable OPS : St.optable.
Hypothesis OPS_plain : St.plain_table OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem memcpy_w_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrW.memcpy_w_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrW.memcpy_w_c] in Happ. unfold CtrW.memcpy_w_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X12) as [nw| | | | | | | | | |] eqn:HX12; try discriminate.
  destruct (wt nw || negb (Z.leb (to_Z (wl nw)) CtrW.MEMCPYW_MAX) || PrimInt63.eqb (wl nw) 0%uint63
            || negb (PrimInt63.eqb (PrimInt63.land (wl nw) 7%uint63) 0%uint63) || negb (CtrW.ww_separated st (wl nw))) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C SEPB]. apply orb_false_iff in C as [C AL8]. apply orb_false_iff in C as [C NZ]. apply orb_false_iff in C as [T LE].
  apply negb_false_iff in LE. apply Z.leb_le in LE. apply negb_false_iff in SEPB. apply negb_false_iff in AL8. unfold CtrW.MEMCPYW_MAX in LE.
  destruct (CtrW.copy_words rsegs (Z.to_nat (to_Z (wl nw) / 8)) 0%uint63 (getr st X11) (getr st X10) st) as [stn|] eqn:CB; [|discriminate].
  destruct (havoc_errno rsegs ERRNO (clobber stn)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  destruct (MemcpyCtr.call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (MemcpyCtr.ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrW.memcpy_w_c] in MSE. rewrite Hpc in MSE.
  set (n := to_Z (wl nw)) in *. pose proof (int_range (wl nw)) as Rn. fold n in Rn.
  assert (N0 : 0 < n).
  { destruct (Z.eq_dec n 0) as [Q|Q]; [| lia]. exfalso. apply Uint63.eqb_false_spec in NZ. apply NZ. apply Uint63.to_Z_inj. exact Q. }
  assert (N8 : n = 8 * (n / 8)).
  { apply Uint63.eqb_correct in AL8. pose proof (land_mk (wl nw) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. rewrite AL8 in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 3%uint63) with 8 in LM. fold n in LM. pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
  set (src := getr st X11) in *. set (dst := getr st X10) in *.
  set (S := bv_unsigned (den E src)). set (D := bv_unsigned (den E dst)).
  pose proof (bv_unsigned_in_range 64 (den E src)) as RS. rewrite bv_modulus_64 in RS. fold S in RS.
  pose proof (bv_unsigned_in_range 64 (den E dst)) as RD. rewrite bv_modulus_64 in RD. fold D in RD.

  unfold CtrW.ww_separated in SEPB. fold src dst in SEPB.
  destruct (addr_of dst) as [[kd od]|] eqn:ADST; [|discriminate]. destruct (addr_of src) as [[ks os]|] eqn:ASRC; [|discriminate].
  assert (HS0 : St.st_ok rsegs OPS E st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo)
    by (rewrite <- MSE; exact HS).

  destruct (CopyFXW.copy_words_ind rsegs OPS E (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              ks kd os od ASRC ADST (Z.to_nat (n / 8)) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(rewrite Z2Nat.id by (apply Z.div_pos; lia); lia) eq_refl
              (CopyFXW.CINVW0 rsegs OPS E _ _ _ _ _ mo src dst st (ms_mem ms) RV ks kd os od HS0) CB) as (mn & bs & CI).
  rewrite Z.add_0_l, Z2Nat.id, <- N8 in CI by (apply Z.div_pos; lia).
  destruct CI as [OKn SHn SRn LEN FRn WRn RDn SRCn SRC0 DSTn DST0].
  assert (XS : forall j, 0 <= j < n -> bv_unsigned (CopyFX.saddr E src j) = S + j).
  { apply CopyFX.addr_exact. intros j Hj. exact (proj2 (SRCn j Hj)). }
  assert (XD : forall j, 0 <= j < n -> bv_unsigned (CopyFX.daddr E dst j) = D + j).
  { apply CopyFX.addr_exact. intros j Hj. destruct (DSTn j Hj) as (_ & B & _). exact B. }
  assert (SN : S + n <= two64) by (pose proof (proj2 (SRCn (n - 1) ltac:(lia))) as B; rewrite (XS (n - 1)) in B by lia; lia).
  assert (DN : D + n <= two64) by (destruct (DSTn (n - 1) ltac:(lia)) as (_ & B & _); rewrite (XD (n - 1)) in B by lia; lia).

  assert (SEP : S + n <= D \/ D + n <= S).
  { destruct (Uint63.eqb ks kd) eqn:Q; cbn [negb orb] in SEPB.
    - apply Uint63.eqb_correct in Q. subst ks.
      destruct (SRC0 N0) as (b & OKb & ES0). destruct (DST0 N0) as (a & OKa & ED0). rewrite OKa, OKb in SEPB.
      rewrite (XS 0) in ES0 by lia. rewrite (XD 0) in ED0 by lia. rewrite Z.add_0_r in ES0, ED0.
      apply orb_prop in SEPB. destruct SEPB as [L|L]; apply Z.leb_le in L; fold n in L; lia.
    - apply Uint63.eqb_false_spec in Q.
      apply (CopyFX.sep_of_pointwise S D n N0). intros j j' Hj Hj' EQ.
      destruct (SRCn j Hj) as (ZS & _). destruct (DSTn j' Hj') as (ZD & _).
      rewrite (XS j Hj) in ZS. rewrite (XD j' Hj') in ZD.
      exact (MemcpyCtr.zones_apart OPS E st ms mo ks kd (S + j) HS Q ZS ltac:(rewrite EQ; exact ZD)). }

  assert (DISJ : forall j j', 0 <= j < n -> 0 <= j' < n -> CopyFX.saddr E src j <> CopyFX.daddr E dst j').
  { intros j j' Hj Hj' EQW. apply (f_equal bv_unsigned) in EQW. rewrite XS, XD in EQW by lia. lia. }
  assert (RDall : forall j, 0 <= j < n -> rb rsegs (ms_mem ms) (S + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (XS j Hj). apply RDn; [exact Hj|]. intros j' Hj'. apply DISJ; lia. }
  assert (SRCB : bytes_at rsegs (ms_mem ms) S bs).
  { apply CopyFX.bytes_at_of_rb; rewrite ?LEN, ?Z2Nat.id; try lia. intros j Hj. apply RDall. lia. }
  destruct (CopyFX.rw_cells_of_views rsegs (ms_mem ms) D (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id; lia)) as (junk & LJ & DSTC).
  { intros j Hj. rewrite Z2Nat.id in Hj by lia. destruct (DSTn j Hj) as (_ & _ & WB & RB). rewrite (XD j Hj) in WB, RB. auto. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR. subst D dst. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S).
  { rewrite <- reg_of_X11, GR. subst S src. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 n).
  { rewrite <- reg_of_X12, GR, HX12. rewrite <- (Z_to_bv_bv_unsigned (den E (VL nw))), unsigned_VL, (w2Z_nowt nw T). reflexivity. }
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S n bs junk K A0 A1 A2
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
  destruct (CopyFXW.copy_words_ind rsegs OPS E' (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              ks kd os od ASRC ADST (Z.to_nat (n / 8)) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(rewrite Z2Nat.id by (apply Z.div_pos; lia); lia) eq_refl
              (CopyFXW.CINVW0 rsegs OPS E' _ _ _ _ _ mo src dst st (ms_mem ms) RV ks kd os od HS0') CB) as (mn' & bs' & CI').
  rewrite Z.add_0_l, Z2Nat.id, <- N8 in CI' by (apply Z.div_pos; lia).
  destruct CI' as [OKn' _ _ LEN' FRn' WRn' RDn' _ _ _ _].
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
      + unfold rb. rewrite (MemcpyCtr.memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
        intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia.
      + rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) at 1 by lia. rewrite BY by lia.
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite LEN; lia).
        unfold rb. replace (Z_to_bv 64 a) with (CopyFX.daddr E' dst (a - D)) by (rewrite DD', DW by lia; f_equal; lia).
        rewrite (WRn' (a - D)) by lia. rewrite BSEQ by lia. reflexivity.
      + unfold rb. rewrite (MemcpyCtr.memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
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
    - rewrite OPSn. apply Forall_forall. intros o Ho.
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS0') o Ho) as OH. cbn [ms_mem MS] in OH.
      apply (St.op_frame OPS _ _ (ms_mem ms) M' mo); [| intros a _ Hm; exact (OM _ Hm)| exact OH].
      intros a Ha FP. symmetry. apply (MemcpyCtr.memcpy_frame _ _ D n MU a Ha). intros IN.
      assert (FP0 : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
      { replace (map (den E) (op_args o)) with (map (den E') (op_args o)); [exact FP|].
        apply map_ext_in. intros u Hu. apply (den_reval (s_next st) E E' EXT). exact (forallb_In _ _ _ u (forallb_In _ _ _ _ P6 Ho) Hu). }
      destruct (DSTn (a - D) ltac:(lia)) as (ZD & _). rewrite (XD (a - D)) in ZD by lia.
      replace (D + (a - D)) with a in ZD by lia. exact (MemcpyCtr.zoneW_not_fp OPS E st ms mo kd a o HS ZD Ho FP0).
    - exact (MemcpyCtr.minv_of_mem_inv M' MI'). }

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x NX0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply MemcpyCtr.kept_or_clobbered; [exact NX0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  pose proof POS as POSn. pose proof B62 as B62n. rewrite <- NXn in POSn, B62n.
  destruct (MemFX.ccall_frame_above rsegs OPS E stn ERRNO r st2 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo
              HSn' RVn POSn B62n HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ EXT HMP ST).
Qed.

End OPS.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsW.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFXW.
Import RMallocG.TwinB MemcpyG.TwinB HeapCtr.TwinB MemcpyCtr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable OPS : St.optable.
Hypothesis OPS_plain : St.plain_table OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem memcpy_w_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrW.memcpy_w_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrW.memcpy_w_c] in Happ. unfold CtrW.memcpy_w_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X12) as [nw| | | | | | | | | |] eqn:HX12; try discriminate.
  destruct (wt nw || negb (Z.leb (to_Z (wl nw)) CtrW.MEMCPYW_MAX) || PrimInt63.eqb (wl nw) 0%uint63
            || negb (PrimInt63.eqb (PrimInt63.land (wl nw) 7%uint63) 0%uint63) || negb (CtrW.ww_separated st (wl nw))) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C SEPB]. apply orb_false_iff in C as [C AL8]. apply orb_false_iff in C as [C NZ]. apply orb_false_iff in C as [T LE].
  apply negb_false_iff in LE. apply Z.leb_le in LE. apply negb_false_iff in SEPB. apply negb_false_iff in AL8. unfold CtrW.MEMCPYW_MAX in LE.
  destruct (CtrW.copy_words rsegs (Z.to_nat (to_Z (wl nw) / 8)) 0%uint63 (getr st X11) (getr st X10) st) as [stn|] eqn:CB; [|discriminate].
  destruct (havoc_errno rsegs ERRNO (clobber stn)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  destruct (MemcpyCtr.TwinB.call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (MemcpyCtr.TwinB.ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrW.memcpy_w_c] in MSE. rewrite Hpc in MSE.
  set (n := to_Z (wl nw)) in *. pose proof (int_range (wl nw)) as Rn. fold n in Rn.
  assert (N0 : 0 < n).
  { destruct (Z.eq_dec n 0) as [Q|Q]; [| lia]. exfalso. apply Uint63.eqb_false_spec in NZ. apply NZ. apply Uint63.to_Z_inj. exact Q. }
  assert (N8 : n = 8 * (n / 8)).
  { apply Uint63.eqb_correct in AL8. pose proof (land_mk (wl nw) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. rewrite AL8 in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 3%uint63) with 8 in LM. fold n in LM. pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
  set (src := getr st X11) in *. set (dst := getr st X10) in *.
  set (S := bv_unsigned (den E src)). set (D := bv_unsigned (den E dst)).
  pose proof (bv_unsigned_in_range 64 (den E src)) as RS. rewrite bv_modulus_64 in RS. fold S in RS.
  pose proof (bv_unsigned_in_range 64 (den E dst)) as RD. rewrite bv_modulus_64 in RD. fold D in RD.

  unfold CtrW.ww_separated in SEPB. fold src dst in SEPB.
  destruct (addr_of dst) as [[kd od]|] eqn:ADST; [|discriminate]. destruct (addr_of src) as [[ks os]|] eqn:ASRC; [|discriminate].
  assert (HS0 : St.st_ok rsegs OPS E st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo)
    by (rewrite <- MSE; exact HS).

  destruct (CopyFXW.copy_words_ind rsegs OPS E (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              ks kd os od ASRC ADST (Z.to_nat (n / 8)) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(rewrite Z2Nat.id by (apply Z.div_pos; lia); lia) eq_refl
              (CopyFXW.CINVW0 rsegs OPS E _ _ _ _ _ mo src dst st (ms_mem ms) RV ks kd os od HS0) CB) as (mn & bs & CI).
  rewrite Z.add_0_l, Z2Nat.id, <- N8 in CI by (apply Z.div_pos; lia).
  destruct CI as [OKn SHn SRn LEN FRn WRn RDn SRCn SRC0 DSTn DST0].
  assert (XS : forall j, 0 <= j < n -> bv_unsigned (CopyFX.saddr E src j) = S + j).
  { apply CopyFX.addr_exact. intros j Hj. exact (proj2 (SRCn j Hj)). }
  assert (XD : forall j, 0 <= j < n -> bv_unsigned (CopyFX.daddr E dst j) = D + j).
  { apply CopyFX.addr_exact. intros j Hj. destruct (DSTn j Hj) as (_ & B & _). exact B. }
  assert (SN : S + n <= two64) by (pose proof (proj2 (SRCn (n - 1) ltac:(lia))) as B; rewrite (XS (n - 1)) in B by lia; lia).
  assert (DN : D + n <= two64) by (destruct (DSTn (n - 1) ltac:(lia)) as (_ & B & _); rewrite (XD (n - 1)) in B by lia; lia).

  assert (SEP : S + n <= D \/ D + n <= S).
  { destruct (Uint63.eqb ks kd) eqn:Q; cbn [negb orb] in SEPB.
    - apply Uint63.eqb_correct in Q. subst ks.
      destruct (SRC0 N0) as (b & OKb & ES0). destruct (DST0 N0) as (a & OKa & ED0). rewrite OKa, OKb in SEPB.
      rewrite (XS 0) in ES0 by lia. rewrite (XD 0) in ED0 by lia. rewrite Z.add_0_r in ES0, ED0.
      apply orb_prop in SEPB. destruct SEPB as [L|L]; apply Z.leb_le in L; fold n in L; lia.
    - apply Uint63.eqb_false_spec in Q.
      apply (CopyFX.sep_of_pointwise S D n N0). intros j j' Hj Hj' EQ.
      destruct (SRCn j Hj) as (ZS & _). destruct (DSTn j' Hj') as (ZD & _).
      rewrite (XS j Hj) in ZS. rewrite (XD j' Hj') in ZD.
      exact (MemcpyCtr.TwinB.zones_apart OPS E st ms mo ks kd (S + j) HS Q ZS ltac:(rewrite EQ; exact ZD)). }

  assert (DISJ : forall j j', 0 <= j < n -> 0 <= j' < n -> CopyFX.saddr E src j <> CopyFX.daddr E dst j').
  { intros j j' Hj Hj' EQW. apply (f_equal bv_unsigned) in EQW. rewrite XS, XD in EQW by lia. lia. }
  assert (RDall : forall j, 0 <= j < n -> rb rsegs (ms_mem ms) (S + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (XS j Hj). apply RDn; [exact Hj|]. intros j' Hj'. apply DISJ; lia. }
  assert (SRCB : bytes_at rsegs (ms_mem ms) S bs).
  { apply CopyFX.bytes_at_of_rb; rewrite ?LEN, ?Z2Nat.id; try lia. intros j Hj. apply RDall. lia. }
  destruct (CopyFX.rw_cells_of_views rsegs (ms_mem ms) D (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id; lia)) as (junk & LJ & DSTC).
  { intros j Hj. rewrite Z2Nat.id in Hj by lia. destruct (DSTn j Hj) as (_ & _ & WB & RB). rewrite (XD j Hj) in WB, RB. auto. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR. subst D dst. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S).
  { rewrite <- reg_of_X11, GR. subst S src. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 n).
  { rewrite <- reg_of_X12, GR, HX12. rewrite <- (Z_to_bv_bv_unsigned (den E (VL nw))), unsigned_VL, (w2Z_nowt nw T). reflexivity. }
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S n bs junk K A0 A1 A2
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
  destruct (CopyFXW.copy_words_ind rsegs OPS E' (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) (seg_rom rsegs) mo src dst st (ms_mem ms)
              ks kd os od ASRC ADST (Z.to_nat (n / 8)) 0 0%uint63 st (ms_mem ms) [] stn ltac:(lia) ltac:(rewrite Z2Nat.id by (apply Z.div_pos; lia); lia) eq_refl
              (CopyFXW.CINVW0 rsegs OPS E' _ _ _ _ _ mo src dst st (ms_mem ms) RV ks kd os od HS0') CB) as (mn' & bs' & CI').
  rewrite Z.add_0_l, Z2Nat.id, <- N8 in CI' by (apply Z.div_pos; lia).
  destruct CI' as [OKn' _ _ LEN' FRn' WRn' RDn' _ _ _ _].
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
      + unfold rb. rewrite (MemcpyCtr.TwinB.memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
        intros j Hj X. apply (f_equal bv_unsigned) in X. rewrite DD', (XD j Hj), Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; exact Ha). lia.
      + rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) at 1 by lia. rewrite BY by lia.
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite LEN; lia).
        unfold rb. replace (Z_to_bv 64 a) with (CopyFX.daddr E' dst (a - D)) by (rewrite DD', DW by lia; f_equal; lia).
        rewrite (WRn' (a - D)) by lia. rewrite BSEQ by lia. reflexivity.
      + unfold rb. rewrite (MemcpyCtr.TwinB.memcpy_frame _ _ D n MU a Ha) by lia. rewrite (FRn' (Z_to_bv 64 a)); [reflexivity|].
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
    - rewrite OPSn. apply Forall_forall. intros o Ho.
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS0') o Ho) as OH. cbn [ms_mem MS] in OH.
      apply (St.op_frame OPS _ _ (ms_mem ms) M' mo); [| intros a _ Hm; exact (OM _ Hm)| exact OH].
      intros a Ha FP. symmetry. apply (MemcpyCtr.TwinB.memcpy_frame _ _ D n MU a Ha). intros IN.
      assert (FP0 : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
      { replace (map (den E) (op_args o)) with (map (den E') (op_args o)); [exact FP|].
        apply map_ext_in. intros u Hu. apply (den_reval (s_next st) E E' EXT). exact (forallb_In _ _ _ u (forallb_In _ _ _ _ P6 Ho) Hu). }
      destruct (DSTn (a - D) ltac:(lia)) as (ZD & _). rewrite (XD (a - D)) in ZD by lia.
      replace (D + (a - D)) with a in ZD by lia. exact (MemcpyCtr.TwinB.zoneW_not_fp OPS E st ms mo kd a o HS ZD Ho FP0).
    - exact (MemcpyCtr.TwinB.minv_of_mem_inv M' MI'). }

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x NX0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply MemcpyCtr.TwinB.kept_or_clobbered; [exact NX0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  pose proof POS as POSn. pose proof B62 as B62n. rewrite <- NXn in POSn, B62n.
  destruct (MemFX.ccall_frame_above rsegs OPS E stn ERRNO r st2 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo
              HSn' RVn POSn B62n HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ EXT HMP ST).
Qed.

End OPS.
End TwinB.
