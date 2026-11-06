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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG MemcpyG CtrFX MemFX CopyFX HeapCtr.
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

Record callP (E : env) (st : sstate) (ms : machine_state) (r : int) : Prop := CALLP {
  cp_resv : s_resv st = RNone;
  cp_svb : st_vars_below (s_next st) st = true;
  cp_pos : 0 < to_Z (s_next st);
  cp_b62 : to_Z (s_next st) + 256 <= 2 ^ 62;
  cp_ra : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv;
  cp_r : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z r);
  cp_regs : forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x);
  cp_minv : Lib.Mem.mem_inv rsegs (ms_mem ms) }.

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

Theorem memcpy_blob_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_blob_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrM.memcpy_blob_c] in Happ. unfold CtrM.memcpy_blob_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|kd od| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (getr st X11) as [w11|ks os| | | | | | | | |] eqn:HX11; try discriminate.
  destruct (negb (weqb od wzero && weqb os wzero) || PrimInt63.eqb kd ks || PrimInt63.eqb kd 0 || PrimInt63.eqb ks 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C Ks0]. apply orb_false_iff in C as [C Kd0]. apply orb_false_iff in C as [OO Kds].
  apply negb_false_iff in OO. apply andb_prop in OO as [Od Os]. apply weqb_eq in Od. apply weqb_eq in Os. subst od os.
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate].
  destruct (Mem.rg_cells rd) eqn:CD; [|discriminate].
  destruct (Mem.rg_cells rs) eqn:CS; [|discriminate].
  destruct (Mem.rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber (setregs st (IMap.add kd (Mem.Region 0%uint63 (getr st X12) true (Mem.BGBlob j 0%uint63) IMap.empty) (s_regs st)))))
    as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LEd]. apply andb_prop in C2 as [C2 LEs]. apply andb_prop in C2 as [C2 Wd].
  apply andb_prop in C2 as [C2 LOd]. apply andb_prop in C2 as [SH LOs].
  apply Uint63.eqb_correct in SH. subst sh. apply Uint63.eqb_correct in LOd. apply Uint63.eqb_correct in LOs.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_reg _ _ _ _ _ _ HS kd rd Hkd) as ROd. pose proof (so_reg _ _ _ _ _ _ HS ks rs Hks) as ROs.
  set (D := bv_unsigned (ev E kd)) in *. set (S := bv_unsigned (ev E ks)) in *. set (nZ := bv_unsigned (den E (getr st X12))).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  apply (known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEd. apply (known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEs.
  fold nZ (hiZ E rd) in LEd. fold nZ (hiZ E rs) in LEs.
  assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity). assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd]. pose proof (ro_range _ _ _ _ _ _ ROs Ks0) as [RLs RHs].
  fold D in RLd, RHd. fold S in RLs, RHs. rewrite LZd in RLd. rewrite LZs in RLs. unfold W64.two64 in RHd, RHs.

  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) ks rs j 0 (Z.to_nat nZ) ROs Ks0 CS BS ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
  fold S in SRC. rewrite Z.add_0_r in SRC.
  set (src := map (fun i => nth (Z.to_nat 0 + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))) in SRC.
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kd rd 0 (Z.to_nat nZ) ROd Kd0 Wd ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { apply (based_sep D S (hiZ E rd) (hiZ E rs) nZ); [| lia| lia| lia]. intros a.
    pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs Hkd Hks ltac:(apply Uint63.eqb_false_spec; exact Kds) Kd0 Ks0 (or_introl Wd) a) as X.
    fold D S in X. rewrite LZd, LZs in X. rewrite !Z.add_0_r in X. exact X. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S).
  { rewrite <- reg_of_X11, GR, HX11, den_VPz. subst S. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrM.memcpy_blob_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  set (rd' := Mem.Region 0%uint63 (getr st X12) true (Mem.BGBlob j 0%uint63) IMap.empty).
  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) kd rd a ROd Kd0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kd rd').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EH : hiZ E rd' = nZ) by reflexivity. assert (EL : loZ rd' = 0) by reflexivity.
    constructor; rewrite ?EH, ?EL; fold D.
    - cbn. exact I.
    - intros _. unfold W64.two64. lia.
    - intros _ a Ha. split; [| split].
      + rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
        destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
      + intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + apply NS. lia.
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c i Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kd0). unfold bg_byte. cbn [rd' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      rewrite MemFX.rb_mrd. replace (D + o) with (D + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
      subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [|lia]. cbn [option_map]. reflexivity. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kd rd rd'
                ltac:(rewrite <- MSE; exact HS) Hkd Kd0 Wd
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZd in NI; lia)
                OM
                (minv_of_mem_inv M' MI') RO' ltac:(rewrite LZd; reflexivity || (cbn; lia)) ltac:(change (hiZ E rd') with nZ; lia)) as HS1.

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  assert (SVB1 : st_vars_below (s_next st) (setregs st (IMap.add kd rd' (s_regs st))) = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kd rd rd' (so_bst _ _ _ _ _ _ HS) SVB Hkd).
    unfold region_vars_below. cbn [rd' Mem.rg_hi Mem.rg_cells]. rewrite andb_true_r.
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _). exact (rf_allb_get _ _ _ P1 X12). }
  destruct (MemFX.ccall_frame rsegs OPS E (setregs st (IMap.add kd rd' (s_regs st))) ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
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

Theorem memcpy_rr_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_rr_c rsegs ERRNO pc).
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
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
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

Theorem memcpy_payload_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_payload_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrM.memcpy_payload_c] in Happ. unfold CtrM.memcpy_payload_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|kp op| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (negb (weqb op wzero) || PrimInt63.eqb kp 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [OO Kp0]. apply negb_false_iff in OO. apply weqb_eq in OO. subst op.
  destruct (CtrM.dst_offset (s_regs st) (getr st X11)) as [[kb OFF]|] eqn:DOFF; [|discriminate].
  destruct (IMap.find kp (s_regs st)) as [rp|] eqn:Hkp; [|discriminate].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:Hkb; [|discriminate].
  destruct (Mem.rg_cells rp) eqn:CPc; [|discriminate].
  destruct (Mem.rg_cells rb) eqn:CBc; [|discriminate].
  destruct (Mem.rg_bg rb) as [| | | |j sh] eqn:BB; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber (setregs st (IMap.add kp (Mem.Region 0%uint63 (getr st X12) false (Mem.BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st)))))
    as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 F13]. apply andb_prop in C2 as [C2 F14]. apply andb_prop in C2 as [C2 Kb0]. apply andb_prop in C2 as [C2 Kbp].
  apply andb_prop in C2 as [C2 Wp]. apply andb_prop in C2 as [C2 LOp]. apply andb_prop in C2 as [C2 LOb]. apply andb_prop in C2 as [J4 SH].
  apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH. subst j sh. apply Uint63.eqb_correct in LOp. apply Uint63.eqb_correct in LOb.
  apply negb_true_iff in Kb0. apply negb_true_iff in Kbp.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS kp rp Hkp) as ROp. pose proof (so_reg _ _ _ _ _ _ HS kb rb Hkb) as ROb.
  set (D := bv_unsigned (ev E kp)) in *. set (Bb := bv_unsigned (ev E kb)) in *.
  set (nZ := bv_unsigned (den E (getr st X12))). set (offZ := bv_unsigned (den E OFF)).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  apply (known_leu_sound E _ _ _ Hfs) in LE1. apply (known_leu_sound E _ _ _ Hfs) in LE2. apply (known_leu_sound E _ _ _ Hfs) in LE3.
  fold nZ (hiZ E rp) in LE1. fold offZ (hiZ E rb) in LE2. fold nZ in LE3.
  rewrite den_sv_alu in LE3. cbn [alu64 alu] in LE3. rewrite bv_sub_unsigned in LE3. fold offZ (hiZ E rb) in LE3.
  pose proof (ro_range _ _ _ _ _ _ ROp Kp0) as [RLp RHp]. pose proof (ro_range _ _ _ _ _ _ ROb Kb0) as [RLb RHb].
  fold D in RLp, RHp. fold Bb in RLb, RHb. unfold W64.two64 in RHp, RHb.
  assert (LZp : loZ rp = 0) by (unfold loZ; rewrite LOp; reflexivity). assert (LZb : loZ rb = 0) by (unfold loZ; rewrite LOb; reflexivity).
  rewrite LZp in RLp. rewrite LZb in RLb.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rb))) as HBR. rewrite bv_modulus_64 in HBR. fold (hiZ E rb) in HBR.
  assert (SUM : offZ + nZ <= hiZ E rb).
  { unfold bv_wrap in LE3. rewrite bv_modulus_64 in LE3. rewrite Z.mod_small in LE3; unfold W64.two64 in *; lia. }

  pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs OFF CtrM.B14) F14) as E14. pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs (getr st X12) CtrM.B13) F13) as E13.

  set (S := Bb + offZ).
  assert (SA : den E (getr st X11) = Z_to_bv 64 S).
  { rewrite (dst_offset_sound E (s_regs st) _ kb OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bb offZ. reflexivity. }
  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) kb rb 4%uint63 offZ (Z.to_nat nZ) ROb Kb0 CBc BB ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
  fold Bb in SRC. fold S in SRC.
  set (src := map (fun i => nth (Z.to_nat offZ + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))) in SRC.
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kp rp 0 (Z.to_nat nZ) ROp Kp0 Wp ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { destruct (Z.eq_dec nZ 0) as [->|N0]; [lia|].
    apply (CopyFX.sep_of_pointwise S D nZ ltac:(lia)). intros j j' Hj Hj' EQ.
    apply (so_disj _ _ _ _ _ _ HS kb rb kp rp Hkb Hkp ltac:(apply Uint63.eqb_false_spec; exact Kbp) Kb0 Kp0 (or_intror Wp) (S + j)).
    fold D Bb. rewrite LZb, LZp. split; [subst S; lia| lia]. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; exact SA).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrM.memcpy_payload_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  set (rp' := Mem.Region 0%uint63 (getr st X12) false (Mem.BGBlob 5%uint63 0%uint63) IMap.empty).
  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) kp rp a ROp Kp0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kp rp').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EH : hiZ E rp' = nZ) by reflexivity. assert (EL : loZ rp' = 0) by reflexivity.
    constructor; rewrite ?EH, ?EL; fold D.
    - cbn. exact I.
    - intros _. unfold W64.two64. lia.
    - intros _ a Ha. split; [| split; [intros X; discriminate X| apply NS; lia]].
      rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
      destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c i Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kp0). unfold bg_byte. cbn [rp' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      rewrite MemFX.rb_mrd. replace (D + o) with (D + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
      subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [|lia]. cbn [option_map].
      f_equal. rewrite <- (PB5 E HPB o); [| rewrite E13 || rewrite <- E13; fold nZ; lia].
      f_equal. rewrite <- E14 || rewrite E14. fold offZ. lia. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kp rp rp'
                ltac:(rewrite <- MSE; exact HS) Hkp Kp0 Wp
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZp in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(rewrite LZp; reflexivity || (cbn; lia)) ltac:(change (hiZ E rp') with nZ; lia)) as HS1.
  assert (SVB1 : st_vars_below (s_next st) (setregs st (IMap.add kp rp' (s_regs st))) = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kp rp rp' (so_bst _ _ _ _ _ _ HS) SVB Hkp).
    unfold region_vars_below. cbn [rp' Mem.rg_hi Mem.rg_cells]. rewrite andb_true_r.
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _). exact (rf_allb_get _ _ _ P1 X12). }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E (setregs st (IMap.add kp rp' (s_regs st))) ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
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

Theorem memcpy_sink_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrA.memcpy_sink_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrA.memcpy_sink_c] in Happ. unfold CtrA.memcpy_sink_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|ka oa| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (negb (weqb oa wzero) || PrimInt63.eqb ka 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [OO Ka0]. apply negb_false_iff in OO. apply weqb_eq in OO. subst oa.
  destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFF]|] eqn:DOFF; [|discriminate].
  destruct (IMap.find ka (s_regs st)) as [ra|] eqn:Hka; [|discriminate].
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
  destruct (Mem.rg_cells ra) eqn:CA; [|discriminate].
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber st)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 Kd0]. apply andb_prop in C2 as [C2 Kda]. apply andb_prop in C2 as [C2 LOd].
  apply andb_prop in C2 as [C2 Wa]. apply andb_prop in C2 as [BGN LOa].
  apply Uint63.eqb_correct in LOa. apply Uint63.eqb_correct in LOd. apply negb_true_iff in Kd0. apply negb_true_iff in Kda.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS ka ra Hka) as ROa. pose proof (so_reg _ _ _ _ _ _ HS kd rd Hkd) as ROd.
  set (D := bv_unsigned (ev E ka)) in *. set (Bd := bv_unsigned (ev E kd)) in *.
  set (nZ := bv_unsigned (den E (getr st X12))). set (offZ := bv_unsigned (den E OFF)).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  apply (known_leu_sound E _ _ _ Hfs) in LE1. apply (known_leu_sound E _ _ _ Hfs) in LE2. apply (known_leu_sound E _ _ _ Hfs) in LE3.
  fold nZ (hiZ E ra) in LE1. fold offZ (hiZ E rd) in LE2. fold nZ in LE3.
  rewrite den_sv_alu in LE3. cbn [alu64 alu] in LE3. rewrite bv_sub_unsigned in LE3. fold offZ (hiZ E rd) in LE3.
  pose proof (ro_range _ _ _ _ _ _ ROa Ka0) as [RLa RHa]. pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd].
  fold D in RLa, RHa. fold Bd in RLd, RHd. unfold W64.two64 in RHa, RHd.
  assert (LZa : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity). assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity).
  rewrite LZa in RLa. rewrite LZd in RLd.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rd))) as HDR. rewrite bv_modulus_64 in HDR. fold (hiZ E rd) in HDR.
  assert (SUM : offZ + nZ <= hiZ E rd).
  { unfold bv_wrap in LE3. rewrite bv_modulus_64 in LE3. rewrite Z.mod_small in LE3; unfold W64.two64 in *; lia. }
  set (S := Bd + offZ).
  assert (SA : den E (getr st X11) = Z_to_bv 64 S).
  { rewrite (sym_offset_sound E (s_regs st) _ kd OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bd offZ. reflexivity. }
  destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) kd rd offZ (Z.to_nat nZ) ROd Kd0 ltac:(lia) ltac:(lia)) as (src & LEN & SRC).
  fold Bd in SRC. fold S in SRC.
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) ka ra 0 (Z.to_nat nZ) ROa Ka0 Wa ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { destruct (Z.eq_dec nZ 0) as [->|N0]; [lia|].
    apply (CopyFX.sep_of_pointwise S D nZ ltac:(lia)). intros j j' Hj Hj' EQ.
    apply (so_disj _ _ _ _ _ _ HS kd rd ka ra Hkd Hka ltac:(apply Uint63.eqb_false_spec; exact Kda) Kd0 Ka0 (or_intror Wa) (S + j)).
    fold D Bd. rewrite LZd, LZa. split; [subst S; lia| lia]. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; exact SA).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrA.memcpy_sink_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) ka ra a ROa Ka0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' ka ra).
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    destruct ROa as [Abst Arange Avalid Acells Ain Abg].
    constructor; try assumption.
    - intros K0 a Ha. destruct (Avalid K0 a Ha) as (V1 & V2 & V3). fold D in Ha. rewrite LZa in Ha.
      destruct (Z_lt_le_dec a (D + nZ)) as [L|G].
      + split; [| split; [| exact V3]].
        * rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
          destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
        * intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + pose proof (bv_unsigned_in_range 64 (ev E ka)) as RK. rewrite bv_modulus_64 in RK. fold D in RK.
        assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D nZ MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]].
        * unfold rb in V1 |- *. rewrite EQM. exact V1.
        * intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W).
    - intros g gr Hg. rewrite CA in Hg. cbn in Hg. discriminate Hg.
    - intros o H1 H2 U. unfold bg_byte. destruct (Mem.rg_bg ra); try discriminate BGN. exact I. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo ka ra ra
                ltac:(rewrite <- MSE; exact HS) Hka Ka0 Wa
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZa in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(lia) ltac:(lia)) as HS1.

  assert (SAME : St.st_ok rsegs OPS E st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { pose proof HS1 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
    cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
    assert (FEQ : forall k, IMap.find k (IMap.add ka ra (s_regs st)) = IMap.find k (s_regs st)).
    { intros k. destruct (Uint63.eqb ka k) eqn:Q.
      - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same by exact (so_bst _ _ _ _ _ _ HS). symmetry. exact Hka.
      - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other by (exact (so_bst _ _ _ _ _ _ HS) || exact Q). reflexivity. }
    destruct st as [pc0 rf0 ff0 rv0 R0 fs0 os0 pv0 nx0]; cbn in *.
    constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
    - exact (so_bst _ _ _ _ _ _ HS).
    - intros k rg Hk. apply Preg. rewrite FEQ. exact Hk.
    - intros k1 q1 k2 q2 H1 H2. apply Pdisj; rewrite FEQ; assumption.
    - intros rr g gr c Hr. apply Ppub. rewrite FEQ. exact Hr.
    - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
      intros (k & rg & Hk & K' & RG). apply NB. exists k, rg. rewrite FEQ. auto.
    -
      intros a FA. apply Pcov. revert a FA. apply St.fx_acc_based. intros a (k & rg & Hk & K' & RG). exists k, rg. rewrite FEQ. auto. }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo SAME RV SVB POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFX.
Import RMallocG.TwinB MemcpyG.TwinB HeapCtr.TwinB.

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

Record callP (E : env) (st : sstate) (ms : machine_state) (r : int) : Prop := CALLP {
  cp_resv : s_resv st = RNone;
  cp_svb : st_vars_below (s_next st) st = true;
  cp_pos : 0 < to_Z (s_next st);
  cp_b62 : to_Z (s_next st) + 256 <= 2 ^ 62;
  cp_ra : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv;
  cp_r : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z r);
  cp_regs : forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x);
  cp_minv : Lib.Mem.mem_inv rsegs (ms_mem ms) }.

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

Theorem memcpy_blob_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_blob_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrM.memcpy_blob_c] in Happ. unfold CtrM.memcpy_blob_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|kd od| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (getr st X11) as [w11|ks os| | | | | | | | |] eqn:HX11; try discriminate.
  destruct (negb (weqb od wzero && weqb os wzero) || PrimInt63.eqb kd ks || PrimInt63.eqb kd 0 || PrimInt63.eqb ks 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C Ks0]. apply orb_false_iff in C as [C Kd0]. apply orb_false_iff in C as [OO Kds].
  apply negb_false_iff in OO. apply andb_prop in OO as [Od Os]. apply weqb_eq in Od. apply weqb_eq in Os. subst od os.
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate].
  destruct (Mem.rg_cells rd) eqn:CD; [|discriminate].
  destruct (Mem.rg_cells rs) eqn:CS; [|discriminate].
  destruct (Mem.rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber (setregs st (IMap.add kd (Mem.Region 0%uint63 (getr st X12) true (Mem.BGBlob j 0%uint63) IMap.empty) (s_regs st)))))
    as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LEd]. apply andb_prop in C2 as [C2 LEs]. apply andb_prop in C2 as [C2 Wd].
  apply andb_prop in C2 as [C2 LOd]. apply andb_prop in C2 as [SH LOs].
  apply Uint63.eqb_correct in SH. subst sh. apply Uint63.eqb_correct in LOd. apply Uint63.eqb_correct in LOs.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_reg _ _ _ _ _ _ HS kd rd Hkd) as ROd. pose proof (so_reg _ _ _ _ _ _ HS ks rs Hks) as ROs.
  set (D := bv_unsigned (ev E kd)) in *. set (S := bv_unsigned (ev E ks)) in *. set (nZ := bv_unsigned (den E (getr st X12))).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  apply (known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEd. apply (known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEs.
  fold nZ (hiZ E rd) in LEd. fold nZ (hiZ E rs) in LEs.
  assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity). assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd]. pose proof (ro_range _ _ _ _ _ _ ROs Ks0) as [RLs RHs].
  fold D in RLd, RHd. fold S in RLs, RHs. rewrite LZd in RLd. rewrite LZs in RLs. unfold W64.two64 in RHd, RHs.

  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) ks rs j 0 (Z.to_nat nZ) ROs Ks0 CS BS ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
  fold S in SRC. rewrite Z.add_0_r in SRC.
  set (src := map (fun i => nth (Z.to_nat 0 + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))) in SRC.
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kd rd 0 (Z.to_nat nZ) ROd Kd0 Wd ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { apply (based_sep D S (hiZ E rd) (hiZ E rs) nZ); [| lia| lia| lia]. intros a.
    pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs Hkd Hks ltac:(apply Uint63.eqb_false_spec; exact Kds) Kd0 Ks0 (or_introl Wd) a) as X.
    fold D S in X. rewrite LZd, LZs in X. rewrite !Z.add_0_r in X. exact X. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S).
  { rewrite <- reg_of_X11, GR, HX11, den_VPz. subst S. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrM.memcpy_blob_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  set (rd' := Mem.Region 0%uint63 (getr st X12) true (Mem.BGBlob j 0%uint63) IMap.empty).
  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) kd rd a ROd Kd0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kd rd').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EH : hiZ E rd' = nZ) by reflexivity. assert (EL : loZ rd' = 0) by reflexivity.
    constructor; rewrite ?EH, ?EL; fold D.
    - cbn. exact I.
    - intros _. unfold W64.two64. lia.
    - intros _ a Ha. split; [| split].
      + rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
        destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
      + intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + apply NS. lia.
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c i Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kd0). unfold bg_byte. cbn [rd' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      rewrite MemFX.rb_mrd. replace (D + o) with (D + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
      subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [|lia]. cbn [option_map]. reflexivity. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kd rd rd'
                ltac:(rewrite <- MSE; exact HS) Hkd Kd0 Wd
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZd in NI; lia)
                OM
                (minv_of_mem_inv M' MI') RO' ltac:(rewrite LZd; reflexivity || (cbn; lia)) ltac:(change (hiZ E rd') with nZ; lia)) as HS1.

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  assert (SVB1 : st_vars_below (s_next st) (setregs st (IMap.add kd rd' (s_regs st))) = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kd rd rd' (so_bst _ _ _ _ _ _ HS) SVB Hkd).
    unfold region_vars_below. cbn [rd' Mem.rg_hi Mem.rg_cells]. rewrite andb_true_r.
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _). exact (rf_allb_get _ _ _ P1 X12). }
  destruct (MemFX.ccall_frame rsegs OPS E (setregs st (IMap.add kd rd' (s_regs st))) ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
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

Theorem memcpy_rr_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_rr_c rsegs ERRNO pc).
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
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
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

Theorem memcpy_payload_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrM.memcpy_payload_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrM.memcpy_payload_c] in Happ. unfold CtrM.memcpy_payload_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|kp op| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (negb (weqb op wzero) || PrimInt63.eqb kp 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [OO Kp0]. apply negb_false_iff in OO. apply weqb_eq in OO. subst op.
  destruct (CtrM.dst_offset (s_regs st) (getr st X11)) as [[kb OFF]|] eqn:DOFF; [|discriminate].
  destruct (IMap.find kp (s_regs st)) as [rp|] eqn:Hkp; [|discriminate].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:Hkb; [|discriminate].
  destruct (Mem.rg_cells rp) eqn:CPc; [|discriminate].
  destruct (Mem.rg_cells rb) eqn:CBc; [|discriminate].
  destruct (Mem.rg_bg rb) as [| | | |j sh] eqn:BB; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber (setregs st (IMap.add kp (Mem.Region 0%uint63 (getr st X12) false (Mem.BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st)))))
    as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 F13]. apply andb_prop in C2 as [C2 F14]. apply andb_prop in C2 as [C2 Kb0]. apply andb_prop in C2 as [C2 Kbp].
  apply andb_prop in C2 as [C2 Wp]. apply andb_prop in C2 as [C2 LOp]. apply andb_prop in C2 as [C2 LOb]. apply andb_prop in C2 as [J4 SH].
  apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH. subst j sh. apply Uint63.eqb_correct in LOp. apply Uint63.eqb_correct in LOb.
  apply negb_true_iff in Kb0. apply negb_true_iff in Kbp.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS kp rp Hkp) as ROp. pose proof (so_reg _ _ _ _ _ _ HS kb rb Hkb) as ROb.
  set (D := bv_unsigned (ev E kp)) in *. set (Bb := bv_unsigned (ev E kb)) in *.
  set (nZ := bv_unsigned (den E (getr st X12))). set (offZ := bv_unsigned (den E OFF)).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  apply (known_leu_sound E _ _ _ Hfs) in LE1. apply (known_leu_sound E _ _ _ Hfs) in LE2. apply (known_leu_sound E _ _ _ Hfs) in LE3.
  fold nZ (hiZ E rp) in LE1. fold offZ (hiZ E rb) in LE2. fold nZ in LE3.
  rewrite den_sv_alu in LE3. cbn [alu64 alu] in LE3. rewrite bv_sub_unsigned in LE3. fold offZ (hiZ E rb) in LE3.
  pose proof (ro_range _ _ _ _ _ _ ROp Kp0) as [RLp RHp]. pose proof (ro_range _ _ _ _ _ _ ROb Kb0) as [RLb RHb].
  fold D in RLp, RHp. fold Bb in RLb, RHb. unfold W64.two64 in RHp, RHb.
  assert (LZp : loZ rp = 0) by (unfold loZ; rewrite LOp; reflexivity). assert (LZb : loZ rb = 0) by (unfold loZ; rewrite LOb; reflexivity).
  rewrite LZp in RLp. rewrite LZb in RLb.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rb))) as HBR. rewrite bv_modulus_64 in HBR. fold (hiZ E rb) in HBR.
  assert (SUM : offZ + nZ <= hiZ E rb).
  { unfold bv_wrap in LE3. rewrite bv_modulus_64 in LE3. rewrite Z.mod_small in LE3; unfold W64.two64 in *; lia. }

  pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs OFF CtrM.B14) F14) as E14. pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs (getr st X12) CtrM.B13) F13) as E13.

  set (S := Bb + offZ).
  assert (SA : den E (getr st X11) = Z_to_bv 64 S).
  { rewrite (dst_offset_sound E (s_regs st) _ kb OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bb offZ. reflexivity. }
  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) kb rb 4%uint63 offZ (Z.to_nat nZ) ROb Kb0 CBc BB ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
  fold Bb in SRC. fold S in SRC.
  set (src := map (fun i => nth (Z.to_nat offZ + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))) in SRC.
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kp rp 0 (Z.to_nat nZ) ROp Kp0 Wp ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { destruct (Z.eq_dec nZ 0) as [->|N0]; [lia|].
    apply (CopyFX.sep_of_pointwise S D nZ ltac:(lia)). intros j j' Hj Hj' EQ.
    apply (so_disj _ _ _ _ _ _ HS kb rb kp rp Hkb Hkp ltac:(apply Uint63.eqb_false_spec; exact Kbp) Kb0 Kp0 (or_intror Wp) (S + j)).
    fold D Bb. rewrite LZb, LZp. split; [subst S; lia| lia]. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; exact SA).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrM.memcpy_payload_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  set (rp' := Mem.Region 0%uint63 (getr st X12) false (Mem.BGBlob 5%uint63 0%uint63) IMap.empty).
  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) kp rp a ROp Kp0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kp rp').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EH : hiZ E rp' = nZ) by reflexivity. assert (EL : loZ rp' = 0) by reflexivity.
    constructor; rewrite ?EH, ?EL; fold D.
    - cbn. exact I.
    - intros _. unfold W64.two64. lia.
    - intros _ a Ha. split; [| split; [intros X; discriminate X| apply NS; lia]].
      rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
      destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c i Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kp0). unfold bg_byte. cbn [rp' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      rewrite MemFX.rb_mrd. replace (D + o) with (D + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
      subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [|lia]. cbn [option_map].
      f_equal. rewrite <- (PB5 E HPB o); [| rewrite E13 || rewrite <- E13; fold nZ; lia].
      f_equal. rewrite <- E14 || rewrite E14. fold offZ. lia. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kp rp rp'
                ltac:(rewrite <- MSE; exact HS) Hkp Kp0 Wp
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZp in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(rewrite LZp; reflexivity || (cbn; lia)) ltac:(change (hiZ E rp') with nZ; lia)) as HS1.
  assert (SVB1 : st_vars_below (s_next st) (setregs st (IMap.add kp rp' (s_regs st))) = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kp rp rp' (so_bst _ _ _ _ _ _ HS) SVB Hkp).
    unfold region_vars_below. cbn [rp' Mem.rg_hi Mem.rg_cells]. rewrite andb_true_r.
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _). exact (rf_allb_get _ _ _ P1 X12). }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E (setregs st (IMap.add kp rp' (s_regs st))) ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
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

Theorem memcpy_sink_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrA.memcpy_sink_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrA.memcpy_sink_c] in Happ. unfold CtrA.memcpy_sink_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|ka oa| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (negb (weqb oa wzero) || PrimInt63.eqb ka 0) eqn:C; [discriminate|].
  apply orb_false_iff in C as [OO Ka0]. apply negb_false_iff in OO. apply weqb_eq in OO. subst oa.
  destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFF]|] eqn:DOFF; [|discriminate].
  destruct (IMap.find ka (s_regs st)) as [ra|] eqn:Hka; [|discriminate].
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
  destruct (Mem.rg_cells ra) eqn:CA; [|discriminate].
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  destruct (havoc_errno rsegs ERRNO (clobber st)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 Kd0]. apply andb_prop in C2 as [C2 Kda]. apply andb_prop in C2 as [C2 LOd].
  apply andb_prop in C2 as [C2 Wa]. apply andb_prop in C2 as [BGN LOa].
  apply Uint63.eqb_correct in LOa. apply Uint63.eqb_correct in LOd. apply negb_true_iff in Kd0. apply negb_true_iff in Kda.

  destruct (call_sound E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS ka ra Hka) as ROa. pose proof (so_reg _ _ _ _ _ _ HS kd rd Hkd) as ROd.
  set (D := bv_unsigned (ev E ka)) in *. set (Bd := bv_unsigned (ev E kd)) in *.
  set (nZ := bv_unsigned (den E (getr st X12))). set (offZ := bv_unsigned (den E OFF)).
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  apply (known_leu_sound E _ _ _ Hfs) in LE1. apply (known_leu_sound E _ _ _ Hfs) in LE2. apply (known_leu_sound E _ _ _ Hfs) in LE3.
  fold nZ (hiZ E ra) in LE1. fold offZ (hiZ E rd) in LE2. fold nZ in LE3.
  rewrite den_sv_alu in LE3. cbn [alu64 alu] in LE3. rewrite bv_sub_unsigned in LE3. fold offZ (hiZ E rd) in LE3.
  pose proof (ro_range _ _ _ _ _ _ ROa Ka0) as [RLa RHa]. pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd].
  fold D in RLa, RHa. fold Bd in RLd, RHd. unfold W64.two64 in RHa, RHd.
  assert (LZa : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity). assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity).
  rewrite LZa in RLa. rewrite LZd in RLd.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rd))) as HDR. rewrite bv_modulus_64 in HDR. fold (hiZ E rd) in HDR.
  assert (SUM : offZ + nZ <= hiZ E rd).
  { unfold bv_wrap in LE3. rewrite bv_modulus_64 in LE3. rewrite Z.mod_small in LE3; unfold W64.two64 in *; lia. }
  set (S := Bd + offZ).
  assert (SA : den E (getr st X11) = Z_to_bv 64 S).
  { rewrite (sym_offset_sound E (s_regs st) _ kd OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bd offZ. reflexivity. }
  destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) kd rd offZ (Z.to_nat nZ) ROd Kd0 ltac:(lia) ltac:(lia)) as (src & LEN & SRC).
  fold Bd in SRC. fold S in SRC.
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) ka ra 0 (Z.to_nat nZ) ROa Ka0 Wa ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold D in DST. rewrite Z.add_0_r in DST.
  assert (SEP : S + nZ <= D \/ D + nZ <= S).
  { destruct (Z.eq_dec nZ 0) as [->|N0]; [lia|].
    apply (CopyFX.sep_of_pointwise S D nZ ltac:(lia)). intros j j' Hj Hj' EQ.
    apply (so_disj _ _ _ _ _ _ HS kd rd ka ra Hkd Hka ltac:(apply Uint63.eqb_false_spec; exact Kda) Kd0 Ka0 (or_intror Wa) (S + j)).
    fold D Bd. rewrite LZd, LZa. split; [subst S; lia| lia]. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst D. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; exact SA).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrA.memcpy_sink_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (NS : forall a, D <= a < D + nZ -> find_segment rsegs a 1 = None).
  { intros a Ha. apply (MemFX.based_no_segment rsegs (s_priv st) E (ms_mem ms) ka ra a ROa Ka0). fold D. lia. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' ka ra).
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    destruct ROa as [Abst Arange Avalid Acells Ain Abg].
    constructor; try assumption.
    - intros K0 a Ha. destruct (Avalid K0 a Ha) as (V1 & V2 & V3). fold D in Ha. rewrite LZa in Ha.
      destruct (Z_lt_le_dec a (D + nZ)) as [L|G].
      + split; [| split; [| exact V3]].
        * rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
          destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
        * intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + pose proof (bv_unsigned_in_range 64 (ev E ka)) as RK. rewrite bv_modulus_64 in RK. fold D in RK.
        assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D nZ MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]].
        * unfold rb in V1 |- *. rewrite EQM. exact V1.
        * intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W).
    - intros g gr Hg. rewrite CA in Hg. cbn in Hg. discriminate Hg.
    - intros o H1 H2 U. unfold bg_byte. destruct (Mem.rg_bg ra); try discriminate BGN. exact I. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo ka ra ra
                ltac:(rewrite <- MSE; exact HS) Hka Ka0 Wa
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D nZ MU a Ha); fold D in NI; rewrite LZa in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(lia) ltac:(lia)) as HS1.

  assert (SAME : St.st_ok rsegs OPS E st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { pose proof HS1 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
    cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
    assert (FEQ : forall k, IMap.find k (IMap.add ka ra (s_regs st)) = IMap.find k (s_regs st)).
    { intros k. destruct (Uint63.eqb ka k) eqn:Q.
      - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same by exact (so_bst _ _ _ _ _ _ HS). symmetry. exact Hka.
      - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other by (exact (so_bst _ _ _ _ _ _ HS) || exact Q). reflexivity. }
    destruct st as [pc0 rf0 ff0 rv0 R0 fs0 os0 pv0 nx0]; cbn in *.
    constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
    - exact (so_bst _ _ _ _ _ _ HS).
    - intros k rg Hk. apply Preg. rewrite FEQ. exact Hk.
    - intros k1 q1 k2 q2 H1 H2. apply Pdisj; rewrite FEQ; assumption.
    - intros rr g gr c Hr. apply Ppub. rewrite FEQ. exact Hr.
    - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
      intros (k & rg & Hk & K' & RG). apply NB. exists k, rg. rewrite FEQ. auto.
    -
      intros a FA. apply Pcov. revert a FA. apply St.fx_acc_based. intros a (k & rg & Hk & K' & RG). exists k, rg. rewrite FEQ. auto. }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo SAME RV SVB POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
Qed.

End OPS.
End TwinB.
