(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout OpsBridge GLib PkStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc StepAcc AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkStepA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module LdPartSoundA.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma load_at_spec : forall pc sz sx rd rs off, LdPart.load_at segs pc = Some (sz, sx, rd, rs, off) ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\
              of_instr i = Some (ILoad sz sx rd rs off).
Proof.
  intros pc sz sx rd rs off H. unfold LdPart.load_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z.
  destruct (of_instr i) as [fi|] eqn:OI; [|discriminate]. destruct fi; try discriminate. injection H as <- <- <- <- <-.
  exists w, i. auto.
Qed.

Lemma rdZ_total : forall (bm : bmem) n a, (forall i, 0 <= i < Z.of_nat n -> bm (a + i) <> None) -> exists z, rdZ bm a n = Some z.
Proof.
  intros bm n. induction n as [|n IH]; intros a H.
  - exists 0. reflexivity.
  - cbn [rdZ]. destruct (bm a) as [b|] eqn:B.
    2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact B. }
    destruct (IH (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia)) as [z ->].
    eexists. reflexivity.
Qed.

Lemma st_ok_recast : forall E st ms mo kd rd rd' fs' nx,
  st_ok segs OPS E st ms mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false ->
  rg_lo rd' = rg_lo rd -> rg_hi rd' = rg_hi rd -> rg_w rd' = rg_w rd ->
  region_ok segs (s_priv st) E (ms_mem ms) kd rd' ->
  Forall (fact_holds E) fs' ->
  st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo kd rd rd' fs' nx HS Hkd K ELO EHI EW RO' HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }
  assert (RNG : forall E0, loZ rd' = loZ rd /\ hiZ E0 rd' = hiZ E0 rd) by (intros; unfold loZ, hiZ; rewrite ELO, EHI; auto).
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'| exact (Preg k r Hk)].
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in X1. rewrite EW in WW. exact (Pdisj kd rd k2 q2 Hkd G2 NE K1 K2 WW a (conj X1 X2)).
    + destruct (RNG E) as [L2 H2']. rewrite L2, H2' in X2. rewrite EW in WW. exact (Pdisj k1 q1 kd rd G1 Hkd NE K1 K2 WW a (conj X1 X2)).
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - intros r g gr c H0 Hg Hc i Hi. destruct (FIND _ _ H0) as [[E0 _]|[_ H0']]; [rewrite <- E0 in K; rewrite Uint63.eqb_refl in K; discriminate K|].
    exact (Ppub r g gr c H0' Hg Hc i Hi).
  - apply Forall_app. split; [exact HF| exact Pfacts].
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in RG. apply NB. exists kd, rd. auto.
    + apply NB. exists k, r. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k & r & H & K' & RG).
    destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in RG. exists kd, rd. auto.
    + exists k, r. auto.
Qed.

Lemma ext_slice_eq : forall (z : Z) (idx w : Z) (dv : word) (W : word),
  0 <= idx -> 1 <= w -> idx + w <= 8 -> bv_unsigned W = z ->
  (forall t, 0 <= t < w -> byte_of W (idx + t) = byte_of dv t) ->
  ext_Z false idx w z = ext_Z false 0 w (bv_unsigned dv).
Proof.
  intros z idx w dv W Hi Hw H8 HW BY.
  pose proof (ext_Z_false_range idx w z ltac:(lia)) as R1. pose proof (ext_Z_false_range 0 w (bv_unsigned dv) ltac:(lia)) as R2.
  pose proof (bv_unsigned_in_range _ W) as RW. pose proof (bv_unsigned_in_range _ dv) as RD.
  rewrite <- (Z.mod_small (ext_Z false idx w z) (2 ^ (8 * w))) by lia.
  rewrite <- (Z.mod_small (ext_Z false 0 w (bv_unsigned dv)) (2 ^ (8 * w))) by lia.
  apply zbytes_eq; [lia|]. intros t Ht.
  rewrite (zbyte_ext_Z false idx w z t) by lia. rewrite (zbyte_ext_Z false 0 w (bv_unsigned dv) t) by lia.
  rewrite Z.add_0_l, <- HW, <- !byte_of_zbyte by lia. rewrite (BY t Ht). reflexivity.
Qed.

Lemma wmax_val : forall w, 1 <= to_Z w <= 4 -> w2Z (LdPart.wmax w) = 2 ^ (8 * to_Z w) - 1.
Proof.
  intros w Hw. unfold LdPart.wmax. rewrite w2Z_wlit || rewrite wlit_ok.
  assert (M8 : to_Z (PrimInt63.mul 8 w) = 8 * to_Z w) by (rewrite Uint63.mul_spec; change (to_Z 8%uint63) with 8; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (P : 2 ^ (8 * to_Z w) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (SL : to_Z (PrimInt63.lsl 1 (PrimInt63.mul 8 w)) = 2 ^ (8 * to_Z w)).
  { rewrite Uint63.lsl_spec, M8. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
  rewrite Uint63.sub_spec, SL. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_two63. unfold two63.
  pose proof (Z.pow_pos_nonneg 2 (8 * to_Z w) ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem ldpart_sound : forall pc, contract_sound segs OPS MP PB (LdPart.ldpart_c segs pc).
Proof.
  intros pc st sts Hspc HAP KS E ms mo HS HMP HPB HK. cbn [c_apply LdPart.ldpart_c] in HAP. unfold LdPart.ldpart_apply in HAP.
  destruct (LdPart.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  set (w := msize_bytes sz) in HAP.
  set (a := sv_alu ALU_ADD (getr st rs) (VL off)) in HAP.
  destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate].
  destruct (PrimInt63.eqb k 0%uint63) eqn:K; [discriminate|].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate].
  cbv zeta in HAP.
  set (g := granule key) in *. set (i := gidx key) in *.
  set (old := match IMap.find g (rg_cells r) with Some gr => g_cells gr | None => [] end) in HAP.
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [COND NPOS].
  apply andb_prop in COND as [COND VB]. apply andb_prop in COND as [COND RDX]. apply andb_prop in COND as [COND FIT].
  apply andb_prop in COND as [COND CR]. apply andb_prop in COND as [BGN IG].
  apply negb_true_iff in RDX.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with (4611686018427387904 - 8) in NLT.
  assert (BG : rg_bg r = BGNone) by (destruct (rg_bg r); try discriminate BGN; reflexivity).
  set (n := s_next st) in *.
  set (v := VP n wzero) in HAP.
  set (dropped := List.filter (fun c => negb (LdPart.cell_apart i w c)) old) in HAP.
  set (nf := (if negb sx && PrimInt63.ltb w 8%uint63 then [FRange n wzero (LdPart.wmax w)] else []) ++ map (LdPart.cell_fact n i) dropped) in HAP.
  set (r' := region_store1 r key w v) in HAP.
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add k r' (s_regs st)) (nf ++ s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)) in HAP.
  apply Some_inj in HAP. subst sts.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.

  assert (W8 : 1 <= to_Z w <= 8) by (subst w; destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  set (wZ := to_Z w) in *.
  pose proof (granule_gidx key ltac:(apply (proj2 (okey_sound _ _ Hk)))) as [GK GI]. fold g i in GK, GI.
  assert (IGZ : to_Z i + wZ <= 8) by (unfold in_granule in IG; apply Uint63.leb_spec in IG; rewrite Uint63.add_spec in IG; change (to_Z 8%uint63) with 8 in IG; fold i in IG; rewrite Z.mod_small in IG by (rewrite wB_two63; unfold two63; lia); lia).

  assert (WOK : wok w) by (subst w; destruct sz; cbn [msize_bytes]; unfold wok; [left| right; left| right; right; left| right; right; right]; reflexivity).
  pose proof (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO WOK CR) as (A0 & AW & RBS & RNG & _).
  specialize (RNG K). fold wZ in AW, RBS, RNG.
  set (A := addrZ E k key) in *.
  assert (EA : A = bv_unsigned (ev E k) + 8 * keyZ g + to_Z i) by (unfold A, addrZ; lia).
  destruct (rdZ_total (bmem_of segs (ms_mem ms)) (Z.to_nat wZ) A) as [z RD].
  { intros t Ht X. rewrite Z2Nat.id in Ht by lia. unfold bmem_of in X.
    replace ((0 <=? A + t) && (A + t <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    destruct (rb segs (ms_mem ms) (A + t)) eqn:RB; [discriminate X| exact (RBS t ltac:(lia) RB)]. }
  pose proof (rdZ_nonneg _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD) as ZR. rewrite Z2Nat.id in ZR by lia.
  set (W := ext_word sx 0 wZ (Z_to_bv 64 z)).
  pose proof two64_eq as T64.
  assert (Z64 : z < two64).
  { assert (2 ^ (8 * wZ) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). rewrite T64. lia. }
  assert (HWz : bv_unsigned W = ext_Z sx 0 wZ z).
  { subst W. unfold ext_word. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 z) by (rewrite bv_modulus_64; lia).
    apply bv_wrap_small. rewrite bv_modulus_64. apply ext_Z_range; lia. }
  assert (BY : forall t, 0 <= t < wZ -> rb segs (ms_mem ms) (A + t) = Some (byte_of W t)).
  { intros t Ht. pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD t ltac:(rewrite Z2Nat.id by lia; lia)) as X.
    unfold bmem_of in X.
    replace ((0 <=? A + t) && (A + t <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    destruct (rb segs (ms_mem ms) (A + t)) as [b|]; [|discriminate X]. cbn [option_map] in X. injection X as X.
    f_equal. apply bv_eq. rewrite X, byte_of_zbyte, HWz by lia. rewrite zbyte_ext_Z by lia. rewrite Z.add_0_l. reflexivity. }
  assert (MB : forall t, 0 <= t < wZ -> ms_mem ms (Z_to_bv 64 (A + t)) = Some (byte_of W t)).
  { intros t Ht. pose proof (BY t Ht) as X. rewrite rb_unfold in X. destruct (ms_mem ms (Z_to_bv 64 (A + t))) as [b|] eqn:MBt; [exact X|].
    exfalso. pose proof (RNG t Ht) as RG. pose proof (MemFX.based_no_segment segs (s_priv st) E (ms_mem ms) k r (A + t) RO K ltac:(unfold A, addrZ; lia)) as NSG.
    destruct (memory_read segs (Z_to_bv 64 (A + t)) 1) as [bs|] eqn:MR; [| discriminate X].
    destruct (memory_read_find_segment segs (A + t) bs ltac:(lia) MR) as [seg SG]. rewrite NSG in SG. discriminate SG. }

  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : st_ok segs OPS E' st ms mo) by exact (st_ok_reval segs OPS n E E' HX st ms mo NPOS VB HS).
  pose proof VB as VB'. unfold st_vars_below in VB'.
  apply andb_prop in VB' as [VB' VBops]. apply andb_prop in VB' as [VB' VBfs]. apply andb_prop in VB' as [VB' VBregs].
  apply andb_prop in VB' as [VB' VBresv]. apply andb_prop in VB' as [VBrf VBff].
  destruct (regs_reval_find n E E' HX (s_regs st) k r BST VBregs Hr) as (EVk & EHIr & Kn & RVB).
  assert (EA' : addrZ E' k key = A) by (unfold A, addrZ; rewrite EVk; reflexivity).
  pose proof (so_reg _ _ _ _ _ _ HS' k r Hr) as RO1.
  assert (Dv : den E' v = W) by (subst v; rewrite MemFX.den_VPz; exact EVn).

  pose proof (so_zero _ _ _ _ _ _ HS') as Hz'.
  destruct (region_store1_sound segs (s_priv st) E' k Hz' (ms_mem ms) r key w v RO1 ltac:(lia) ltac:(fold i; lia)
              ltac:(intros t Ht; split; [intros _; rewrite EHIr; pose proof (RNG t Ht); lia| intros X; rewrite K in X; discriminate X])) as [ROw FRw].
  cbv zeta in ROw, FRw. assert (EA'' : bv_unsigned (ev E' k) + keyZ key = A) by (rewrite EVk; reflexivity). rewrite EA'' in ROw, FRw. fold r' in ROw.
  set (m' := write_to_mem (ms_mem ms) (Z_to_bv 64 A) (store_bytes w (den E' v))) in ROw, FRw.
  assert (SBL : length (store_bytes w (den E' v)) = Z.to_nat wZ) by (rewrite store_bytes_length; reflexivity).
  assert (MM : forall x, m' x = ms_mem ms x).
  { intros x. pose proof (bv_unsigned_in_range 64 x) as RX. rewrite bv_modulus_64 in RX. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    set (ax := bv_unsigned x) in *.
    destruct (Z_lt_le_dec ax A) as [L1|G1]; [apply FRw; [unfold two64|]; lia|].
    destruct (Z_lt_le_dec ax (A + wZ)) as [L2|G2]; [| apply FRw; [unfold two64|]; lia].
    replace ax with (A + (ax - A)) by lia. subst m'. rewrite write_to_mem_in by (rewrite ?SBL, ?Z2Nat.id; lia).
    rewrite store_bytes_nth_error by lia. rewrite Dv. symmetry. apply MB. lia. }
  assert (RO' : region_ok segs (s_priv st) E' (ms_mem ms) k r').
  { apply (region_ok_frame segs (s_priv st) E' m' (ms_mem ms) k r' Hz' ROw). intros aa _ _ _. symmetry. apply MM. }
  assert (ER' : rg_lo r' = rg_lo r /\ rg_hi r' = rg_hi r /\ rg_w r' = rg_w r).
  { subst r'. unfold region_store1. destruct (IMap.find (granule key) (rg_cells r)) as [[d0 s0]|]; cbn; auto. }
  destruct ER' as (ELO & EHI & EW).

  assert (HS1 : st_ok segs OPS E' st1 ms mo).
  { apply (st_ok_recast E' st ms mo k r r' nf (PrimInt63.add n 1%uint63) HS' Hr K ELO EHI EW RO').
    subst nf. apply Forall_app. split.
    - destruct (negb sx && PrimInt63.ltb w 8%uint63) eqn:NR; [| constructor].
      apply andb_prop in NR as [SX W7]. apply negb_true_iff in SX. apply Uint63.ltb_spec in W7. change (to_Z 8%uint63) with 8 in W7. fold wZ in W7.
      constructor; [| constructor]. cbn [fact_holds]. rewrite EVn, HWz, wzero_ok || rewrite EVn, HWz.
      assert (W4 : wZ <= 4) by (subst wZ w; destruct sz; cbn [msize_bytes] in W7 |- *; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8 in W7]; lia).
      rewrite (wmax_val w) by (fold wZ; lia). fold wZ. change (w2Z wzero) with 0. subst sx.
      pose proof (ext_Z_false_range 0 wZ z ltac:(lia)). lia.
    - apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (c & <- & Hc). subst dropped. apply filter_In in Hc as [Hc NA].
      destruct (IMap.find g (rg_cells r)) as [gr|] eqn:Fg; [| destruct Hc].
      pose proof (ro_cells _ _ _ _ _ _ RO g gr Fg) as [_ CELLS]. pose proof (proj1 (Forall_forall _ _) CELLS c Hc) as (C1 & C2 & C3 & C4).
      pose proof (proj1 (forallb_forall _ _) FIT c Hc) as FC. cbn beta in FC. rewrite (proj1 (negb_true_iff _) NA) in FC. cbn [orb] in FC.
      unfold LdPart.cell_inside in FC. apply andb_prop in FC as [I1 I2]. apply Uint63.leb_spec in I1. apply Uint63.leb_spec in I2.
      rewrite !Uint63.add_spec in I2. rewrite !Z.mod_small in I2 by (rewrite wB_two63; unfold two63; pose proof (Uint63.to_Z_bounded (c_idx c)); pose proof (Uint63.to_Z_bounded (c_w c)); lia).
      fold wZ in I2.
      assert (VBc : sv_vars_below n (c_v c) = true).
      { apply andb_prop in RVB as [_ RC]. eapply slot_vars_below_In; [| exact Hc]. exact (proj1 (IMap.forallb_spec _ _ (ro_bst _ _ _ _ _ _ RO)) RC g gr Fg). }
      assert (SUBi : to_Z (PrimInt63.sub (c_idx c) i) = to_Z (c_idx c) - to_Z i).
      { rewrite Uint63.sub_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. pose proof (Uint63.to_Z_bounded (c_idx c)). lia. }
      unfold LdPart.cell_fact. cbn [fact_holds].
      rewrite !den_sv_ext by (unfold width_ok; rewrite ?SUBi; change (to_Z 0%uint63) with 0; lia).
      change (VP n wzero) with v. rewrite Dv, (den_reval n E E' HX _ VBc). unfold ext_word. f_equal. change (to_Z 0%uint63) with 0. rewrite SUBi.
      apply (ext_slice_eq (bv_unsigned W) (to_Z (c_idx c) - to_Z i) (to_Z (c_w c)) (den E (c_v c)) W); [lia| lia| lia| reflexivity|].
      intros t Ht. pose proof (BY (to_Z (c_idx c) - to_Z i + t) ltac:(lia)) as X1. pose proof (C4 t Ht) as X2.
      replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + t) with (A + (to_Z (c_idx c) - to_Z i + t)) in X2 by lia.
      rewrite X1 in X2. apply Some_inj in X2. exact X2. }

  destruct (load_at_spec _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 A).
  { change (getr st1 rs) with (getr st rs). fold a. apply (access_addr E' a k o key A Hz' Ha Hk); [symmetry; exact EA'| lia| lia]. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS (AccStep.CH_cov OPS) (AccStep.LAW_cov OPS) MP HMPA E' st1 ms mo wi ins sz sx rd rs off A z v HS1 HMP PCB Hf' He Hd Hof DA A0
              ltac:(fold w wZ; lia) ltac:(fold w wZ; exact RD) ltac:(fold w wZ; rewrite Dv; reflexivity)) as (ms' & mo' & STEP & MEM & HS2 & MP2).
  {
    intros j Hj. unfold AccStep.CH_cov. apply (so_cover _ _ _ _ _ _ HS1). left.
    exists k, r'. split; [subst st1; cbn [s_regs]; apply IMap.find_add_same; exact BST|]. split; [exact K|].
    pose proof (region_store1_fields r key w v) as (F1 & F2 & _ & _). fold r' in F1, F2.
    unfold loZ, hiZ. rewrite F1, F2. fold (loZ r). fold (hiZ E' r). rewrite EHIr, EVk.
    fold w wZ in Hj. pose proof (RNG j Hj) as X. unfold addrZ in EA'. lia. }
  apply (rz_astep segs ms mo ms' mo' KS (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo' HX MP2 HS2).
Qed.

End WithSegs.
End LdPartSoundA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Notation OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.LdPart.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAcc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Acc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepAcc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.AccStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStepA.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module LdPartSoundA.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma load_at_spec : forall pc sz sx rd rs off, LdPart.load_at segs pc = Some (sz, sx, rd, rs, off) ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\
              of_instr i = Some (ILoad sz sx rd rs off).
Proof.
  intros pc sz sx rd rs off H. unfold LdPart.load_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z.
  destruct (of_instr i) as [fi|] eqn:OI; [|discriminate]. destruct fi; try discriminate. injection H as <- <- <- <- <-.
  exists w, i. auto.
Qed.

Lemma rdZ_total : forall (bm : bmem) n a, (forall i, 0 <= i < Z.of_nat n -> bm (a + i) <> None) -> exists z, rdZ bm a n = Some z.
Proof.
  intros bm n. induction n as [|n IH]; intros a H.
  - exists 0. reflexivity.
  - cbn [rdZ]. destruct (bm a) as [b|] eqn:B.
    2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact B. }
    destruct (IH (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia)) as [z ->].
    eexists. reflexivity.
Qed.

Lemma st_ok_recast : forall E st ms mo kd rd rd' fs' nx,
  st_ok segs OPS E st ms mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false ->
  rg_lo rd' = rg_lo rd -> rg_hi rd' = rg_hi rd -> rg_w rd' = rg_w rd ->
  region_ok segs (s_priv st) E (ms_mem ms) kd rd' ->
  Forall (fact_holds E) fs' ->
  st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo kd rd rd' fs' nx HS Hkd K ELO EHI EW RO' HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }
  assert (RNG : forall E0, loZ rd' = loZ rd /\ hiZ E0 rd' = hiZ E0 rd) by (intros; unfold loZ, hiZ; rewrite ELO, EHI; auto).
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'| exact (Preg k r Hk)].
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in X1. rewrite EW in WW. exact (Pdisj kd rd k2 q2 Hkd G2 NE K1 K2 WW a (conj X1 X2)).
    + destruct (RNG E) as [L2 H2']. rewrite L2, H2' in X2. rewrite EW in WW. exact (Pdisj k1 q1 kd rd G1 Hkd NE K1 K2 WW a (conj X1 X2)).
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - intros r g gr c H0 Hg Hc i Hi. destruct (FIND _ _ H0) as [[E0 _]|[_ H0']]; [rewrite <- E0 in K; rewrite Uint63.eqb_refl in K; discriminate K|].
    exact (Ppub r g gr c H0' Hg Hc i Hi).
  - apply Forall_app. split; [exact HF| exact Pfacts].
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in RG. apply NB. exists kd, rd. auto.
    + apply NB. exists k, r. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k & r & H & K' & RG).
    destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + destruct (RNG E) as [L1 H1']. rewrite L1, H1' in RG. exists kd, rd. auto.
    + exists k, r. auto.
Qed.

Lemma ext_slice_eq : forall (z : Z) (idx w : Z) (dv : word) (W : word),
  0 <= idx -> 1 <= w -> idx + w <= 8 -> bv_unsigned W = z ->
  (forall t, 0 <= t < w -> byte_of W (idx + t) = byte_of dv t) ->
  ext_Z false idx w z = ext_Z false 0 w (bv_unsigned dv).
Proof.
  intros z idx w dv W Hi Hw H8 HW BY.
  pose proof (ext_Z_false_range idx w z ltac:(lia)) as R1. pose proof (ext_Z_false_range 0 w (bv_unsigned dv) ltac:(lia)) as R2.
  pose proof (bv_unsigned_in_range _ W) as RW. pose proof (bv_unsigned_in_range _ dv) as RD.
  rewrite <- (Z.mod_small (ext_Z false idx w z) (2 ^ (8 * w))) by lia.
  rewrite <- (Z.mod_small (ext_Z false 0 w (bv_unsigned dv)) (2 ^ (8 * w))) by lia.
  apply zbytes_eq; [lia|]. intros t Ht.
  rewrite (zbyte_ext_Z false idx w z t) by lia. rewrite (zbyte_ext_Z false 0 w (bv_unsigned dv) t) by lia.
  rewrite Z.add_0_l, <- HW, <- !byte_of_zbyte by lia. rewrite (BY t Ht). reflexivity.
Qed.

Lemma wmax_val : forall w, 1 <= to_Z w <= 4 -> w2Z (LdPart.wmax w) = 2 ^ (8 * to_Z w) - 1.
Proof.
  intros w Hw. unfold LdPart.wmax. rewrite w2Z_wlit || rewrite wlit_ok.
  assert (M8 : to_Z (PrimInt63.mul 8 w) = 8 * to_Z w) by (rewrite Uint63.mul_spec; change (to_Z 8%uint63) with 8; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (P : 2 ^ (8 * to_Z w) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (SL : to_Z (PrimInt63.lsl 1 (PrimInt63.mul 8 w)) = 2 ^ (8 * to_Z w)).
  { rewrite Uint63.lsl_spec, M8. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
  rewrite Uint63.sub_spec, SL. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_two63. unfold two63.
  pose proof (Z.pow_pos_nonneg 2 (8 * to_Z w) ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem ldpart_sound : forall pc, contract_sound segs OPS MP PB (LdPart.ldpart_c segs pc).
Proof.
  intros pc st sts Hspc HAP KS E ms mo HS HMP HPB HK. cbn [c_apply LdPart.ldpart_c] in HAP. unfold LdPart.ldpart_apply in HAP.
  destruct (LdPart.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  set (w := msize_bytes sz) in HAP.
  set (a := sv_alu ALU_ADD (getr st rs) (VL off)) in HAP.
  destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate].
  destruct (PrimInt63.eqb k 0%uint63) eqn:K; [discriminate|].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate].
  cbv zeta in HAP.
  set (g := granule key) in *. set (i := gidx key) in *.
  set (old := match IMap.find g (rg_cells r) with Some gr => g_cells gr | None => [] end) in HAP.
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [COND NPOS].
  apply andb_prop in COND as [COND VB]. apply andb_prop in COND as [COND RDX]. apply andb_prop in COND as [COND FIT].
  apply andb_prop in COND as [COND CR]. apply andb_prop in COND as [BGN IG].
  apply negb_true_iff in RDX.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with (4611686018427387904 - 8) in NLT.
  assert (BG : rg_bg r = BGNone) by (destruct (rg_bg r); try discriminate BGN; reflexivity).
  set (n := s_next st) in *.
  set (v := VP n wzero) in HAP.
  set (dropped := List.filter (fun c => negb (LdPart.cell_apart i w c)) old) in HAP.
  set (nf := (if negb sx && PrimInt63.ltb w 8%uint63 then [FRange n wzero (LdPart.wmax w)] else []) ++ map (LdPart.cell_fact n i) dropped) in HAP.
  set (r' := region_store1 r key w v) in HAP.
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add k r' (s_regs st)) (nf ++ s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)) in HAP.
  apply Some_inj in HAP. subst sts.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.

  assert (W8 : 1 <= to_Z w <= 8) by (subst w; destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  set (wZ := to_Z w) in *.
  pose proof (granule_gidx key ltac:(apply (proj2 (okey_sound _ _ Hk)))) as [GK GI]. fold g i in GK, GI.
  assert (IGZ : to_Z i + wZ <= 8) by (unfold in_granule in IG; apply Uint63.leb_spec in IG; rewrite Uint63.add_spec in IG; change (to_Z 8%uint63) with 8 in IG; fold i in IG; rewrite Z.mod_small in IG by (rewrite wB_two63; unfold two63; lia); lia).

  assert (WOK : wok w) by (subst w; destruct sz; cbn [msize_bytes]; unfold wok; [left| right; left| right; right; left| right; right; right]; reflexivity).
  pose proof (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO WOK CR) as (A0 & AW & RBS & RNG & _).
  specialize (RNG K). fold wZ in AW, RBS, RNG.
  set (A := addrZ E k key) in *.
  assert (EA : A = bv_unsigned (ev E k) + 8 * keyZ g + to_Z i) by (unfold A, addrZ; lia).
  destruct (rdZ_total (bmem_of segs (ms_mem ms)) (Z.to_nat wZ) A) as [z RD].
  { intros t Ht X. rewrite Z2Nat.id in Ht by lia. unfold bmem_of in X.
    replace ((0 <=? A + t) && (A + t <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    destruct (rb segs (ms_mem ms) (A + t)) eqn:RB; [discriminate X| exact (RBS t ltac:(lia) RB)]. }
  pose proof (rdZ_nonneg _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD) as ZR. rewrite Z2Nat.id in ZR by lia.
  set (W := ext_word sx 0 wZ (Z_to_bv 64 z)).
  pose proof two64_eq as T64.
  assert (Z64 : z < two64).
  { assert (2 ^ (8 * wZ) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). rewrite T64. lia. }
  assert (HWz : bv_unsigned W = ext_Z sx 0 wZ z).
  { subst W. unfold ext_word. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 z) by (rewrite bv_modulus_64; lia).
    apply bv_wrap_small. rewrite bv_modulus_64. apply ext_Z_range; lia. }
  assert (BY : forall t, 0 <= t < wZ -> rb segs (ms_mem ms) (A + t) = Some (byte_of W t)).
  { intros t Ht. pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD t ltac:(rewrite Z2Nat.id by lia; lia)) as X.
    unfold bmem_of in X.
    replace ((0 <=? A + t) && (A + t <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    destruct (rb segs (ms_mem ms) (A + t)) as [b|]; [|discriminate X]. cbn [option_map] in X. injection X as X.
    f_equal. apply bv_eq. rewrite X, byte_of_zbyte, HWz by lia. rewrite zbyte_ext_Z by lia. rewrite Z.add_0_l. reflexivity. }
  assert (MB : forall t, 0 <= t < wZ -> ms_mem ms (Z_to_bv 64 (A + t)) = Some (byte_of W t)).
  { intros t Ht. pose proof (BY t Ht) as X. rewrite rb_unfold in X. destruct (ms_mem ms (Z_to_bv 64 (A + t))) as [b|] eqn:MBt; [exact X|].
    exfalso. pose proof (RNG t Ht) as RG. pose proof (MemFX.based_no_segment segs (s_priv st) E (ms_mem ms) k r (A + t) RO K ltac:(unfold A, addrZ; lia)) as NSG.
    destruct (memory_read segs (Z_to_bv 64 (A + t)) 1) as [bs|] eqn:MR; [| discriminate X].
    destruct (memory_read_find_segment segs (A + t) bs ltac:(lia) MR) as [seg SG]. rewrite NSG in SG. discriminate SG. }

  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : st_ok segs OPS E' st ms mo) by exact (st_ok_reval segs OPS n E E' HX st ms mo NPOS VB HS).
  pose proof VB as VB'. unfold st_vars_below in VB'.
  apply andb_prop in VB' as [VB' VBops]. apply andb_prop in VB' as [VB' VBfs]. apply andb_prop in VB' as [VB' VBregs].
  apply andb_prop in VB' as [VB' VBresv]. apply andb_prop in VB' as [VBrf VBff].
  destruct (regs_reval_find n E E' HX (s_regs st) k r BST VBregs Hr) as (EVk & EHIr & Kn & RVB).
  assert (EA' : addrZ E' k key = A) by (unfold A, addrZ; rewrite EVk; reflexivity).
  pose proof (so_reg _ _ _ _ _ _ HS' k r Hr) as RO1.
  assert (Dv : den E' v = W) by (subst v; rewrite MemFX.den_VPz; exact EVn).

  pose proof (so_zero _ _ _ _ _ _ HS') as Hz'.
  destruct (region_store1_sound segs (s_priv st) E' k Hz' (ms_mem ms) r key w v RO1 ltac:(lia) ltac:(fold i; lia)
              ltac:(intros t Ht; split; [intros _; rewrite EHIr; pose proof (RNG t Ht); lia| intros X; rewrite K in X; discriminate X])) as [ROw FRw].
  cbv zeta in ROw, FRw. assert (EA'' : bv_unsigned (ev E' k) + keyZ key = A) by (rewrite EVk; reflexivity). rewrite EA'' in ROw, FRw. fold r' in ROw.
  set (m' := write_to_mem (ms_mem ms) (Z_to_bv 64 A) (store_bytes w (den E' v))) in ROw, FRw.
  assert (SBL : length (store_bytes w (den E' v)) = Z.to_nat wZ) by (rewrite store_bytes_length; reflexivity).
  assert (MM : forall x, m' x = ms_mem ms x).
  { intros x. pose proof (bv_unsigned_in_range 64 x) as RX. rewrite bv_modulus_64 in RX. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    set (ax := bv_unsigned x) in *.
    destruct (Z_lt_le_dec ax A) as [L1|G1]; [apply FRw; [unfold two64|]; lia|].
    destruct (Z_lt_le_dec ax (A + wZ)) as [L2|G2]; [| apply FRw; [unfold two64|]; lia].
    replace ax with (A + (ax - A)) by lia. subst m'. rewrite write_to_mem_in by (rewrite ?SBL, ?Z2Nat.id; lia).
    rewrite store_bytes_nth_error by lia. rewrite Dv. symmetry. apply MB. lia. }
  assert (RO' : region_ok segs (s_priv st) E' (ms_mem ms) k r').
  { apply (region_ok_frame segs (s_priv st) E' m' (ms_mem ms) k r' Hz' ROw). intros aa _ _ _. symmetry. apply MM. }
  assert (ER' : rg_lo r' = rg_lo r /\ rg_hi r' = rg_hi r /\ rg_w r' = rg_w r).
  { subst r'. unfold region_store1. destruct (IMap.find (granule key) (rg_cells r)) as [[d0 s0]|]; cbn; auto. }
  destruct ER' as (ELO & EHI & EW).

  assert (HS1 : st_ok segs OPS E' st1 ms mo).
  { apply (st_ok_recast E' st ms mo k r r' nf (PrimInt63.add n 1%uint63) HS' Hr K ELO EHI EW RO').
    subst nf. apply Forall_app. split.
    - destruct (negb sx && PrimInt63.ltb w 8%uint63) eqn:NR; [| constructor].
      apply andb_prop in NR as [SX W7]. apply negb_true_iff in SX. apply Uint63.ltb_spec in W7. change (to_Z 8%uint63) with 8 in W7. fold wZ in W7.
      constructor; [| constructor]. cbn [fact_holds]. rewrite EVn, HWz, wzero_ok || rewrite EVn, HWz.
      assert (W4 : wZ <= 4) by (subst wZ w; destruct sz; cbn [msize_bytes] in W7 |- *; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8 in W7]; lia).
      rewrite (wmax_val w) by (fold wZ; lia). fold wZ. change (w2Z wzero) with 0. subst sx.
      pose proof (ext_Z_false_range 0 wZ z ltac:(lia)). lia.
    - apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (c & <- & Hc). subst dropped. apply filter_In in Hc as [Hc NA].
      destruct (IMap.find g (rg_cells r)) as [gr|] eqn:Fg; [| destruct Hc].
      pose proof (ro_cells _ _ _ _ _ _ RO g gr Fg) as [_ CELLS]. pose proof (proj1 (Forall_forall _ _) CELLS c Hc) as (C1 & C2 & C3 & C4).
      pose proof (proj1 (forallb_forall _ _) FIT c Hc) as FC. cbn beta in FC. rewrite (proj1 (negb_true_iff _) NA) in FC. cbn [orb] in FC.
      unfold LdPart.cell_inside in FC. apply andb_prop in FC as [I1 I2]. apply Uint63.leb_spec in I1. apply Uint63.leb_spec in I2.
      rewrite !Uint63.add_spec in I2. rewrite !Z.mod_small in I2 by (rewrite wB_two63; unfold two63; pose proof (Uint63.to_Z_bounded (c_idx c)); pose proof (Uint63.to_Z_bounded (c_w c)); lia).
      fold wZ in I2.
      assert (VBc : sv_vars_below n (c_v c) = true).
      { apply andb_prop in RVB as [_ RC]. eapply slot_vars_below_In; [| exact Hc]. exact (proj1 (IMap.forallb_spec _ _ (ro_bst _ _ _ _ _ _ RO)) RC g gr Fg). }
      assert (SUBi : to_Z (PrimInt63.sub (c_idx c) i) = to_Z (c_idx c) - to_Z i).
      { rewrite Uint63.sub_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. pose proof (Uint63.to_Z_bounded (c_idx c)). lia. }
      unfold LdPart.cell_fact. cbn [fact_holds].
      rewrite !den_sv_ext by (unfold width_ok; rewrite ?SUBi; change (to_Z 0%uint63) with 0; lia).
      change (VP n wzero) with v. rewrite Dv, (den_reval n E E' HX _ VBc). unfold ext_word. f_equal. change (to_Z 0%uint63) with 0. rewrite SUBi.
      apply (ext_slice_eq (bv_unsigned W) (to_Z (c_idx c) - to_Z i) (to_Z (c_w c)) (den E (c_v c)) W); [lia| lia| lia| reflexivity|].
      intros t Ht. pose proof (BY (to_Z (c_idx c) - to_Z i + t) ltac:(lia)) as X1. pose proof (C4 t Ht) as X2.
      replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + t) with (A + (to_Z (c_idx c) - to_Z i + t)) in X2 by lia.
      rewrite X1 in X2. apply Some_inj in X2. exact X2. }

  destruct (load_at_spec _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 A).
  { change (getr st1 rs) with (getr st rs). fold a. apply (access_addr E' a k o key A Hz' Ha Hk); [symmetry; exact EA'| lia| lia]. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS (AccStep.CH_cov OPS) (AccStep.LAW_cov OPS) MP HMPA E' st1 ms mo wi ins sz sx rd rs off A z v HS1 HMP PCB Hf' He Hd Hof DA A0
              ltac:(fold w wZ; lia) ltac:(fold w wZ; exact RD) ltac:(fold w wZ; rewrite Dv; reflexivity)) as (ms' & mo' & STEP & MEM & HS2 & MP2).
  {
    intros j Hj. unfold AccStep.CH_cov. apply (so_cover _ _ _ _ _ _ HS1). left.
    exists k, r'. split; [subst st1; cbn [s_regs]; apply IMap.find_add_same; exact BST|]. split; [exact K|].
    pose proof (region_store1_fields r key w v) as (F1 & F2 & _ & _). fold r' in F1, F2.
    unfold loZ, hiZ. rewrite F1, F2. fold (loZ r). fold (hiZ E' r). rewrite EHIr, EVk.
    fold w wZ in Hj. pose proof (RNG j Hj) as X. unfold addrZ in EA'. lia. }
  apply (rz_astep segs ms mo ms' mo' KS (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo' HX MP2 HS2).
Qed.

End WithSegs.
End LdPartSoundA.
End TwinB.
