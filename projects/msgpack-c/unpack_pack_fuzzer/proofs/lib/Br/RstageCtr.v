(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Omono.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocBlocks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv KRel HeapCore RMallocG MemcpyG CtrFX MemFX CopyFX AW HeapCtr HeapCtrB MemcpyCtr.
Set Keyed Unification.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.
Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) ->
  0x52000 <= a < 0x88000 /\ ~ ralloc_static a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable RS : int.
Hypothesis RS_range : 0x10000 <= to_Z RS /\ to_Z RS + 65536 <= 0x88000.
Hypothesis OPS3_bytes : forall E (woff wn : word) m mo, PB (eb E) -> St.op_holds OPS CtrB.RSTAGE_ID [woff; wn] m mo ->
  bv_unsigned wn <= 65536 /\
  forall i, 0 <= i < bv_unsigned wn -> m (Z_to_bv 64 (to_Z RS + i)) = Some (nth (Z.to_nat (bv_unsigned woff + i)) (eb E 4%uint63) (Z_to_bv 8 0)).
Hypothesis OPS3_advance : forall (woff wn : word) m m' mo, St.op_holds OPS CtrB.RSTAGE_ID [woff; wn] m mo ->
  St.op_holds OPS CtrB.RSTAGE_ID [(woff + wn)%bv; Z_to_bv 64 0] m' mo.
Hypothesis OPS3_fp : forall args args', St.op_fp OPS CtrB.RSTAGE_ID args = St.op_fp OPS CtrB.RSTAGE_ID args'.

Lemma justified_above : forall E st wl k r, facts_hold E (s_facts st) -> regions_justified st wl = true -> IMap.bst (s_regs st) ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 -> k <> STACK_ID -> win_lookup wl k = None ->
  loZ r = 0 /\ bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k).
Proof.
  intros E st wl k r Hfs JU B Hk K0 K1 WL. unfold regions_justified in JU. cbv zeta in JU.
  pose proof (proj1 (IMap.forallb_spec _ _ B) JU k r Hk) as J.
  destruct (region_justified_inv E _ _ _ _ _ Hfs J K0 K1) as (L0 & [SJ|(len & kd & WL' & _)]); [|rewrite WL in WL'; discriminate WL'].
  split; [unfold loZ; rewrite L0; reflexivity| exact SJ].
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros A f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma sym_offset_vars_below : forall n R a k off,
  sv_vars_below n a = true -> CtrA.sym_offset R a = Some (k, off) -> sv_vars_below n off = true.
Proof.
  intros n R a k off V H. unfold CtrA.sym_offset in H.
  destruct a as [|k1 o1|op x y| | | | | | | |]; cbn [sym_addr_of] in H; try discriminate H.
  - destruct (weqb o1 wzero); injection H as _ <-; reflexivity.
  - cbn [sv_vars_below] in V. apply andb_prop in V as [Vx Vy].
    destruct op; try discriminate H.
    destruct x as [|kx ox| | | | | | | | |];
      [ | destruct (IMap.find kx R);
          [ injection H as _ <-; apply MemFX.sv_vars_below_alu; [left; reflexivity| exact Vy| reflexivity]
          | destruct y as [|ky oy| | | | | | | | |]; try discriminate H;
            destruct (IMap.find ky R); [injection H as _ <-; exact Vx| discriminate H] ] |..].
    all: destruct y as [|ky oy| | | | | | | | |]; try discriminate H;
         destruct (IMap.find ky R); [injection H as _ <-; apply MemFX.sv_vars_below_alu; [left; reflexivity| exact Vx| reflexivity]| discriminate H].
Qed.

Theorem rstage_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrB.rstage_c rsegs ERRNO RS pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrB.rstage_c] in Happ. unfold CtrB.rstage_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X11) as [rsw| | | | | | | | | |] eqn:HX11; try discriminate.
  destruct (stack_ok st 0%uint63) as [[ksp klo1]|] eqn:SOK; [|discriminate].
  destruct (negb (weqb rsw (wlit RS)) || negb (Nat.eqb (count_op CtrB.RSTAGE_ID (s_ops st)) 1)) eqn:C; [discriminate|].
  apply orb_false_iff in C as [RSW CNT]. apply negb_false_iff in RSW. apply weqb_eq in RSW. subst rsw.
  apply negb_false_iff in CNT. apply Nat.eqb_eq in CNT.
  destruct (heap_windows st klo1) as [[hargs0 [|[[kw wlen] kd] [|]]]|] eqn:HW; try discriminate.
  destruct (sym_offset (s_regs st) (getr st X10)) as [[kb X]|] eqn:DOFF; [|discriminate].
  destruct (find_op CtrB.RSTAGE_ID (s_ops st)) as [[|off [|n' [|]]]|] eqn:F3; try discriminate.
  destruct (negb (PrimInt63.eqb kw kb) || negb (weqb kd CtrLib.K_BLOCK)) eqn:C; [discriminate|].
  apply orb_false_iff in C as [KW KD]. apply negb_false_iff in KW. apply Uint63.eqb_correct in KW. subst kw.
  apply negb_false_iff in KD. apply weqb_eq in KD. subst kd.
  destruct (IMap.find kb (s_regs st)) as [rgb|] eqn:Hkb; [|discriminate].
  destruct (Mem.rg_cells rgb) eqn:CBL; [|discriminate].
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (hi' := CtrB.new_hi (s_facts st) X (getr st X12)) in Happ.
  set (rgb' := Mem.Region 0%uint63 hi' true (Mem.BGBlob 4%uint63 0%uint63) IMap.empty) in Happ.
  set (st1 := setregs st (IMap.add kb rgb' (s_regs st))) in Happ.
  set (st2 := set_ops st1 (set_op CtrB.RSTAGE_ID [sv_alu ALU_ADD off (getr st X12); VL wzero] (s_ops st1))) in Happ.
  destruct (havoc_errno rsegs ERRNO (clobber st2)) as [st3|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LEn]. apply andb_prop in C2 as [C2 LEX]. apply andb_prop in C2 as [C2 EQn]. apply andb_prop in C2 as [C2 EQoff].
  apply andb_prop in C2 as [C2 Wb]. apply andb_prop in C2 as [PRE LOb]. apply Uint63.eqb_correct in LOb.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as EZ0. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  destruct (stack_sound OPS E st ms mo 0%uint63 ksp klo1 HS ltac:(vm_compute; reflexivity) SOK)
    as (spoff & r1 & HX2 & Hr1 & W1 & BG1 & Hksp & -> & K16 & KNEG & SPE & LO0 & ROOM & HI1 & STK). change (to_Z 0%uint63) with 0 in ROOM.
  destruct (heap_windows_inv st (Mem.rg_lo r1) hargs0 _ HW) as (Hf & Hc & nw_ & md & Aw & nw & rest & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite Eh, (decode_hargs E md Aw nw rest nw_ T N L) in D. injection D as <- <- <- <-.

  destruct (stack_window_In E nw_ rest (Mem.rg_lo r1) SW) as (wlo & swlen & Hwlo & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[_ CE]|[[KB' _]|[KS _]]]); cbn [w_kind w_lo] in *;
    [| unfold K_BLOCK, K_STACK in KB'; lia | unfold K_SUB, K_STACK in KS; lia].
  assert (Elo : bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + loZ r1).
  { rewrite den_VP. destruct (okey_sound _ _ Hwlo) as [EK _]. unfold loZ in *. rewrite <- EK. apply Z.mod_small. unfold two64. lia. }
  rewrite Elo in CE. cbn [aw_ceiling AWI] in CE.

  destruct (nonstack_windows_In E nw_ rest _ kb wlen CtrLib.K_BLOCK NW ltac:(left; reflexivity)) as (Kb0 & Kb1 & _ & INWb).
  pose proof (proj1 (Forall_forall _ _) WF _ INWb) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
    [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
  assert (Kb0' : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
  set (Db := bv_unsigned (ev E kb)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  destruct (aw_blocks_okI _ _ _ _ _ (proj1 HA) BLB) as (B0 & B1 & B2 & _ & BIMGX). cbn [w_iv w_lo w_len fst snd aw_ceiling AWI] in B0, B1, B2, BIMGX.
  assert (USER : forall a, Db <= a < Db + wlenZ -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None)
    by (intros a Ha; exact (aw_user_okI _ _ _ _ _ a (proj1 HA) BLB Ha)).
  destruct HA as ((s & LBf & PERM & RC & KRL & MT & CL & RP) & _).
  assert (BIMG : Db + wlenZ <= RIMG_LO \/ RIMG_HI <= Db).
  { assert (Hb' : In (Db, wlenZ) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact BLB]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & BI & _).
    unfold blk_addr, blk_size in BI, Eb. rewrite <- (f_equal fst Eb), <- (f_equal snd Eb) in BI || idtac. cbn [fst snd] in BI.
    injection Eb as E1 E2. rewrite E1, E2 in BI. exact BI. }

  set (Xz := bv_unsigned (den E X)). set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)).
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. rewrite bv_modulus_64 in XR. fold Xz in XR.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. rewrite bv_modulus_64 in WLR. fold wlenZ in WLR.
  apply (known_leu_sound E _ _ _ Hfs) in LEX. fold Xz wlenZ in LEX.
  apply (known_leu_sound E _ _ _ Hfs) in LEn. rewrite den_sv_alu in LEn. cbn [alu64 alu] in LEn. rewrite bv_sub_unsigned in LEn. fold nZ Xz wlenZ in LEn.
  assert (SUM : Xz + nZ <= wlenZ).
  { unfold bv_wrap in LEn. rewrite bv_modulus_64 in LEn. rewrite Z.mod_small in LEn; unfold W64.two64 in *; lia. }
  pose proof (known_eq_sound E _ _ _ Hfs EQoff) as Eoff. pose proof (known_eq_sound E _ _ _ Hfs EQn) as En.

  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo CtrB.RSTAGE_ID _ (so_ops _ _ _ _ _ _ HS) F3) as H3. cbn [map] in H3.
  destruct (OPS3_bytes E (den E off) (den E n') (ms_mem ms) mo HPB H3) as [N64K BY3]. rewrite En in N64K, BY3. fold nZ in N64K, BY3.
  rewrite Eoff in BY3. fold Xz in BY3.
  set (S := to_Z RS) in *. set (D := Db + Xz).
  set (src := map (fun i => nth (Z.to_nat Xz + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))).
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  assert (SRC : bytes_at rsegs (ms_mem ms) S src).
  { pose proof two64_eq as T64'. apply CopyFX.bytes_at_of_rb; [lia| rewrite LEN, Z2Nat.id by lia; lia|]. rewrite LEN, Z2Nat.id by lia.
    intros j Hj. unfold rb. rewrite (BY3 j) by lia. f_equal. subst src.
    rewrite nth_map_seq by lia. cbn beta. f_equal. rewrite <- Z2Nat.inj_add by lia. reflexivity. }

  pose proof two64_eq as T64. pose proof alloc_ceiling_lt64 as C64.
  destruct (CopyFX.rw_cells_of_views rsegs (ms_mem ms) D (Z.to_nat nZ) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold D; lia)) as (junk & LJ & DST).
  { intros j Hj. rewrite Z2Nat.id in Hj by lia. destruct (USER (D + j) ltac:(unfold D; lia)) as [M1 NS1]. split.
    - unfold rb. destruct (ms_mem ms (Z_to_bv 64 (D + j))); [discriminate| exfalso; exact (M1 eq_refl)].
    - unfold wb, wview. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold D; lia). rewrite NS1.
      destruct (ms_mem ms (Z_to_bv 64 (D + j))); [reflexivity| exfalso; exact (M1 eq_refl)]. }
  assert (SEP : S + nZ <= D \/ D + nZ <= S) by (unfold D, RIMG_LO, RIMG_HI in *; lia).

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, (sym_offset_sound E (s_regs st) _ kb X DOFF). apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold Db Xz. unfold D.
    rewrite (bv_wrap_small 64 (Db + Xz)) by (rewrite bv_modulus_64; lia). reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR, HX11, den_wlit; reflexivity).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. fold nsv. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrB.rstage_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(unfold D; lia) ltac:(unfold S in *; lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (EHI : hiZ E rgb' = Xz + nZ).
  { unfold hiZ, rgb'. cbn [Mem.rg_hi]. unfold hi', CtrB.new_hi.
    assert (DEF : bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
    { rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned. fold Xz nZ. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold W64.two64. lia. }
    destruct nsv as [| |[] sz X'| | | | | | | |]; try exact DEF.
    destruct (known_eq (s_facts st) X' X) eqn:KQ; [| exact DEF].
    apply (known_eq_sound E _ _ _ Hfs) in KQ.
    unfold nZ. cbn [den alu64 alu]. rewrite KQ. rewrite bv_sub_unsigned. fold Xz. pose proof (bv_unsigned_in_range 64 (den E sz)) as SR. rewrite bv_modulus_64 in SR.
    unfold bv_wrap. rewrite bv_modulus_64.

    unfold nZ in SUM. cbn [den alu64 alu] in SUM. rewrite KQ, bv_sub_unsigned in SUM. fold Xz in SUM. unfold bv_wrap in SUM. rewrite bv_modulus_64 in SUM.
    destruct (Z_lt_le_dec (bv_unsigned (den E sz)) Xz) as [LT|GE].
    - rewrite (Z.mod_small_iff) in SUM || idtac.
      replace ((bv_unsigned (den E sz) - Xz) mod W64.two64) with (bv_unsigned (den E sz) - Xz + W64.two64) in *
        by (first [symmetry; apply (Z.mod_unique_pos _ _ (-1)) | apply (Z.mod_unique_pos _ _ (-1))]; unfold W64.two64 in *; lia). unfold W64.two64 in *. lia.
    - rewrite Z.mod_small by (unfold W64.two64 in *; lia). lia. }
  assert (BLK : forall a, Db <= a < Db + wlenZ -> ms_mem ms (Z_to_bv 64 a) <> None /\ M' (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None).
  { intros a Ha. destruct (USER a Ha) as [M1 NS1]. split; [exact M1|]. split; [exact (OM _ M1)| exact NS1]. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kb rgb').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EL : loZ rgb' = 0) by reflexivity.
    constructor; rewrite ?EHI, ?EL; fold Db.
    - cbn. exact I.
    - intros _. pose proof alloc_ceiling_lt64. unfold W64.two64. lia.
    - intros _ a Ha. destruct (BLK a ltac:(lia)) as (M1 & M2 & NS1). split; [| split; [| exact NS1]].
      + unfold rb. destruct (M' (Z_to_bv 64 a)); [discriminate| exfalso; exact (M2 eq_refl)].
      + intros _. unfold wb, wview. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; pose proof alloc_ceiling_lt64; unfold W64.two64; lia). rewrite NS1.
        destruct (M' (Z_to_bv 64 a)); [reflexivity| exfalso; exact (M2 eq_refl)].
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kb0'). unfold bg_byte. cbn [rgb' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      destruct (Z_lt_le_dec o Xz) as [LT|GE].
      +
        apply orb_prop in PRE. destruct PRE as [PRE|X0].
        2:{ apply (known_eq_sound E _ _ _ Hfs) in X0. exfalso. unfold Xz in LT. rewrite X0, unsigned_VL in LT. change (w2Z wzero) with 0 in LT. lia. }
        apply andb_prop in PRE as [BGP HIP]. destruct (Mem.rg_bg rgb) as [| | | |j sh] eqn:BGB; try discriminate BGP.
        apply andb_prop in BGP as [J4 SH0]. apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH0. subst j sh.
        apply (known_eq_sound E _ _ _ Hfs) in HIP.
        pose proof (ro_bg _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HS kb rgb Hkb) o ltac:(intros _; unfold loZ, hiZ; rewrite LOb, HIP; fold Xz; change (keyZ 0%uint63) with 0; lia)
                      ltac:(intros X1; rewrite Kb0' in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CBL in F; cbn in F; discriminate F)) as G.
        unfold bg_byte in G. rewrite BGB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G. fold Db in G.
        unfold rb in G |- *. rewrite (memcpy_frame _ _ D nZ MU (Db + o)) by (unfold D; lia). exact G.
      +
        rewrite MemFX.rb_mrd. replace (Db + o) with (D + Z.of_nat (Z.to_nat (o - Xz))) by (unfold D; lia). rewrite BY by lia.
        subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat (o - Xz)) (Z.to_nat nZ)); [|lia]. cbn [option_map].
        f_equal. f_equal. lia. }

  pose proof (stack_sound OPS E st ms mo 0%uint63 ksp (Mem.rg_lo r1) HS ltac:(vm_compute; reflexivity) SOK) as SSD.
  assert (ZONE : forall a, 0 <= a < two64 ->
            (Db + loZ rgb' <= a < Db + hiZ E rgb' \/ M' (Z_to_bv 64 a) <> ms_mem ms (Z_to_bv 64 a)) ->
            (forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
               ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
            /\ find_segment rsegs a 1 = None
            /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))))).
  { intros a Ha NC.
    assert (INB : Db <= a < Db + wlenZ).
    { destruct NC as [RG|CH]; [rewrite EHI in RG; change (loZ rgb') with 0 in RG; lia|].
      destruct (Z_lt_le_dec a D) as [L1|G1]; [exfalso; apply CH; apply (memcpy_frame _ _ D nZ MU a Ha); lia|].
      destruct (Z_lt_le_dec a (D + nZ)) as [L2|G2]; [unfold D in *; lia| exfalso; apply CH; apply (memcpy_frame _ _ D nZ MU a Ha); lia]. }
    destruct (BLK a INB) as (M1 & M2 & NS1).
    split; [| split; [exact NS1|]].
    - intros k2 r2 Hk2 NK2 K20 RG2.
      destruct (Uint63.eqb k2 STACK_ID) eqn:Q1.
      + apply Uint63.eqb_correct in Q1. subst k2. rewrite Hr1 in Hk2. injection Hk2 as <-. lia.
      + apply Uint63.eqb_false_spec in Q1.
        assert (WL : win_lookup [(kb, wlen, CtrLib.K_BLOCK)] k2 = None).
        { cbn [win_lookup]. replace (PrimInt63.eqb kb k2) with false; [reflexivity|]. symmetry. apply Uint63.eqb_false_spec. congruence. }
        destruct (justified_above E st _ k2 r2 Hfs JU BST Hk2 ltac:(apply Uint63.eqb_false_spec; exact K20) Q1 WL) as [L2 SPk].
        rewrite SPE in SPk. rewrite L2 in RG2. lia.
    - intros o Ho FP. destruct (Uint63.eqb (op_id o) HEAP_ID) eqn:QH.
      + apply Uint63.eqb_correct in QH.
        assert (EA : op_args o = hargs0).
        { destruct (find_op_unique HEAP_ID (s_ops st) hargs0 Hf Hc) as (l1 & l2 & E0 & F1 & F2). rewrite E0 in Ho.
          apply in_app_iff in Ho as [Ho|[Ho|Ho]].
          - exfalso. pose proof (proj1 (Forall_forall _ _) F1 o Ho) as NI. unfold not_id in NI. rewrite QH, Uint63.eqb_refl in NI || (rewrite QH in NI; cbn in NI). discriminate NI.
          - subst o. reflexivity.
          - exfalso. pose proof (proj1 (Forall_forall _ _) F2 o Ho) as NI. unfold not_id in NI. rewrite QH in NI. rewrite (proj2 (Uint63.eqb_spec _ _) eq_refl) in NI. discriminate NI. }
        rewrite QH, EA, OPS_fp1 in FP. rewrite Eh in FP.
        apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md Aw nw rest nw_ T N L))) in FP as (_ & _ & NWS).
        apply NWS. unfold in_ws. apply in_ivs_In. exists (Db, wlenZ). split; [| unfold in_iv; cbn [fst snd]; lia].
        apply in_map_iff. exists (Win Db wlenZ K_BLOCK). split; [reflexivity| exact INWb].
      + apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [RNG _]. unfold RIMG_LO, RIMG_HI in BIMG. lia. }
  pose proof (MemFX.st_ok_based_replace rsegs OPS OPS_plain E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kb rgb rgb'
                ltac:(rewrite <- MSE; exact HS) Hkb Kb0' ZONE OM (minv_of_mem_inv M' MI') RO') as HS1.

  assert (HS2 : St.st_ok rsegs OPS E st2 (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { pose proof HS1 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
    unfold st2, st1, set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
    split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
    - apply (ops_hold_set_op OPS E E (s_ops st) CtrB.RSTAGE_ID [off; n'] _ M' M' mo mo F3 CNT Pops).
      + intros o _ _ H. exact H.
      + cbn [map]. rewrite den_sv_alu, den_VL. cbn [alu64 alu]. rewrite <- En. change (wbv wzero) with (Z_to_bv 64 0).
        exact (OPS3_advance (den E off) (den E n') (ms_mem ms) M' mo H3).
    - apply (ops_apart_set_op rsegs OPS E E (s_ops st) CtrB.RSTAGE_ID [off; n'] _ _ (IMap.add kb rgb' (s_regs st)) (s_priv st) F3 CNT Papart).
      + intros o a _ _ H FP. exact (H FP).
      + intros a FP. rewrite (OPS3_fp _ (map (den E) [off; n'])) in FP. exact (ops_apart_find rsegs OPS E (s_ops st) _ (s_priv st) CtrB.RSTAGE_ID [off; n'] a Papart F3 FP).
    -
      intros xa _. apply St.plain_cover. exact OPS_plain. }

  destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (VX : sv_vars_below (s_next st) X = true).
  { pose proof (rf_allb_get _ _ _ P1 X10) as V10. change (rf_get (s_rf st) X10) with (getr st X10) in V10.
    exact (sym_offset_vars_below _ _ _ _ _ V10 DOFF). }
  assert (Vn : sv_vars_below (s_next st) nsv = true) by (pose proof (rf_allb_get _ _ _ P1 X12) as V12; exact V12).
  assert (Voff : sv_vars_below (s_next st) off = true).
  { pose proof (forallb_In _ _ _ _ P6 (find_op_In _ _ _ F3)) as V3. cbn [op_args forallb] in V3. apply andb_prop in V3 as [V3 _]. exact V3. }
  assert (Vhi : sv_vars_below (s_next st) hi' = true).
  { unfold hi', CtrB.new_hi. destruct nsv as [| |[] sz X'| | | | | | | |]; try (apply MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]).
    destruct (known_eq (s_facts st) X' X); [| apply MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]].
    cbn [sv_vars_below] in Vn. apply andb_prop in Vn as [Vsz _]. exact Vsz. }
  assert (SVB2 : st_vars_below (s_next st) st2 = true).
  { assert (SVB1 : st_vars_below (s_next st) st1 = true).
    { apply (MemFX.st_vars_below_setregs (s_next st) st kb rgb rgb' BST SVB Hkb). unfold region_vars_below. cbn [rgb' Mem.rg_hi Mem.rg_cells]. rewrite Vhi. reflexivity. }
    unfold st_vars_below in SVB1 |- *. unfold st2, set_ops. cbn [s_rf s_ff s_resv s_regs s_facts s_ops].
    apply andb_prop in SVB1 as [SVB1 _]. rewrite SVB1. cbn [andb].
    destruct (find_op_unique CtrB.RSTAGE_ID (s_ops st) [off; n'] F3 CNT) as (l1 & l2 & E0 & F1 & F2).
    unfold st1, setregs. cbn [s_ops]. rewrite E0, (set_op_split CtrB.RSTAGE_ID _ l1 l2 [off; n'] F1).
    rewrite E0 in P6. rewrite forallb_app in P6 |- *. cbn [forallb op_args] in P6 |- *. apply andb_prop in P6 as [P6a P6b]. apply andb_prop in P6b as [_ P6c].
    rewrite P6a, P6c, (MemFX.sv_vars_below_alu (s_next st) ALU_ADD off nsv (or_introl eq_refl) Voff Vn). reflexivity. }
  assert (RV2 : s_resv st2 = RNone) by exact RV.
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st2 ERRNO r st3 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo
              HS2 RV2 SVB2 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
Qed.
End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMalloc_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFX.
Import HeapCore.TwinB RMallocG.TwinB MemcpyG.TwinB AW.TwinB HeapCtr.TwinB HeapCtrB.TwinB MemcpyCtr.TwinB.

Set Keyed Unification.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.
Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) ->
  0x53000 <= a < 0x8a000 /\ ~ ralloc_static a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable RS : int.
Hypothesis RS_range : 0x10000 <= to_Z RS /\ to_Z RS + 65536 <= 0x8a000.
Hypothesis OPS3_bytes : forall E (woff wn : word) m mo, PB (eb E) -> St.op_holds OPS CtrB.RSTAGE_ID [woff; wn] m mo ->
  bv_unsigned wn <= 65536 /\
  forall i, 0 <= i < bv_unsigned wn -> m (Z_to_bv 64 (to_Z RS + i)) = Some (nth (Z.to_nat (bv_unsigned woff + i)) (eb E 4%uint63) (Z_to_bv 8 0)).
Hypothesis OPS3_advance : forall (woff wn : word) m m' mo, St.op_holds OPS CtrB.RSTAGE_ID [woff; wn] m mo ->
  St.op_holds OPS CtrB.RSTAGE_ID [(woff + wn)%bv; Z_to_bv 64 0] m' mo.
Hypothesis OPS3_fp : forall args args', St.op_fp OPS CtrB.RSTAGE_ID args = St.op_fp OPS CtrB.RSTAGE_ID args'.

Lemma justified_above : forall E st wl k r, facts_hold E (s_facts st) -> regions_justified st wl = true -> IMap.bst (s_regs st) ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 -> k <> STACK_ID -> win_lookup wl k = None ->
  loZ r = 0 /\ bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k).
Proof.
  intros E st wl k r Hfs JU B Hk K0 K1 WL. unfold regions_justified in JU. cbv zeta in JU.
  pose proof (proj1 (IMap.forallb_spec _ _ B) JU k r Hk) as J.
  destruct (region_justified_inv E _ _ _ _ _ Hfs J K0 K1) as (L0 & [SJ|(len & kd & WL' & _)]); [|rewrite WL in WL'; discriminate WL'].
  split; [unfold loZ; rewrite L0; reflexivity| exact SJ].
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros A f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma sym_offset_vars_below : forall n R a k off,
  sv_vars_below n a = true -> CtrA.sym_offset R a = Some (k, off) -> sv_vars_below n off = true.
Proof.
  intros n R a k off V H. unfold CtrA.sym_offset in H.
  destruct a as [|k1 o1|op x y| | | | | | | |]; cbn [sym_addr_of] in H; try discriminate H.
  - destruct (weqb o1 wzero); injection H as _ <-; reflexivity.
  - cbn [sv_vars_below] in V. apply andb_prop in V as [Vx Vy].
    destruct op; try discriminate H.
    destruct x as [|kx ox| | | | | | | | |];
      [ | destruct (IMap.find kx R);
          [ injection H as _ <-; apply MemFX.sv_vars_below_alu; [left; reflexivity| exact Vy| reflexivity]
          | destruct y as [|ky oy| | | | | | | | |]; try discriminate H;
            destruct (IMap.find ky R); [injection H as _ <-; exact Vx| discriminate H] ] |..].
    all: destruct y as [|ky oy| | | | | | | | |]; try discriminate H;
         destruct (IMap.find ky R); [injection H as _ <-; apply MemFX.sv_vars_below_alu; [left; reflexivity| exact Vx| reflexivity]| discriminate H].
Qed.

Theorem rstage_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (CtrB.rstage_c rsegs ERRNO RS pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrB.rstage_c] in Happ. unfold CtrB.rstage_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X11) as [rsw| | | | | | | | | |] eqn:HX11; try discriminate.
  destruct (stack_ok st 0%uint63) as [[ksp klo1]|] eqn:SOK; [|discriminate].
  destruct (negb (weqb rsw (wlit RS)) || negb (Nat.eqb (count_op CtrB.RSTAGE_ID (s_ops st)) 1)) eqn:C; [discriminate|].
  apply orb_false_iff in C as [RSW CNT]. apply negb_false_iff in RSW. apply weqb_eq in RSW. subst rsw.
  apply negb_false_iff in CNT. apply Nat.eqb_eq in CNT.
  destruct (heap_windows st klo1) as [[hargs0 [|[[kw wlen] kd] [|]]]|] eqn:HW; try discriminate.
  destruct (sym_offset (s_regs st) (getr st X10)) as [[kb X]|] eqn:DOFF; [|discriminate].
  destruct (find_op CtrB.RSTAGE_ID (s_ops st)) as [[|off [|n' [|]]]|] eqn:F3; try discriminate.
  destruct (negb (PrimInt63.eqb kw kb) || negb (weqb kd CtrLib.K_BLOCK)) eqn:C; [discriminate|].
  apply orb_false_iff in C as [KW KD]. apply negb_false_iff in KW. apply Uint63.eqb_correct in KW. subst kw.
  apply negb_false_iff in KD. apply weqb_eq in KD. subst kd.
  destruct (IMap.find kb (s_regs st)) as [rgb|] eqn:Hkb; [|discriminate].
  destruct (Mem.rg_cells rgb) eqn:CBL; [|discriminate].
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (hi' := CtrB.new_hi (s_facts st) X (getr st X12)) in Happ.
  set (rgb' := Mem.Region 0%uint63 hi' true (Mem.BGBlob 4%uint63 0%uint63) IMap.empty) in Happ.
  set (st1 := setregs st (IMap.add kb rgb' (s_regs st))) in Happ.
  set (st2 := set_ops st1 (set_op CtrB.RSTAGE_ID [sv_alu ALU_ADD off (getr st X12); VL wzero] (s_ops st1))) in Happ.
  destruct (havoc_errno rsegs ERRNO (clobber st2)) as [st3|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 LEn]. apply andb_prop in C2 as [C2 LEX]. apply andb_prop in C2 as [C2 EQn]. apply andb_prop in C2 as [C2 EQoff].
  apply andb_prop in C2 as [C2 Wb]. apply andb_prop in C2 as [PRE LOb]. apply Uint63.eqb_correct in LOb.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as EZ0. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  destruct (stack_sound OPS E st ms mo 0%uint63 ksp klo1 HS ltac:(vm_compute; reflexivity) SOK)
    as (spoff & r1 & HX2 & Hr1 & W1 & BG1 & Hksp & -> & K16 & KNEG & SPE & LO0 & ROOM & HI1 & STK). change (to_Z 0%uint63) with 0 in ROOM.
  destruct (heap_windows_inv st (Mem.rg_lo r1) hargs0 _ HW) as (Hf & Hc & nw_ & md & Aw & nw & rest & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite Eh, (decode_hargs E md Aw nw rest nw_ T N L) in D. injection D as <- <- <- <-.

  destruct (stack_window_In E nw_ rest (Mem.rg_lo r1) SW) as (wlo & swlen & Hwlo & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[_ CE]|[[KB' _]|[KS _]]]); cbn [w_kind w_lo] in *;
    [| unfold K_BLOCK, K_STACK in KB'; lia | unfold K_SUB, K_STACK in KS; lia].
  assert (Elo : bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + loZ r1).
  { rewrite den_VP. destruct (okey_sound _ _ Hwlo) as [EK _]. unfold loZ in *. rewrite <- EK. apply Z.mod_small. unfold two64. lia. }
  rewrite Elo in CE. cbn [aw_ceiling AWI] in CE.

  destruct (nonstack_windows_In E nw_ rest _ kb wlen CtrLib.K_BLOCK NW ltac:(left; reflexivity)) as (Kb0 & Kb1 & _ & INWb).
  pose proof (proj1 (Forall_forall _ _) WF _ INWb) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
    [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
  assert (Kb0' : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
  set (Db := bv_unsigned (ev E kb)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  destruct (aw_blocks_okI _ _ _ _ _ (proj1 HA) BLB) as (B0 & B1 & B2 & _ & BIMGX). cbn [w_iv w_lo w_len fst snd aw_ceiling AWI] in B0, B1, B2, BIMGX.
  assert (USER : forall a, Db <= a < Db + wlenZ -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None)
    by (intros a Ha; exact (aw_user_okI _ _ _ _ _ a (proj1 HA) BLB Ha)).
  destruct HA as ((s & LBf & PERM & RC & KRL & MT & CL & RP) & _).
  assert (BIMG : Db + wlenZ <= RIMG_LO \/ RIMG_HI <= Db).
  { assert (Hb' : In (Db, wlenZ) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact BLB]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & BI & _).
    unfold blk_addr, blk_size in BI, Eb. rewrite <- (f_equal fst Eb), <- (f_equal snd Eb) in BI || idtac. cbn [fst snd] in BI.
    injection Eb as E1 E2. rewrite E1, E2 in BI. exact BI. }

  set (Xz := bv_unsigned (den E X)). set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)).
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. rewrite bv_modulus_64 in XR. fold Xz in XR.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NR. rewrite bv_modulus_64 in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. rewrite bv_modulus_64 in WLR. fold wlenZ in WLR.
  apply (known_leu_sound E _ _ _ Hfs) in LEX. fold Xz wlenZ in LEX.
  apply (known_leu_sound E _ _ _ Hfs) in LEn. rewrite den_sv_alu in LEn. cbn [alu64 alu] in LEn. rewrite bv_sub_unsigned in LEn. fold nZ Xz wlenZ in LEn.
  assert (SUM : Xz + nZ <= wlenZ).
  { unfold bv_wrap in LEn. rewrite bv_modulus_64 in LEn. rewrite Z.mod_small in LEn; unfold W64.two64 in *; lia. }
  pose proof (known_eq_sound E _ _ _ Hfs EQoff) as Eoff. pose proof (known_eq_sound E _ _ _ Hfs EQn) as En.

  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo CtrB.RSTAGE_ID _ (so_ops _ _ _ _ _ _ HS) F3) as H3. cbn [map] in H3.
  destruct (OPS3_bytes E (den E off) (den E n') (ms_mem ms) mo HPB H3) as [N64K BY3]. rewrite En in N64K, BY3. fold nZ in N64K, BY3.
  rewrite Eoff in BY3. fold Xz in BY3.
  set (S := to_Z RS) in *. set (D := Db + Xz).
  set (src := map (fun i => nth (Z.to_nat Xz + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat nZ))).
  assert (LEN : length src = Z.to_nat nZ) by (subst src; apply MemFX.blob_slice_length).
  assert (SRC : bytes_at rsegs (ms_mem ms) S src).
  { pose proof two64_eq as T64'. apply CopyFX.bytes_at_of_rb; [lia| rewrite LEN, Z2Nat.id by lia; lia|]. rewrite LEN, Z2Nat.id by lia.
    intros j Hj. unfold rb. rewrite (BY3 j) by lia. f_equal. subst src.
    rewrite nth_map_seq by lia. cbn beta. f_equal. rewrite <- Z2Nat.inj_add by lia. reflexivity. }

  pose proof two64_eq as T64. pose proof alloc_ceiling_lt64 as C64.
  destruct (CopyFX.rw_cells_of_views rsegs (ms_mem ms) D (Z.to_nat nZ) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold D; lia)) as (junk & LJ & DST).
  { intros j Hj. rewrite Z2Nat.id in Hj by lia. destruct (USER (D + j) ltac:(unfold D; lia)) as [M1 NS1]. split.
    - unfold rb. destruct (ms_mem ms (Z_to_bv 64 (D + j))); [discriminate| exfalso; exact (M1 eq_refl)].
    - unfold wb, wview. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold D; lia). rewrite NS1.
      destruct (ms_mem ms (Z_to_bv 64 (D + j))); [reflexivity| exfalso; exact (M1 eq_refl)]. }
  assert (SEP : S + nZ <= D \/ D + nZ <= S) by (unfold D, RIMG_LO, RIMG_HI in *; lia).

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { rewrite <- reg_of_X10, GR, (sym_offset_sound E (s_regs st) _ kb X DOFF). apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold Db Xz. unfold D.
    rewrite (bv_wrap_small 64 (Db + Xz)) by (rewrite bv_modulus_64; lia). reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR, HX11, den_wlit; reflexivity).
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 nZ).
  { rewrite <- reg_of_X12, GR. fold nsv. subst nZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrB.rstage_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S nZ src junk K A0 A1 A2
           ltac:(unfold D; lia) ltac:(unfold S in *; lia) ltac:(lia) RA1 SRC LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (EHI : hiZ E rgb' = Xz + nZ).
  { unfold hiZ, rgb'. cbn [Mem.rg_hi]. unfold hi', CtrB.new_hi.
    assert (DEF : bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
    { rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned. fold Xz nZ. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold W64.two64. lia. }
    destruct nsv as [| |[] sz X'| | | | | | | |]; try exact DEF.
    destruct (known_eq (s_facts st) X' X) eqn:KQ; [| exact DEF].
    apply (known_eq_sound E _ _ _ Hfs) in KQ.
    unfold nZ. cbn [den alu64 alu]. rewrite KQ. rewrite bv_sub_unsigned. fold Xz. pose proof (bv_unsigned_in_range 64 (den E sz)) as SR. rewrite bv_modulus_64 in SR.
    unfold bv_wrap. rewrite bv_modulus_64.

    unfold nZ in SUM. cbn [den alu64 alu] in SUM. rewrite KQ, bv_sub_unsigned in SUM. fold Xz in SUM. unfold bv_wrap in SUM. rewrite bv_modulus_64 in SUM.
    destruct (Z_lt_le_dec (bv_unsigned (den E sz)) Xz) as [LT|GE].
    - rewrite (Z.mod_small_iff) in SUM || idtac.
      replace ((bv_unsigned (den E sz) - Xz) mod W64.two64) with (bv_unsigned (den E sz) - Xz + W64.two64) in *
        by (first [symmetry; apply (Z.mod_unique_pos _ _ (-1)) | apply (Z.mod_unique_pos _ _ (-1))]; unfold W64.two64 in *; lia). unfold W64.two64 in *. lia.
    - rewrite Z.mod_small by (unfold W64.two64 in *; lia). lia. }
  assert (BLK : forall a, Db <= a < Db + wlenZ -> ms_mem ms (Z_to_bv 64 a) <> None /\ M' (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None).
  { intros a Ha. destruct (USER a Ha) as [M1 NS1]. split; [exact M1|]. split; [exact (OM _ M1)| exact NS1]. }
  assert (RO' : St.region_ok rsegs (s_priv st) E M' kb rgb').
  { destruct RW as [[CW BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    assert (EL : loZ rgb' = 0) by reflexivity.
    constructor; rewrite ?EHI, ?EL; fold Db.
    - cbn. exact I.
    - intros _. pose proof alloc_ceiling_lt64. unfold W64.two64. lia.
    - intros _ a Ha. destruct (BLK a ltac:(lia)) as (M1 & M2 & NS1). split; [| split; [| exact NS1]].
      + unfold rb. destruct (M' (Z_to_bv 64 a)); [discriminate| exfalso; exact (M2 eq_refl)].
      + intros _. unfold wb, wview. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; pose proof alloc_ceiling_lt64; unfold W64.two64; lia). rewrite NS1.
        destruct (M' (Z_to_bv 64 a)); [reflexivity| exfalso; exact (M2 eq_refl)].
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kb0'). unfold bg_byte. cbn [rgb' Mem.rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      destruct (Z_lt_le_dec o Xz) as [LT|GE].
      +
        apply orb_prop in PRE. destruct PRE as [PRE|X0].
        2:{ apply (known_eq_sound E _ _ _ Hfs) in X0. exfalso. unfold Xz in LT. rewrite X0, unsigned_VL in LT. change (w2Z wzero) with 0 in LT. lia. }
        apply andb_prop in PRE as [BGP HIP]. destruct (Mem.rg_bg rgb) as [| | | |j sh] eqn:BGB; try discriminate BGP.
        apply andb_prop in BGP as [J4 SH0]. apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH0. subst j sh.
        apply (known_eq_sound E _ _ _ Hfs) in HIP.
        pose proof (ro_bg _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HS kb rgb Hkb) o ltac:(intros _; unfold loZ, hiZ; rewrite LOb, HIP; fold Xz; change (keyZ 0%uint63) with 0; lia)
                      ltac:(intros X1; rewrite Kb0' in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CBL in F; cbn in F; discriminate F)) as G.
        unfold bg_byte in G. rewrite BGB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G. fold Db in G.
        unfold rb in G |- *. rewrite (memcpy_frame _ _ D nZ MU (Db + o)) by (unfold D; lia). exact G.
      +
        rewrite MemFX.rb_mrd. replace (Db + o) with (D + Z.of_nat (Z.to_nat (o - Xz))) by (unfold D; lia). rewrite BY by lia.
        subst src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat (o - Xz)) (Z.to_nat nZ)); [|lia]. cbn [option_map].
        f_equal. f_equal. lia. }

  pose proof (stack_sound OPS E st ms mo 0%uint63 ksp (Mem.rg_lo r1) HS ltac:(vm_compute; reflexivity) SOK) as SSD.
  assert (ZONE : forall a, 0 <= a < two64 ->
            (Db + loZ rgb' <= a < Db + hiZ E rgb' \/ M' (Z_to_bv 64 a) <> ms_mem ms (Z_to_bv 64 a)) ->
            (forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
               ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
            /\ find_segment rsegs a 1 = None
            /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))))).
  { intros a Ha NC.
    assert (INB : Db <= a < Db + wlenZ).
    { destruct NC as [RG|CH]; [rewrite EHI in RG; change (loZ rgb') with 0 in RG; lia|].
      destruct (Z_lt_le_dec a D) as [L1|G1]; [exfalso; apply CH; apply (memcpy_frame _ _ D nZ MU a Ha); lia|].
      destruct (Z_lt_le_dec a (D + nZ)) as [L2|G2]; [unfold D in *; lia| exfalso; apply CH; apply (memcpy_frame _ _ D nZ MU a Ha); lia]. }
    destruct (BLK a INB) as (M1 & M2 & NS1).
    split; [| split; [exact NS1|]].
    - intros k2 r2 Hk2 NK2 K20 RG2.
      destruct (Uint63.eqb k2 STACK_ID) eqn:Q1.
      + apply Uint63.eqb_correct in Q1. subst k2. rewrite Hr1 in Hk2. injection Hk2 as <-. lia.
      + apply Uint63.eqb_false_spec in Q1.
        assert (WL : win_lookup [(kb, wlen, CtrLib.K_BLOCK)] k2 = None).
        { cbn [win_lookup]. replace (PrimInt63.eqb kb k2) with false; [reflexivity|]. symmetry. apply Uint63.eqb_false_spec. congruence. }
        destruct (justified_above E st _ k2 r2 Hfs JU BST Hk2 ltac:(apply Uint63.eqb_false_spec; exact K20) Q1 WL) as [L2 SPk].
        rewrite SPE in SPk. rewrite L2 in RG2. lia.
    - intros o Ho FP. destruct (Uint63.eqb (op_id o) HEAP_ID) eqn:QH.
      + apply Uint63.eqb_correct in QH.
        assert (EA : op_args o = hargs0).
        { destruct (find_op_unique HEAP_ID (s_ops st) hargs0 Hf Hc) as (l1 & l2 & E0 & F1 & F2). rewrite E0 in Ho.
          apply in_app_iff in Ho as [Ho|[Ho|Ho]].
          - exfalso. pose proof (proj1 (Forall_forall _ _) F1 o Ho) as NI. unfold not_id in NI. rewrite QH, Uint63.eqb_refl in NI || (rewrite QH in NI; cbn in NI). discriminate NI.
          - subst o. reflexivity.
          - exfalso. pose proof (proj1 (Forall_forall _ _) F2 o Ho) as NI. unfold not_id in NI. rewrite QH in NI. rewrite (proj2 (Uint63.eqb_spec _ _) eq_refl) in NI. discriminate NI. }
        rewrite QH, EA, OPS_fp1 in FP. rewrite Eh in FP.
        apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md Aw nw rest nw_ T N L))) in FP as (_ & _ & NWS).
        apply NWS. unfold in_ws. apply in_ivs_In. exists (Db, wlenZ). split; [| unfold in_iv; cbn [fst snd]; lia].
        apply in_map_iff. exists (Win Db wlenZ K_BLOCK). split; [reflexivity| exact INWb].
      + apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [RNG _]. unfold RIMG_LO, RIMG_HI in BIMG. lia. }
  pose proof (MemFX.st_ok_based_replace rsegs OPS OPS_plain E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kb rgb rgb'
                ltac:(rewrite <- MSE; exact HS) Hkb Kb0' ZONE OM (minv_of_mem_inv M' MI') RO') as HS1.

  assert (HS2 : St.st_ok rsegs OPS E st2 (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { pose proof HS1 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
    unfold st2, st1, set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
    split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
    - apply (ops_hold_set_op OPS E E (s_ops st) CtrB.RSTAGE_ID [off; n'] _ M' M' mo mo F3 CNT Pops).
      + intros o _ _ H. exact H.
      + cbn [map]. rewrite den_sv_alu, den_VL. cbn [alu64 alu]. rewrite <- En. change (wbv wzero) with (Z_to_bv 64 0).
        exact (OPS3_advance (den E off) (den E n') (ms_mem ms) M' mo H3).
    - apply (ops_apart_set_op rsegs OPS E E (s_ops st) CtrB.RSTAGE_ID [off; n'] _ _ (IMap.add kb rgb' (s_regs st)) (s_priv st) F3 CNT Papart).
      + intros o a _ _ H FP. exact (H FP).
      + intros a FP. rewrite (OPS3_fp _ (map (den E) [off; n'])) in FP. exact (ops_apart_find rsegs OPS E (s_ops st) _ (s_priv st) CtrB.RSTAGE_ID [off; n'] a Papart F3 FP).
    -
      intros xa _. apply St.plain_cover. exact OPS_plain. }

  destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (VX : sv_vars_below (s_next st) X = true).
  { pose proof (rf_allb_get _ _ _ P1 X10) as V10. change (rf_get (s_rf st) X10) with (getr st X10) in V10.
    exact (sym_offset_vars_below _ _ _ _ _ V10 DOFF). }
  assert (Vn : sv_vars_below (s_next st) nsv = true) by (pose proof (rf_allb_get _ _ _ P1 X12) as V12; exact V12).
  assert (Voff : sv_vars_below (s_next st) off = true).
  { pose proof (forallb_In _ _ _ _ P6 (find_op_In _ _ _ F3)) as V3. cbn [op_args forallb] in V3. apply andb_prop in V3 as [V3 _]. exact V3. }
  assert (Vhi : sv_vars_below (s_next st) hi' = true).
  { unfold hi', CtrB.new_hi. destruct nsv as [| |[] sz X'| | | | | | | |]; try (apply MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]).
    destruct (known_eq (s_facts st) X' X); [| apply MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]].
    cbn [sv_vars_below] in Vn. apply andb_prop in Vn as [Vsz _]. exact Vsz. }
  assert (SVB2 : st_vars_below (s_next st) st2 = true).
  { assert (SVB1 : st_vars_below (s_next st) st1 = true).
    { apply (MemFX.st_vars_below_setregs (s_next st) st kb rgb rgb' BST SVB Hkb). unfold region_vars_below. cbn [rgb' Mem.rg_hi Mem.rg_cells]. rewrite Vhi. reflexivity. }
    unfold st_vars_below in SVB1 |- *. unfold st2, set_ops. cbn [s_rf s_ff s_resv s_regs s_facts s_ops].
    apply andb_prop in SVB1 as [SVB1 _]. rewrite SVB1. cbn [andb].
    destruct (find_op_unique CtrB.RSTAGE_ID (s_ops st) [off; n'] F3 CNT) as (l1 & l2 & E0 & F1 & F2).
    unfold st1, setregs. cbn [s_ops]. rewrite E0, (set_op_split CtrB.RSTAGE_ID _ l1 l2 [off; n'] F1).
    rewrite E0 in P6. rewrite forallb_app in P6 |- *. cbn [forallb op_args] in P6 |- *. apply andb_prop in P6 as [P6a P6b]. apply andb_prop in P6b as [_ P6c].
    rewrite P6a, P6c, (MemFX.sv_vars_below_alu (s_next st) ALU_ADD off nsv (or_introl eq_refl) Voff Vn). reflexivity. }
  assert (RV2 : s_resv st2 = RNone) by exact RV.
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st2 ERRNO r st3 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo
              HS2 RV2 SVB2 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
Qed.
End CEIL.
End TwinB.
