(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundAlu PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkStack PkPeek CapLen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkMid.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepA PlanS HeapOp UB UG TR PK PKL PkStack.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkShrink.
Import PkMid.PkMid.

Definition PCMAXi : int := 4611686018427387840%uint63.

Section WithSegs.
Variable segs : list Segment.

Definition instr_at (pc : int) (k : int) : option instr :=
  match fetch_word segs (Z_to_bv 64 (to_Z (PrimInt63.add pc k))) with
  | Some w => if is_ecall w then None else
              match decode_any w with Some (i, z) => if Z.eqb z 4 then Some i else None | None => None end
  | None => None
  end.

Definition isr (r : reg) (x : r5) : bool := match r5_of_reg r with Some y => r5_eqb y x | None => false end.

Definition code_ok (pc : int) : bool :=
  match instr_at pc 0%uint63, instr_at pc 4%uint63, instr_at pc 8%uint63, instr_at pc 12%uint63,
        instr_at pc 16%uint63, instr_at pc 20%uint63, instr_at pc 24%uint63, instr_at pc 28%uint63 with
  | Some (Branch BC_EQ r5a r7a _), Some (Branch BC_LTU r1b r4b _), Some (OpImm ALU_ADD r7c r0c imm), Some (Mul M_MULH r2d r2d' r7d),
    Some (ShiftImm ALU_SRA r6e r6e' sh), Some (Op ALU_XOR r2f r2f' r6f), Some (Op ALU_SLTU r2g r0g r2g'), Some (Branch BC_NE r2h r0h _) =>
      isr r5a X15 && isr r7a X17 && isr r1b X11 && isr r4b X14 && isr r7c X17 && isr r0c X0 && Z.eqb (bv_unsigned (sext 64 imm)) 24
      && isr r2d X12 && isr r2d' X12 && isr r7d X17 && isr r6e X16 && isr r6e' X16 && Z.eqb (bv_unsigned sh) 63
      && isr r2f X12 && isr r2f' X12 && isr r6f X16 && isr r2g X12 && isr r0g X0 && isr r2g' X12 && isr r2h X12 && isr r0h X0
  | _, _, _, _, _, _, _, _ => false
  end.

Definition a5_ok (fs : list fact) (v b4 : sv) : bool :=
  match v with
  | VL w => weqb w wone
  | VAlu ALU_SLTU (VL z) y => weqb z wzero && same fs y b4
  | _ => false
  end.

Definition a7_ok (v a1 : sv) : bool :=
  match v with
  | VL w => weqb w wzero
  | VAlu ALU_SLTU y (VL o) => weqb o wone && sv_eqb y a1
  | _ => false
  end.

Definition a6_ok (v c : sv) : bool :=
  match v with
  | VAlu ALU_SUB (VAlu ALU_SLL x (VL s5)) (VAlu ALU_SLL x' (VL s3)) => weqb s5 w5 && weqb s3 w3 && sv_eqb x c && sv_eqb x' c
  | _ => false
  end.

Definition a1_ok (fs : list fact) (v a6 b : sv) : bool :=
  match v with
  | VAlu ALU_ADD p q => (sv_eqb p a6 && same fs q b) || (sv_eqb q a6 && same fs p b)
  | _ => false
  end.

Definition pkshrink_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match cnt_of2 fs (getr st X12) with
  | Some (e, b) =>
      if PrimInt63.ltb (s_pc st) PCMAXi
         && (if ghost_ok st b e then true else has_vd fs b e)
         && a6_ok (getr st X16) (getr st X12)
         && a1_ok fs (getr st X11) (getr st X16) b
         && same fs (getr st X14) b
         && Step.dec_false (decide_eq0 fs (getr st X14))
         && a5_ok fs (getr st X15) (getr st X14)
         && a7_ok (getr st X17) (getr st X11)
         && code_ok (s_pc st)
      then Some [setpc (setr (setr (setr (setr st X11 e) X12 (VL wzero)) X16 (VL wzero)) X17 (VL W24)) (PrimInt63.add (s_pc st) 32%uint63)]
      else None
  | None => None
  end.

Definition pkshrink_contract (pc : int) : contract := Contract pc pkshrink_apply.
End WithSegs.

Lemma cnt_word : forall (wb we : word) n, bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  bv_unsigned (mul_div M_MUL (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) (wbv INV3)) = n.
Proof.
  intros wb we n EQ RN. unfold CapLen.VD_MAXZ in RN.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  assert (SUBu : bv_unsigned (alu64 ALU_SUB we wb) = 24 * n).
  { cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) = 3 * n).
  { cbn [alu64 alu]. cbn [alu64 alu] in SUBu. rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 _) by (rewrite SUBu; unfold two63; lia).
    rewrite SUBu, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (24 * n) with (3 * n * 8) by lia. rewrite Z.div_mul by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  unfold mul_div. rewrite bv_mul_unsigned, SRAu, wbv_unsigned.
  replace (w2Z INV3) with 12297829382473034411 by (vm_compute; reflexivity).
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  replace (3 * n * 12297829382473034411) with (n + (2 * n) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma a6_word : forall (x : word) n, bv_unsigned x = n -> 0 <= n <= CapLen.VD_MAXZ ->
  bv_unsigned (alu64 ALU_SUB (alu64 ALU_SLL x (wbv w5)) (alu64 ALU_SLL x (wbv w3))) = 24 * n.
Proof.
  intros x n Xu RN. unfold CapLen.VD_MAXZ in RN.
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SH5 : bv_unsigned (bv_and (wbv w5) (Z_to_bv 64 63)) = 5) by (rewrite shamt6_bv; reflexivity).
  cbn [alu64 alu]. rewrite bv_sub_unsigned, !bv_shiftl_unsigned, SH3, SH5, Xu, !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  rewrite (Z.mod_small (n * 32)) by lia. rewrite (Z.mod_small (n * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mulh24_zero : forall (x : word) n, bv_unsigned x = n -> 0 <= n <= CapLen.VD_MAXZ ->
  mul_div M_MULH x (Z_to_bv 64 24) = Z_to_bv 64 0.
Proof.
  intros x n Xu RN. unfold CapLen.VD_MAXZ in RN. unfold mul_div, bv_mulhss.
  rewrite (bv_signed_small63 x) by (rewrite Xu; unfold two63; lia). rewrite Xu.
  replace (bv_signed (Z_to_bv 64 24)) with 24 by (vm_compute; reflexivity).
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sra63_zero : forall (y : word) n, bv_unsigned y = 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  alu64 ALU_SRA y (zext 64 (Z_to_bv 6 63)) = Z_to_bv 64 0.
Proof.
  intros y n Yu RN. unfold CapLen.VD_MAXZ in RN. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_ashiftr_unsigned.
  replace (bv_unsigned (bv_and (zext 64 (Z_to_bv 6 63)) (Z_to_bv 64 63))) with 63 by (vm_compute; reflexivity).
  rewrite (bv_signed_small63 y) by (rewrite Yu; unfold two63; lia). rewrite Yu, Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma pc_add_bv : forall pc k, PrimInt63.ltb pc PCMAXi = true -> 0 <= to_Z k <= 32 ->
  Z_to_bv 64 (to_Z (PrimInt63.add pc k)) = (Z_to_bv 64 (to_Z pc) + Z_to_bv 64 (to_Z k))%bv.
Proof.
  intros pc k H Hk. apply Uint63.ltb_spec in H. change (to_Z PCMAXi) with (2^62 - 64) in H.
  pose proof (Uint63.to_Z_bounded pc) as B. change wB with (2^63) in B.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. rewrite Uint63.add_spec.
  unfold bv_wrap, bv_modulus. change wB with (2^63). change (2 ^ Z.of_N 64) with (2^64).
  replace ((to_Z pc + to_Z k) mod 2 ^ 63) with (to_Z pc + to_Z k) by (symmetry; apply Z.mod_small; lia).
  rewrite (Z.mod_small (to_Z pc) (2^64)) by lia. rewrite (Z.mod_small (to_Z k) (2^64)) by lia. reflexivity.
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma isr_spec : forall r x, isr r x = true -> r = reg_of_r5 x.
Proof.
  intros r x H. unfold isr in H. destruct (r5_of_reg r) as [y|] eqn:Q; [|discriminate].
  apply r5_eqb_spec in H. subst y. symmetry. exact (reg_of_r5_of_reg _ _ Q).
Qed.

Lemma instr_at_spec : forall pc k i, instr_at segs pc k = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 (to_Z (PrimInt63.add pc k))) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros pc k i H. unfold instr_at in H.
  destruct (fetch_word segs _) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i' z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z. injection H as <-. exists w. auto.
Qed.

Ltac zlit := repeat match goal with |- context [Uint63.to_Z ?k] => is_constructor k || (let z := eval vm_compute in (Uint63.to_Z k) in change (Uint63.to_Z k) with z) end; lia.

Lemma rget_pc : forall v c r, rget (with_pc v c) r = rget c r.
Proof. intros v c r. destruct c. reflexivity. Qed.

Lemma rget_rset : forall rd wv c r, r5_eqb rd X0 = false ->
  rget (rset (reg_of_r5 rd) wv c) (reg_of_r5 r) = if r5_eqb r rd then wv else rget c (reg_of_r5 r).
Proof.
  intros rd wv c r Hrd. unfold rset. rewrite is_x0_reg_of_r5, Hrd. unfold rget. rewrite is_x0_reg_of_r5.
  destruct c as [cr cf cp cfc crv]. cbn [c_regs with_regs].
  destruct (r5_eqb r X0) eqn:RX.
  - apply r5_eqb_spec in RX. subst r. destruct (r5_eqb X0 rd) eqn:Q; [|reflexivity].
    apply r5_eqb_spec in Q. subst rd. discriminate Hrd.
  - apply reg_get_set.
Qed.

Lemma rget_x0 : forall c, rget c (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros c. unfold rget. rewrite is_x0_reg_of_r5. reflexivity. Qed.

Lemma pc_with_pc : forall v c, Sem.c_pc (with_pc v c) = v.
Proof. intros v c. destruct c. reflexivity. Qed.
Lemma pc_rset : forall r wv c, Sem.c_pc (rset r wv c) = Sem.c_pc c.
Proof. intros r wv c. unfold rset. destruct (is_x0 r); [reflexivity|]. destruct c. reflexivity. Qed.

Ltac r5lit := repeat match goal with |- context [r5_eqb ?a ?b] => is_constructor a; is_constructor b; let v := eval vm_compute in (r5_eqb a b) in change (r5_eqb a b) with v end; cbv iota.
Ltac creg := repeat (rewrite ?rget_pc, ?rget_rset, ?rget_x0 by reflexivity); r5lit.

Ltac dvar_in H :=
  lazymatch type of H with
  | (match ?c with _ => _ end) = true => destruct c; try discriminate H
  end.

Lemma code_ok_spec : forall pc, code_ok segs pc = true -> exists im0 im1 imm sh im7,
  instr_at segs pc 0%uint63 = Some (Branch BC_EQ (reg_of_r5 X15) (reg_of_r5 X17) im0) /\
  instr_at segs pc 4%uint63 = Some (Branch BC_LTU (reg_of_r5 X11) (reg_of_r5 X14) im1) /\
  instr_at segs pc 8%uint63 = Some (OpImm ALU_ADD (reg_of_r5 X17) (reg_of_r5 X0) imm) /\ bv_unsigned (sext 64 imm) = 24 /\
  instr_at segs pc 12%uint63 = Some (Mul M_MULH (reg_of_r5 X12) (reg_of_r5 X12) (reg_of_r5 X17)) /\
  instr_at segs pc 16%uint63 = Some (ShiftImm ALU_SRA (reg_of_r5 X16) (reg_of_r5 X16) sh) /\ bv_unsigned sh = 63 /\
  instr_at segs pc 20%uint63 = Some (Op ALU_XOR (reg_of_r5 X12) (reg_of_r5 X12) (reg_of_r5 X16)) /\
  instr_at segs pc 24%uint63 = Some (Op ALU_SLTU (reg_of_r5 X12) (reg_of_r5 X0) (reg_of_r5 X12)) /\
  instr_at segs pc 28%uint63 = Some (Branch BC_NE (reg_of_r5 X12) (reg_of_r5 X0) im7).
Proof.
  intros pc H. unfold code_ok in H.
  destruct (instr_at segs pc 0%uint63) as [i0|]; [|discriminate]. destruct i0; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 4%uint63) as [i1|]; [|discriminate]. destruct i1; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 8%uint63) as [i2|]; [|discriminate]. destruct i2; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 12%uint63) as [i3|]; [|discriminate]. destruct i3; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 16%uint63) as [i4|]; [|discriminate]. destruct i4; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 20%uint63) as [i5|]; [|discriminate]. destruct i5; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 24%uint63) as [i6|]; [|discriminate]. destruct i6; try discriminate H. dvar_in H.
  destruct (instr_at segs pc 28%uint63) as [i7|]; [|discriminate]. destruct i7; try discriminate H. dvar_in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with Q : isr ?r ?x = true |- _ => apply isr_spec in Q; subst r end.
  repeat match goal with Q : Z.eqb ?a ?b = true |- _ => apply Z.eqb_eq in Q end.
  eexists _, _, _, _, _. repeat split; try reflexivity; assumption.
Qed.

Lemma step_core : forall ms mo w i c',
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  (forall cc a n, ~ Acc.mem_acc i cc a n) ->
  Sem.exec (Z_to_bv 64 4) i (core_of ms) = EDone c' ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms mo = MachineOk (ms_upd ms c' (ms_mem ms), mo).
Proof.
  intros ms mo w i c' FW EC DEC NM EX SVC.
  apply (Acc.account_step_noacc segs ms w i _ mo FW EC DEC NM).
  rewrite (step_exec segs ms w i FW EC DEC), EX, interp_EDone. reflexivity.
Qed.

Lemma st_ok_core : forall E st ms model rf' (npci : int) (c' : core),
  st_ok segs OPS E st ms model ->
  rf_get rf' X0 = VL wzero ->
  (forall r, rget c' (reg_of_r5 r) = den E (rf_get rf' r)) ->
  c_fregs c' = ms_fregs ms -> c_fcsr c' = ms_fcsr ms -> c_resv c' = ms_resv ms -> Sem.c_pc c' = Z_to_bv 64 (to_Z npci) ->
  st_ok segs OPS E (SS npci rf' (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st))
        (ms_upd ms c' (ms_mem ms)) model.
Proof.
  intros E st ms model rf' npci c' HS X0' REGS FR FC RV PC.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct c' as [cr cf cp cfc crv]. cbn [c_fregs c_fcsr c_resv Sem.c_pc] in FR, FC, RV, PC. subst cf cfc crv cp.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next ms_upd c_regs c_fregs Sem.c_pc c_fcsr c_resv
                    ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]; try assumption; try reflexivity.
Qed.

Theorem pkshrink_sound : forall M_PC, contract_sound segs OPS MP PB (pkshrink_contract segs M_PC).
Proof.
  intros M_PC st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [pkshrink_contract c_apply] in HA. unfold pkshrink_apply in HA.
  destruct (cnt_of2 (s_facts st) (getr st X12)) as [[e b]|] eqn:CO; [|discriminate].
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end. injection HA as <-.
  apply andb_prop in C as [C CODE]. apply andb_prop in C as [C A7]. apply andb_prop in C as [C A5]. apply andb_prop in C as [C NZ].
  apply andb_prop in C as [C S14]. apply andb_prop in C as [C A1]. apply andb_prop in C as [C A6]. apply andb_prop in C as [PCB GO].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.

  assert (GEOM : exists n, bv_unsigned (den E e) = bv_unsigned (den E b) + 24 * n /\ 0 <= n <= CapLen.VD_MAXZ).
  { destruct (ghost_ok st b e) eqn:GOK; [exact (ghost_ok_geom segs IMGX AW CW OPS HOPS CW3 E st ms model b e HS GOK)|].
    exact (has_vd_geom E _ b e FH GO). }
  destruct GEOM as (n & GEO & RN).
  set (wb := den E b) in *. set (we := den E e) in *.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.

  assert (W12 : bv_unsigned (den E (getr st X12)) = n) by exact (cnt_of2_val E _ _ e b n FH CO GEO RN).
  assert (W16 : bv_unsigned (den E (getr st X16)) = 24 * n).
  { unfold a6_ok in A6. destruct (getr st X16) as [| |o1 y1 y2| | | | | | | |]; try discriminate A6. destruct o1; try discriminate A6.
    destruct y1 as [| |o2 x s5v| | | | | | | |]; try discriminate A6. destruct o2; try discriminate A6.
    destruct s5v as [s5| | | | | | | | | |]; try discriminate A6.
    destruct y2 as [| |o3 x' s3v| | | | | | | |]; try discriminate A6. destruct o3; try discriminate A6.
    destruct s3v as [s3| | | | | | | | | |]; try discriminate A6.
    apply andb_prop in A6 as [A6 E4]. apply andb_prop in A6 as [A6 E3]. apply andb_prop in A6 as [E1 E2].
    apply weqb_eq in E1. apply weqb_eq in E2. apply sv_eqb_eq in E3. apply sv_eqb_eq in E4. subst s5 s3 x x'.
    cbn [den]. apply (a6_word _ n W12 RN). }
  assert (W14 : den E (getr st X14) = wb) by exact (same_sound E _ _ _ FH S14).
  assert (W11 : den E (getr st X11) = we).
  { unfold a1_ok in A1. destruct (getr st X11) as [| |o1 p q| | | | | | | |]; try discriminate A1. destruct o1; try discriminate A1.
    assert (SUM : forall u v : word, bv_unsigned u = 24 * n -> v = wb -> alu64 ALU_ADD u v = we /\ alu64 ALU_ADD v u = we).
    { intros u v Hu ->. cbn [alu64 alu].
      assert (E1 : (u + wb)%bv = we).
      { apply bv_eq. rewrite bv_add_unsigned, Hu. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
      split; [exact E1|]. rewrite <- E1. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia. }
    apply orb_prop in A1 as [A1|A1]; apply andb_prop in A1 as [P Q].
    - apply sv_eqb_eq in P. subst p. apply (same_sound E _ _ _ FH) in Q.
      cbn [den]. fold wb in Q. exact (proj1 (SUM _ _ W16 Q)).
    - apply sv_eqb_eq in P. subst q. apply (same_sound E _ _ _ FH) in Q.
      cbn [den]. fold wb in Q. exact (proj2 (SUM _ _ W16 Q)). }
  assert (NZb : bv_unsigned wb <> 0).
  { unfold Step.dec_false in NZ. destruct (decide_eq0 (s_facts st) (getr st X14)) as [[|]|] eqn:D; try discriminate NZ.
    pose proof (decide_eq0_sound E (s_facts st) FH _ _ D) as Q. rewrite W14 in Q. unfold bv_eqb in Q.
    rewrite Z_to_bv_unsigned in Q. cbn in Q. destruct (Z.eqb_spec (bv_unsigned wb) (bv_wrap 64 0)); [discriminate|].
    change (bv_wrap 64 0) with 0 in n0. exact n0. }
  assert (W15 : den E (getr st X15) = Z_to_bv 64 1).
  { unfold a5_ok in A5. destruct (getr st X15) as [w| |o1 z y| | | | | | | |]; try discriminate A5.
    - apply weqb_eq in A5. subst w. cbn [den]. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned. reflexivity.
    - destruct o1; try discriminate A5. destruct z as [z| | | | | | | | | |]; try discriminate A5.
      apply andb_prop in A5 as [Ez Sy]. apply weqb_eq in Ez. subst z.
      apply (same_sound E _ _ _ FH) in Sy. cbn [den]. rewrite Sy, W14.
      cbn [alu64 alu]. unfold bv_ltu. rewrite wbv_unsigned. change (w2Z wzero) with 0.
      destruct (Z.ltb_spec 0 (bv_unsigned wb)); [reflexivity| lia]. }
  assert (W17 : den E (getr st X17) = Z_to_bv 64 0).
  { unfold a7_ok in A7. destruct (getr st X17) as [w| |o1 y ov| | | | | | | |]; try discriminate A7.
    - apply weqb_eq in A7. subst w. cbn [den]. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned. reflexivity.
    - destruct o1; try discriminate A7. destruct ov as [o| | | | | | | | | |]; try discriminate A7.
      apply andb_prop in A7 as [Eo Sy]. apply weqb_eq in Eo. subst o. apply sv_eqb_eq in Sy. subst y.
      cbn [den]. cbn [den] in W11. rewrite W11. cbn [alu64 alu]. unfold bv_ltu. rewrite wbv_unsigned. change (w2Z wone) with 1.
      destruct (Z.ltb_spec (bv_unsigned we) 1); [lia| reflexivity]. }

  destruct (code_ok_spec _ CODE) as (im0 & im1 & imm & sh & im7 & I0 & I1 & I2 & IMM & I3 & I4 & SH & I5 & I6 & I7).
  destruct (instr_at_spec _ _ _ I0) as (w0 & F0 & E0 & D0). destruct (instr_at_spec _ _ _ I1) as (w1 & F1 & E1 & D1).
  destruct (instr_at_spec _ _ _ I2) as (w2 & F2 & E2 & D2). destruct (instr_at_spec _ _ _ I3) as (w3' & F3 & E3 & D3).
  destruct (instr_at_spec _ _ _ I4) as (w4 & F4 & E4 & D4). destruct (instr_at_spec _ _ _ I5) as (w5' & F5 & E5 & D5).
  destruct (instr_at_spec _ _ _ I6) as (w6 & F6 & E6 & D6). destruct (instr_at_spec _ _ _ I7) as (w7 & F7 & E7 & D7).

  set (pc0 := s_pc st) in *.
  pose proof (so_pc _ _ _ _ _ _ HS) as MPC. pose proof (so_svc _ _ _ _ _ _ HS) as SVC.
  pose proof (so_regs _ _ _ _ _ _ HS) as REGS. fold (core_of ms) in REGS.
  set (c0 := core_of ms) in *.
  assert (R15 : rget c0 (reg_of_r5 X15) = Z_to_bv 64 1) by (rewrite REGS; exact W15).
  assert (R17 : rget c0 (reg_of_r5 X17) = Z_to_bv 64 0) by (rewrite REGS; exact W17).
  assert (R11 : rget c0 (reg_of_r5 X11) = we) by (rewrite REGS; exact W11).
  assert (R14 : rget c0 (reg_of_r5 X14) = wb) by (rewrite REGS; exact W14).
  assert (R12 : bv_unsigned (rget c0 (reg_of_r5 X12)) = n) by (rewrite REGS; exact W12).
  assert (R16 : bv_unsigned (rget c0 (reg_of_r5 X16)) = 24 * n) by (rewrite REGS; exact W16).

  assert (PC0B : to_Z pc0 < 2^62 - 64) by (pose proof PCB as PCB'; apply Uint63.ltb_spec in PCB'; exact PCB').
  pose proof (Uint63.to_Z_bounded pc0) as B0. change wB with (2^63) in B0.
  set (p := fun z : Z => Z_to_bv 64 (to_Z pc0 + z)).
  assert (PZ : forall k, 0 <= to_Z k <= 32 -> Z_to_bv 64 (to_Z (PrimInt63.add pc0 k)) = p (to_Z k)).
  { intros k Hk0. unfold p. f_equal. rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
  assert (P0 : p 0 = ms_pc_val ms) by (rewrite MPC; unfold p, pc0; f_equal; lia).
  assert (PSTEP : forall z, 0 <= z -> z + 4 <= 32 -> (p z + Z_to_bv 64 4)%bv = p (z + 4)).
  { intros z H0 H1. unfold p. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite !bv_modulus_64. unfold two64.
    rewrite (Z.mod_small (to_Z pc0 + z)) by lia. rewrite (Z.mod_small 4) by lia. rewrite !Z.mod_small by lia. lia. }

  set (c1 := with_pc (p 4) c0).
  set (c2 := with_pc (p 8) c1).
  set (c3 := rset (reg_of_r5 X17) (Z_to_bv 64 24) (with_pc (p 12) c2)).
  set (c4 := rset (reg_of_r5 X12) (Z_to_bv 64 0) (with_pc (p 16) c3)).
  set (c5 := rset (reg_of_r5 X16) (Z_to_bv 64 0) (with_pc (p 20) c4)).
  set (c6 := rset (reg_of_r5 X12) (Z_to_bv 64 0) (with_pc (p 24) c5)).
  set (c7 := rset (reg_of_r5 X12) (Z_to_bv 64 0) (with_pc (p 28) c6)).
  set (c8 := with_pc (p 32) c7).
  set (mk := fun c => ms_upd ms c (ms_mem ms)).
  assert (PC0 : Sem.c_pc c0 = p 0) by (rewrite P0; reflexivity).
  assert (X17nz : r5_eqb X17 X0 = false) by reflexivity.
  assert (X12nz : r5_eqb X12 X0 = false) by reflexivity.
  assert (X16nz : r5_eqb X16 X0 = false) by reflexivity.

  assert (FETCH : forall k w c, Sem.c_pc c = p (to_Z k) -> 0 <= to_Z k <= 32 ->
            fetch_word segs (Z_to_bv 64 (to_Z (PrimInt63.add pc0 k))) = Some w -> fetch_word segs (ms_pc_val (mk c)) = Some w).
  { intros k w c Hc Hk0 Hw. cbn [mk ms_upd ms_pc_val]. rewrite Hc, <- (PZ k Hk0). exact Hw. }
  assert (SVC' : forall c, ms_svc_pending (mk c) = None) by (intros c; reflexivity).
  assert (CORE : forall c, core_of (mk c) = c) by (intros c; destruct c; reflexivity).
  assert (MEM : forall c, ms_mem (mk c) = ms_mem ms) by (intros c; reflexivity).
  assert (MK : forall c c', ms_upd (mk c) c' (ms_mem (mk c)) = mk c') by (intros c c'; reflexivity).
  assert (MK0 : forall c', ms_upd ms c' (ms_mem ms) = mk c') by (intros c'; reflexivity).
  assert (NMbr : forall bc r1 r2 im cc a k, ~ Acc.mem_acc (Branch bc r1 r2 im) cc a k) by (intros; intro H; exact H).
  assert (NMoi : forall o r1 r2 im cc a k, ~ Acc.mem_acc (OpImm o r1 r2 im) cc a k) by (intros; intro H; exact H).
  assert (NMmu : forall o r1 r2 r3 cc a k, ~ Acc.mem_acc (Mul o r1 r2 r3) cc a k) by (intros; intro H; exact H).
  assert (NMsh : forall o r1 r2 sa cc a k, ~ Acc.mem_acc (ShiftImm o r1 r2 sa) cc a k) by (intros; intro H; exact H).
  assert (NMop : forall o r1 r2 r3 cc a k, ~ Acc.mem_acc (Op o r1 r2 r3) cc a k) by (intros; intro H; exact H).

  assert (PC1 : Sem.c_pc c1 = p 4) by reflexivity.
  assert (PC2 : Sem.c_pc c2 = p 8) by reflexivity.
  assert (PC3 : Sem.c_pc c3 = p 12) by (unfold c3; rewrite pc_rset, pc_with_pc; reflexivity).
  assert (PC4 : Sem.c_pc c4 = p 16) by (unfold c4; rewrite pc_rset, pc_with_pc; reflexivity).
  assert (PC5 : Sem.c_pc c5 = p 20) by (unfold c5; rewrite pc_rset, pc_with_pc; reflexivity).
  assert (PC6 : Sem.c_pc c6 = p 24) by (unfold c6; rewrite pc_rset, pc_with_pc; reflexivity).
  assert (PC7 : Sem.c_pc c7 = p 28) by (unfold c7; rewrite pc_rset, pc_with_pc; reflexivity).

  assert (S0 : mi_account_step segs ms model = MachineOk (mk c1, model)).
  { rewrite <- MK0. apply (step_core ms model w0 (Branch BC_EQ (reg_of_r5 X15) (reg_of_r5 X17) im0) c1);
      [rewrite <- P0; rewrite (PZ 0%uint63 ltac:(zlit)) in F0; exact F0| exact E0| exact D0| apply NMbr| |exact SVC].
    cbn [Sem.exec]. fold c0. rewrite R15, R17.
    replace (branch_taken BC_EQ (Z_to_bv 64 1) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
    unfold c1. rewrite PC0, (PSTEP 0) by lia. reflexivity. }

  assert (S1 : mi_account_step segs (mk c1) model = MachineOk (mk c2, model)).
  { rewrite <- (MK c1). apply (step_core (mk c1) model w1 (Branch BC_LTU (reg_of_r5 X11) (reg_of_r5 X14) im1) c2);
      [exact (FETCH 4%uint63 _ _ PC1 ltac:(zlit) F1)| exact E1| exact D1| apply NMbr| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. unfold c1 at 1 2. rewrite !rget_pc, R11, R14.
    replace (branch_taken BC_LTU we wb) with false.
    2:{ unfold branch_taken, bv_ltu. destruct (Z.ltb_spec (bv_unsigned we) (bv_unsigned wb)); [lia| reflexivity]. }
    unfold c2. rewrite PC1, (PSTEP 4) by lia. reflexivity. }

  assert (S2 : mi_account_step segs (mk c2) model = MachineOk (mk c3, model)).
  { rewrite <- (MK c2). apply (step_core (mk c2) model w2 (OpImm ALU_ADD (reg_of_r5 X17) (reg_of_r5 X0) imm) c3);
      [exact (FETCH 8%uint63 _ _ PC2 ltac:(zlit) F2)| exact E2| exact D2| apply NMoi| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite rget_x0.
    replace (alu64 ALU_ADD (Z_to_bv 64 0) (sext 64 imm)) with (Z_to_bv 64 24).
    2:{ cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, IMM, Z_to_bv_unsigned. reflexivity. }
    unfold c3. rewrite PC2, (PSTEP 8) by lia. reflexivity. }

  assert (C3_12 : rget c3 (reg_of_r5 X12) = rget c0 (reg_of_r5 X12)) by (unfold c3, c2, c1; creg; reflexivity).
  assert (C3_17 : rget c3 (reg_of_r5 X17) = Z_to_bv 64 24) by (unfold c3; creg; reflexivity).
  assert (C4_16 : rget c4 (reg_of_r5 X16) = rget c0 (reg_of_r5 X16)) by (unfold c4, c3, c2, c1; creg; reflexivity).
  assert (C5_12 : rget c5 (reg_of_r5 X12) = Z_to_bv 64 0) by (unfold c5, c4; creg; reflexivity).
  assert (C5_16 : rget c5 (reg_of_r5 X16) = Z_to_bv 64 0) by (unfold c5; creg; reflexivity).
  assert (C6_12 : rget c6 (reg_of_r5 X12) = Z_to_bv 64 0) by (unfold c6; creg; reflexivity).
  assert (C7_12 : rget c7 (reg_of_r5 X12) = Z_to_bv 64 0) by (unfold c7; creg; reflexivity).

  assert (S3 : mi_account_step segs (mk c3) model = MachineOk (mk c4, model)).
  { rewrite <- (MK c3). apply (step_core (mk c3) model w3' (Mul M_MULH (reg_of_r5 X12) (reg_of_r5 X12) (reg_of_r5 X17)) c4);
      [exact (FETCH 12%uint63 _ _ PC3 ltac:(zlit) F3)| exact E3| exact D3| apply NMmu| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite C3_12, C3_17, (mulh24_zero _ n R12 RN).
    unfold c4. rewrite PC3, (PSTEP 12) by lia. reflexivity. }

  assert (S4 : mi_account_step segs (mk c4) model = MachineOk (mk c5, model)).
  { rewrite <- (MK c4). apply (step_core (mk c4) model w4 (ShiftImm ALU_SRA (reg_of_r5 X16) (reg_of_r5 X16) sh) c5);
      [exact (FETCH 16%uint63 _ _ PC4 ltac:(zlit) F4)| exact E4| exact D4| apply NMsh| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite C4_16.
    replace sh with (Z_to_bv 6 63) by (apply bv_eq; rewrite SH; reflexivity).
    rewrite (sra63_zero _ n R16 RN).
    unfold c5. rewrite PC4, (PSTEP 16) by lia. reflexivity. }

  assert (S5 : mi_account_step segs (mk c5) model = MachineOk (mk c6, model)).
  { rewrite <- (MK c5). apply (step_core (mk c5) model w5' (Op ALU_XOR (reg_of_r5 X12) (reg_of_r5 X12) (reg_of_r5 X16)) c6);
      [exact (FETCH 20%uint63 _ _ PC5 ltac:(zlit) F5)| exact E5| exact D5| apply NMop| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite C5_12, C5_16.
    replace (alu64 ALU_XOR (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; reflexivity).
    unfold c6. rewrite PC5, (PSTEP 20) by lia. reflexivity. }

  assert (S6 : mi_account_step segs (mk c6) model = MachineOk (mk c7, model)).
  { rewrite <- (MK c6). apply (step_core (mk c6) model w6 (Op ALU_SLTU (reg_of_r5 X12) (reg_of_r5 X0) (reg_of_r5 X12)) c7);
      [exact (FETCH 24%uint63 _ _ PC6 ltac:(zlit) F6)| exact E6| exact D6| apply NMop| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite rget_x0, C6_12.
    replace (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; reflexivity).
    unfold c7. rewrite PC6, (PSTEP 24) by lia. reflexivity. }

  assert (S7 : mi_account_step segs (mk c7) model = MachineOk (mk c8, model)).
  { rewrite <- (MK c7). apply (step_core (mk c7) model w7 (Branch BC_NE (reg_of_r5 X12) (reg_of_r5 X0) im7) c8);
      [exact (FETCH 28%uint63 _ _ PC7 ltac:(zlit) F7)| exact E7| exact D7| apply NMbr| |apply SVC'].
    rewrite CORE. cbn [Sem.exec]. rewrite rget_x0, C7_12.
    replace (branch_taken BC_NE (Z_to_bv 64 0) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
    unfold c8. rewrite PC7, (PSTEP 28) by lia. reflexivity. }

  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as HALT.
  assert (HS8 : st_ok segs OPS E (setpc (setr (setr (setr (setr st X11 e) X12 (VL wzero)) X16 (VL wzero)) X17 (VL W24)) (PrimInt63.add pc0 32%uint63)) (mk c8) model).
  { unfold mk. unfold setpc, setr. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
    apply (st_ok_core E st ms model); [exact HS| | | | | |].
    - pose proof (so_x0 _ _ _ _ _ _ HS) as Z0. cbn. cbn in Z0. exact Z0.
    - assert (NEQ : forall a c : r5, r5_eqb a c = false -> c <> a) by (intros a c H ->; rewrite r5_eqb_refl in H; discriminate H).
      assert (LIT : forall w, den E (VL w) = Z_to_bv 64 (w2Z w)) by (intros w; cbn [den]; reflexivity).
      intros r. unfold c8, c7, c6, c5, c4, c3, c2, c1. rewrite rget_pc. creg.
      destruct (r5_eqb r X17) eqn:E17.
      { apply r5_eqb_spec in E17; subst r. rewrite rf_get_set_same. r5lit. rewrite LIT. reflexivity. }
      rewrite (rf_get_set_other _ _ X17 r) by exact (NEQ _ _ E17).
      destruct (r5_eqb r X16) eqn:E16.
      { apply r5_eqb_spec in E16; subst r. rewrite rf_get_set_same. r5lit. rewrite LIT. reflexivity. }
      rewrite (rf_get_set_other _ _ X16 r) by exact (NEQ _ _ E16).
      destruct (r5_eqb r X12) eqn:E12.
      { apply r5_eqb_spec in E12; subst r. rewrite rf_get_set_same. rewrite LIT. reflexivity. }
      rewrite (rf_get_set_other _ _ X12 r) by exact (NEQ _ _ E12).
      destruct (r5_eqb r X11) eqn:E11.
      { apply r5_eqb_spec in E11; subst r. rewrite rf_get_set_same. unfold c0. rewrite REGS. exact W11. }
      rewrite (rf_get_set_other _ _ X11 r) by exact (NEQ _ _ E11).
      unfold c0. exact (REGS r).
    - unfold c8, c7, c6, c5, c4, c3, c2, c1, c0. reflexivity.
    - unfold c8, c7, c6, c5, c4, c3, c2, c1, c0. reflexivity.
    - unfold c8, c7, c6, c5, c4, c3, c2, c1, c0. reflexivity.
    - unfold c8. rewrite pc_with_pc. symmetry. apply (PZ 32%uint63). zlit. }

  apply (rz_astep segs ms model (mk c1) model K HALT SVC S0).
  apply (rz_astep segs (mk c1) model (mk c2) model K HALT (SVC' c1) S1).
  apply (rz_astep segs (mk c2) model (mk c3) model K HALT (SVC' c2) S2).
  apply (rz_astep segs (mk c3) model (mk c4) model K HALT (SVC' c3) S3).
  apply (rz_astep segs (mk c4) model (mk c5) model K HALT (SVC' c4) S4).
  apply (rz_astep segs (mk c5) model (mk c6) model K HALT (SVC' c5) S5).
  apply (rz_astep segs (mk c6) model (mk c7) model K HALT (SVC' c6) S6).
  apply (rz_astep segs (mk c7) model (mk c8) model K HALT (SVC' c7) S7).
  apply (Hk _ (or_introl eq_refl) E (mk c8) model); [| exact HMP| exact HS8].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.

End Sound.
End PkShrink.
