(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk DriverCfg RealizesCfg RealizesAbort.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface HIfaceInit P_hbase P_h_fuzz_base.

Module P_h_reserve.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rec (n : Z) : Z := if (Z.lor n 7 =? 23)%Z then 25%Z else Z.lor n 7.

Lemma lor7_bounds : forall n, (0 <= n)%Z -> (n <= Z.lor n 7 <= n + 7)%Z /\ (Z.lor n 7 mod 2 = 1)%Z.
Proof.
  intros n Hn. pose proof (Z.add_lor_land n 7) as H1.
  assert (E : Z.land n 7 = (n mod 8)%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  assert (L : (0 <= Z.land n 7 <= 7)%Z) by (rewrite E; pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia).
  split; [lia|].
  assert (B : Z.testbit (Z.lor n 7) 0 = true) by (rewrite Z.lor_spec; apply orb_true_r).
  rewrite Z.bit0_odd, Zodd_mod in B. apply Z.eqb_eq in B. exact B.
Qed.

Lemma rec_bounds : forall n, (23 <= n <= 128)%Z -> (23 <= rec n <= 135)%Z /\ (rec n mod 2 = 1)%Z /\ (n <= rec n)%Z.
Proof.
  intros n Hn. unfold rec. destruct (lor7_bounds n ltac:(lia)) as [B O].
  destruct (Z.eqb_spec (Z.lor n 7) 23); [repeat split; try lia; reflexivity|]. repeat split; lia.
Qed.

Lemma lor7_eq : forall n, (0 <= n)%Z -> Z.lor n 7 = (n - n mod 8 + 7)%Z.
Proof.
  intros n Hn. pose proof (Z.add_lor_land n 7) as H1.
  assert (E : Z.land n 7 = (n mod 8)%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  lia.
Qed.

Lemma rec_mono : forall a b, (23 <= a <= b)%Z -> (rec a <= rec b)%Z.
Proof.
  intros a b H. unfold rec. rewrite !lor7_eq by lia.
  destruct (Z.eqb_spec (a - a mod 8 + 7) 23) as [Ea|Ea]; destruct (Z.eqb_spec (b - b mod 8 + 7) 23) as [Eb|Eb];
    Z.div_mod_to_equations; lia.
Qed.

Definition reserve_short_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a2 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS) /\ munch [] m m' /\ wmono PSEGS m m' /\ True.

Definition reserve_short_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o n : Z),
    rw_cells PSEGS m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> (0 <= n <= 22)%Z ->
    evt PSEGS (reserve_short_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x468ec) fc None m (seg_rom PSEGS)).

Lemma reserve_short_spec : reserve_short_stmt.
Proof.
  unfold reserve_short_stmt. intros until n. intros OBJ Hn.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
  step. (* [comment removed for export] *)
  clear RD0.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_vm.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  apply evt_done. unfold reserve_short_post. eexists. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact I].
Qed.

Section RESERVE.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  (* [comment removed for export] *)
  Definition reserve_long_contract : Prop :=
    forall (fx : FPState) regs m md hs (o n : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE (rec n + 1) <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 n -> (23 <= n <= 128)%Z ->
      rw_cells PSEGS m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk PSEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (p : Z) (buf : list byte),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE (rec n + 1))%Z -> (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) ->
         blocks_add (blocks hs) (blocks hs') (p, rec n + 1)%Z -> ~ In (p, rec n + 1)%Z (blocks hs) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(o, o + 24); (p, p + rec n + 1); (sp_of regs - SOE_NEED, sp_of regs)]%Z) m m' ->
         stk PSEGS m' (sp_of regs - SOE_NEED) (sp_of regs) ->
         rw_cells PSEGS m' o [C8 (Z_to_bv 64 (rec n + 2)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 p)] ->
         u8arr PSEGS m' p buf -> length buf = Z.to_nat (rec n + 1) ->
         realizes_cfg PSEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom PSEGS)) md') K) ->
      realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x468ec) m (seg_rom PSEGS)) md) K.

  #[using="STATIC HOK MEMCPY"] Lemma reserve_long_ok : reserve_long_contract.
  Proof. LiaFast.lf_pins (fun (STATIC HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (soe_R_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as SOE.
    intros fx regs m md hs o n ret K HP MD UB Ha0 Ha1 Hn OBJ Hso Hoe Hra Hret Hgp Htp AL SPB HT ST CONT.
    destruct (rec_bounds n Hn) as (Hr1 & Hr2 & Hr3).
    resume MD. rewrite Ha0, Ha1, Hra.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
    step. (* [comment removed for export] *)
    clear RD0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_vm.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit n) by lia.
    let Hc := fresh "Hc" in if_cases Hc.
    - cond_cleanup Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RN : rec n = 25%Z) by (unfold rec; rewrite (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
      rewrite RN in CONT, UB.
      eapply (SOE _ r1 m md hs o 25%Z ret K HP MD UB).
      + rewrite HR1. getr_leaf. reflexivity.
      + rewrite HR1. getr_leaf. reflexivity.
      + lia.
      + lia.
      + reflexivity.
      + exact OBJ.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact Hso.
      + exact Hoe.
      + rewrite HR1. getr_leaf. reflexivity.
      + exact Hret.
      + rewrite HR1. getr_leaf. exact Hgp.
      + rewrite HR1. getr_leaf. exact Htp.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact AL.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact SPB.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact HT.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact ST.
      + intros fx' regs' m' md' hs' p buf Hfx HP' MD' VM UBc KP BA FRSH CS MU ST' OB' BUF LB.
        assert (SP1 : sp_of r1 = sp_of regs) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
        rewrite SP1 in MU, ST'.
        apply (CONT fx' regs' m' md' hs' p buf); try assumption; try congruence.
        destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
        repeat split;
          first [ rewrite C2 | rewrite C3 | rewrite C4 | rewrite C8 | rewrite C9 | rewrite C18 | rewrite C19
                | rewrite C20 | rewrite C21 | rewrite C22 | rewrite C23 | rewrite C24 | rewrite C25 | rewrite C26 | rewrite C27 ];
          rewrite HR1; getr_leaf; reflexivity.
    - cond_cleanup Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RN : rec n = Z.lor n 7) by (unfold rec; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
      rewrite RN in CONT, Hr1, Hr2, UB.
      eapply (SOE _ r1 m md hs o (Z.lor n 7) ret K HP MD UB).
      + rewrite HR1. getr_leaf. reflexivity.
      + rewrite HR1. getr_leaf. reflexivity.
      + lia.
      + lia.
      + exact Hr2.
      + exact OBJ.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact Hso.
      + exact Hoe.
      + rewrite HR1. getr_leaf. reflexivity.
      + exact Hret.
      + rewrite HR1. getr_leaf. exact Hgp.
      + rewrite HR1. getr_leaf. exact Htp.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact AL.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact SPB.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact HT.
      + unfold sp_of in *. rewrite HR1. getr_leaf. exact ST.
      + intros fx' regs' m' md' hs' p buf Hfx HP' MD' VM UBc KP BA FRSH CS MU ST' OB' BUF LB.
        assert (SP1 : sp_of r1 = sp_of regs) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
        rewrite SP1 in MU, ST'.
        apply (CONT fx' regs' m' md' hs' p buf); try assumption; try congruence.
        destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
        repeat split;
          first [ rewrite C2 | rewrite C3 | rewrite C4 | rewrite C8 | rewrite C9 | rewrite C18 | rewrite C19
                | rewrite C20 | rewrite C21 | rewrite C22 | rewrite C23 | rewrite C24 | rewrite C25 | rewrite C26 | rewrite C27 ];
          rewrite HR1; getr_leaf; reflexivity.
  Qed.
End RESERVE.
End P_h_reserve.

Module P_h_crls_short.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_reserve OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_loop OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CRLS_SHORT.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  #[using="HOK"] Lemma crls_short_ok : crls_contract_if cfg HI GP TP HTOP STATIC (fun rem0 => (rem0 <= 22)%Z).
  Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros fx regs m md hs o f ptr0 rem0 ojunk bs0 ret K Hr22 HP MD UB Ha0 Ha1 Ha2 OBJ Ho8 FDP Hrem PAY LPAY PAYB
      Hso Hoe Hsf Hfe Hof Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold CRLS_NEED, SOE_NEED, P_MNEED in *.
    resume MD. rewrite Ha0, Ha1, Ha2, Hra.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bytes_at_bound _ _ _ _ PAY) as Bpay.
    (* [comment removed for export] *)
    assert (PAYLO : (rem0 = 0 \/ ptr0 + rem0 <= HTOP)%Z).
    { destruct PAYB as [->|(q & k & Hq & Hq1 & Hq2)]; [left; reflexivity|right].
      destruct (BOK _ _ _ HP) as [B1 _]. destruct (B1 q k Hq) as (_ & Hreg & _). unfold P_IMG_LO, P_IMG_END in Hreg. lia. }
    assert (DATAF0 : forall mm, munch [(bv_unsigned sp - (48 + (80 + (16 + 8192))), bv_unsigned sp); (o, o + 24); (f, f + 16)]%Z m mm ->
                       bytes_at PSEGS mm ptr0 bs0).
    { intros mm MUm. destruct PAYLO as [E0|E0].
      - rewrite E0 in LPAY. destruct bs0; [|cbn in LPAY; lia]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
      - eapply bytes_at_transport; [exact PAY | exact MUm |]. cbn [disjoint_from]. rewrite LPAY. repeat split; try exact I; lia. }
    clear PAY.
    pose proof (munch_refl [(bv_unsigned sp - (48 + (80 + (16 + 8192))), bv_unsigned sp); (o, o + 24); (f, f + 16)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    carve_frame 48%nat ST.
    do 7 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with H : rw_cells PSEGS _ o _ |- _ => rename H into OBJ0 end.
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call reserve_short_spec.
    1:{ exact OBJ0. } 1:{ lia. }
    lazymatch goal with H : rw_cells PSEGS _ o _ |- _ => rename H into OBJ1 end.
    destruct (fresh_short PSEGS _ _ OBJ1) as [OB0 OBA]. clear OBJ1.
    change (Z_to_bv 8 0) with (Z_to_bv 8 (2 * 0)) in OB0.
    lazymatch goal with H : rw_cells PSEGS _ (bv_unsigned sp + -48) _ |- _ => rename H into FR end.
    lazymatch goal with H : rw_cells PSEGS _ f _ |- _ => rename H into FDP1 end.
    lazymatch goal with H : stk PSEGS _ _ (bv_unsigned sp + -48) |- _ => rename H into ST1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* [comment removed for export] *)
    assert (TAIL : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 : word) (m' : word -> option byte)
                          (s' ptr' rem' : Z) (ob' : list byte),
      munch [(bv_unsigned sp - (48 + (80 + (16 + 8192))), bv_unsigned sp); (o, o + 24); (f, f + 16)]%Z m m' -> wmono PSEGS m m' ->
      stk PSEGS m' (bv_unsigned sp - (48 + (80 + (16 + 8192)))) (bv_unsigned sp + -48) ->
      rw_cells PSEGS m' (bv_unsigned sp + -48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 ret] ->
      rw_cells PSEGS m' f [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')] -> (ptr' + rem' = ptr0 + rem0)%Z -> (0 <= rem' <= rem0)%Z ->
      rw_cells PSEGS m' o [C1 (Z_to_bv 8 (2 * s'))] -> u8arr PSEGS m' (o + 1) ob' -> length ob' = 23%nat ->
      (0 <= s' <= 22)%Z -> (s' <= rem0 - rem')%Z ->
      evt PSEGS (Qrz PSEGS cfg md K)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) (getr regs 3) (getr regs 4) x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) x19 x20 (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) x28 x29 x30 x31)
            fp_regs (Z_to_bv 64 0x22da4) fp_csr None m' (seg_rom PSEGS))).
    { intros until ob'. intros MU' WM' ST' FR' FDP' Hpr Hrr OB' OBA' LOB' Hs1 Hs2.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s')) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s')) by lia. rewrite land1_mod2. replace ((2 * s') mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s')), (shr1_even s') by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd; [clear Hd | clear Hd; step (* [comment removed for export] *)].
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_taken.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_vm.
      all: step. (* [comment removed for export] *)
      all: if_vm.
      all: step. (* [comment removed for export] *)
      all: do 7 step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: rewrite (ret_pc_even_w ret Hret).
      all: exit_rz r3 HR3.
      all: apply (CONT _ r3 m' md hs s' ptr' rem'); [congruence | | exact MD | exact (vm_only_refl md) | clear; unfold MCHARGE; lia | eapply keep_munch; [|exact MU']; keep_side | | | | | exact FDP' | exact Hpr | exact Hrr | lia | lia | ].
      all: first [ solve [eapply FRAME; [exact HP | exact MU' | exact WM' |]; intros z Hz; cbn [outside] in Hz;
              destruct (outside_dec (owned hs) z) as [Ho|Ho]; [exact Ho|]; destruct (BOK _ _ _ HP) as [_ O1];
              pose proof (O1 z Ho) as [Hz1 _]; lia]
           | solve [repeat split; rewrite HR3; getr_leaf; try reflexivity; apply bv_eq; rewrite !unsigned_lit by lia; lia]
           | solve [eapply munch_weaken; [|exact MU']; intros z Hz; rewrite !outside_app in Hz; destruct Hz as (_ & Hz); cbn [outside app] in Hz |- *; repeat split; try exact I; lia]
           | solve [intros q k Hq; split; [exact Hq|]; destruct (BOK _ _ _ HP) as [B1 _]; destruct (B1 q k Hq) as (_ & Hqr & _); unfold P_IMG_LO, P_IMG_END in Hqr;
             eapply agree_on_of_munch; [exact MU' | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia]]
           | solve [eapply stk_release in FR'; [ | exact ST' | lia ]; cbn [cells_size csize Nat.add] in FR';
             replace (bv_unsigned sp + -48 + Z.of_nat 48)%Z with (bv_unsigned sp) in FR' by lia; exact FR']
           | solve [left; split; [lia|]; split; [intros y; tauto|]; split; [exact OB'|]; exists ob'; split; [exact LOB' | exact OBA']] ].
      all: fail. }
    step. (* [comment removed for export] *)
    if_vm.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    let Hc := fresh "Hc" in if_cases Hc.
    - cond_cleanup Hc.
      eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 0%Z ptr0 0%Z (repeat (Z_to_bv 8 0) 23)); try eassumption; try lia.
      1:{ rewrite Hc in FDP1. exact FDP1. }
      1:{ apply repeat_length. }
    - cond_cleanup Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (DATAF : forall mm, munch [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (o, o + 24); (f, f + 16)]%Z m1 mm ->
                        bytes_at PSEGS mm ptr0 bs0).
      { intros mm MUm. apply DATAF0. eapply munch_trans; [exact MU|].
        eapply munch_weaken; [|exact MUm]. unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. repeat split; try exact I; lia. }
      eapply evt_cut.
      { eapply (loopS_loop (Z_to_bv 64 (bv_unsigned sp + -48)) (getr regs 3) (getr regs 4) (getr regs 21) (getr regs 22)
                  (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr m1 o f ptr0 rem0 bs0)
          with (k := 129%nat) (i := 1%Z) (s := 0%Z) (rem := rem0).
        all: try rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia.
        all: try eassumption; try lia.
        - replace (ptr0 + rem0 - rem0)%Z with ptr0 by lia. exact FDP1.
        - apply repeat_length.
        - destruct (stk_split PSEGS m1 _ (bv_unsigned sp + -48 - 64) _ ST1 ltac:(lia)) as [_ S2]. exact S2.
        - apply munch_refl.
        - apply wmono_refl. }
      intros ms' PO. destruct PO as (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x28 & x29 & x30 & x31
                                      & m' & s' & ptr' & rem' & ob' & -> & MU' & WM' & ST' & FDP' & Hpr & OB' & OBA' & LOB' & Hs').
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in * by lia.
      destruct (stk_split PSEGS m1 _ (bv_unsigned sp + -48 - 64) _ ST1 ltac:(lia)) as [S1 _].
      apply (stk_transport_munch PSEGS [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (o, o + 24); (f, f + 16)]%Z m1 m') in S1;
        [|exact MU' | cbn [disjoint_from]; repeat split; try exact I; lia].
      pose proof (stk_merge PSEGS m' _ _ _ S1 ST' ltac:(lia)) as STm.
      apply (rw_cells_transport_munch PSEGS [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (o, o + 24); (f, f + 16)]%Z m1 m') in FR;
        [|exact MU' | cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; lia].
      eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' s' ptr' rem' ob'); try eassumption; try lia.
      + eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. repeat split; try exact I; lia.
      + eapply wmono_trans; eassumption.
  Qed.
End CRLS_SHORT.
End P_h_crls_short.

Module P_h_soe2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_new OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_delete OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_memmove OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SOE2.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  Definition soe_S2_contract : Prop :=
    forall (fx : FPState) regs m md hs (o c s p t : Z) (buf : list byte) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE (t + 1) <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 t ->
      (23 <= c)%Z -> (c + 1 <= 2^26)%Z -> (c mod 2 = 1)%Z -> (23 <= t < c)%Z -> (t mod 2 = 1)%Z -> (23 <= s <= t)%Z ->
      rw_cells PSEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] ->
      In (p, c + 1)%Z (blocks hs) -> u8arr PSEGS m p buf -> length buf = Z.to_nat (c + 1) ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk PSEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (p' : Z) (buf' : list byte),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE (t + 1))%Z -> (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) ->
         (forall y, In y (blocks hs') <-> y = (p', t + 1)%Z \/ (In y (blocks hs) /\ y <> (p, c + 1)%Z)) ->
         ~ In (p', t + 1)%Z (blocks hs) ->
         callee_saved regs regs' ->
         munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP); (o, o + 24); (sp_of regs - SOE_NEED, sp_of regs)]%Z) m m' ->
         (forall q k, In (q, k) (blocks hs) -> (q, k) <> (p, c + 1)%Z -> agree_on m m' q k) ->
         stk PSEGS m' (sp_of regs - SOE_NEED) (sp_of regs) ->
         rw_cells PSEGS m' o [C8 (Z_to_bv 64 (t + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p')] ->
         u8arr PSEGS m' p' buf' -> length buf' = Z.to_nat (t + 1) ->
         realizes_cfg PSEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom PSEGS)) md') K) ->
      realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22e50) m (seg_rom PSEGS)) md) K.

  #[using="HOK MEMCPY"] Lemma soe_S2_ok : soe_S2_contract.
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (new_ok cfg HI GP TP HTOP STATIC HOK) as NEW.
    pose proof (delete_ok cfg HI GP TP HTOP STATIC HOK) as DEL.
    pose proof (memmove_disj_spec MEMCPY) as MEMMOVE.
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros fx regs m md hs o c s p t buf ret K HP MD UB Ha0 Ha1 Hc1 Hc2 Hodd Ht Htodd Hs OBJ HIN BUFA LB Hso Hoe Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold SOE_NEED, P_MNEED in *.
    destruct (BOK _ _ _ HP) as [B1 O1].
    destruct (B1 p (c + 1)%Z HIN) as (Hn1 & Hreg & BST & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
    resume MD. rewrite Ha0, Ha1, Hra.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (munch_refl [(o, o + 24); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    carve_frame 80%nat ST.
    do 10 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
    step. (* [comment removed for export] *)
    clear RD0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (cap_byte0_odd c) by lia.
    step. (* [comment removed for export] *)
    rewrite (cap_landm2 c) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    rewrite (cap_land1 c) by lia.
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    exit_rz r1 HR1.
    lazymatch type of MU with ?T => change (keep T) in MU end.
    assert (HP1 : Heap hs m0 md).
    { unfold keep in MU. eapply FRAME; [exact HP | exact MU | exact WM |].
      intros z Hz. cbn [outside] in Hz. destruct (outside_dec (owned hs) z) as [Ho|Ho]; [exact Ho|].
      specialize (O1 z Ho). lia. }
    assert (SP1 : sp_of r1 = (bv_unsigned sp + -80)%Z).
    { unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. reflexivity. }
    eapply (NEW _ r1 m0 md hs (t + 1)%Z (Z_to_bv 64 0x22ef0) K HP1 MD UB).
    - rewrite HR1. getr_leaf. reflexivity.
    - lia.
    - rewrite HR1. getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1. getr_leaf. exact Hgp.
    - rewrite HR1. getr_leaf. exact Htp.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - rewrite SP1. replace (bv_unsigned sp + -80 - (16 + 8192))%Z with (bv_unsigned sp - (80 + (16 + 8192)))%Z by lia. exact ST.
    - intros fx2 r2 m2 md2 hs2 p' Hfx2 HP2 MD2 VM2 UB2 KP2 Ha02 Hp16 BADD FRESH CS MU2 ST2.
      rewrite SP1 in MU2, ST2.
      destruct (BOK _ _ _ HP2) as [B2 O2].
      destruct (B2 p' (t + 1)%Z (proj2 (BADD (p', t + 1)%Z) (or_introl eq_refl))) as (Hn2 & Hreg2 & BST2 & BDO2 & BDJ2).
      unfold P_IMG_LO, P_IMG_END in Hreg2.
      assert (HIN2 : In (p, c + 1)%Z (blocks hs2)) by (apply BADD; right; exact HIN).
      assert (NEQ : (p', t + 1)%Z <> (p, c + 1)%Z) by (intros E; apply FRESH; rewrite E; exact HIN).
      pose proof (BDJ2 p (c + 1)%Z HIN2 (fun E => NEQ (eq_sym E))) as DJ.
      (* [comment removed for export] *)
      assert (AGF : agree_on m0 m2 (bv_unsigned sp + -80)%Z 80).
      { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; split; [lia | split; [lia|exact I]] | lia | lia | left; lia]. }
      assert (AGO : agree_on m0 m2 o 24).
      { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; split; [lia | split; [lia|exact I]] | lia | lia | left; lia]. }
      assert (AGB : agree_on m0 m2 p (c + 1)%Z).
      { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; split; [lia | split; [lia|exact I]] | lia | lia | right; exists p, (c + 1)%Z; repeat split; try assumption; lia]. }
      lazymatch goal with H : rw_cells PSEGS m0 (bv_unsigned sp + -80) _ |- _ => rename H into FR end.
      apply (rw_cells_agree PSEGS m0 m2) in FR; [|exact AGF].
      apply (rw_cells_agree PSEGS m0 m2) in OBJ; [|exact AGO].
      apply (u8arr_agree PSEGS m0 m2) in BUFA; [|rewrite LB, Z2Nat.id by lia; exact AGB].
      clear AGF AGO AGB.
      (* [comment removed for export] *)
      destruct (stk_carve PSEGS m2 p' (p' + (t + 1)) (Z.to_nat (t + 1)) BST2 ltac:(lia)) as [_ [buf0 BUF]].
      replace (p' + (t + 1) - Z.of_nat (Z.to_nat (t + 1)))%Z with p' in BUF by lia.
      assert (LB0 : length buf0 = Z.to_nat (t + 1)) by exact (proj1 (proj1 (proj1 BUF))).
      pose proof (u8arr_of_rw_cells PSEGS _ _ _ _ BUF) as NBUF. clear BUF.
      lazymatch type of MU2 with ?T => change (keep T) in MU2 end.
      resume MD2. rewrite Ha02. cs_resume CS HR1.
      pose proof (munch_refl [(o, o + 24); (p', p' + (t + 1)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m2) as MU'.
      pose proof (wmono_refl PSEGS m2) as WM'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_true.
      step. (* [comment removed for export] *)
      if_taken.
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (bytes_at_sub PSEGS m2 p buf 0 (Z.to_nat (s + 1)) (proj1 BUFA) ltac:(lia)) as SRC.
      rewrite Z.add_0_r in SRC. change (skipn 0 buf) with buf in SRC.
      rewrite <- (firstn_skipn (Z.to_nat (s + 1)) buf0) in NBUF. apply u8arr_app in NBUF. destruct NBUF as [DST0 DST1].
      assert (LF0 : length (firstn (Z.to_nat (s + 1)) buf0) = Z.to_nat (s + 1)) by (rewrite firstn_length_le; lia).
      assert (LFb : length (firstn (Z.to_nat (s + 1)) buf) = Z.to_nat (s + 1)) by (rewrite firstn_length_le; lia).
      assert (LS0 : length (skipn (Z.to_nat (s + 1)) buf0) = Z.to_nat (t - s)) by (rewrite skipn_length, LB0; lia).
      rewrite LF0 in DST1. rewrite Z2Nat.id in DST1 by lia.
      pose proof (unsigned_lit p ltac:(lia)) as ULp. pose proof (unsigned_lit p' ltac:(lia)) as ULp'.
      pose proof (unsigned_lit (s + 1) ltac:(lia)) as ULs.
      call MEMMOVE.
      1:{ rewrite ULp. exact SRC. }
      1:{ rewrite ULp'. exact DST0. }
      1:{ rewrite LF0, LFb. reflexivity. }
      1:{ rewrite LFb, ULs. lia. }
      1:{ rewrite ULs. lia. }
      1:{ rewrite ULp, ULp', ULs. lia. }
      1:{ rewrite ULp', ULs. lia. }
      1:{ rewrite ULp, ULs. lia. }
      1:{ reflexivity. }
      name_mem m3.
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r3 HR3.
      lazymatch type of MU' with ?T => change (keep T) in MU' end.
      assert (HP3 : Heap hs2 m3 md2).
      { unfold keep in MU'. eapply FRAME; [exact HP2 | exact MU' | exact WM' |].
        intros z Hz. cbn [outside] in Hz. destruct (outside_dec (owned hs2) z) as [Ho|Ho]; [exact Ho|].
        pose proof (O2 z Ho) as [Hz1 _].
        assert (Hzb : ~ (p' <= z < p' + (t + 1))%Z) by (intros Hin; exact (Ho (disjoint_outside _ _ _ z BDO2 Hin))).
        lia. }
      assert (SP3 : sp_of r3 = (bv_unsigned sp + -80)%Z).
      { unfold sp_of. rewrite HR3. getr_leaf. rewrite unsigned_lit by lia. reflexivity. }
      eapply (DEL _ r3 m3 md2 hs2 p (c + 1)%Z (Z_to_bv 64 0x22f68) K HP3 MD2).
      + rewrite HR3. getr_leaf. reflexivity.
      + right. exact HIN2.
      + rewrite HR3. getr_leaf. reflexivity.
      + reflexivity.
      + rewrite HR3. getr_leaf. exact Hgp.
      + rewrite HR3. getr_leaf. exact Htp.
      + rewrite SP3. Z.div_mod_to_equations. lia.
      + rewrite SP3. lia.
      + unfold P_FNEED. rewrite SP3. lia.
      + unfold P_FNEED. rewrite SP3. lazymatch goal with H : stk PSEGS m3 ?lo ?hi |- _ =>
          destruct (stk_split PSEGS m3 lo (bv_unsigned sp + -80 - 8192) hi H ltac:(lia)) as [_ H2];
          replace hi with (bv_unsigned sp + -80)%Z in H2 by lia; exact H2 end.
      + intros fx4 r4 m4 md4 hs4 Hfx4 HP4 MD4 VM4 UB4 KP4 BDEL CS4 MU4 ST4.
        rewrite (proj2 (Z.eqb_neq p 0) ltac:(lia)) in BDEL.
        rewrite SP3 in MU4, ST4. unfold P_FNEED in MU4, ST4.
        assert (HIN4 : In (p', t + 1)%Z (blocks hs4)) by (apply BDEL; split; [apply BADD; left; reflexivity | exact NEQ]).
        (* [comment removed for export] *)
        lazymatch goal with H : u8arr PSEGS m3 (bv_unsigned (Z_to_bv 64 p')) _ |- _ => rename H into DST0' end.
        rewrite ULp' in DST0'.
        assert (DST1' : u8arr PSEGS m3 (p' + Z.of_nat (length (firstn (Z.to_nat (s + 1)) buf))) (skipn (Z.to_nat (s + 1)) buf0)).
        { rewrite LFb, Z2Nat.id by lia. exact DST1. }
        pose proof (proj2 (u8arr_app PSEGS m3 p' _ _) (conj DST0' DST1')) as NBUF'. clear DST0' DST1' DST1.
        assert (AGF : agree_on m3 m4 (bv_unsigned sp + -80)%Z 80).
        { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs2 hs4 m3 m4 md2 md4 _ _ _ BOK HP3 HP4 MU4);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
        assert (AGO : agree_on m3 m4 o 24).
        { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs2 hs4 m3 m4 md2 md4 _ _ _ BOK HP3 HP4 MU4);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
        assert (AGN : agree_on m3 m4 p' (t + 1)%Z).
        { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs2 hs4 m3 m4 md2 md4 _ _ _ BOK HP3 HP4 MU4);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | right; exists p', (t + 1)%Z; repeat split; try assumption; try lia].
          apply BADD. left. reflexivity. }
        lazymatch goal with H : stk PSEGS m3 _ (bv_unsigned sp + -80) |- _ => rename H into STlo end.
        destruct (stk_split PSEGS m3 _ (bv_unsigned sp + -80 - 8192) _ STlo ltac:(lia)) as [STlo' _]. clear STlo.
        assert (AGS : agree_on m3 m4 (bv_unsigned sp - (80 + (16 + 8192)))%Z 16).
        { eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs2 hs4 m3 m4 md2 md4 _ _ _ BOK HP3 HP4 MU4);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
        lazymatch goal with H : rw_cells PSEGS m3 (bv_unsigned sp + -80) _ |- _ => rename H into FR3 end.
        lazymatch goal with H : rw_cells PSEGS m3 o _ |- _ => rename H into OBJ3 end.
        apply (rw_cells_agree PSEGS m3 m4) in FR3; [|exact AGF].
        apply (rw_cells_agree PSEGS m3 m4) in OBJ3; [|exact AGO].
        apply (u8arr_agree PSEGS m3 m4) in NBUF'; [|rewrite app_length, LFb, LS0; replace (Z.of_nat (Z.to_nat (s + 1) + Z.to_nat (t - s))) with (t + 1)%Z by lia; exact AGN].
        apply (stk_agree PSEGS m3 m4) in STlo'; [|eapply agree_on_sub; [exact AGS | lia | lia]].
        clear AGF AGO AGN AGS.
        lazymatch type of MU4 with ?T => change (keep T) in MU4 end.
        resume MD4. cs_resume CS4 HR3.
        pose proof (munch_refl [(o, o + 24); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m4) as MU5.
        pose proof (wmono_refl PSEGS m4) as WM5.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        do 10 step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (ret_pc_even_w ret Hret).
        exit_rz r5 HR5.
        unfold keep in MU, MU2, MU', MU4.
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (mkst _ _ ?mm _) _) _ => rename mm into mF end.
        lazymatch goal with H : rw_cells PSEGS mF o _ |- _ => rename H into OB' end.
        rewrite (unsigned_lit (t + 1)) in OB' by lia. rewrite lor1_even in OB' by (Z.div_mod_to_equations; lia).
        replace (t + 1 + 1)%Z with (t + 2)%Z in OB' by lia.
        lazymatch goal with H : u8arr PSEGS mF p' _ |- _ => rename H into NB end.
        apply (CONT _ r5 mF md4 hs4 p' (firstn (Z.to_nat (s + 1)) buf ++ skipn (Z.to_nat (s + 1)) buf0)); [congruence | | exact MD4 | exact (vm_only_trans _ _ _ VM2 VM4) | clear - UB2 UB4; lia | apply (keep_trans P_KEEP m m0 mF); [eapply keep_munch; [|exact MU]; keep_side | apply (keep_trans P_KEEP m0 m2 mF); [exact KP2 | apply (keep_trans P_KEEP m2 m3 mF); [eapply keep_munch; [|exact MU']; keep_side | apply (keep_trans P_KEEP m3 m4 mF); [exact KP4 | eapply keep_munch; [|exact MU5]; keep_side]]]] | | exact FRESH | | | | | exact OB' | exact NB | ].
        * eapply FRAME; [exact HP4 | exact MU5 | exact WM5 |].
          intros z Hz. cbn [outside] in Hz.
          destruct (outside_dec (owned hs4) z) as [Ho|Ho]; [exact Ho|]. destruct (BOK _ _ _ HP4) as [_ O4].
          pose proof (O4 z Ho) as [Hz1 _]. lia.
        * intros y. unfold blocks_del in BDEL. unfold blocks_add in BADD. rewrite (BDEL y), (BADD y). split; [intros [[A|A] B]; [left; exact A | right; split; assumption]|].
          intros [A|[A B]]; split; [left; exact A | rewrite A; exact NEQ | right; exact A | exact B].
        * repeat split; rewrite HR5; getr_leaf; reflexivity.
        * intros z Hz. rewrite !outside_app in Hz. destruct Hz as (Hs0 & Hz3). cbn [outside app] in Hz3. unfold P_IMG_LO, P_IMG_END in Hz3.
          assert (OH : forall hsx mx mdx, Heap hsx mx mdx -> outside (owned hsx) (bv_unsigned z)).
          { intros hsx mx mdx Hx. eapply (owned_out PSEGS _ _ _ _ _ _ _ _ hsx mx mdx); [exact BOK | exact Hx | exact Hs0 | | ]; unfold P_IMG_LO, P_IMG_END in *; lia. }
          rewrite (MU5 z) by (cbn [outside]; repeat split; try exact I; lia).
          rewrite (MU4 z) by (apply outside_app; split; [apply (OH _ _ _ HP3) | apply outside_app; split;
                              [apply (OH _ _ _ HP4) | cbn [outside]; repeat split; try exact I; lia]]).
          rewrite (MU' z) by (cbn [outside]; repeat split; try exact I; lia).
          rewrite (MU2 z) by (apply outside_app; split; [apply (OH _ _ _ HP1) | apply outside_app; split;
                              [apply (OH _ _ _ HP2) | cbn [outside]; repeat split; try exact I; lia]]).
          rewrite (MU z) by (cbn [outside]; repeat split; try exact I; lia). reflexivity.
        * intros q k Hq Hne. destruct (B1 q k Hq) as (Hk1 & Hqr & _ & QDO & QDJ). unfold P_IMG_LO, P_IMG_END in Hqr.
          assert (Hq2 : In (q, k) (blocks hs2)) by (apply BADD; right; exact Hq).
          assert (Hq4 : In (q, k) (blocks hs4)) by (apply BDEL; split; assumption).
          assert (Hqne' : (q, k) <> (p', t + 1)%Z) by (intros E; apply FRESH; rewrite <- E; exact Hq).
          pose proof (BDJ2 q k Hq2 Hqne') as QD'.
          eapply agree_on_trans; [eapply agree_on_of_munch; [exact MU | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia] |].
          eapply agree_on_trans; [eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try assumption; lia] |].
          eapply agree_on_trans; [eapply agree_on_of_munch; [exact MU' | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia] |].
          eapply agree_on_trans; [eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs2 hs4 m3 m4 md2 md4 _ _ _ BOK HP3 HP4 MU4);
            [ | lia | lia | right; exists q, k; repeat split; try assumption; lia] |].
          { cbn [disjoint_from]. split; [|split; [lia | exact I]].
            pose proof (QDJ p (c + 1)%Z HIN ltac:(intros E; apply Hne; rewrite E; reflexivity)) as D'. lia. }
          eapply agree_on_of_munch; [exact MU5 | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia].
        * lazymatch goal with H : stk PSEGS mF _ (bv_unsigned sp + -80) |- _ => rename H into ST' end.
          lazymatch goal with H : stk PSEGS mF _ (bv_unsigned sp + -80 - 8192) |- _ => rename H into STlo2 end.
          lazymatch goal with H : rw_cells PSEGS mF (bv_unsigned sp + -80) _ |- _ => rename H into FR' end.
          eapply stk_release in FR'; [ | exact ST' | lia ]. cbn [cells_size csize Nat.add] in FR'.
          replace (bv_unsigned sp + -80 + Z.of_nat 80)%Z with (bv_unsigned sp) in FR' by lia.
          pose proof (stk_merge PSEGS mF _ _ _ STlo2 FR' ltac:(lia)) as STF.
          replace (bv_unsigned sp - (80 + (16 + 8192)))%Z with (bv_unsigned sp + -80 - (16 + 8192))%Z by lia. exact STF.
        * rewrite app_length, LFb, LS0. lia.
  Qed.
End SOE2.
End P_h_soe2.

Module P_h_crls_ltail.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_soe2 OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_reserve.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LTAIL.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  Definition ltail_result (hs hs' : hi_HS HI) (m' : word -> option byte) (o c s p : Z) : Prop :=
    ((s <= 22)%Z /\ blocks_del (blocks hs) (blocks hs') (p, c + 1)%Z /\ rw_cells PSEGS m' o [C1 (Z_to_bv 8 (2 * s))] /\
       exists ob, length ob = 23%nat /\ u8arr PSEGS m' (o + 1) ob)
    \/ (exists (c' p' : Z) (buf' : list byte), (23 <= c' < 2^26)%Z /\ (c' mod 2 = 1)%Z /\ (s <= c')%Z /\
          (forall y, In y (blocks hs') <-> y = (p', c' + 1)%Z \/ (In y (blocks hs) /\ y <> (p, c + 1)%Z)) /\
          (forall y, In y (blocks hs) -> y <> (p, c + 1)%Z -> y <> (p', c' + 1)%Z) /\
          rw_cells PSEGS m' o [C8 (Z_to_bv 64 (c' + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p')] /\
          u8arr PSEGS m' p' buf' /\ length buf' = Z.to_nat (c' + 1)).

  Definition ltail_contract : Prop :=
    forall (fx : FPState) regs m md hs (o c s p : Z) (buf : list byte) (sv0 sv1 sv2 sv3 sv4 ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE 136 <= UBOUND)%Z ->
      getr regs 8 = Z_to_bv 64 o ->
      rw_cells PSEGS m (sp_of regs) [C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 ret] ->
      rw_cells PSEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] ->
      (23 <= c < 2^26)%Z -> (c mod 2 = 1)%Z -> (0 <= s <= c)%Z -> (s <= 128)%Z -> ((23 <= s)%Z -> (rec s <= c)%Z) ->
      In (p, c + 1)%Z (blocks hs) -> u8arr PSEGS m p buf -> length buf = Z.to_nat (c + 1) ->
      (sp_of regs + 48 <= o)%Z -> (o + 24 < 2^64)%Z ->
      (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk PSEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs',
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE 136)%Z -> (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) ->
         getr regs' 2 = Z_to_bv 64 (sp_of regs + 48) -> getr regs' 8 = sv0 -> getr regs' 9 = sv1 ->
         getr regs' 18 = sv2 -> getr regs' 19 = sv3 -> getr regs' 20 = sv4 ->
         getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
         getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
         getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
         getr regs' 27 = getr regs 27 ->
         munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP); (o, o + 24); (sp_of regs - SOE_NEED, sp_of regs + 48)]%Z) m m' ->
         (forall q k, In (q, k) (blocks hs) -> (q, k) <> (p, c + 1)%Z -> In (q, k) (blocks hs') /\ agree_on m m' q k) ->
         stk PSEGS m' (sp_of regs - SOE_NEED) (sp_of regs + 48) ->
         ltail_result hs hs' m' o c s p ->
         realizes_cfg PSEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom PSEGS)) md') K) ->
      realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22da4) m (seg_rom PSEGS)) md) K.

  #[using="HOK MEMCPY"] Lemma ltail_ok : ltail_contract.
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (soe_S1_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as S1.
    pose proof (soe_S2_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as S2.
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros fx regs m md hs o c s p buf sv0 sv1 sv2 sv3 sv4 ret K HP MD UB Hs0 FR OBJ Hc1 Hodd Hs Hs128 Hrec HIN BUFA LB
      Hso Hoe Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold SOE_NEED, P_MNEED in *.
    destruct (BOK _ _ _ HP) as [B1 O1].
    destruct (B1 p (c + 1)%Z HIN) as (Hn1 & Hreg & BST & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
    resume MD. rewrite Hs0.
    set (spc := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 spc) as Rsp. unfold bv_modulus in Rsp.
    pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
    step. (* [comment removed for export] *)
    clear RD0.
    step. (* [comment removed for export] *)
    rewrite (cap_byte0_odd c) by lia.
    step. (* [comment removed for export] *)
    if_vm.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit s) by lia.
    (* [comment removed for export] *)
    assert (EPI : forall (fx1 : FPState) (r2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model),
      md_ok md2 -> getr r2 2 = spc ->
      rw_cells PSEGS m2 (bv_unsigned spc) [C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 ret] ->
      (forall (fx' : FPState) regs', @fp_csr fx' = @fp_csr fx1 -> getr regs' 2 = Z_to_bv 64 (bv_unsigned spc + 48) ->
         getr regs' 8 = sv0 -> getr regs' 9 = sv1 -> getr regs' 18 = sv2 -> getr regs' 19 = sv3 -> getr regs' 20 = sv4 ->
         getr regs' 3 = getr r2 3 -> getr regs' 4 = getr r2 4 -> getr regs' 21 = getr r2 21 -> getr regs' 22 = getr r2 22 ->
         getr regs' 23 = getr r2 23 -> getr regs' 24 = getr r2 24 -> getr regs' 25 = getr r2 25 -> getr regs' 26 = getr r2 26 ->
         getr regs' 27 = getr r2 27 ->
         realizes_cfg PSEGS cfg (mkCfg (@mkst fx' regs' ret m2 (seg_rom PSEGS)) md2) K) ->
      realizes_cfg PSEGS cfg (mkCfg (@mkst fx1 r2 (Z_to_bv 64 0x22e00) m2 (seg_rom PSEGS)) md2) K).
    { intros fx1 r2 m2 md2 MD2 SP2 FR2 C. resume MD2. rewrite SP2.
      do 7 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ret_pc_even_w ret Hret).
      exit_rz r3 HR3.
      apply C; first [congruence | (rewrite HR3; getr_leaf; reflexivity)]. }
    destruct (Z_le_gt_dec s 22) as [Hs22|Hs22].
    - (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd; [clear Hd | clear Hd; step (* [comment removed for export] *)].
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_taken.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_vm.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: rewrite (cap_landm2 c) by lia.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_not_taken.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: exit_rz r1 HR1.
      all: assert (SP1 : sp_of r1 = bv_unsigned spc) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      all: eapply (S1 _ r1 m md hs o c s p buf (Z_to_bv 64 0x22e00) K HP MD).
      all: try (rewrite HR1; getr_leaf; reflexivity).
      all: try (rewrite SP1; lia).
      all: try lia.
      all: try (rewrite HR1; getr_leaf; assumption).
      all: try (rewrite SP1; assumption).
      all: try assumption.
      all: try reflexivity.
      all: intros fx2 r2 m2 md2 hs2 ob Hfx2 HP2 MD2 VM2 UB2 KP2 BDEL CS MU2 ST2 OB' OBA' LOB'.
      all: rewrite SP1 in MU2, ST2. all: unfold SOE_NEED, P_MNEED in MU2, ST2.
      all: assert (AGF : agree_on m m2 (bv_unsigned spc) 48);
             [ eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ _ BOK HP HP2 MU2);
               [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia] | ].
      all: apply (rw_cells_agree PSEGS m m2) in FR; [|exact AGF].
      all: assert (C2' : getr r2 2 = spc) by (destruct CS as (C2 & _); rewrite C2, HR1; getr_leaf; reflexivity).
      all: apply (EPI fx2 r2 m2 md2 MD2 C2' FR).
      all: intros fx' regs' Hfx' G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27.
      all: destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
      all: apply (CONT fx' regs' m2 md2 hs2); [congruence | exact HP2 | exact MD2 | exact VM2 | clear - UB2; unfold MCHARGE in *; lia | exact KP2 | exact G2 | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | .. ].
      all: try (match goal with |- getr ?ra ?ka = getr ?rb ?kb => first [rewrite G3, C3 | rewrite G4, C4 | rewrite G21, C21 | rewrite G22, C22 | rewrite G23, C23
                 | rewrite G24, C24 | rewrite G25, C25 | rewrite G26, C26 | rewrite G27, C27]; rewrite HR1; getr_leaf; reflexivity end).
      all: try solve [ eapply (munch_coarsen PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ BOK HP HP2 MU2);
                  intros z Hz; cbn [outside app] in Hz |- *; unfold P_IMG_LO, P_IMG_END in *; repeat split; try exact I; lia ].
      all: try solve [ intros q k Hq Hne; split; [apply BDEL; split; assumption|];
                  destruct (B1 q k Hq) as (_ & Hqr & _ & _ & QDJ); unfold P_IMG_LO, P_IMG_END in Hqr;
                  pose proof (QDJ p (c + 1)%Z HIN ltac:(intros E; apply Hne; rewrite E; reflexivity)) as D';
                  eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ _ BOK HP HP2 MU2);
                  [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try lia];
                  [exact Hq | apply BDEL; split; assumption] ].
      all: try solve [ eapply stk_release in FR; [ | exact ST2 | lia ]; cbn [cells_size csize Nat.add] in FR;
                  replace (bv_unsigned spc + Z.of_nat 48)%Z with (bv_unsigned spc + 48)%Z in FR by lia; exact FR ].
      all: try solve [ left; split; [lia|]; split; [exact BDEL|]; split; [exact OB'|]; exists ob; split; [exact LOB' | exact OBA'] ].
    - (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd;
        [ cond_cleanup Hd;
          replace (Z_to_bv 64 (Z.lor s 7)) with (Z_to_bv 64 (rec s)) by (unfold rec; rewrite (proj2 (Z.eqb_neq _ _) Hd); reflexivity)
        | cond_cleanup Hd; step; (* [comment removed for export] *)
          replace (Z_to_bv 64 25) with (Z_to_bv 64 (rec s)) by (unfold rec; rewrite (proj2 (Z.eqb_eq _ _) Hd); reflexivity) ].
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_not_taken.
      all: step. (* [comment removed for export] *)
      all: if_vm.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: rewrite (cap_landm2 c) by lia.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: pose proof (rec_bounds s ltac:(lia)) as (Hr1 & Hr2 & Hr3); specialize (Hrec ltac:(lia)).
      all: let Hf := fresh "Hf" in if_cases Hf; cond_cleanup Hf.
      { (* [comment removed for export] *)
        exit_rz r1 HR1.
          apply (EPI _ r1 m md MD ltac:(rewrite HR1; getr_leaf; reflexivity) FR).
          intros fx' regs' Hfx' G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27.
          apply (CONT fx' regs' m md hs); [congruence | exact HP | exact MD | exact (vm_only_refl md) | clear; unfold MCHARGE; lia | exact (keep_refl P_KEEP m) | exact G2 | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | .. ].
          all: try (match goal with |- getr ?ra ?ka = getr ?rb ?kb => first [rewrite G3 | rewrite G4 | rewrite G21 | rewrite G22 | rewrite G23
                     | rewrite G24 | rewrite G25 | rewrite G26 | rewrite G27]; rewrite HR1; getr_leaf; reflexivity end).
          * apply munch_refl.
          * intros q k Hq Hne. split; [exact Hq|]. intros i Hi. reflexivity.
          * eapply stk_release in FR; [ | exact ST | lia ]. cbn [cells_size csize Nat.add] in FR.
            replace (bv_unsigned spc + Z.of_nat 48)%Z with (bv_unsigned spc + 48)%Z in FR by lia. exact FR.
          * right. exists c, p, buf. split; [lia|]. split; [exact Hodd|]. split; [lia|].
            split; [|split; [intros y _ Hy; exact Hy | split; [rewrite Hf in *; exact OBJ | split; [exact BUFA | exact LB]]]].
            intros y. split; [|intros [->|[A _]]; [exact HIN | exact A]].
            intros Hy. destruct y as [y1 y2]. destruct (Z.eq_dec y1 p) as [->|Hy1]; [destruct (Z.eq_dec y2 (c + 1)) as [->|Hy2]|].
            -- left. reflexivity.
            -- right. split; [exact Hy|]. intros E. inversion E. lia.
            -- right. split; [exact Hy|]. intros E. inversion E. lia.
      }
      { (* [comment removed for export] *)
        step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          exit_rz r1 HR1.
          assert (SP1 : sp_of r1 = bv_unsigned spc) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
          assert (Rs : (23 <= s <= 128)%Z) by lia. destruct (rec_bounds s Rs) as (RS1 & _ & _).
          assert (UBs : (U md + MCHARGE (rec s + 1) <= UBOUND)%Z) by (clear - UB RS1; unfold MCHARGE in *; lia).
          eapply (S2 _ r1 m md hs o c s p (rec s) buf (Z_to_bv 64 0x22e00) K HP MD UBs).
          all: try (rewrite HR1; getr_leaf; reflexivity).
          all: try (rewrite SP1; lia).
          all: try lia.
          all: try (rewrite HR1; getr_leaf; assumption).
          all: try (rewrite SP1; assumption).
          all: try assumption.
          all: try reflexivity.
          intros fx2 r2 m2 md2 hs2 p' buf' Hfx2 HP2 MD2 VM2 UB2 KP2 BREL FRESH CS MU2 AG2 ST2 OB' BUF' LB'.
          rewrite SP1 in MU2, ST2. unfold SOE_NEED, P_MNEED in MU2, ST2.
          assert (AGF : agree_on m m2 (bv_unsigned spc) 48).
          { eapply (static_agree STATIC _ P_IMG_LO P_IMG_END HTOP m m2 _ _ SOK MU2);
              [cbn [disjoint_from]; repeat split; try exact I; lia | lia | unfold P_IMG_LO; lia | unfold P_IMG_LO, P_IMG_END; lia | lia]. }
          apply (rw_cells_agree PSEGS m m2) in FR; [|exact AGF].
          assert (C2' : getr r2 2 = spc) by (destruct CS as (C2 & _); rewrite C2, HR1; getr_leaf; reflexivity).
          apply (EPI fx2 r2 m2 md2 MD2 C2' FR).
          intros fx' regs' Hfx' G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27.
          destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
          apply (CONT fx' regs' m2 md2 hs2); [congruence | exact HP2 | exact MD2 | exact VM2 | clear - UB2 RS1; unfold MCHARGE in *; lia | exact KP2 | exact G2 | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | .. ].
          all: try (match goal with |- getr ?ra ?ka = getr ?rb ?kb => first [rewrite G3, C3 | rewrite G4, C4 | rewrite G21, C21 | rewrite G22, C22 | rewrite G23, C23
                     | rewrite G24, C24 | rewrite G25, C25 | rewrite G26, C26 | rewrite G27, C27]; rewrite HR1; getr_leaf; reflexivity end).
          * eapply munch_weaken; [|exact MU2]. intros z Hz. rewrite !outside_app in Hz |- *. destruct Hz as (HzS & Hz).
            split; [exact HzS|]. cbn [outside app] in Hz |- *. unfold P_IMG_LO, P_IMG_END in *. repeat split; try exact I; lia.
          * intros q k Hq Hne. split; [apply BREL; right; split; assumption | exact (AG2 q k Hq Hne)].
          * eapply stk_release in FR; [ | exact ST2 | lia ]. cbn [cells_size csize Nat.add] in FR.
            replace (bv_unsigned spc + Z.of_nat 48)%Z with (bv_unsigned spc + 48)%Z in FR by lia. exact FR.
          * right. exists (rec s), p', buf'. split; [lia|]. split; [exact Hr2|]. split; [lia|].
            split; [exact BREL|]. split; [|split; [exact OB' | split; [exact BUF' | exact LB']]].
            intros y Hy Hne E. apply FRESH. rewrite <- E. exact Hy.
      }
      { (* [comment removed for export] *)
        exit_rz r1 HR1.
          apply (EPI _ r1 m md MD ltac:(rewrite HR1; getr_leaf; reflexivity) FR).
          intros fx' regs' Hfx' G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27.
          apply (CONT fx' regs' m md hs); [congruence | exact HP | exact MD | exact (vm_only_refl md) | clear; unfold MCHARGE; lia | exact (keep_refl P_KEEP m) | exact G2 | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | .. ].
          all: try (match goal with |- getr ?ra ?ka = getr ?rb ?kb => first [rewrite G3 | rewrite G4 | rewrite G21 | rewrite G22 | rewrite G23
                     | rewrite G24 | rewrite G25 | rewrite G26 | rewrite G27]; rewrite HR1; getr_leaf; reflexivity end).
          * apply munch_refl.
          * intros q k Hq Hne. split; [exact Hq|]. intros i Hi. reflexivity.
          * eapply stk_release in FR; [ | exact ST | lia ]. cbn [cells_size csize Nat.add] in FR.
            replace (bv_unsigned spc + Z.of_nat 48)%Z with (bv_unsigned spc + 48)%Z in FR by lia. exact FR.
          * right. exists c, p, buf. split; [lia|]. split; [exact Hodd|]. split; [lia|].
            split; [|split; [intros y _ Hy; exact Hy | split; [rewrite Hf in *; exact OBJ | split; [exact BUFA | exact LB]]]].
            intros y. split; [|intros [->|[A _]]; [exact HIN | exact A]].
            intros Hy. destruct y as [y1 y2]. destruct (Z.eq_dec y1 p) as [->|Hy1]; [destruct (Z.eq_dec y2 (c + 1)) as [->|Hy2]|].
            -- left. reflexivity.
            -- right. split; [exact Hy|]. intros E. inversion E. lia.
            -- right. split; [exact Hy|]. intros E. inversion E. lia.
      }
      { (* [comment removed for export] *)
        step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          exit_rz r1 HR1.
          assert (SP1 : sp_of r1 = bv_unsigned spc) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
          assert (Rs : (23 <= s <= 128)%Z) by lia. destruct (rec_bounds s Rs) as (RS1 & _ & _).
          assert (UBs : (U md + MCHARGE (rec s + 1) <= UBOUND)%Z) by (clear - UB RS1; unfold MCHARGE in *; lia).
          eapply (S2 _ r1 m md hs o c s p (rec s) buf (Z_to_bv 64 0x22e00) K HP MD UBs).
          all: try (rewrite HR1; getr_leaf; reflexivity).
          all: try (rewrite SP1; lia).
          all: try lia.
          all: try (rewrite HR1; getr_leaf; assumption).
          all: try (rewrite SP1; assumption).
          all: try assumption.
          all: try reflexivity.
          intros fx2 r2 m2 md2 hs2 p' buf' Hfx2 HP2 MD2 VM2 UB2 KP2 BREL FRESH CS MU2 AG2 ST2 OB' BUF' LB'.
          rewrite SP1 in MU2, ST2. unfold SOE_NEED, P_MNEED in MU2, ST2.
          assert (AGF : agree_on m m2 (bv_unsigned spc) 48).
          { eapply (static_agree STATIC _ P_IMG_LO P_IMG_END HTOP m m2 _ _ SOK MU2);
              [cbn [disjoint_from]; repeat split; try exact I; lia | lia | unfold P_IMG_LO; lia | unfold P_IMG_LO, P_IMG_END; lia | lia]. }
          apply (rw_cells_agree PSEGS m m2) in FR; [|exact AGF].
          assert (C2' : getr r2 2 = spc) by (destruct CS as (C2 & _); rewrite C2, HR1; getr_leaf; reflexivity).
          apply (EPI fx2 r2 m2 md2 MD2 C2' FR).
          intros fx' regs' Hfx' G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27.
          destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
          apply (CONT fx' regs' m2 md2 hs2); [congruence | exact HP2 | exact MD2 | exact VM2 | clear - UB2 RS1; unfold MCHARGE in *; lia | exact KP2 | exact G2 | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | .. ].
          all: try (match goal with |- getr ?ra ?ka = getr ?rb ?kb => first [rewrite G3, C3 | rewrite G4, C4 | rewrite G21, C21 | rewrite G22, C22 | rewrite G23, C23
                     | rewrite G24, C24 | rewrite G25, C25 | rewrite G26, C26 | rewrite G27, C27]; rewrite HR1; getr_leaf; reflexivity end).
          * eapply munch_weaken; [|exact MU2]. intros z Hz. rewrite !outside_app in Hz |- *. destruct Hz as (HzS & Hz).
            split; [exact HzS|]. cbn [outside app] in Hz |- *. unfold P_IMG_LO, P_IMG_END in *. repeat split; try exact I; lia.
          * intros q k Hq Hne. split; [apply BREL; right; split; assumption | exact (AG2 q k Hq Hne)].
          * eapply stk_release in FR; [ | exact ST2 | lia ]. cbn [cells_size csize Nat.add] in FR.
            replace (bv_unsigned spc + Z.of_nat 48)%Z with (bv_unsigned spc + 48)%Z in FR by lia. exact FR.
          * right. exists (rec s), p', buf'. split; [lia|]. split; [exact Hr2|]. split; [lia|].
            split; [exact BREL|]. split; [|split; [exact OB' | split; [exact BUF' | exact LB']]].
            intros y Hy Hne E. apply FRESH. rewrite <- E. exact Hy.
      }
  Qed.
End LTAIL.
End P_h_crls_ltail.

Module P_h_crls_long.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_reserve OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_loop OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls_ltail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CRLS_LONG.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  #[using="HOK MEMCPY"] Lemma crls_long_ok : crls_contract_if cfg HI GP TP HTOP STATIC (fun rem0 => (23 <= rem0)%Z).
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (reserve_long_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as RES.
    pose proof (ltail_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as TAIL.
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros fx regs m md hs o f ptr0 rem0 ojunk bs0 ret K Hr23 HP MD UB Ha0 Ha1 Ha2 OBJ Ho8 FDP Hrem PAY LPAY PAYB
      Hso Hoe Hsf Hfe Hof Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold CRLS_NEED, SOE_NEED, P_MNEED in *.
    destruct PAYB as [E0|(q0 & k0 & Hq0 & Hq01 & Hq02)]; [lia|].
    destruct (BOK _ _ _ HP) as [B1 O1].
    destruct (B1 q0 k0 Hq0) as (Hk0 & Hreg0 & _ & QDO0 & QDJ0). unfold P_IMG_LO, P_IMG_END in Hreg0.
    resume MD. rewrite Ha0, Ha1, Ha2, Hra.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bytes_at_bound _ _ _ _ PAY) as Bpay.
    pose proof (munch_refl [(bv_unsigned sp - (48 + (80 + (16 + 8192))), bv_unsigned sp); (o, o + 24); (f, f + 16)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    carve_frame 48%nat ST.
    do 7 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with H : rw_cells PSEGS _ o _ |- _ => rename H into OBJ0 end.
    lazymatch goal with H : rw_cells PSEGS _ (bv_unsigned sp + -48) _ |- _ => rename H into FR end.
    lazymatch goal with H : rw_cells PSEGS _ f _ |- _ => rename H into FDP1 end.
    lazymatch goal with H : stk PSEGS _ _ (bv_unsigned sp + -48) |- _ => rename H into ST1 end.
    lazymatch goal with H : bytes_at PSEGS _ ptr0 bs0 |- _ => rename H into PAY1 end.
    name_mem m0.
    (* [comment removed for export] *)
    assert (MERGE : forall (fx1 : FPState) (rq : bvmap 5 word), @fp_csr fx1 = @fp_csr fx ->
        getr rq 2 = Z_to_bv 64 (bv_unsigned sp + -48) -> getr rq 3 = getr regs 3 -> getr rq 4 = getr regs 4 ->
        getr rq 8 = Z_to_bv 64 o -> getr rq 9 = Z_to_bv 64 128 -> getr rq 18 = Z_to_bv 64 f ->
        getr rq 11 = Z_to_bv 64 (Z.min 128 rem0) ->
        getr rq 21 = getr regs 21 -> getr rq 22 = getr regs 22 -> getr rq 23 = getr regs 23 -> getr rq 24 = getr regs 24 ->
        getr rq 25 = getr regs 25 -> getr rq 26 = getr regs 26 -> getr rq 27 = getr regs 27 ->
        realizes_cfg PSEGS cfg (mkCfg (@mkst fx1 rq (Z_to_bv 64 0x22d38) m0 (seg_rom PSEGS)) md) K).
    { intros fx1 rq Hfx1 Q2 Q3 Q4 Q8 Q9 Q18 Q11 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
      resume MD. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q11, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: exit_rz r1 HR1.
      all: lazymatch type of MU with ?T => change (keep T) in MU end.
      all: assert (HP1 : Heap hs m0 md) by (unfold keep in MU; eapply FRAME; [exact HP | exact MU | exact WM |];
              intros z Hz; cbn [outside] in Hz; destruct (outside_dec (owned hs) z) as [Ho|Ho]; [exact Ho|];
              specialize (O1 z Ho); lia).
      all: assert (SP1 : sp_of r1 = (bv_unsigned sp + -48)%Z) by (unfold sp_of; rewrite HR1; getr_leaf; rewrite unsigned_lit by lia; reflexivity).
      all: assert (Rn : (23 <= Z.min 128 rem0 <= 128)%Z) by lia.
      all: destruct (rec_bounds (Z.min 128 rem0) Rn) as (RN1 & _ & _).
      all: assert (UBr : (U md + MCHARGE (rec (Z.min 128 rem0) + 1) <= UBOUND)%Z) by (clear - UB RN1; unfold MCHARGE in *; lia).
      all: eapply (RES _ r1 m0 md hs o (Z.min 128 rem0) (Z_to_bv 64 0x22d40) K HP1 MD UBr).
      all: try (rewrite HR1; getr_leaf; first [reflexivity | (f_equal; lia)]).
      all: try lia.
      all: try (rewrite SP1; lia).
      all: try (rewrite HR1; getr_leaf; assumption).
      all: try (rewrite SP1; Z.div_mod_to_equations; lia).
      all: try reflexivity.
      all: try exact OBJ0.
      all: try (rewrite SP1; unfold SOE_NEED, P_MNEED; lia).
      all: try (rewrite SP1; unfold SOE_NEED, P_MNEED; replace (bv_unsigned sp + -48 - (80 + (16 + 8192)))%Z with (bv_unsigned sp - (48 + (80 + (16 + 8192))))%Z by lia; exact ST1).
      all: intros fx2 r2 m2 md2 hs2 p buf Hfx2 HP2 MD2 VM2 UB2 KP2 BADD FRESH CS MU2 ST2 OBJ2 BUF2 LB2.
      all: rewrite SP1 in MU2, ST2. all: unfold SOE_NEED, P_MNEED in MU2, ST2.
      all: set (n := Z.min 128 rem0) in *.
      all: assert (Hn : (23 <= n <= 128 /\ n <= rem0)%Z) by (unfold n; lia).
      all: pose proof (rec_bounds n ltac:(lia)) as (Hc1 & Hc2 & Hc3).
      all: set (c := rec n) in *.
      all: destruct (BOK _ _ _ HP2) as [B2 O2].
      all: destruct (B2 p (c + 1)%Z (proj2 (BADD (p, c + 1)%Z) (or_introl eq_refl))) as (Hn2 & Hreg2 & BST2 & BDO2 & BDJ2).
      all: unfold P_IMG_LO, P_IMG_END in Hreg2.
      all: assert (HINQ2 : In (q0, k0) (blocks hs2)) by (apply BADD; right; exact Hq0).
      all: assert (DJP : (p + (c + 1) <= q0 \/ q0 + k0 <= p)%Z)
             by (apply (BDJ2 q0 k0 HINQ2); intros E; apply FRESH; rewrite <- E; exact Hq0).
      all: assert (AGF : agree_on m0 m2 (bv_unsigned sp + -48)%Z 48) by
             (eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
              [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]).
      all: assert (AGD : agree_on m0 m2 f 16) by
             (eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
              [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]).
      all: assert (AGP : agree_on m0 m2 ptr0 rem0) by
             (eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
              [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | right; exists q0, k0; repeat split; try assumption; lia]).
      all: apply (rw_cells_agree PSEGS m0 m2) in FR; [|exact AGF].
      all: apply (rw_cells_agree PSEGS m0 m2) in FDP1; [|exact AGD].
      all: apply (bytes_at_agree PSEGS m0 m2) in PAY1; [|rewrite LPAY; exact AGP].
      all: clear AGF AGD AGP.
      all: lazymatch type of MU2 with ?T => change (keep T) in MU2 end.
      all: resume MD2. all: cs_resume CS HR1.
      all: pose proof (munch_refl [(bv_unsigned sp - (48 + (80 + (16 + 8192))), bv_unsigned sp); (o, o + 24); (f, f + 16); (p, p + c + 1)]%Z m2) as MU'.
      all: pose proof (wmono_refl PSEGS m2) as WM'.
      all: step. (* [comment removed for export] *)
      all: if_vm.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: if_not_taken.
      all: step. (* [comment removed for export] *)
      all: step. (* [comment removed for export] *)
      all: pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      all: eapply evt_cut; [ eapply (loopL_loop (Z_to_bv 64 (bv_unsigned sp + -48)) (getr regs 3) (getr regs 4) (getr regs 21) (getr regs 22)
                    (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr m2 o f ptr0 rem0 bs0 c p)
                    with (k := 129%nat) (i := 1%Z) (s := 0%Z) (rem := rem0) | ].
      all: try rewrite USP.
      all: try lia.
      all: try exact OBJ2.
      all: try exact BUF2.
      all: try exact LB2.
      all: try apply munch_refl.
      all: try apply wmono_refl.
      all: try (replace (ptr0 + rem0 - rem0)%Z with ptr0 by lia; exact FDP1).
      all: try (destruct (stk_split PSEGS m2 _ (bv_unsigned sp + -48 - 64) _ ST2 ltac:(lia)) as [_ S2]; exact S2).
      all: try (intros mm MUm; eapply bytes_at_transport; [exact PAY1 | exact MUm | cbn [disjoint_from]; rewrite LPAY; repeat split; try exact I; lia]).
      all: intros ms' PO; destruct PO as (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x28 & x29 & x30 & x31
                                        & m3 & s' & ptr' & rem' & ob' & -> & MU3 & WM3 & ST3 & FDP3 & Hpr & OB3 & BUF3 & LOB3 & Hs3).
      all: rewrite USP in *.
      all: apply (rw_cells_transport_munch PSEGS [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (o, o + 24); (f, f + 16); (p, p + c + 1)]%Z m2 m3) in FR;
             [|exact MU3 | cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; lia].
      all: destruct (stk_split PSEGS m2 _ (bv_unsigned sp + -48 - 64) _ ST2 ltac:(lia)) as [S1 _].
      all: apply (stk_transport_munch PSEGS [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (o, o + 24); (f, f + 16); (p, p + c + 1)]%Z m2 m3) in S1;
             [|exact MU3 | cbn [disjoint_from]; repeat split; try exact I; lia].
      all: pose proof (stk_merge PSEGS m3 _ _ _ S1 ST3 ltac:(lia)) as STm.
      all: exit_rz r3 HR3.
      all: lazymatch type of MU' with ?T => change (keep T) in MU' end.
      all: assert (HP3 : Heap hs2 m3 md2) by (unfold keep in MU'; eapply FRAME; [exact HP2 | eapply munch_trans; [exact MU'|] | eapply wmono_trans; [exact WM' | exact WM3] |];
              [ eapply munch_weaken; [|exact MU3]; unfold sub_fp; intros z Hz; cbn [outside] in Hz |- *; repeat split; try exact I; lia
              | intros z Hz; cbn [outside] in Hz; destruct (outside_dec (owned hs2) z) as [Ho|Ho]; [exact Ho|];
                pose proof (O2 z Ho) as [Hz1 _];
                assert (Hzb : ~ (p <= z < p + (c + 1))%Z) by (intros Hin; exact (Ho (disjoint_outside _ _ _ z BDO2 Hin))); lia ]).
      all: assert (SP3 : sp_of r3 = (bv_unsigned sp + -48)%Z) by (unfold sp_of; rewrite HR3; getr_leaf; rewrite unsigned_lit by lia; reflexivity).
      all: assert (Hsn : (s' <= n)%Z) by (unfold n; lia).
      all: eapply (TAIL _ r3 m3 md2 hs2 o c s' p ob' (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ret K HP3 MD2 ltac:(clear - UB UB2 RN1; unfold MCHARGE in *; lia)).
      all: try (rewrite HR3; getr_leaf; first [reflexivity | assumption]).
      all: try (rewrite SP3; first [exact FR | exact STm | lia | (Z.div_mod_to_equations; lia)]).
      all: try lia.
      all: try assumption.
      all: try (intros Hs23; pose proof (rec_mono s' n ltac:(lia)); unfold c; lia).
      all: try (apply BADD; left; reflexivity).
      all: try (rewrite SP3; unfold SOE_NEED, P_MNEED; lia).
      all: try (rewrite SP3; unfold SOE_NEED, P_MNEED; replace (bv_unsigned sp + -48 - (80 + (16 + 8192)))%Z with (bv_unsigned sp - (48 + (80 + (16 + 8192))))%Z by lia; exact STm).
      all: intros fx4 r4 m4 md4 hs3 Hfx4 HP4 MD4 VM4 UB4 KP4 G2 G8 G9 G18 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27 MU4 AG4 ST4 RES4.
      all: rewrite SP3 in G2, MU4, ST4. all: unfold SOE_NEED, P_MNEED in MU4, ST4.
      all: unfold keep in MU, MU2, MU'.
      all: assert (FDP4 : rw_cells PSEGS m4 f [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')]) by
             (eapply rw_cells_agree; [exact FDP3|];
              eapply (static_agree STATIC _ P_IMG_LO P_IMG_END HTOP m3 m4 _ _ SOK MU4);
              [cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; lia | lia | unfold P_IMG_LO; lia | unfold P_IMG_LO, P_IMG_END; lia | simpl_sizes; lia]).
      all: apply (CONT fx4 r4 m4 md4 hs3 s' ptr' rem'); [congruence | exact HP4 | exact MD4 | exact (vm_only_trans _ _ _ VM2 VM4) | clear - UB2 UB4 RN1; unfold MCHARGE in *; lia | apply (keep_trans P_KEEP m m0 m4); [eapply keep_munch; [|exact MU]; keep_side | apply (keep_trans P_KEEP m0 m2 m4); [exact KP2 | apply (keep_trans P_KEEP m2 m3 m4); [eapply keep_trans; [eapply keep_munch; [|exact MU']; keep_side | eapply keep_munch; [|exact MU3]; keep_side] | exact KP4]]] | | | | | exact FDP4 | exact (proj1 Hpr) | lia | lia | lia | ].
      1:{ repeat split.
          all: first [ exact G8 | exact G9 | exact G18 | exact G19 | exact G20
                  | (rewrite G2; apply bv_eq; rewrite unsigned_lit by lia; unfold sp; lia)
                  | (first [rewrite G3 | rewrite G4 | rewrite G21 | rewrite G22 | rewrite G23 | rewrite G24 | rewrite G25 | rewrite G26 | rewrite G27];
                     rewrite HR3; getr_leaf; reflexivity) ]. }
      1:{ clear DJP Hreg0 Hof. intros z Hz. rewrite outside_app in Hz. destruct Hz as (HzS & Hz). cbn [outside app] in Hz. unfold P_IMG_LO, P_IMG_END in Hz.
          rewrite (MU4 z) by (apply outside_app; split; [exact HzS | cbn [outside app]; unfold P_IMG_LO, P_IMG_END; repeat split; try exact I; lia]).
          rewrite (MU3 z) by (cbn [outside]; repeat split; try exact I; lia).
          rewrite (MU2 z) by (apply outside_app; split;
                                 [ eapply (owned_out PSEGS _ _ _ _ _ _ _ _ hs m0 md); [exact BOK | exact HP1 | exact HzS | unfold P_IMG_LO; lia | unfold P_IMG_END; lia]
                                 | apply outside_app; split;
                                   [ eapply (owned_out PSEGS _ _ _ _ _ _ _ _ hs2 m2 md2); [exact BOK | exact HP2 | exact HzS | unfold P_IMG_LO; lia | unfold P_IMG_END; lia]
                                   | cbn [outside]; repeat split; try exact I; lia ] ]).
          rewrite (MU z) by (cbn [outside]; repeat split; try exact I; lia). reflexivity. }
      1:{ clear DJP Hreg0 Hof. intros q k Hq.
          assert (Hq2 : In (q, k) (blocks hs2)) by (apply BADD; right; exact Hq).
          assert (Hqne : (q, k) <> (p, c + 1)%Z) by (intros E; apply FRESH; rewrite <- E; exact Hq).
          destruct (B1 q k Hq) as (_ & Hqr & _ & _ & _). unfold P_IMG_LO, P_IMG_END in Hqr.
          pose proof (BDJ2 q k Hq2 Hqne) as QD'.
          destruct (AG4 q k Hq2 Hqne) as [Hq3 AG4q]. split; [exact Hq3|].
          eapply agree_on_trans; [eapply agree_on_of_munch; [exact MU | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia] |].
          eapply agree_on_trans; [eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
            [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try assumption; lia] |].
          eapply agree_on_trans; [eapply agree_on_of_munch; [exact MU3 | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia] |].
          exact AG4q. }
      1:{ replace (bv_unsigned sp - (48 + (80 + (16 + 8192))))%Z with (bv_unsigned sp + -48 - (80 + (16 + 8192)))%Z by lia.
          replace (bv_unsigned sp) with (bv_unsigned sp + -48 + 48)%Z at 2 by lia. exact ST4. }
      1:{ unfold ltail_result in RES4. unfold str_result. destruct RES4 as [(Hs22 & BDEL & OBs & ob & LOB & OBA) | (c' & p' & buf' & Hc'1 & Hc'2 & Hc'3 & BREL & BFR & OBl & BUFl & LBl)].
          - left. split; [exact Hs22|]. split; [|split; [exact OBs | exists ob; split; assumption]].
            intros y. unfold blocks_del in BDEL. unfold blocks_add in BADD. rewrite (BDEL y), (BADD y).
            split; [intros [[A|A] B]; [exfalso; exact (B A) | exact A] | intros Hy; split; [right; exact Hy | intros E; apply FRESH; rewrite <- E; exact Hy]].
          - right. exists c', p', buf'. split; [exact Hc'1|]. split; [exact Hc'2|]. split; [exact Hc'3|].
            split; [|split; [|split; [exact OBl | split; [exact BUFl | exact LBl]]]].
            + intros y. rewrite (BREL y). unfold blocks_add in BADD. rewrite (BADD y).
              split; [intros [A|[[A|A] B]]; [left; exact A | exfalso; exact (B A) | right; exact A] |
                      intros [A|A]; [left; exact A | right; split; [right; exact A | intros E; apply FRESH; rewrite <- E; exact A]]].
            + intros Hy. apply (BFR (p', c' + 1)%Z); [apply BADD; right; exact Hy | intros E; apply FRESH; rewrite <- E; exact Hy | reflexivity]. }
    }
    step. (* [comment removed for export] *)
    let Hc := fresh "Hc" in if_cases Hc;
      [ cond_cleanup Hc | cond_cleanup Hc; step (* [comment removed for export] *) ].
    all: exit_rz rq HRq.
    all: apply (MERGE _ rq); [congruence | ..].
    all: rewrite HRq; getr_leaf; first [reflexivity | (f_equal; lia) | (apply bv_eq; rewrite !unsigned_lit by lia; lia)].
  Qed.
End CRLS_LONG.
End P_h_crls_long.

Module P_h_crls.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls_short OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls_long.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CRLS.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.

  #[using="HOK MEMCPY"] Lemma crls_ok : crls_contract cfg HI GP TP HTOP STATIC.
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    intros fx regs m md hs o f ptr0 rem0 ojunk bs0 ret K _.
    destruct (Z_le_gt_dec rem0 22) as [H|H].
    - exact (crls_short_ok cfg HI GP TP HTOP STATIC HOK fx regs m md hs o f ptr0 rem0 ojunk bs0 ret K H).
    - exact (crls_long_ok cfg HI GP TP HTOP STATIC HOK MEMCPY fx regs m md hs o f ptr0 rem0 ojunk bs0 ret K ltac:(cbn; lia)).
  Qed.
End CRLS.
End P_h_crls.

Module P_h_fuzz_E.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_from_chars_double_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_delete OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section FZE.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).
  Local Notation fz_cont := (fz_cont cfg HI HTOP STATIC).
  Local Notation fz_acc := (fz_acc HI HTOP STATIC).
  Local Notation ctx_ok := (ctx_ok HI GP TP HTOP STATIC).
  Local Notation regs_ok := (regs_ok HI GP TP).

  Definition saves_cells (c : fz_ctx HI) : list cell :=
    [C8 (getr (z_regs c) 9); C8 (getr (z_regs c) 8); C8 (z_ret c)].

  #[using="Type"] Lemma fz_epi : forall (c : fz_ctx HI) (fx : FPState) regs m md hs,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md [] -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells c) ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22c94) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros c fx regs m md hs CX CONT ACC UA RG SAV ST FRM.
    pose proof ACC as (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP).
    destruct RG as (SPR & R3 & R4 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    unfold saves_cells in SAV. unfold sp_of in *. unfold P_h_fuzz_base.fz_cont in CONT.
    resume MD.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ret_pc_even_w (z_ret c) Eret).
    exit_rz r1 HR1.
    apply (CONT _ r1 m md hs); [exact HP | exact MD | exact VM | clear - UA; unfold FUZZ_CHARGE; lia | exact KP | rewrite HR1; getr_leaf; reflexivity | | rewrite Hfc; exact FRM | | exact MU0 | | ].
    - repeat split; rewrite HR1; getr_leaf; try reflexivity; try congruence.
      apply bv_eq. rewrite unsigned_lit by lia. rewrite SPR. reflexivity.
    - intros y. rewrite (BL y). cbn. tauto.
    - intros p n Hpn. apply agree_blocks_eq. exact (AG0 p n Hpn).
    - pose proof (stk_release PSEGS m _ _ _ ST SAV ltac:(lia)) as S. cbn [cells_size csize Nat.add] in S.
      eapply stk_at; [exact S | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac regs_ok_tree RG HR :=
    let SPR := fresh "SPR" in let R3 := fresh "R3" in let R4 := fresh "R4" in
    destruct RG as (SPR & R3 & R4 & ?R18 & ?R19 & ?R20 & ?R21 & ?R22 & ?R23 & ?R24 & ?R25 & ?R26 & ?R27);
    unfold P_h_fuzz_base.regs_ok, sp_of; repeat split; rewrite HR; getr_leaf; first [assumption | lia].

  #[using="HOK"] Lemma fz_dtor_d : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bd,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bd) -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells c) ->
    str_obj m (sp_of regs + 56) bd ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs + 56) ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22c78) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bd CX CONT ACC UA RG SAV OBJ ST REST FRM.
    pose proof ACC as (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof (str_obj_stk _ _ _ OBJ) as OST.
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct bd as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      resume MD.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (cap_landm2 cap) by lia.
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & _ & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      unfold FUZZ_NEED, from_chars_double_need in *.
      assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned (getr regs 2) - P_FNEED <= bv_unsigned (getr regs 2) + 56)%Z) by (unfold P_FNEED; lia).
      destruct (stk_split PSEGS m _ (bv_unsigned (getr regs 2) - P_FNEED) _ ST T1) as [STa STb]. clear T1.
      assert (T1 : (bv_unsigned (getr regs 2) - P_FNEED <= bv_unsigned (getr regs 2) <= bv_unsigned (getr regs 2) + 56)%Z) by (unfold P_FNEED; lia).
      destruct (stk_split PSEGS m _ (bv_unsigned (getr regs 2)) _ STb T1) as [STb' STc]. clear STb T1.
      eapply (delete_ok cfg HI GP TP HTOP STATIC HOK _ r1 m md hs p (cap + 1)%Z (Z_to_bv 64 0x22c94) (z_K c) HP MD).
      + rewrite HR1; getr_leaf; reflexivity.
      + right. exact Hin.
      + rewrite HR1; getr_leaf; reflexivity.
      + reflexivity.
      + rewrite HR1; getr_leaf; exact R3.
      + rewrite HR1; getr_leaf; exact R4.
      + rewrite SP1. Z.div_mod_to_equations. lia.
      + rewrite SP1. lia.
      + rewrite SP1. unfold P_FNEED. lia.
      + rewrite SP1. exact STb'.
      + intros fx2 r2 m2 md2 hs2 Hfx2 HP2 MD2 VM2 UB2 KP2 BL2 CS MU2 ST2.
        rewrite SP1 in MU2, ST2.
        replace (p =? 0)%Z with false in BL2 by (symmetry; apply Z.eqb_neq; lia). cbv iota in BL2.
        assert (MUc : munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++ [(bv_unsigned (getr regs 2) - P_FNEED, bv_unsigned (getr regs 2))])%Z m m2).
        { eapply (munch_coarsen PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ BOK HP HP2 MU2).
          intros x Hx. cbn [outside app] in Hx |- *. unfold P_IMG_LO, P_IMG_END in Hx. unfold P_FNEED in *. lia. }
        assert (ACC2 : fz_acc c hs2 m2 md2 []).
        { destruct (acc_del (blocks (z_hs c)) (blocks hs) (blocks hs2) [] (p, cap + 1)%Z BL FR ND BL2) as (BL' & FR' & ND').
          eapply (fz_acc_cps cfg HI GP TP HTOP STATIC HOK c hs m md _ hs2 m2 md2 _ [] CX ACC HP2 MD2 VM2 KP2 MUc); [ | | exact BL' | exact FR' | exact ND'].
          - intros x Hx. cbn [outside] in Hx. unfold P_FNEED in Hx. unfold FUZZ_NEED, from_chars_double_need. lia.
          - intros q k Hq.
            assert (Hq1 : In (q, k) (blocks hs)) by (apply BL; left; exact Hq).
            assert (Hne : (q, k) <> (p, cap + 1)%Z) by (intros E; apply (FR (p, cap + 1)%Z (or_introl eq_refl)); rewrite <- E; exact Hq).
            assert (Hq2 : In (q, k) (blocks hs2)) by (apply BL2; split; [exact Hq1 | exact Hne]).
            destruct (B1 q k Hq1) as (_ & Hqr & _). unfold P_IMG_LO, P_IMG_END in Hqr.
            pose proof (BDJ q k Hq1 Hne) as DJ.
            eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ _ BOK HP HP2 MU2);
              [cbn [disjoint_from]; unfold P_FNEED; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try assumption; lia]. }
        unfold P_FNEED in *. xport SOK MUc.
        pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
        assert (SP2 : sp_of r2 = bv_unsigned (getr regs 2)) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
        apply (fz_epi c fx2 r2 m2 md2 hs2 CX CONT ACC2 ltac:(clear - UA UB2; lia) RG2).
        * rewrite SP2. exact SAV.
        * rewrite SP2. unfold FUZZ_NEED, from_chars_double_need.
          eapply stk_merge'; [exact STa | | reflexivity | lia].
          eapply stk_merge'; [exact ST2 | | reflexivity | lia].
          eapply stk_merge'; [exact STc | | reflexivity | lia].
          eapply stk_merge'; [exact OST | exact REST | lia | lia].
        * rewrite Hfx2, Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      resume MD.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      apply (fz_epi c fx0 r1 m md hs CX CONT ACC UA RG1).
      + rewrite SP1. exact SAV.
      + rewrite SP1. unfold FUZZ_NEED, from_chars_double_need. eapply stk_merge'; [exact ST | | reflexivity | lia]. eapply stk_merge'; [exact OST | exact REST | lia | lia].
      + rewrite Hfc. exact FRM.
  Qed.

  #[using="HOK"] Lemma fz_dtor_f : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bf bd,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells c) ->
    str_obj m (sp_of regs + 56) bd ->
    str_obj m (sp_of regs + 32) bf ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs + 32) ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22c5c) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bf bd CX CONT ACC UA RG SAV OBJD OBJ ST REST FRM.
    pose proof ACC as (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof (str_obj_stk _ _ _ OBJ) as OST.
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct bf as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      resume MD.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (cap_landm2 cap) by lia.
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & _ & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned (getr regs 2) - P_FNEED <= bv_unsigned (getr regs 2) + 32)%Z) by (unfold P_FNEED; lia).
      destruct (stk_split PSEGS m _ (bv_unsigned (getr regs 2) - P_FNEED) _ ST T1) as [STa STb]. clear T1.
      assert (T1 : (bv_unsigned (getr regs 2) - P_FNEED <= bv_unsigned (getr regs 2) <= bv_unsigned (getr regs 2) + 32)%Z) by (unfold P_FNEED; lia).
      destruct (stk_split PSEGS m _ (bv_unsigned (getr regs 2)) _ STb T1) as [STb' STc]. clear STb T1.
      eapply (delete_ok cfg HI GP TP HTOP STATIC HOK _ r1 m md hs p (cap + 1)%Z (Z_to_bv 64 0x22c78) (z_K c) HP MD).
      + rewrite HR1; getr_leaf; reflexivity.
      + right. exact Hin.
      + rewrite HR1; getr_leaf; reflexivity.
      + reflexivity.
      + rewrite HR1; getr_leaf; exact R3.
      + rewrite HR1; getr_leaf; exact R4.
      + rewrite SP1. Z.div_mod_to_equations. lia.
      + rewrite SP1. lia.
      + rewrite SP1. unfold P_FNEED. lia.
      + rewrite SP1. exact STb'.
      + intros fx2 r2 m2 md2 hs2 Hfx2 HP2 MD2 VM2 UB2 KP2 BL2 CS MU2 ST2.
        rewrite SP1 in MU2, ST2.
        replace (p =? 0)%Z with false in BL2 by (symmetry; apply Z.eqb_neq; lia). cbv iota in BL2.
        assert (MUc : munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++ [(bv_unsigned (getr regs 2) - P_FNEED, bv_unsigned (getr regs 2))])%Z m m2).
        { eapply (munch_coarsen PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ BOK HP HP2 MU2).
          intros x Hx. cbn [outside app] in Hx |- *. unfold P_IMG_LO, P_IMG_END in Hx. unfold P_FNEED in *. lia. }
        assert (ACC2 : fz_acc c hs2 m2 md2 (opt_list bd)).
        { destruct (acc_del (blocks (z_hs c)) (blocks hs) (blocks hs2) (opt_list bd) (p, cap + 1)%Z BL FR ND BL2) as (BL' & FR' & ND').
          eapply (fz_acc_cps cfg HI GP TP HTOP STATIC HOK c hs m md _ hs2 m2 md2 _ (opt_list bd) CX ACC HP2 MD2 VM2 KP2 MUc); [ | | exact BL' | exact FR' | exact ND'].
          - intros x Hx. cbn [outside] in Hx. unfold P_FNEED in Hx. unfold FUZZ_NEED, from_chars_double_need. lia.
          - intros q k Hq.
            assert (Hq1 : In (q, k) (blocks hs)) by (apply BL; left; exact Hq).
            assert (Hne : (q, k) <> (p, cap + 1)%Z) by (intros E; apply (FR (p, cap + 1)%Z (or_introl eq_refl)); rewrite <- E; exact Hq).
            assert (Hq2 : In (q, k) (blocks hs2)) by (apply BL2; split; [exact Hq1 | exact Hne]).
            destruct (B1 q k Hq1) as (_ & Hqr & _). unfold P_IMG_LO, P_IMG_END in Hqr.
            pose proof (BDJ q k Hq1 Hne) as DJ.
            eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ _ BOK HP HP2 MU2);
              [cbn [disjoint_from]; unfold P_FNEED; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try assumption; lia]. }
        unfold P_FNEED in *. xport SOK MUc.
        pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
        assert (SP2 : sp_of r2 = bv_unsigned (getr regs 2)) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
        apply (fz_dtor_d c fx2 r2 m2 md2 hs2 bd CX CONT ACC2 ltac:(clear - UA UB2; lia) RG2).
        * rewrite SP2. exact SAV.
        * rewrite SP2. exact OBJD.
        * rewrite SP2. unfold FUZZ_NEED, from_chars_double_need.
          eapply stk_merge'; [exact STa | | reflexivity | lia].
          eapply stk_merge'; [exact ST2 | | reflexivity | lia].
          eapply stk_merge'; [exact STc | eapply stk_at; [exact OST | reflexivity | lia] | reflexivity | lia].
        * rewrite SP2. exact REST.
        * rewrite Hfx2, Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      resume MD.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      apply (fz_dtor_d c fx0 r1 m md hs bd CX CONT ACC UA RG1).
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. unfold FUZZ_NEED, from_chars_double_need. eapply stk_merge'; [exact ST | eapply stk_at; [exact OST | reflexivity | lia] | reflexivity | lia].
      + rewrite SP1. exact REST.
      + rewrite Hfc. exact FRM.
  Qed.

  #[using="HOK"] Lemma fz_dtor_i : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bi bf bd,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bi ++ opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells c) ->
    str_obj m (sp_of regs + 56) bd ->
    str_obj m (sp_of regs + 32) bf ->
    str_obj m (sp_of regs) bi ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    stk PSEGS m (sp_of regs + 24) (sp_of regs + 32) ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22c40) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bi bf bd CX CONT ACC UA RG SAV OBJD OBJF OBJ ST RES REST FRM.
    pose proof ACC as (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof (str_obj_stk _ _ _ OBJ) as OST.
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct bi as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      resume MD.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (cap_landm2 cap) by lia.
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & _ & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned (getr regs 2) - P_FNEED <= bv_unsigned (getr regs 2))%Z) by (unfold P_FNEED; lia).
      destruct (stk_split PSEGS m _ (bv_unsigned (getr regs 2) - P_FNEED) _ ST T1) as [STa STb]. clear T1.
      eapply (delete_ok cfg HI GP TP HTOP STATIC HOK _ r1 m md hs p (cap + 1)%Z (Z_to_bv 64 0x22c5c) (z_K c) HP MD).
      + rewrite HR1; getr_leaf; reflexivity.
      + right. exact Hin.
      + rewrite HR1; getr_leaf; reflexivity.
      + reflexivity.
      + rewrite HR1; getr_leaf; exact R3.
      + rewrite HR1; getr_leaf; exact R4.
      + rewrite SP1. Z.div_mod_to_equations. lia.
      + rewrite SP1. lia.
      + rewrite SP1. unfold P_FNEED. lia.
      + rewrite SP1. exact STb.
      + intros fx2 r2 m2 md2 hs2 Hfx2 HP2 MD2 VM2 UB2 KP2 BL2 CS MU2 ST2.
        rewrite SP1 in MU2, ST2.
        replace (p =? 0)%Z with false in BL2 by (symmetry; apply Z.eqb_neq; lia). cbv iota in BL2.
        assert (MUc : munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++ [(bv_unsigned (getr regs 2) - P_FNEED, bv_unsigned (getr regs 2))])%Z m m2).
        { eapply (munch_coarsen PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ BOK HP HP2 MU2).
          intros x Hx. cbn [outside app] in Hx |- *. unfold P_IMG_LO, P_IMG_END in Hx. unfold P_FNEED in *. lia. }
        assert (ACC2 : fz_acc c hs2 m2 md2 (opt_list bf ++ opt_list bd)).
        { destruct (acc_del (blocks (z_hs c)) (blocks hs) (blocks hs2) (opt_list bf ++ opt_list bd) (p, cap + 1)%Z BL FR ND BL2) as (BL' & FR' & ND').
          eapply (fz_acc_cps cfg HI GP TP HTOP STATIC HOK c hs m md _ hs2 m2 md2 _ (opt_list bf ++ opt_list bd) CX ACC HP2 MD2 VM2 KP2 MUc); [ | | exact BL' | exact FR' | exact ND'].
          - intros x Hx. cbn [outside] in Hx. unfold P_FNEED in Hx. unfold FUZZ_NEED, from_chars_double_need. lia.
          - intros q k Hq.
            assert (Hq1 : In (q, k) (blocks hs)) by (apply BL; left; exact Hq).
            assert (Hne : (q, k) <> (p, cap + 1)%Z) by (intros E; apply (FR (p, cap + 1)%Z (or_introl eq_refl)); rewrite <- E; exact Hq).
            assert (Hq2 : In (q, k) (blocks hs2)) by (apply BL2; split; [exact Hq1 | exact Hne]).
            destruct (B1 q k Hq1) as (_ & Hqr & _). unfold P_IMG_LO, P_IMG_END in Hqr.
            pose proof (BDJ q k Hq1 Hne) as DJ.
            eapply (cps_agree PSEGS _ _ _ _ _ _ _ _ hs hs2 m m2 md md2 _ _ _ BOK HP HP2 MU2);
              [cbn [disjoint_from]; unfold P_FNEED; repeat split; try exact I; lia | lia | lia | right; exists q, k; repeat split; try assumption; lia]. }
        unfold P_FNEED in *. xport SOK MUc.
        pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
        assert (SP2 : sp_of r2 = bv_unsigned (getr regs 2)) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
        apply (fz_dtor_f c fx2 r2 m2 md2 hs2 bf bd CX CONT ACC2 ltac:(clear - UA UB2; lia) RG2).
        * rewrite SP2. exact SAV.
        * rewrite SP2. exact OBJD.
        * rewrite SP2. exact OBJF.
        * rewrite SP2. unfold FUZZ_NEED, from_chars_double_need.
          eapply stk_merge'; [exact STa | | reflexivity | lia].
          eapply stk_merge'; [exact ST2 | | reflexivity | lia].
          eapply stk_merge'; [eapply stk_at; [exact OST | reflexivity | reflexivity] | eapply stk_at; [exact RES | reflexivity | reflexivity] | lia | lia].
        * rewrite SP2. exact REST.
        * rewrite Hfx2, Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      resume MD.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      apply (fz_dtor_f c fx0 r1 m md hs bf bd CX CONT ACC UA RG1).
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact OBJF.
      + rewrite SP1. unfold FUZZ_NEED, from_chars_double_need.
        eapply stk_merge'; [exact ST | | reflexivity | lia].
        eapply stk_merge'; [eapply stk_at; [exact OST | reflexivity | reflexivity] | eapply stk_at; [exact RES | reflexivity | reflexivity] | lia | lia].
      + rewrite SP1. exact REST.
      + rewrite Hfc. exact FRM.
  Qed.
End FZE.
End P_h_fuzz_E.

Module P_h_fuzz_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_E.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section FZD.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis FCI : from_chars_int_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).
  Local Notation fz_cont := (fz_cont cfg HI HTOP STATIC).
  Local Notation fz_acc := (fz_acc HI HTOP STATIC).
  Local Notation ctx_ok := (ctx_ok HI GP TP HTOP STATIC).
  Local Notation regs_ok := (regs_ok HI GP TP).

  Ltac regs_ok_tree RG HR :=
    let SPR := fresh "SPR" in let R3 := fresh "R3" in let R4 := fresh "R4" in
    destruct RG as (SPR & R3 & R4 & ?R18 & ?R19 & ?R20 & ?R21 & ?R22 & ?R23 & ?R24 & ?R25 & ?R26 & ?R27);
    unfold P_h_fuzz_base.regs_ok, sp_of; repeat split; rewrite HR; getr_leaf; first [assumption | lia].

  (* [comment removed for export] *)
  #[using="HOK FCI"] Lemma fz_D2 : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bi bf bd rold tptr tlen tbs,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bi ++ opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    getr regs 10 = Z_to_bv 64 tptr -> getr regs 11 = Z_to_bv 64 (tptr + tlen) ->
    bytes_at PSEGS m tptr tbs -> Z.of_nat (length tbs) = tlen ->
    ((tptr = sp_of regs + 1 /\ tlen <= 22) \/ (16 <= tptr /\ tptr + tlen <= HTOP))%Z ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    str_obj m (sp_of regs + 56) bd -> str_obj m (sp_of regs + 32) bf -> str_obj m (sp_of regs) bi ->
    rw_cells PSEGS m (sp_of regs + 24) [C4 rold] ->
    stk PSEGS m (sp_of regs + 28) (sp_of regs + 32) ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22c28) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bi bf bd rold tptr tlen tbs CX CONT ACC UA RG Ha0 Ha1 TXT LTX WHERE SAV OBJD OBJF OBJI RESI RESF ST REST FRM.
    pose proof ACC as (HP & MD & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    destruct (acc_ro HI HTOP STATIC _ _ _ _ _ ACC) as [PR1 PR2].
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    pose proof (bytes_at_bound _ _ _ _ TXT) as BTX.
    resume MD. rewrite Ha0, Ha1.
    set (sp := getr regs 2) in *.
    pose proof (munch_refl [(z_sp c - (128 + (112 + 2496) + 5760), z_sp c)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned sp - 96 <= bv_unsigned sp)%Z) by lia.
    destruct (stk_split PSEGS m _ (bv_unsigned sp - 96) _ ST T1) as [STa STb]. clear T1 ST.
    assert (USa0 : bv_unsigned (Z_to_bv 64 tptr) = tptr) by (apply unsigned_lit; lia).
    assert (USa1 : bv_unsigned (Z_to_bv 64 (tptr + tlen)) = (tptr + tlen)%Z) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 24)) = (bv_unsigned sp + 24)%Z) by (apply unsigned_lit; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fz_call FCI.
    { reflexivity. }
    { reflexivity. }
    { rewrite USa0. exact TXT. }
    { rewrite USa0, USa1. lia. }
    { rewrite USa0, USa1. lia. }
    { rewrite USP. exact RESI. }
    { exact STb. }
    { exact PR1. }
    { rewrite USa0, USa1, USP. lia. }
    { rewrite USP. lia. }
    { rewrite USa0, USa1. lia. }
    { rewrite USP. lia. }
    { lia. }
    { exact FRM. }
    rewrite ?USP in *.
    lazymatch goal with H : rw_cells PSEGS ?mm (bv_unsigned sp + 24) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into RESI' end.
    lazymatch goal with H : stk PSEGS ?mm (bv_unsigned sp - 96) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STb' end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    exit_rz r1 HR1.
    assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
    assert (SP1 : sp_of r1 = bv_unsigned sp) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
    assert (ACC1 : fz_acc c hs m1 md (opt_list bi ++ opt_list bf ++ opt_list bd)).
    { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC MU WM).
      intros z Hz. cbn [outside] in Hz. unfold FUZZ_NEED, from_chars_double_need. lia. }
    pose proof (stk_of_rw_cells PSEGS m1 _ _ RESI') as SRI. cbn [cells_size csize Nat.add] in SRI.
    apply (fz_dtor_i cfg HI GP TP HTOP STATIC HOK c fx0 r1 m1 md hs bi bf bd CX CONT ACC1 UA RG1).
    - rewrite SP1. exact SAV.
    - rewrite SP1. exact OBJD.
    - rewrite SP1. exact OBJF.
    - rewrite SP1. exact OBJI.
    - rewrite SP1. unfold FUZZ_NEED, from_chars_double_need. eapply stk_merge'; [exact STa | exact STb' | reflexivity | lia].
    - rewrite SP1. eapply stk_merge'; [exact SRI | exact RESF | lia | lia].
    - rewrite SP1. exact REST.
    - rewrite Hfc. assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK FCI"] Lemma fz_D : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bi bf bd rold,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bi ++ opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 6 * MCHARGE 136)%Z -> regs_ok c regs ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    str_obj m (sp_of regs + 56) bd -> str_obj m (sp_of regs + 32) bf -> str_obj m (sp_of regs) bi ->
    rw_cells PSEGS m (sp_of regs + 24) [C4 rold] ->
    stk PSEGS m (sp_of regs + 28) (sp_of regs + 32) ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 104) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22bfc) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bi bf bd rold CX CONT ACC UA RG SAV OBJD OBJF OBJI RESI RESF ST REST FRM.
    pose proof ACC as (HP & MD & BL & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof OBJI as OBJ.
    unfold sp_of in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct bi as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & BST & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      assert (T1 : (p <= p + s <= p + (cap + 1))%Z) by lia.
      destruct (stk_split PSEGS m _ (p + s) _ BST T1) as [BS1 _]. clear T1.
      assert (T1 : (p <= p + s)%Z) by lia.
      destruct (stk_bytes PSEGS m p (p + s) BS1 T1) as (tbs & Ltbs & TXT). clear T1.
      resume MD.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      apply (fz_D2 c fx0 r1 m md hs (Some (p, cap + 1)%Z) bf bd rold p s tbs CX CONT ACC UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. first [reflexivity | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + lia.
      + right. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact OBJF.
      + rewrite SP1. exact OBJI.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF.
      + rewrite SP1. exact ST.
      + rewrite SP1. exact REST.
      + rewrite Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      pose proof (bytes_at_sub PSEGS m (bv_unsigned (getr regs 2) + 1) ob 0 (Z.to_nat s) (proj1 OBA) ltac:(lia)) as TXT.
      rewrite skipn_O, Z.add_0_r in TXT.
      resume MD.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)), (shr1_even s) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      apply (fz_D2 c fx0 r1 m md hs None bf bd rold (bv_unsigned (getr regs 2) + 1) s (firstn (Z.to_nat s) ob) CX CONT ACC UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. first [reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + rewrite firstn_length_le by lia. lia.
      + left. rewrite SP1. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact OBJF.
      + rewrite SP1. exact OBJI.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF.
      + rewrite SP1. exact ST.
      + rewrite SP1. exact REST.
      + rewrite Hfc. exact FRM.
  Qed.
End FZD.
End P_h_fuzz_D.

Module P_h_fuzz_C.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy_stmt P_from_chars_double_stmt P_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_E OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= fz_transport_chunks segs m a bs.

Section FZC.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Hypothesis FCF : from_chars_float_stmt.
  Hypothesis FCI : from_chars_int_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).
  Local Notation fz_cont := (fz_cont cfg HI HTOP STATIC).
  Local Notation fz_acc := (fz_acc HI HTOP STATIC).
  Local Notation ctx_ok := (ctx_ok HI GP TP HTOP STATIC).
  Local Notation regs_ok := (regs_ok HI GP TP).

  Ltac regs_ok_tree RG HR :=
    let SPR := fresh "SPR" in let R3 := fresh "R3" in let R4 := fresh "R4" in
    destruct RG as (SPR & R3 & R4 & ?R18 & ?R19 & ?R20 & ?R21 & ?R22 & ?R23 & ?R24 & ?R25 & ?R26 & ?R27);
    unfold P_h_fuzz_base.regs_ok, sp_of; repeat split; rewrite HR; getr_leaf; first [assumption | lia].

  (* [comment removed for export] *)
  #[using="HOK MEMCPY FCF FCI"] Lemma fz_C2 : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bf bd fmt ptr rem ji ri rf tptr tlen tbs,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 4 * MCHARGE 136)%Z -> regs_ok c regs ->
    getr regs 8 = Z_to_bv 64 fmt -> (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z -> getr regs 9 = Z_to_bv 64 FCF_OPT2 ->
    getr regs 10 = Z_to_bv 64 tptr -> getr regs 11 = Z_to_bv 64 (tptr + tlen) ->
    bytes_at PSEGS m tptr tbs -> Z.of_nat (length tbs) = tlen -> (tlen <= 2^26)%Z ->
    ((tptr = sp_of regs + 33 /\ tlen <= 22) \/ (16 <= tptr /\ tptr + tlen <= HTOP))%Z ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    rw_cells PSEGS m (sp_of regs + 88) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> pay_ok HI c ptr rem ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 88) ->
    str_obj m (sp_of regs + 56) bd -> str_obj m (sp_of regs + 32) bf ->
    rw_cells PSEGS m (sp_of regs) [CB 24 ji] ->
    rw_cells PSEGS m (sp_of regs + 24) [CB 4 ri] ->
    rw_cells PSEGS m (sp_of regs + 28) [C4 rf] ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22bd8) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY FCF FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bf bd fmt ptr rem ji ri rf tptr tlen tbs CX CONT ACC UA RG R8 FMT R9 Ha0 Ha1 TXT LTX Htl WHERE
      SAV FDP PAY RESD OBJD OBJF JUNK RESI RESF ST FRM.
    pose proof ACC as (HP & MD & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    destruct (acc_ro HI HTOP STATIC _ _ _ _ _ ACC) as [PR1 PR2].
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    pose proof (bytes_at_bound _ _ _ _ TXT) as BTX.
    resume MD. rewrite R8, R9, Ha0, Ha1.
    set (sp := getr regs 2) in *.
    pose proof (munch_refl [(z_sp c - (128 + (112 + 2496) + 5760), z_sp c)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned sp - (112 + 2496) <= bv_unsigned sp)%Z) by lia.
    destruct (stk_split PSEGS m _ (bv_unsigned sp - (112 + 2496)) _ ST T1) as [STa STb]. clear T1 ST.
    assert (USa0 : bv_unsigned (Z_to_bv 64 tptr) = tptr) by (apply unsigned_lit; lia).
    assert (USa1 : bv_unsigned (Z_to_bv 64 (tptr + tlen)) = (tptr + tlen)%Z) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 28)) = (bv_unsigned sp + 28)%Z) by (apply unsigned_lit; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fz_call FCF.
    { reflexivity. }
    { exact FMT. }
    { reflexivity. }
    { rewrite USa0. exact TXT. }
    { rewrite USa0, USa1. lia. }
    { rewrite USa0, USa1. lia. }
    { rewrite USa1. lia. }
    { rewrite USP. exact RESF. }
    { rewrite USP. Z.div_mod_to_equations. lia. }
    { unfold from_chars_float_need. exact STb. }
    { Z.div_mod_to_equations. lia. }
    { unfold from_chars_float_need. lia. }
    { rewrite USa0. lia. }
    { rewrite USP. lia. }
    { rewrite USP. lia. }
    { exact PR1. }
    { exact PR2. }
    { exact FRM. }
    { rewrite USa0, USa1. unfold from_chars_float_need. lia. }
    { rewrite USP. unfold from_chars_float_need. lia. }
    { rewrite USa0, USa1, USP. lia. }
    rewrite ?USP in *.
    lazymatch goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM' end.
    lazymatch goal with H : rw_cells PSEGS ?mm (bv_unsigned sp + 28) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into RESF' end.
    lazymatch goal with H : stk PSEGS ?mm (bv_unsigned sp - from_chars_float_need) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STb' end.
    unfold from_chars_float_need in STb'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    lazymatch goal with H : rw_cells PSEGS m1 (bv_unsigned sp + 24) _ |- _ => rename H into RESI' end.
    exit_rz r1 HR1.
    assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
    assert (SP1 : sp_of r1 = bv_unsigned sp) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
    assert (ACC1 : fz_acc c hs m1 md (opt_list bf ++ opt_list bd)).
    { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC MU WM).
      intros z Hz. cbn [outside] in Hz. unfold FUZZ_NEED, from_chars_double_need. lia. }
    pose proof ACC1 as (HP1 & _).
    destruct (pay_bytes cfg HI GP TP HTOP STATIC HOK c hs m1 md _ ptr rem ACC1 PAY) as (bs0 & PAYB & LPAY).
    pose proof (pay_blocks HI HTOP STATIC c hs m1 md _ ptr rem ACC1 PAY) as PAYIN.
    pose proof PAY as (Hp0 & Hrem & Hpr & _).
    assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned sp - CRLS_NEED <= bv_unsigned sp)%Z) by (unfold CRLS_NEED, SOE_NEED, P_MNEED; lia).
    pose proof (stk_merge PSEGS m1 _ _ _ STa STb' ltac:(lia)) as STw.
    destruct (stk_split PSEGS m1 _ (bv_unsigned sp - CRLS_NEED) _ STw T1) as [STa' STb'']. clear T1 STw STa STb'.
    pose proof (stk_of_rw_cells PSEGS m1 _ _ RESF') as SRF. cbn [cells_size csize Nat.add] in SRF. clear RESF'.
    eapply (crls_ok cfg HI GP TP HTOP STATIC HOK MEMCPY _ r1 m1 md hs (bv_unsigned sp) (bv_unsigned sp + 88)%Z ptr rem ji bs0
              (Z_to_bv 64 0x22bfc) (z_K c) I HP1 MD ltac:(clear - UA UCX; unfold FUZZ_CHARGE, MCHARGE in *; lia)).
    - rewrite HR1; getr_leaf. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
    - rewrite HR1; getr_leaf. reflexivity.
    - rewrite HR1; getr_leaf. reflexivity.
    - exact JUNK.
    - Z.div_mod_to_equations. lia.
    - exact FDP.
    - lia.
    - exact PAYB.
    - exact LPAY.
    - exact PAYIN.
    - rewrite SP1. lia.
    - lia.
    - rewrite SP1. lia.
    - lia.
    - lia.
    - rewrite HR1; getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1; getr_leaf. exact R3.
    - rewrite HR1; getr_leaf. exact R4.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite SP1. lia.
    - rewrite SP1. unfold CRLS_NEED, SOE_NEED, P_MNEED in *. lia.
    - rewrite SP1. exact STb''.
    - intros fx2 r2 m2 md2 hs2 s ptr' rem' Hfx2 HP2 MD2 VM2 UB2 KP2 CS MU2 AG2 ST2 FDP2 Hpr2 Hrem2 Hs1 Hs2 STR.
      rewrite SP1 in MU2, ST2.
      destruct (fz_acc_crls cfg HI GP TP HTOP STATIC HOK c hs m1 md _ hs2 m2 md2 (bv_unsigned sp) (bv_unsigned sp + 88)%Z (bv_unsigned sp) s
                  CX ACC1 HP2 MD2 VM2 KP2 MU2 AG2) as (bi & OBJI & ACC2);
        [unfold CRLS_NEED, SOE_NEED, P_MNEED, FUZZ_NEED, from_chars_double_need; lia | lia | lia | lia | lia | lia | exact STR | ].
      change (munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++
                     [(bv_unsigned sp, bv_unsigned sp + 24); (bv_unsigned sp + 88, bv_unsigned sp + 88 + 16);
                      (bv_unsigned sp - CRLS_NEED, bv_unsigned sp)])%Z m1 m2) in MU2.
      unfold CRLS_NEED, SOE_NEED, P_MNEED in *.
      clear JUNK FDP. xport SOK MU2.
      pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
      assert (SP2 : sp_of r2 = bv_unsigned sp) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
      pose proof (stk_of_rw_cells PSEGS m2 _ _ FDP2) as SFD. cbn [cells_size csize Nat.add] in SFD.
      eapply (fz_D cfg HI GP TP HTOP STATIC HOK FCI c fx2 r2 m2 md2 hs2 bi bf bd _ CX CONT ACC2 ltac:(clear - UA UB2; lia) RG2).
      + rewrite SP2. exact SAV.
      + rewrite SP2. exact OBJD.
      + rewrite SP2. exact OBJF.
      + rewrite SP2. eapply str_obj_at; [exact OBJI | lia].
      + rewrite SP2. exact RESI'.
      + rewrite SP2. eapply stk_at; [exact SRF | reflexivity | lia].
      + rewrite SP2. unfold FUZZ_NEED, from_chars_double_need. eapply stk_merge'; [exact STa' | exact ST2 | reflexivity | lia].
      + rewrite SP2. eapply stk_merge'; [exact RESD | eapply stk_at; [exact SFD | reflexivity | lia] | reflexivity | lia].
      + rewrite Hfx2, Hfc. exact FRM'.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK MEMCPY FCF FCI"] Lemma fz_C : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bf bd fmt ptr rem ji ri rf,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bf ++ opt_list bd) -> (U md <= U (z_md c) + 4 * MCHARGE 136)%Z -> regs_ok c regs ->
    getr regs 8 = Z_to_bv 64 fmt -> (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z -> getr regs 9 = Z_to_bv 64 FCF_OPT2 ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    rw_cells PSEGS m (sp_of regs + 88) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> pay_ok HI c ptr rem ->
    stk PSEGS m (sp_of regs + 80) (sp_of regs + 88) ->
    str_obj m (sp_of regs + 56) bd -> str_obj m (sp_of regs + 32) bf ->
    rw_cells PSEGS m (sp_of regs) [CB 24 ji] ->
    rw_cells PSEGS m (sp_of regs + 24) [CB 4 ri] ->
    rw_cells PSEGS m (sp_of regs + 28) [CB 4 rf] ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22ba8) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY FCF FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bf bd fmt ptr rem ji ri rf CX CONT ACC UA RG R8 FMT R9 SAV FDP PAY RESD OBJD OBJF JUNK RESI RESF ST FRM.
    pose proof ACC as (HP & MD & BL & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof OBJF as OBJ.
    unfold sp_of in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    pose proof (munch_refl [(z_sp c - (128 + (112 + 2496) + 5760), z_sp c)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    destruct bf as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & BST & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      assert (T1 : (p <= p + s <= p + (cap + 1))%Z) by lia.
      destruct (stk_split PSEGS m _ (p + s) _ BST T1) as [BS1 _]. clear T1 BST.
      assert (T1 : (p <= p + s)%Z) by lia.
      destruct (stk_bytes PSEGS m p (p + s) BS1 T1) as (tbs & Ltbs & TXT). clear T1 BS1.
      resume MD. rewrite R8, R9.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      lazymatch goal with H : rw_cells PSEGS m1 (bv_unsigned (getr regs 2) + 28) _ |- _ => rename H into RESF' end.
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      assert (ACC1 : fz_acc c hs m1 md (opt_list (Some (p, cap + 1)%Z) ++ opt_list bd)).
      { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC MU WM).
        intros z Hz. cbn [outside] in Hz. unfold FUZZ_NEED, from_chars_double_need. lia. }
      eapply (fz_C2 c fx0 r1 m1 md hs (Some (p, cap + 1)%Z) bd fmt ptr rem ji ri _ p s tbs CX CONT ACC1 UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + exact FMT.
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. first [reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + lia.
      + lia.
      + right. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact FDP.
      + exact PAY.
      + rewrite SP1. exact RESD.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact OBJF.
      + rewrite SP1. exact JUNK.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF'.
      + rewrite SP1. exact ST.
      + rewrite Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      pose proof (bytes_at_sub PSEGS m (bv_unsigned (getr regs 2) + 32 + 1) ob 0 (Z.to_nat s) (proj1 OBA) ltac:(lia)) as TXT.
      rewrite skipn_O, Z.add_0_r in TXT.
      resume MD. rewrite R8, R9.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)), (shr1_even s) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      lazymatch goal with H : rw_cells PSEGS m1 (bv_unsigned (getr regs 2) + 28) _ |- _ => rename H into RESF' end.
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      assert (ACC1 : fz_acc c hs m1 md (opt_list None ++ opt_list bd)).
      { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC MU WM).
        intros z Hz. cbn [outside] in Hz. unfold FUZZ_NEED, from_chars_double_need. lia. }
      eapply (fz_C2 c fx0 r1 m1 md hs None bd fmt ptr rem ji ri _ (bv_unsigned (getr regs 2) + 32 + 1)%Z s (firstn (Z.to_nat s) ob)
                CX CONT ACC1 UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + exact FMT.
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. f_equal. lia.
      + rewrite HR1; getr_leaf. first [reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + rewrite firstn_length_le by lia. lia.
      + lia.
      + left. rewrite SP1. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact FDP.
      + exact PAY.
      + rewrite SP1. exact RESD.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact OBJF.
      + rewrite SP1. exact JUNK.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF'.
      + rewrite SP1. exact ST.
      + rewrite Hfc. exact FRM.
  Qed.
End FZC.
End P_h_fuzz_C.

Module P_h_fuzz_B.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy_stmt P_from_chars_double_stmt P_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_pushback OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_E OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_D OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section FZB.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Hypothesis FCD : from_chars_double_stmt.
  Hypothesis FCF : from_chars_float_stmt.
  Hypothesis FCI : from_chars_int_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).
  Local Notation fz_cont := (fz_cont cfg HI HTOP STATIC).
  Local Notation fz_acc := (fz_acc HI HTOP STATIC).
  Local Notation ctx_ok := (ctx_ok HI GP TP HTOP STATIC).
  Local Notation regs_ok := (regs_ok HI GP TP).

  Ltac regs_ok_tree RG HR :=
    let SPR := fresh "SPR" in let R3 := fresh "R3" in let R4 := fresh "R4" in
    destruct RG as (SPR & R3 & R4 & ?R18 & ?R19 & ?R20 & ?R21 & ?R22 & ?R23 & ?R24 & ?R25 & ?R26 & ?R27);
    unfold P_h_fuzz_base.regs_ok, sp_of; repeat split; rewrite HR; getr_leaf; first [assumption | lia].

  (* [comment removed for export] *)
  #[using="HOK MEMCPY FCD FCF FCI"] Lemma fz_B2 : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bd fmt ptr rem vd ji ri rf jf tptr tlen tbs,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bd) -> (U md <= U (z_md c) + 2 * MCHARGE 136)%Z -> regs_ok c regs ->
    getr regs 8 = Z_to_bv 64 fmt -> (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z ->
    getr regs 10 = Z_to_bv 64 tptr -> getr regs 11 = Z_to_bv 64 (tptr + tlen) ->
    bytes_at PSEGS m tptr tbs -> Z.of_nat (length tbs) = tlen -> (tlen <= 2^26)%Z ->
    ((tptr = sp_of regs + 57 /\ tlen <= 22) \/ (16 <= tptr /\ tptr + tlen <= HTOP))%Z ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    rw_cells PSEGS m (sp_of regs + 88) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> pay_ok HI c ptr rem ->
    rw_cells PSEGS m (sp_of regs + 80) [C8 vd] ->
    str_obj m (sp_of regs + 56) bd ->
    rw_cells PSEGS m (sp_of regs) [CB 24 ji] ->
    rw_cells PSEGS m (sp_of regs + 24) [CB 4 ri] ->
    rw_cells PSEGS m (sp_of regs + 28) [CB 4 rf] ->
    rw_cells PSEGS m (sp_of regs + 32) [CB 24 jf] ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22b7c) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY FCD FCF FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bd fmt ptr rem vd ji ri rf jf tptr tlen tbs CX CONT ACC UA RG R8 FMT Ha0 Ha1 TXT LTX Htl WHERE
      SAV FDP PAY RESD OBJD JUNKI RESI RESF JUNKF ST FRM.
    pose proof ACC as (HP & MD & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    destruct (acc_ro HI HTOP STATIC _ _ _ _ _ ACC) as [PR1 PR2].
    unfold sp_of, saves_cells in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    pose proof (bytes_at_bound _ _ _ _ TXT) as BTX.
    resume MD. rewrite R8, Ha0, Ha1.
    set (sp := getr regs 2) in *.
    pose proof (munch_refl [(z_sp c - (128 + (112 + 2496) + 5760), z_sp c)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned sp - (112 + 2496) <= bv_unsigned sp)%Z) by lia.
    destruct (stk_split PSEGS m _ (bv_unsigned sp - (112 + 2496)) _ ST T1) as [STa STb]. clear T1 ST.
    assert (USa0 : bv_unsigned (Z_to_bv 64 tptr) = tptr) by (apply unsigned_lit; lia).
    assert (USa1 : bv_unsigned (Z_to_bv 64 (tptr + tlen)) = (tptr + tlen)%Z) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 80)) = (bv_unsigned sp + 80)%Z) by (apply unsigned_lit; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fz_call FCD.
    { reflexivity. }
    { exact FMT. }
    { reflexivity. }
    { rewrite USa0. exact TXT. }
    { rewrite USa0, USa1. lia. }
    { rewrite USa0, USa1. lia. }
    { rewrite USa1. lia. }
    { rewrite USP. exact RESD. }
    { rewrite USP. Z.div_mod_to_equations. lia. }
    { unfold from_chars_double_need. exact STb. }
    { Z.div_mod_to_equations. lia. }
    { unfold from_chars_double_need. lia. }
    { rewrite USa0. lia. }
    { rewrite USP. lia. }
    { rewrite USP. lia. }
    { exact PR1. }
    { exact PR2. }
    { exact FRM. }
    { rewrite USa0, USa1. unfold from_chars_double_need. lia. }
    { rewrite USP. unfold from_chars_double_need. lia. }
    { rewrite USa0, USa1, USP. lia. }
    rewrite ?USP in *.
    lazymatch goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM' end.
    lazymatch goal with H : rw_cells PSEGS ?mm (bv_unsigned sp + 80) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into RESD' end.
    lazymatch goal with H : stk PSEGS ?mm (bv_unsigned sp - from_chars_double_need) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STb' end.
    unfold from_chars_double_need in STb'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    exit_rz r1 HR1.
    assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
    assert (SP1 : sp_of r1 = bv_unsigned sp) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
    assert (ACC1 : fz_acc c hs m1 md (opt_list bd)).
    { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC MU WM).
      intros z Hz. cbn [outside] in Hz. unfold FUZZ_NEED, from_chars_double_need. lia. }
    pose proof ACC1 as (HP1 & _).
    destruct (pay_bytes cfg HI GP TP HTOP STATIC HOK c hs m1 md _ ptr rem ACC1 PAY) as (bs0 & PAYB & LPAY).
    pose proof (pay_blocks HI HTOP STATIC c hs m1 md _ ptr rem ACC1 PAY) as PAYIN.
    pose proof PAY as (Hp0 & Hrem & Hpr & _).
    assert (T1 : (z_sp c - (128 + (112 + 2496) + 5760) <= bv_unsigned sp - CRLS_NEED <= bv_unsigned sp)%Z) by (unfold CRLS_NEED, SOE_NEED, P_MNEED; lia).
    pose proof (stk_merge PSEGS m1 _ _ _ STa STb' ltac:(lia)) as STw.
    destruct (stk_split PSEGS m1 _ (bv_unsigned sp - CRLS_NEED) _ STw T1) as [STa' STb'']. clear T1 STw STa STb'.
    pose proof (stk_of_rw_cells PSEGS m1 _ _ RESD') as SRD. cbn [cells_size csize Nat.add] in SRD. clear RESD'.
    eapply (crls_ok cfg HI GP TP HTOP STATIC HOK MEMCPY _ r1 m1 md hs (bv_unsigned sp + 32)%Z (bv_unsigned sp + 88)%Z ptr rem jf bs0
              (Z_to_bv 64 0x22ba8) (z_K c) I HP1 MD ltac:(clear - UA UCX; unfold FUZZ_CHARGE, MCHARGE in *; lia)).
    - rewrite HR1; getr_leaf. reflexivity.
    - rewrite HR1; getr_leaf. reflexivity.
    - rewrite HR1; getr_leaf. reflexivity.
    - exact JUNKF.
    - Z.div_mod_to_equations. lia.
    - exact FDP.
    - lia.
    - exact PAYB.
    - exact LPAY.
    - exact PAYIN.
    - rewrite SP1. lia.
    - lia.
    - rewrite SP1. lia.
    - lia.
    - lia.
    - rewrite HR1; getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1; getr_leaf. exact R3.
    - rewrite HR1; getr_leaf. exact R4.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite SP1. lia.
    - rewrite SP1. unfold CRLS_NEED, SOE_NEED, P_MNEED in *. lia.
    - rewrite SP1. exact STb''.
    - intros fx2 r2 m2 md2 hs2 s ptr' rem' Hfx2 HP2 MD2 VM2 UB2 KP2 CS MU2 AG2 ST2 FDP2 Hpr2 Hrem2 Hs1 Hs2 STR.
      rewrite SP1 in MU2, ST2.
      destruct (fz_acc_crls cfg HI GP TP HTOP STATIC HOK c hs m1 md _ hs2 m2 md2 (bv_unsigned sp + 32)%Z (bv_unsigned sp + 88)%Z (bv_unsigned sp) s
                  CX ACC1 HP2 MD2 VM2 KP2 MU2 AG2) as (bf & OBJF & ACC2);
        [unfold CRLS_NEED, SOE_NEED, P_MNEED, FUZZ_NEED, from_chars_double_need; lia | lia | lia | lia | lia | lia | exact STR | ].
      change (munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++
                     [(bv_unsigned sp + 32, bv_unsigned sp + 32 + 24); (bv_unsigned sp + 88, bv_unsigned sp + 88 + 16);
                      (bv_unsigned sp - CRLS_NEED, bv_unsigned sp)])%Z m1 m2) in MU2.
      unfold CRLS_NEED, SOE_NEED, P_MNEED in *.
      clear JUNKF FDP. xport SOK MU2.
      pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
      assert (SP2 : sp_of r2 = bv_unsigned sp) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
      pose proof (pay_ok_step HI c ptr rem ptr' rem' PAY Hpr2 Hrem2) as PAY2.
      pose proof CS as (C2 & C3 & C4 & C8 & C9 & _).
      eapply (fz_C cfg HI GP TP HTOP STATIC HOK MEMCPY FCF FCI c fx2 r2 m2 md2 hs2 bf bd fmt ptr' rem' ji ri rf CX CONT ACC2 ltac:(clear - UA UB2; lia) RG2).
      + rewrite C8, HR1; getr_leaf. reflexivity.
      + exact FMT.
      + rewrite C9, HR1; getr_leaf. reflexivity.
      + rewrite SP2. exact SAV.
      + rewrite SP2. exact FDP2.
      + exact PAY2.
      + rewrite SP2. eapply stk_at; [exact SRD | reflexivity | lia].
      + rewrite SP2. exact OBJD.
      + rewrite SP2. eapply str_obj_at; [exact OBJF | lia].
      + rewrite SP2. exact JUNKI.
      + rewrite SP2. exact RESI.
      + rewrite SP2. exact RESF.
      + rewrite SP2. unfold FUZZ_NEED, from_chars_double_need. eapply stk_merge'; [exact STa' | exact ST2 | reflexivity | lia].
      + rewrite Hfx2, Hfc. exact FRM'.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK MEMCPY FCD FCF FCI"] Lemma fz_B : forall (c : fz_ctx HI) (fx : FPState) regs m md hs bd fmt ptr rem vd ji ri rf jf,
    ctx_ok c -> fz_cont c -> fz_acc c hs m md (opt_list bd) -> (U md <= U (z_md c) + 2 * MCHARGE 136)%Z -> regs_ok c regs ->
    getr regs 8 = Z_to_bv 64 fmt -> (fmt = 1 \/ fmt = 4 \/ fmt = 5)%Z ->
    rw_cells PSEGS m (sp_of regs + 104) (saves_cells HI c) ->
    rw_cells PSEGS m (sp_of regs + 88) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> pay_ok HI c ptr rem ->
    rw_cells PSEGS m (sp_of regs + 80) [C8 vd] ->
    str_obj m (sp_of regs + 56) bd ->
    rw_cells PSEGS m (sp_of regs) [CB 24 ji] ->
    rw_cells PSEGS m (sp_of regs + 24) [CB 4 ri] ->
    rw_cells PSEGS m (sp_of regs + 28) [CB 4 rf] ->
    rw_cells PSEGS m (sp_of regs + 32) [CB 24 jf] ->
    stk PSEGS m (z_sp c - FUZZ_NEED) (sp_of regs) ->
    frm0 (@fp_csr fx) ->
    realizes_cfg PSEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x22b50) m (seg_rom PSEGS)) md) (z_K c).
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY FCD FCF FCI : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros c fx regs m md hs bd fmt ptr rem vd ji ri rf jf CX CONT ACC UA RG R8 FMT SAV FDP PAY RESD OBJD JUNKI RESI RESF JUNKF ST FRM.
    pose proof ACC as (HP & MD & BL & _).
    pose proof CX as (Hal & HT & E3 & E4 & Eret & SRO & SPB & UCX).
    pose proof RG as (SPR & R3 & R4 & _).
    pose proof OBJD as OBJ.
    unfold sp_of in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (z_sp_range HI c) as Rz. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct bd as [[p n]|].
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (cap & s & -> & Hc1 & Hodd & Hs & OBJ).
      assert (Hin : In (p, cap + 1)%Z (blocks hs)) by (apply BL; right; left; reflexivity).
      destruct (BOK _ _ _ HP) as [B1 O1].
      destruct (B1 p (cap + 1)%Z Hin) as (Hn1 & Hreg & BST & BDO & BDJ). unfold P_IMG_LO, P_IMG_END in Hreg.
      assert (T1 : (p <= p + s <= p + (cap + 1))%Z) by lia.
      destruct (stk_split PSEGS m _ (p + s) _ BST T1) as [BS1 _]. clear T1 BST.
      assert (T1 : (p <= p + s)%Z) by lia.
      destruct (stk_bytes PSEGS m p (p + s) BS1 T1) as (tbs & Ltbs & TXT). clear T1 BS1.
      resume MD. rewrite R8.
      pose proof (rd_byte0_C8 PSEGS _ _ _ _ OBJ) as RD0.
      step. (* [comment removed for export] *)
      clear RD0.
      step. (* [comment removed for export] *)
      rewrite (cap_byte0_odd cap) by lia.
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      eapply (fz_B2 c fx0 r1 m md hs (Some (p, cap + 1)%Z) fmt ptr rem vd ji ri rf jf p s tbs CX CONT ACC UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + exact FMT.
      + rewrite HR1; getr_leaf. reflexivity.
      + rewrite HR1; getr_leaf. first [reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + lia.
      + lia.
      + right. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact FDP.
      + exact PAY.
      + rewrite SP1. exact RESD.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact JUNKI.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF.
      + rewrite SP1. exact JUNKF.
      + rewrite SP1. exact ST.
      + rewrite Hfc. exact FRM.
    - (* [comment removed for export] *)
      cbn [str_obj] in OBJ. destruct OBJ as (s & Hs & OBJ & ob & Lob & OBA).
      pose proof (bytes_at_sub PSEGS m (bv_unsigned (getr regs 2) + 56 + 1) ob 0 (Z.to_nat s) (proj1 OBA) ltac:(lia)) as TXT.
      rewrite skipn_O, Z.add_0_r in TXT.
      resume MD. rewrite R8.
      step. (* [comment removed for export] *)
      rewrite (zxb_lit8 (2 * s)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_vm.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2 * s)), (shr1_even s) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      exit_rz r1 HR1.
      assert (RG1 : regs_ok c r1) by regs_ok_tree RG HR1.
      assert (SP1 : sp_of r1 = bv_unsigned (getr regs 2)) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      eapply (fz_B2 c fx0 r1 m md hs None fmt ptr rem vd ji ri rf jf (bv_unsigned (getr regs 2) + 56 + 1)%Z s (firstn (Z.to_nat s) ob)
                CX CONT ACC UA RG1).
      + rewrite HR1; getr_leaf. reflexivity.
      + exact FMT.
      + rewrite HR1; getr_leaf. f_equal. lia.
      + rewrite HR1; getr_leaf. first [reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; f_equal; lia)].
      + exact TXT.
      + rewrite firstn_length_le by lia. lia.
      + lia.
      + left. rewrite SP1. lia.
      + rewrite SP1. exact SAV.
      + rewrite SP1. exact FDP.
      + exact PAY.
      + rewrite SP1. exact RESD.
      + rewrite SP1. exact OBJD.
      + rewrite SP1. exact JUNKI.
      + rewrite SP1. exact RESI.
      + rewrite SP1. exact RESF.
      + rewrite SP1. exact JUNKF.
      + rewrite SP1. exact ST.
      + rewrite Hfc. exact FRM.
  Qed.
End FZB.
End P_h_fuzz_B.

Module P_h_fuzz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double_stmt P_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_arbitrary_format OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_h_crls_stmt OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_crls OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_E OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz_B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rw_cells_CB_split_at : forall m A A' (n1 n2 : nat) j, rw_cells PSEGS m A [CB (n1 + n2) j] -> A' = (A + Z.of_nat n1)%Z ->
  exists j1 j2, rw_cells PSEGS m A [CB n1 j1] /\ rw_cells PSEGS m A' [CB n2 j2].
Proof.
  intros m A A' n1 n2 j H ->.
  pose proof (rw_cells_split_CB PSEGS m A [] (n1 + n2) j [] [n1; n2] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2.
  apply (rw_cells_app PSEGS m A [CB n1 (firstn n1 j)] [CB n2 (firstn n2 (skipn n1 j))]) in H2. destruct H2 as [H1 H2].
  exists (firstn n1 j), (firstn n2 (skipn n1 j)). split; [exact H1|]. cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Section FZA.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : P_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Hypothesis AF : arbitrary_format_stmt.
  Hypothesis FCD : from_chars_double_stmt.
  Hypothesis FCF : from_chars_float_stmt.
  Hypothesis FCI : from_chars_int_stmt.
  (* [comment removed for export] *)
  Hypothesis SRO : Forall (fun r => forall x, (fst r <= x < snd r)%Z -> outside STATIC x \/ ~ outside P_KEEP x) P_RO.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).
  Local Notation fz_cont := (fz_cont cfg HI HTOP STATIC).
  Local Notation fz_acc := (fz_acc HI HTOP STATIC).
  Local Notation ctx_ok := (ctx_ok HI GP TP HTOP STATIC).
  Local Notation regs_ok := (regs_ok HI GP TP).

  #[using="HOK MEMCPY AF FCD FCF FCI SRO"] Lemma fuzz_ok : fuzz_contract PSEGS cfg (hi_HS HI) Heap blocks GP TP P_IMG_LO P_IMG_END HTOP STATIC P_KEEP 0x22b18 FUZZ_NEED P_RO.
  Proof. LiaFast.lf_pins (fun (HOK MEMCPY AF FCD FCF FCI SRO : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold P_IMG_LO, P_IMG_END in HTOPB.
    intros fx regs m md hs size ret K HP MD UB Ha1 Hsize PAYIN Hra Hret Hgp Htp AL SPB HT ST FRM RO CONT.
    set (c := FZC regs m hs K md : fz_ctx HI).
    assert (CX : ctx_ok c).
    { unfold P_h_fuzz_base.ctx_ok, z_sp, z_ret, c. cbn [z_regs z_md]. rewrite Hra. repeat split; assumption. }
    assert (FC : fz_cont c).
    { unfold P_h_fuzz_base.fz_cont, z_sp, z_ret, c. cbn [z_regs z_m z_hs z_K z_md]. rewrite Hra. intros fx' regs' m' md' hs' H1 H2 H0 HU H0k H3 H4 H5 H6 H7 H8 H9. exact (CONT fx' regs' m' md' hs' H1 H2 H0 HU H0k H3 H4 H5 H6 H7 H8 H9). }
    assert (ACC0 : fz_acc c hs m md []).
    { unfold P_h_fuzz_base.fz_acc, c. cbn [z_regs z_m z_hs z_K z_md]. refine (conj HP (conj MD (conj _ (conj _ (conj _ (conj _ (conj _ (conj RO (conj (vm_only_refl md) (keep_refl _ m)))))))))).
      - intros y. cbn. tauto.
      - intros y [].
      - constructor.
      - apply munch_refl.
      - intros q k Hq i Hi. reflexivity. }
    unfold sp_of in *.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    unfold FUZZ_NEED, from_chars_double_need in *.
    (* [comment removed for export] *)
    assert (PAY0 : pay_ok HI c (bv_unsigned (getr regs 10)) size).
    { unfold pay_ok, c. cbn [z_hs]. pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R; unfold bv_modulus in R.
      destruct PAYIN as [E0|Hin].
      - subst size. repeat split; first [lia | left; reflexivity].
      - destruct (BOK _ _ _ HP) as [B1 O1]. destruct (B1 _ _ Hin) as (_ & Hreg & _). unfold P_IMG_LO, P_IMG_END in Hreg.
        repeat split; try lia. right. exists (bv_unsigned (getr regs 10)), size. split; [exact Hin|]. lia. }
    assert (PAYW : (size = 0 \/ (16 <= bv_unsigned (getr regs 10) /\ bv_unsigned (getr regs 10) + size <= HTOP))%Z).
    { destruct PAYIN as [E0|Hin]; [left; exact E0|]. right.
      destruct (BOK _ _ _ HP) as [B1 O1]. destruct (B1 _ _ Hin) as (_ & Hreg & _). unfold P_IMG_LO, P_IMG_END in Hreg. lia. }
    resume MD.
    set (sp := getr regs 2) in *.
    pose proof (munch_refl [(bv_unsigned sp - (128 + (112 + 2496) + 5760), bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    destruct (acc_ro HI HTOP STATIC _ _ _ _ _ ACC0) as [PR1 PR2]. clear RO.
    carve_frame 128%nat ST.
    (* [comment removed for export] *)
    assert (T1 : (bv_unsigned sp + -104 = bv_unsigned sp + -128 + Z.of_nat 24)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 24 104 _ FR T1) as (ji & j1 & JUNKI & F1). clear FR T1.
    assert (T1 : (bv_unsigned sp + -100 = bv_unsigned sp + -104 + Z.of_nat 4)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 4 100 _ F1 T1) as (ri & j2 & RESI & F2). clear F1 T1.
    assert (T1 : (bv_unsigned sp + -96 = bv_unsigned sp + -100 + Z.of_nat 4)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 4 96 _ F2 T1) as (rf & j3 & RESF & F3). clear F2 T1.
    assert (T1 : (bv_unsigned sp + -72 = bv_unsigned sp + -96 + Z.of_nat 24)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 24 72 _ F3 T1) as (jf & j4 & JUNKF & F4). clear F3 T1.
    assert (T1 : (bv_unsigned sp + -48 = bv_unsigned sp + -72 + Z.of_nat 24)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 24 48 _ F4 T1) as (jd & j5 & JUNKD & F5). clear F4 T1.
    assert (T1 : (bv_unsigned sp + -40 = bv_unsigned sp + -48 + Z.of_nat 8)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 8 40 _ F5 T1) as (jr & j6 & RESD & F6). clear F5 T1.
    assert (T1 : (bv_unsigned sp + -24 = bv_unsigned sp + -40 + Z.of_nat 16)%Z) by lia.
    destruct (rw_cells_CB_split_at m _ _ 16 24 _ F6 T1) as (jp & js & FDP & SAV). clear F6 T1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite Ha1 in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
    assert (ACCA : fz_acc c hs mA md []).
    { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ mA _ CX ACC0 MU WM).
      intros z Hz. cbn [outside] in Hz. unfold z_sp, FUZZ_NEED, from_chars_double_need, c. cbn [z_regs]. unfold sp_of. fold sp. lia. }
    destruct (pay_bytes cfg HI GP TP HTOP STATIC HOK c hs mA md _ _ size ACCA PAY0) as (bs & PAYB & LPAY).
    clear ACCA.
    assert (USF : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -40)) = (bv_unsigned sp + -40)%Z) by (apply unsigned_lit; lia).
    fz_call AF.
    { rewrite USF. exact FDP. }
    { exact PAYB. }
    { exact LPAY. }
    { exact PR1. }
    { rewrite USF. lia. }
    rewrite ?USF in *.
    lazymatch goal with H : rw_cells PSEGS ?mm (bv_unsigned sp + -40) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FDP' end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    exit_rz r1 HR1.
    assert (SP1 : sp_of r1 = (bv_unsigned sp - 128)%Z) by (unfold sp_of; rewrite HR1; getr_leaf; rewrite unsigned_lit by lia; lia).
    assert (RG1 : regs_ok c r1).
    { unfold P_h_fuzz_base.regs_ok, z_sp, c. cbn [z_regs]. rewrite SP1. unfold sp_of. fold sp.
      repeat split; first [lia | (rewrite HR1; getr_leaf; first [reflexivity | assumption])]. }
    assert (ACC1 : fz_acc c hs m1 md []).
    { eapply (fz_acc_frame cfg HI GP TP HTOP STATIC HOK c hs m md _ m1 _ CX ACC0 MU WM).
      intros z Hz. cbn [outside] in Hz. unfold z_sp, FUZZ_NEED, from_chars_double_need, c. cbn [z_regs]. unfold sp_of. fold sp. lia. }
    set (rem := af_remaining size) in *.
    assert (PAY : pay_ok HI c (bv_unsigned (getr regs 10)) rem).
    { unfold rem, af_remaining. destruct (size =? 0)%Z eqn:E0; [apply Z.eqb_eq in E0 | apply Z.eqb_neq in E0].
      - rewrite E0 in PAY0. exact PAY0.
      - destruct PAY0 as (A1 & A2 & A3 & A4). split; [lia|]. split; [lia|]. split; [lia|].
        destruct A4 as [E|(q & k & Hq & B1 & B2)]; [lia|]. right. exists q, k. split; [exact Hq|]. lia. }
    pose proof ACC1 as (HP1 & _).
    destruct (pay_bytes cfg HI GP TP HTOP STATIC HOK c hs m1 md _ _ rem ACC1 PAY) as (bs0 & PAYB0 & LPAY0).
    pose proof (pay_blocks HI HTOP STATIC c hs m1 md _ _ rem ACC1 PAY) as PAYIN0.
    pose proof PAY as (Hp0 & Hrem & Hpr & _).
    assert (T1 : (bv_unsigned sp - (128 + (112 + 2496) + 5760) <= bv_unsigned sp + -128 - CRLS_NEED <= bv_unsigned sp + -128)%Z) by (unfold CRLS_NEED, SOE_NEED, P_MNEED; lia).
    destruct (stk_split PSEGS m1 _ (bv_unsigned sp + -128 - CRLS_NEED) _ ST T1) as [STa STb]. clear T1 ST.
    eapply (crls_ok cfg HI GP TP HTOP STATIC HOK MEMCPY _ r1 m1 md hs (bv_unsigned sp + -72)%Z (bv_unsigned sp + -40)%Z
              (bv_unsigned (getr regs 10)) rem jd bs0 (Z_to_bv 64 0x22b50) K I HP1 MD ltac:(clear - UB; unfold FUZZ_CHARGE, MCHARGE in *; lia)).
    - rewrite HR1; getr_leaf. apply bv_eq. rewrite !unsigned_lit by lia. lia.
    - rewrite HR1; getr_leaf. apply bv_eq. rewrite !unsigned_lit by lia. lia.
    - rewrite HR1; getr_leaf. reflexivity.
    - exact JUNKD.
    - Z.div_mod_to_equations. lia.
    - lazymatch goal with H : rw_cells PSEGS m1 (bv_unsigned sp + -40) _ |- _ => rewrite Z_to_bv_bv_unsigned; exact H end.
    - lia.
    - exact PAYB0.
    - exact LPAY0.
    - exact PAYIN0.
    - rewrite SP1. lia.
    - lia.
    - rewrite SP1. lia.
    - lia.
    - lia.
    - rewrite HR1; getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1; getr_leaf. exact Hgp.
    - rewrite HR1; getr_leaf. exact Htp.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite SP1. lia.
    - rewrite SP1. unfold CRLS_NEED, SOE_NEED, P_MNEED in *. lia.
    - rewrite SP1. eapply stk_at; [exact STb | lia | lia].
    - intros fx2 r2 m2 md2 hs2 s ptr' rem' Hfx2 HP2 MD2 VM2 UB2 KP2 CS MU2 AG2 ST2 FDP2 Hpr2 Hrem2 Hs1 Hs2 STR.
      rewrite SP1 in MU2, ST2.
      destruct (fz_acc_crls cfg HI GP TP HTOP STATIC HOK c hs m1 md _ hs2 m2 md2 (bv_unsigned sp + -72)%Z (bv_unsigned sp + -40)%Z
                  (bv_unsigned sp - 128)%Z s CX ACC1 HP2 MD2 VM2 KP2 MU2 AG2) as (bd & OBJD & ACC2);
        [unfold z_sp, c, CRLS_NEED, SOE_NEED, P_MNEED, FUZZ_NEED, from_chars_double_need; cbn [z_regs]; unfold sp_of; fold sp; lia
        | lia | unfold z_sp, c; cbn [z_regs]; unfold sp_of; fold sp; lia | lia | unfold z_sp, c; cbn [z_regs]; unfold sp_of; fold sp; lia | lia | exact STR | ].
      rewrite app_nil_r in ACC2.
      change (munch (STATIC ++ [(0, P_IMG_LO); (P_IMG_END, HTOP)] ++
                     [(bv_unsigned sp + -72, bv_unsigned sp + -72 + 24); (bv_unsigned sp + -40, bv_unsigned sp + -40 + 16);
                      (bv_unsigned sp - 128 - CRLS_NEED, bv_unsigned sp - 128)])%Z m1 m2) in MU2.
      unfold CRLS_NEED, SOE_NEED, P_MNEED in *.
      lazymatch goal with H : rw_cells PSEGS m1 (bv_unsigned sp + -40) _ |- _ => clear H end. clear JUNKD.
      xport SOK MU2.
      pose proof (regs_ok_cs HI GP TP c r1 r2 RG1 CS) as RG2.
      assert (SP2 : sp_of r2 = (bv_unsigned sp - 128)%Z) by (destruct CS as (C2 & _); unfold sp_of; rewrite C2; exact SP1).
      pose proof (pay_ok_step HI c _ _ ptr' rem' PAY Hpr2 Hrem2) as PAY2.
      pose proof CS as (C2 & C3 & C4 & C8 & C9 & _).
      eapply (fz_B cfg HI GP TP HTOP STATIC HOK MEMCPY FCD FCF FCI c fx2 r2 m2 md2 hs2 bd (af_result size bs) ptr' rem' _ ji ri rf jf
                CX FC ACC2 ltac:(unfold c; cbn [z_md]; clear - UB2; lia) RG2).
      + rewrite C8, HR1; getr_leaf. reflexivity.
      + apply af_fmt.
      + rewrite SP2. unfold saves_cells, z_ret, c. cbn [z_regs]. eapply rw_cells_at; [exact SAV | lia].
      + rewrite SP2. eapply rw_cells_at; [exact FDP2 | lia].
      + exact PAY2.
      + rewrite SP2. eapply rw_cells_at; [eassumption | lia].
      + rewrite SP2. eapply str_obj_at; [exact OBJD | lia].
      + rewrite SP2. eapply rw_cells_at; [exact JUNKI | lia].
      + rewrite SP2. eapply rw_cells_at; [exact RESI | lia].
      + rewrite SP2. eapply rw_cells_at; [exact RESF | lia].
      + rewrite SP2. eapply rw_cells_at; [exact JUNKF | lia].
      + rewrite SP2. unfold z_sp, c, FUZZ_NEED, from_chars_double_need. cbn [z_regs]. unfold sp_of. fold sp.
        eapply stk_merge'; [exact STa | exact ST2 | lia | lia].
      + rewrite Hfx2, Hfc. exact FRM.
  Qed.
End FZA.
End P_h_fuzz.

Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.HIfaceInit OSSVerify.Proofs.fast_float.from_chars.lib.H.P_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base OSSVerify.Proofs.fast_float.from_chars.lib.PAssemble.P_h_fuzz.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy_stmt P_from_chars_double_stmt P_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require P_h_fuzz_base.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_lib_closed.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvHeap PDrvRead PDir PTgt3 PKeepMono PHeapIGlue PTop PHeapInst.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngL4 MngL4I MngL4F MngL4H AXG_mwk AXG_mwd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ivl_disj (a b : ivl) : bool := (Z.leb (snd a) (fst b) || Z.leb (snd b) (fst a))%bool.
(* [comment removed for export] *)
Definition sub_or_disj (A C B : list ivl) : bool :=
  forallb (fun s => existsb (fun c => (Z.leb (fst c) (fst s) && Z.leb (snd s) (snd c))%bool) C || forallb (ivl_disj s) A)%bool B.

Lemma not_outside_in : forall A x, ~ ioutside A x -> exists a, In a A /\ fst a <= x < snd a.
Proof.
  induction A as [|[lo hi] A IH]; intros x H; cbn [ioutside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (a & Ha & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists a. split; [right; exact Ha | exact Hx].
  - destruct (IH x) as (a & Ha & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists a. split; [right; exact Ha | exact Hx].
Qed.
Lemma outside_in : forall C c x, ioutside C x -> In c C -> ~ (fst c <= x < snd c).
Proof.
  induction C as [|[lo hi] C IH]; intros c x H Hc; [destruct Hc|]. cbn [ioutside] in H. destruct H as [H1 H2].
  destruct Hc as [<-|Hc]; [exact H1 | exact (IH c x H2 Hc)].
Qed.
Lemma outside_all : forall B x, (forall b, In b B -> ~ (fst b <= x < snd b)) -> ioutside B x.
Proof.
  induction B as [|[lo hi] B IH]; intros x H; cbn [ioutside]; [exact I|].
  split; [exact (H (lo, hi) (or_introl eq_refl)) | apply IH; intros b Hb; exact (H b (or_intror Hb))].
Qed.
Lemma outside_sub_or_disj : forall A C B x, sub_or_disj A C B = true -> ~ ioutside A x -> ioutside C x -> ioutside B x.
Proof.
  intros A C B x H HA HC. destruct (not_outside_in A x HA) as (a & Ha & Hxa). apply outside_all. intros b Hb Hxb.
  unfold sub_or_disj in H. rewrite forallb_forall in H. specialize (H b Hb). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as (c & Hc & Hcb). apply andb_prop in Hcb as [H1 H2]. apply Z.leb_le in H1, H2.
    exact (outside_in C c x HC Hc ltac:(lia)).
  - rewrite forallb_forall in H. specialize (H a Ha). unfold ivl_disj in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma stat_x : forall x, ~ ioutside EXGX x -> ioutside STATIC_P x.
Proof. intros x H. apply (outside_sub_or_disj EXGX [] STATIC_P x); [vm_compute; reflexivity | exact H | exact I]. Qed.
Lemma stat_i : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC_P x.
Proof. intros x H1 H2. apply (outside_sub_or_disj IMGIV (CELLS_NE ++ ERRC) STATIC_P x); [vm_compute; reflexivity | exact H1 | exact H2]. Qed.
Lemma stat_r : forall x, RSX x -> ioutside STATIC_P x.
Proof.
  intros x H. apply (outside_sub_or_disj [(RS_LO, RS_LO + 65536)] [] STATIC_P x); [vm_compute; reflexivity | | exact I].
  unfold RSX in H. cbn [ioutside]. tauto.
Qed.
Lemma stat_ro : forall x, 0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4 -> ~ PTgt3.KRO x -> ioutside STATIC_P x.
Proof.
  intros x H1 H2. apply (outside_sub_or_disj PRO [(0x16100, 0x16120); (0x182a8, 0x18327)] STATIC_P x); [vm_compute; reflexivity | |].
  - unfold PRO. cbn [ioutside]. tauto.
  - unfold PTgt3.KRO in H2. cbn [ioutside]. lia.
Qed.
(* [comment removed for export] *)
Lemma stat_sro : Forall (fun r => forall x, fst r <= x < snd r -> ioutside STATIC_P x \/ ~ ioutside P_KEEP x) P_RO.
Proof.
  apply Forall_forall. intros [lo hi] Hr x Hx. cbn [fst snd] in Hx.
  destruct (HIface.outside_dec P_KEEP x) as [Ho|Ho]; [left | right; exact Ho].
  apply (outside_sub_or_disj [(lo, hi)] P_KEEP STATIC_P x); [| cbn [ioutside]; lia | exact Ho].
  unfold P_RO in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma keep_cells : keep_sub CELLS_NE P_KEEP.
Proof. intros a H. unfold CELLS_NE in H. unfold P_KEEP. cbn [ioutside] in *. tauto. Qed.

Lemma heap_ok_keep : forall cfg HI GP TP IMG_LO IMG_END HTOP STATIC PCM MNEED PCF FNEED,
  heap_ok PSEGS cfg HI GP TP IMG_LO IMG_END HTOP STATIC P_KEEP PCM MNEED PCF FNEED ->
  heap_ok PSEGS cfg HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE PCM MNEED PCF FNEED.
Proof.
  intros cfg HI GP TP IMG_LO IMG_END HTOP STATIC PCM MNEED PCF FNEED (A & B & C & D & E).
  split; [exact A|]. split; [exact (malloc_contract_mono _ _ _ _ _ _ _ _ _ _ _ keep_cells _ _ B)|].
  split; [exact (free_contract_mono _ _ _ _ _ _ _ _ _ _ _ keep_cells _ _ C)|]. split; [exact D | exact E].
Qed.

Lemma malloc_contract_init_mono : forall segs cfg HS Heap blocks owned GP TP HTOP K1 K2 HeapI INIT PCM NEED, keep_sub K1 K2 ->
  malloc_contract_init segs cfg HS Heap blocks owned GP TP HTOP K2 HeapI INIT PCM NEED ->
  malloc_contract_init segs cfg HS Heap blocks owned GP TP HTOP K1 HeapI INIT PCM NEED.
Proof.
  intros segs cfg HS Heap blocks owned GP TP HTOP K1 K2 HeapI INIT PCM NEED HK H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 KC.
  apply (H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14).
  intros fx' regs' m' md' hs' p C1 C2 C3 C4 C5 C6. apply (KC fx' regs' m' md' hs' p C1 C2 C3 C4 C5).
  intros a Ha. exact (C6 a (HK a Ha)).
Qed.

(* [comment removed for export] *)
Section Asm.
(* [comment removed for export] *)
Let DIRWK : forall fx, @direct_wk_stmt fx := fun fx => @direct_wk fx.

#[using="Type"] Lemma dcfg_alloc_off : sc_alloc DCFG = false.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="DIRWK"] Lemma hok_p : forall HTOP, HTR HTOP -> P_heap_ok DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP STATIC_P.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). intros HTOP HR. unfold HTR in HR. exact (plain_heap_ok DCFG HTOP (Z_to_bv 64 0x10800) dcfg_alloc_off ltac:(lia) DIRWK). Qed.

#[using="DIRWK"] Lemma hok_c : forall HTOP, HTR HTOP ->
  heap_ok PSEGS DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) 0x10000 0x97000 HTOP STATIC_P CELLS_NE 0x51310 8192 0x511d0 8192.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). intros HTOP HR. apply heap_ok_keep. exact (hok_p HTOP HR). Qed.

#[using="DIRWK"] Lemma hoki_c : forall HTOP, HTR HTOP ->
  heap_init_ok PSEGS DCFG (HI HTOP) (HeapI HTOP) INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP CELLS_NE 0x51310 8192.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  intros HTOP HR. split.
  - apply (malloc_contract_init_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ keep_cells). unfold HTR in HR.
    exact (proj1 (plain_heap_init_ok DCFG HTOP (Z_to_bv 64 0x10800) dcfg_alloc_off ltac:(lia) DIRWK)).
  - exact (heap_frame_init_L4 HTOP).
Qed.

#[using="DIRWK"] Lemma hfz_c : forall HTOP, HTR HTOP ->
  fuzz_contract PSEGS DCFG (hi_HS (HI HTOP)) (hi_Heap (HI HTOP)) (hi_blocks (HI HTOP)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0)
    0x10000 0x97000 HTOP STATIC_P CELLS_NE 0x22b18 8496 PRO.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  intros HTOP HR. eapply fuzz_contract_mono; [exact keep_cells|].
  exact (fuzz_ok DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP STATIC_P (hok_p HTOP HR)
           P_memcpy.memcpy_spec OSSVerify.Proofs.fast_float.from_chars.lib.H.P_h_fuzz_base.P_arbitrary_format.arbitrary_format_spec P_lib_closed.P_from_chars_double_closed
           P_lib_closed.P_from_chars_float_closed P_lib_closed.P_from_chars_int_closed stat_sro).
Qed.

(* [comment removed for export] *)
#[using="DIRWK"] Theorem plain_realizes_A_lim : forall lim, 2 ^ 31 <= lim ->
  image_realizes_cfg_e DCFG PSEGS Plain.M.init_pc
  Plain.M.phdrs lim SPEC.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  exact (plain_realizes_lim STATIC_P stat_x stat_i stat_r stat_ro HI hok_c
    (fun HTOP hs m m' md H1 H2 H3 => heap_errno_frame HTOP hs m m' md H1 H2 H3)
    (fun HTOP hs m m' md H1 H2 H3 H4 => heap_cells_frame HTOP hs m m' md H1 H2 H3 H4)
    (fun HTOP hs m md H1 => heap_need_locks HTOP hs m md H1)
    (fun HTOP hs m md md' H1 H2 _ _ => heap_model_vm HTOP hs m md md' H1 H2)
    (fun HTOP hs m md H1 => hp_kro HTOP hs m md H1)
    (fun HTOP => HeapI HTOP) (fun HTOP => INIT) hoki_c
    (fun HTOP hs m md H1 => heapI_owned HTOP hs m md H1)
    (fun HTOP hs m m' md H1 H2 H3 => heapI_errno_frame HTOP hs m m' md H1 H2 H3)
    (fun HTOP hs m m' md H1 H2 H3 H4 => heapI_cells_frame HTOP hs m m' md H1 H2 H3 H4)
    (fun HTOP hs m md md' H1 H2 _ _ => heapI_model_vm HTOP hs m md md' H1 H2)
    (fun sp0 av ev uid tid hw rdraw regs mem brk mbase lim inp Hsp Hva Hve Hfits Hbrk Hmb Hlim ME =>
       heapI_main sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Hfits ME brk mbase lim inp Hbrk Hmb Hlim)
    hfz_c).
Qed.

(* [comment removed for export] *)
#[using="DIRWK"] Theorem plain_realizes_A : image_realizes_cfg_e DCFG PSEGS Plain.M.init_pc
  Plain.M.phdrs source_alloc_limit SPEC.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). apply plain_realizes_A_lim. unfold source_alloc_limit. lia. Qed.

(* [comment removed for export] *)
#[using="DIRWK"] Theorem plain_realizes_A_san : image_realizes_cfg_e DCFG PSEGS Plain.M.init_pc
  Plain.M.phdrs Equivalence.SanitizerBudgets.lim_source SPEC.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). apply plain_realizes_A_lim. unfold Equivalence.SanitizerBudgets.lim_source, Equivalence.sanitizer_source_limit. lia. Qed.
End Asm.
