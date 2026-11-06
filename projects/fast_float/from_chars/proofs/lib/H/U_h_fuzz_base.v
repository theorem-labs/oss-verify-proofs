(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_ciir_stmt U_from_chars_double_stmt U_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.

Module U_h_new.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface U_hbase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section NEW.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.

  #[using="STATIC HOK"] Lemma new_ok : malloc_contract USEGS cfg (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) GP TP HTOP U_KEEP
                   0x6179c (16 + U_MNEED).
  Proof. LiaFast.lf_pins (fun (STATIC HOK : LiaFast.U) => LiaFast.u0).
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold U_IMG_LO, U_IMG_END in HTOPB.
    intros fx regs m md hs n ret K HP MD UB Ha0 Hn Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold U_MNEED in *.
    resume MD. rewrite Ha0, Hra.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp.
    pose proof (munch_refl [(bv_unsigned (getr regs 2) - 16, bv_unsigned (getr regs 2))]%Z m) as MU.
    pose proof (wmono_refl USEGS m) as WM.
    carve_frame 16%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    exit_rz r1 HR1.
    (* [comment removed for export] *)
    assert (HP1 : hi_Heap HI hs m1 md).
    { eapply FRAME; [exact HP | exact MU | exact WM |].
      intros x Hx. destruct (BOK _ _ _ HP) as [_ O1]. cbn [outside] in Hx.
      destruct (outside_dec (hi_owned HI hs) x) as [Ho|Ho]; [exact Ho|]. specialize (O1 x Ho). lia. }
    eapply (MALLOC _ r1 m1 md hs n (Z_to_bv 64 0x617b8) K HP1 MD UB).
    - rewrite HR1. getr_leaf. f_equal. unfold v_sltiu. rewrite unsigned_lit by lia.
      replace (bv_wrap 64 1) with 1%Z by reflexivity. destruct (Z.ltb_spec n 1); [lia|]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    - exact Hn.
    - rewrite HR1. getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1. getr_leaf. exact Hgp.
    - rewrite HR1. getr_leaf. exact Htp.
    - unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
    - unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. lia.
    - unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. lia.
    - unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia.
      replace (bv_unsigned (getr regs 2) + -16 - 8192)%Z with (bv_unsigned (getr regs 2) - (16 + 8192))%Z by lia. exact ST.
    - intros fx2 r2 m2 md2 hs2 p Hfx2 HP2 MD2 VM2 UB2 KP2 Ha02 Hp16 BADD FRESH CS MU2 ST2.
      assert (SP1 : sp_of r1 = (bv_unsigned (getr regs 2) + -16)%Z).
      { unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. reflexivity. }
      rewrite SP1 in MU2, ST2.
      destruct (BOK _ _ _ HP2) as [B2 _].
      destruct (B2 p n (proj2 (BADD (p, n)) (or_introl eq_refl))) as (Hn1 & Hreg & _). unfold U_IMG_LO, U_IMG_END in Hreg.
      (* [comment removed for export] *)
      assert (AG : agree_on m1 m2 (bv_unsigned (getr regs 2) + -16)%Z 16).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m1 m2 md md2 _ _ _ BOK HP1 HP2 MU2).
        - cbn [disjoint_from]. split; [|split; [lia|exact I]]. unfold U_IMG_LO, U_IMG_END in Hreg. lia.
        - lia.
        - lia.
        - left. lia. }
      apply (rw_cells_agree USEGS m1 m2) in FR; [|exact AG].
      resume MD2.
      destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
      rewrite Ha02, C2. rewrite HR1. getr_leaf.
      step. (* [comment removed for export] *)
      if_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ret_pc_even_w ret Hret).
      exit_rz r3 HR3.
      apply (CONT _ r3 m2 md2 hs2 p); [congruence | exact HP2 | exact MD2 | exact VM2 | exact UB2 | apply (keep_trans U_KEEP m m1 m2); [eapply keep_munch; [|exact MU]; keep_side | exact KP2] | ..].
      + rewrite HR3. getr_leaf. reflexivity.
      + exact Hp16.
      + exact BADD.
      + exact FRESH.
      + repeat split; rewrite HR3; getr_leaf;
          first [ reflexivity | rewrite ?unsigned_lit by lia; apply bv_eq; rewrite unsigned_lit by lia; lia
                | match goal with |- getr r2 ?k = _ => first [rewrite C3 | rewrite C4 | rewrite C9 | rewrite C18 | rewrite C19
                    | rewrite C20 | rewrite C21 | rewrite C22 | rewrite C23 | rewrite C24 | rewrite C25 | rewrite C26 | rewrite C27];
                    rewrite HR1; getr_leaf; reflexivity end ].
      + eapply (munch_cps_trans _ _ _ _ _ m m1 m2 MU MU2).
        * intros x Hx. rewrite !outside_app in Hx. destruct Hx as (_ & _ & C). cbn [outside] in *. split; [lia | exact I].
        * intros x Hx. rewrite !outside_app in Hx. destruct Hx as (A & B & C). cbn [outside] in *.
          split; [exact A|]. split; [exact B|]. split; [exact (proj1 C)|]. split; [lia | exact I].
      + eapply stk_release in FR; [ | exact ST2 | lia ]. cbn [cells_size csize Nat.add] in FR.
        replace (bv_unsigned (getr regs 2) - (16 + 8192))%Z with (bv_unsigned (getr regs 2) + -16 - 8192)%Z by lia.
        replace (bv_unsigned (getr regs 2)) with (bv_unsigned (getr regs 2) + -16 + Z.of_nat 16)%Z at 2 by lia. exact FR.
  Qed.
End NEW.
End U_h_new.

Module U_h_delete.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface U_hbase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section DELETE.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.

  #[using="STATIC HOK"] Lemma delete_ok : free_contract USEGS cfg (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) GP TP HTOP U_KEEP
                      0x46f10 U_FNEED.
  Proof. LiaFast.lf_pins (fun (STATIC HOK : LiaFast.U) => LiaFast.u0).
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK).
    intros fx regs m md hs p k ret K HP MD Ha0 Hpk Hra Hret Hgp Htp AL SPB HT ST CONT.
    resume MD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    exit_rz r1 HR1.
    eapply (FREE _ r1 m md hs p k ret K HP MD).
    - rewrite HR1. getr_leaf. exact Ha0.
    - exact Hpk.
    - rewrite HR1. getr_leaf. exact Hra.
    - exact Hret.
    - rewrite HR1. getr_leaf. exact Hgp.
    - rewrite HR1. getr_leaf. exact Htp.
    - unfold sp_of in *. rewrite HR1. getr_leaf. exact AL.
    - unfold sp_of in *. rewrite HR1. getr_leaf. exact SPB.
    - unfold sp_of in *. rewrite HR1. getr_leaf. exact HT.
    - unfold sp_of in *. rewrite HR1. getr_leaf. exact ST.
    - intros fx2 r2 m2 md2 hs2 Hfx2 HP2 MD2 VM2 UB2 KP2 BL CS MU2 ST2.
      assert (SP1 : sp_of r1 = sp_of regs) by (unfold sp_of; rewrite HR1; getr_leaf; reflexivity).
      rewrite SP1 in MU2, ST2.
      apply (CONT fx2 r2 m2 md2 hs2); [congruence | exact HP2 | exact MD2 | exact VM2 | exact UB2 | exact KP2 | exact BL | | exact MU2 | exact ST2].
      destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
      repeat split;
        first [ rewrite C2 | rewrite C3 | rewrite C4 | rewrite C8 | rewrite C9 | rewrite C18 | rewrite C19
              | rewrite C20 | rewrite C21 | rewrite C22 | rewrite C23 | rewrite C24 | rewrite C25 | rewrite C26 | rewrite C27 ];
        rewrite HR1; getr_leaf; reflexivity.
  Qed.
End DELETE.
End U_h_delete.

Module U_h_memmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memmove_disj_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs old : list byte),
    bytes_at USEGS m (bv_unsigned a1) bs ->
    u8arr USEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (1 <= bv_unsigned a2 < 2^62)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt USEGS (memcpy_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a1) (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x604ac) fc None m (seg_rom USEGS)).

Lemma memmove_disj_spec : memcpy_stmt -> memmove_disj_stmt.
Proof.
  intros MEMCPY. unfold memmove_disj_stmt.
  intros until old. intros SRC DST LEN N N1 DISJ NW1 NW2 RA.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, R1, R2.
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  let Hc := fresh "Hc" in if_cases Hc; [clear Hc|].
  2:{ exfalso. apply (proj1 (Bool.negb_false_iff _)) in Hc. unfold bv_ltu in Hc. apply Z.ltb_lt in Hc.
      rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap, bv_modulus in Hc.
      rewrite Z.shiftl_mul_pow2 in Hc by lia. change (2 ^ 1)%Z with 2%Z in Hc.
      change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hc.
      rewrite (Z.mod_small (bv_unsigned a2 * 2) (2^64)) in Hc by lia.
      rewrite (Z.mod_small (bv_unsigned a2 + bv_unsigned a0) (2^64)) in Hc by lia.
      replace ((0 - bv_unsigned a2 * 2) mod 2^64)%Z with (2^64 - bv_unsigned a2 * 2)%Z in Hc
        by (rewrite <- (Z.mod_small (2^64 - bv_unsigned a2 * 2) (2^64)) by lia;
            replace (0 - bv_unsigned a2 * 2)%Z with ((2^64 - bv_unsigned a2 * 2) + (-1) * 2^64)%Z by lia;
            rewrite Z.mod_add by lia; reflexivity).
      destruct DISJ as [D1|D1].
      - rewrite Z.mod_small in Hc by lia. lia.
      - replace (bv_unsigned a1 - (bv_unsigned a2 + bv_unsigned a0))%Z
          with ((2^64 + bv_unsigned a1 - (bv_unsigned a2 + bv_unsigned a0)) + (-1) * 2^64)%Z in Hc by lia.
        rewrite Z.mod_add in Hc by lia. rewrite Z.mod_small in Hc by lia. lia. }
  step. (* [comment removed for export] *)
  eapply MEMCPY; eassumption || lia.
Qed.
End U_h_memmove.

Module U_h_soe.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_new OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_delete OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_memmove.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SOE_NEED : Z := 80 + (16 + U_MNEED).

Lemma lor1_even : forall z, (z mod 2 = 0)%Z -> Z.lor z 1 = (z + 1)%Z.
Proof.
  intros z Hz. pose proof (Z.add_lor_land z 1) as H.
  assert (L : Z.land z 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones by lia; exact Hz).
  lia.
Qed.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section SOE.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  (* [comment removed for export] *)
  Definition soe_R_contract : Prop :=
    forall (fx : FPState) regs m md hs (o t : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE (t + 1) <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 t ->
      (23 <= t)%Z -> (t + 1 <= 2^26)%Z -> (t mod 2 = 1)%Z ->
      rw_cells USEGS m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk USEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (p : Z) (buf : list byte),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE (t + 1))%Z -> (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) ->
         blocks_add (blocks hs) (blocks hs') (p, t + 1)%Z -> ~ In (p, t + 1)%Z (blocks hs) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(o, o + 24); (p, p + t + 1); (sp_of regs - SOE_NEED, sp_of regs)]%Z) m m' ->
         stk USEGS m' (sp_of regs - SOE_NEED) (sp_of regs) ->
         rw_cells USEGS m' o [C8 (Z_to_bv 64 (t + 2)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 p)] ->
         u8arr USEGS m' p buf -> length buf = Z.to_nat (t + 1) ->
         realizes_cfg USEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom USEGS)) md') K) ->
      realizes_cfg USEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x231b4) m (seg_rom USEGS)) md) K.

  #[using="STATIC HOK MEMCPY"] Lemma soe_R_ok : soe_R_contract.
  Proof. LiaFast.lf_pins (fun (STATIC HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (new_ok cfg HI GP TP HTOP STATIC HOK) as NEW.
    pose proof (memmove_disj_spec MEMCPY) as MEMMOVE.
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold U_IMG_LO, U_IMG_END in HTOPB.
    intros fx regs m md hs o t ret K HP MD UB Ha0 Ha1 Ht1 Ht2 Hodd OBJ Hso Hoe Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold SOE_NEED, U_MNEED in *.
    resume MD. rewrite Ha0, Ha1, Hra.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl USEGS m) as WM.
    carve_frame 80%nat ST.
    do 11 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (rd_byte0_C8 USEGS _ _ _ _ OBJ) as RD0.
    step. (* [comment removed for export] *)
    clear RD0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    name_mem m0.
    exit_rz r1 HR1.
    assert (HP1 : Heap hs m0 md).
    { eapply FRAME; [exact HP | exact MU | exact WM |].
      intros x Hx. destruct (BOK _ _ _ HP) as [_ O1]. cbn [outside] in Hx.
      destruct (outside_dec (owned hs) x) as [Ho|Ho]; [exact Ho|]. specialize (O1 x Ho). lia. }
    assert (SP1 : sp_of r1 = (bv_unsigned sp + -80)%Z).
    { unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. reflexivity. }
    eapply (NEW _ r1 m0 md hs (t + 1)%Z (Z_to_bv 64 0x23230) K HP1 MD UB).
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
    - intros fx2 r2 m2 md2 hs2 p Hfx2 HP2 MD2 VM2 UB2 KP2 Ha02 Hp16 BADD FRESH CS MU2 ST2.
      rewrite SP1 in MU2, ST2.
      destruct (BOK _ _ _ HP2) as [B2 O2].
      destruct (B2 p (t + 1)%Z (proj2 (BADD (p, t + 1)%Z) (or_introl eq_refl))) as (Hn1 & Hreg & BST & BDO & BDJ).
      unfold U_IMG_LO, U_IMG_END in Hreg.
      (* [comment removed for export] *)
      assert (AGF : agree_on m0 m2 (bv_unsigned sp + -80)%Z 80).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; split; [lia | split; [lia|exact I]] | lia | lia | left; lia]. }
      assert (AGO : agree_on m0 m2 o 24).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m0 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; split; [lia | split; [lia|exact I]] | lia | lia | left; lia]. }
      apply (rw_cells_agree USEGS m0 m2) in FR; [|exact AGF].
      apply (rw_cells_agree USEGS m0 m2) in OBJ; [|exact AGO].
      clear AGF AGO. rename MU into MU0. rename WM into WM0.
      lazymatch type of MU0 with ?T => change (keep T) in MU0 end.
      (* [comment removed for export] *)
      destruct (stk_carve USEGS m2 p (p + (t + 1)) (Z.to_nat (t + 1)) BST ltac:(lia)) as [_ [buf0 BUF]].
      replace (p + (t + 1) - Z.of_nat (Z.to_nat (t + 1)))%Z with p in BUF by lia.
      assert (LB0 : length buf0 = Z.to_nat (t + 1)) by exact (proj1 (proj1 (proj1 BUF))).
      pose proof (u8arr_of_rw_cells USEGS _ _ _ _ BUF) as BUFA. clear BUF.
      lazymatch type of MU2 with ?T => change (keep T) in MU2 end.
      resume MD2. rewrite Ha02. cs_resume CS HR1.
      pose proof (munch_refl [(o, o + 24); (p, p + (t + 1)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m2) as MU.
      pose proof (wmono_refl USEGS m2) as WM.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (bytes_at_sub USEGS m2 o _ 1 1 (cells_bytes_of_rw USEGS _ _ _ OBJ) ltac:(cbn; lia)) as SRC.
      change (firstn 1 (skipn 1 (cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) with [Z_to_bv 8 0] in SRC.
      change (Z.of_nat 1) with 1%Z in SRC.
      rewrite <- (firstn_skipn 1 buf0) in BUFA. apply u8arr_app in BUFA. destruct BUFA as [DST0 DST1].
      pose proof (unsigned_lit p ltac:(lia)) as ULp. pose proof (unsigned_lit (o + 1) ltac:(lia)) as ULo.
      pose proof (unsigned_lit 1 ltac:(lia)) as UL1.
      rewrite firstn_length_le in DST1 by lia. change (Z.of_nat 1) with 1%Z in DST1.
      assert (LS1 : length (skipn 1 buf0) = Z.to_nat t) by (rewrite skipn_length, LB0; lia).
      assert (LF1 : length (firstn 1 buf0) = 1%nat) by (rewrite firstn_length_le; lia).
      assert (SUBFP : sub_fp [(bv_unsigned (Z_to_bv 64 p), bv_unsigned (Z_to_bv 64 p) + bv_unsigned (Z_to_bv 64 1))]%Z
                 [(o, o + 24); (p, p + (t + 1)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z).
      { unfold sub_fp; cbn [outside]; intros. slia. }
      call MEMMOVE.
      1:{ rewrite ULo. exact SRC. }
      1:{ rewrite ULp. exact DST0. }
      1:{ rewrite LF1. reflexivity. }
      1:{ rewrite UL1. reflexivity. }
      1:{ rewrite UL1. lia. }
      1:{ rewrite ULp, ULo, UL1. lia. }
      1:{ rewrite ULp, UL1. lia. }
      1:{ rewrite ULo, UL1. lia. }
      1:{ reflexivity. }
      name_mem m3.
      step. (* [comment removed for export] *)
      if_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 11 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ret_pc_even_w ret Hret).
      exit_rz r3 HR3.
      unfold keep in MU0, MU2.
      (* [comment removed for export] *)
      lazymatch goal with H : rw_cells USEGS m1 o _ |- _ => rename H into OBJ' end.
      rewrite (unsigned_lit (t + 1)) in OBJ' by lia. rewrite lor1_even in OBJ' by (Z.div_mod_to_equations; lia).
      lazymatch goal with H : u8arr USEGS m1 (bv_unsigned (Z_to_bv 64 p)) _ |- _ => rename H into D0' end.
      rewrite ULp in D0'.
      lazymatch goal with H : u8arr USEGS m1 (p + _) (skipn 1 buf0) |- _ => rename H into D1' end.
      pose proof (proj2 (u8arr_app USEGS m1 p _ _) (conj D0' ltac:(cbn; rewrite ?Z.add_0_r; exact D1'))) as BUF'.
      replace (t + 1 + 1)%Z with (t + 2)%Z in OBJ' by lia.
      apply (CONT fx1 r3 m1 md2 hs2 p ([Z_to_bv 8 0] ++ skipn 1 buf0)); [congruence | | exact MD2 | exact VM2 | exact UB2 | apply (keep_trans U_KEEP m m0 m1); [eapply keep_munch; [|exact MU0]; keep_side | apply (keep_trans U_KEEP m0 m2 m1); [exact KP2 | eapply keep_munch; [|exact MU]; keep_side]] | exact BADD | exact FRESH | | | | exact OBJ' | exact BUF' | ].
      + eapply FRAME; [exact HP2 | exact MU | exact WM |].
        intros z Hz. cbn [outside] in Hz.
        destruct (outside_dec (owned hs2) z) as [Ho|Ho]; [exact Ho|]. pose proof (O2 z Ho) as [Hz1 _].
        assert (Hzb : ~ (p <= z < p + (t + 1))%Z) by (intros Hin; exact (Ho (disjoint_outside _ _ _ z BDO Hin))).
        lia.
      + repeat split; rewrite HR3; getr_leaf; reflexivity.
      + (* [comment removed for export] *)
        intros z Hz. rewrite !outside_app in Hz. destruct Hz as (Hz1 & Hz2 & Hz3). cbn [outside] in Hz3.
        rewrite (MU z) by (cbn [outside]; repeat split; try exact I; lia).
        rewrite (MU2 z) by (apply outside_app; split; [exact Hz1 | apply outside_app; split; [exact Hz2 | cbn [outside]; split; [lia | split; [lia | exact I]]]]).
        rewrite (MU0 z) by (cbn [outside]; split; [lia | exact I]). reflexivity.
      + lazymatch goal with H : stk USEGS m1 _ (bv_unsigned sp + -80) |- _ => rename H into ST' end.
        lazymatch goal with H : rw_cells USEGS m1 (bv_unsigned sp + -80) _ |- _ => rename H into FR' end.
        eapply stk_release in FR'; [ | exact ST' | lia ]. cbn [cells_size csize Nat.add] in FR'.
        replace (bv_unsigned sp + -80 + Z.of_nat 80)%Z with (bv_unsigned sp) in FR' by lia.
        replace (bv_unsigned sp - (80 + (16 + 8192)))%Z with (bv_unsigned sp + -80 - (16 + 8192))%Z by lia. exact FR'.
      + rewrite app_length, LS1. cbn [length]. lia.
  Qed.
End SOE.
End U_h_soe.


Module U_h_crls_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface U_hbase.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Definition CRLS_NEED : Z := 64 + SOE_NEED.

Section CRLS_STMT.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  (* [comment removed for export] *)
  Definition str_result (hs hs' : hi_HS HI) (m' : word -> option byte) (o s : Z) : Prop :=
    ((s <= 22)%Z /\ blocks_same (blocks hs) (blocks hs') /\ rw_cells USEGS m' o [C1 (Z_to_bv 8 (2 * s))] /\
       exists ob, length ob = 23%nat /\ u8arr USEGS m' (o + 1) ob)
    \/ (exists (c p : Z) (buf : list byte), (23 <= c < 2^26)%Z /\ (c mod 2 = 1)%Z /\ (s <= c)%Z /\
          blocks_add (blocks hs) (blocks hs') (p, c + 1)%Z /\ ~ In (p, c + 1)%Z (blocks hs) /\
          rw_cells USEGS m' o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] /\
          u8arr USEGS m' p buf /\ length buf = Z.to_nat (c + 1)).

  Definition crls_contract_if (COND : Z -> Prop) : Prop :=
    forall (fx : FPState) regs m md hs (o f ptr0 rem0 : Z) (ojunk bs0 : list byte) (ret : word) (K : TSet),
      COND rem0 ->
      Heap hs m md -> md_ok md -> (U md + 2 * MCHARGE 136 <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 f -> getr regs 12 = Z_to_bv 64 128 ->
      rw_cells USEGS m o [CB 24 ojunk] -> (o mod 8 = 0)%Z ->
      rw_cells USEGS m f [C8 (Z_to_bv 64 ptr0); C8 (Z_to_bv 64 rem0)] ->
      (0 <= rem0 <= 2^26)%Z -> bytes_at USEGS m ptr0 bs0 -> Z.of_nat (length bs0) = rem0 ->
      (rem0 = 0%Z \/ exists q k, In (q, k) (blocks hs) /\ (q <= ptr0)%Z /\ (ptr0 + rem0 <= q + k)%Z) ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z -> (sp_of regs <= f)%Z -> (f + 16 < 2^64)%Z ->
      (o + 24 <= f \/ f + 16 <= o)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - CRLS_NEED)%Z ->
      stk USEGS m (sp_of regs - CRLS_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (s ptr' rem' : Z),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + 2 * MCHARGE 136)%Z -> (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) -> callee_saved regs regs' ->
         munch (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP); (o, o + 24); (f, f + 16);
                           (sp_of regs - CRLS_NEED, sp_of regs)]%Z) m m' ->
         (forall q k, In (q, k) (blocks hs) -> In (q, k) (blocks hs') /\ agree_on m m' q k) ->
         stk USEGS m' (sp_of regs - CRLS_NEED) (sp_of regs) ->
         rw_cells USEGS m' f [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')] ->
         (ptr' + rem' = ptr0 + rem0)%Z -> (0 <= rem' <= rem0)%Z -> (0 <= s <= 128)%Z -> (s <= rem0)%Z ->
         str_result hs hs' m' o s ->
         realizes_cfg USEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom USEGS)) md') K) ->
      realizes_cfg USEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x2303c) m (seg_rom USEGS)) md) K.
  Definition crls_contract : Prop := crls_contract_if (fun _ => True).
End CRLS_STMT.
End U_h_crls_stmt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_crls_stmt.
Import ListNotations.

Module U_h_soe1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_new OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_delete OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_memmove OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma land1_mod2 : forall x, Z.land x 1 = (x mod 2)%Z.
Proof. intros x. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma landm2 : forall x, (0 <= x)%Z -> Z.land x (-2) = (x - x mod 2)%Z.
Proof.
  intros x Hx. change (-2)%Z with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  pose proof (Z.div_mod x 2 ltac:(lia)). lia.
Qed.

Lemma cap_byte0_odd : forall c, (0 <= c < 2^60)%Z -> (c mod 2 = 1)%Z ->
  Z.land (bv_unsigned (zxb (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (c + 2)))))) 1 = 1%Z.
Proof.
  intros c Hc Hodd. unfold zxb. rewrite (unsigned_lit (c + 2)) by lia.
  rewrite Z_to_bv_unsigned. rewrite land1_mod2.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2 ^ Z.of_N 8)%Z with 256%Z.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
  rewrite (Z.mod_small ((c + 2) mod 256) (2^64)) by (pose proof (Z.mod_pos_bound (c + 2) 256); lia).
  replace 256%Z with (2 * 128)%Z by reflexivity. rewrite Z.rem_mul_r by lia.
  rewrite Z.add_mod by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma cap_land1 : forall c, (0 <= c < 2^60)%Z -> (c mod 2 = 1)%Z -> Z.land (bv_unsigned (Z_to_bv 64 (c + 2))) 1 = 1%Z.
Proof. intros c Hc Hodd. rewrite (unsigned_lit (c + 2)) by lia. rewrite land1_mod2. Z.div_mod_to_equations. lia. Qed.

Lemma cap_landm2 : forall c, (0 <= c < 2^60)%Z -> (c mod 2 = 1)%Z ->
  Z.land (bv_unsigned (Z_to_bv 64 (c + 2))) 18446744073709551614 = (c + 1)%Z.
Proof.
  intros c Hc Hodd. rewrite (unsigned_lit (c + 2)) by lia.
  change 18446744073709551614%Z with (Z.land (-2) (Z.ones 64)). rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite landm2 by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section SOE1.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  Definition soe_S1_contract : Prop :=
    forall (fx : FPState) regs m md hs (o c s p : Z) (buf : list byte) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 22 ->
      (23 <= c)%Z -> (c + 1 <= 2^26)%Z -> (c mod 2 = 1)%Z -> (0 <= s <= 22)%Z ->
      rw_cells USEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] ->
      In (p, c + 1)%Z (blocks hs) -> u8arr USEGS m p buf -> length buf = Z.to_nat (c + 1) ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk USEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (ob : list byte),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md)%Z -> (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) ->
         blocks_del (blocks hs) (blocks hs') (p, c + 1)%Z ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(o, o + 24); (p, p + (c + 1)); (sp_of regs - SOE_NEED, sp_of regs)]%Z) m m' ->
         stk USEGS m' (sp_of regs - SOE_NEED) (sp_of regs) ->
         rw_cells USEGS m' o [C1 (Z_to_bv 8 (2 * s))] -> u8arr USEGS m' (o + 1) ob -> length ob = 23%nat ->
         realizes_cfg USEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom USEGS)) md') K) ->
      realizes_cfg USEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x231b4) m (seg_rom USEGS)) md) K.

  #[using="STATIC HOK MEMCPY"] Lemma soe_S1_ok : soe_S1_contract.
  Proof. LiaFast.lf_pins (fun (STATIC HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (delete_ok cfg HI GP TP HTOP STATIC HOK) as DEL.
    pose proof (memmove_disj_spec MEMCPY) as MEMMOVE.
    destruct HOK as ((HTOPB & SOK) & MALLOC & FREE & FRAME & BOK). unfold U_IMG_LO, U_IMG_END in HTOPB.
    intros fx regs m md hs o c s p buf ret K HP MD Ha0 Ha1 Hc1 Hc2 Hodd Hs OBJ HIN BUFA LB Hso Hoe Hra Hret Hgp Htp AL SPB HT ST CONT.
    unfold sp_of in *. unfold SOE_NEED, U_MNEED in *.
    destruct (BOK _ _ _ HP) as [B1 O1].
    destruct (B1 p (c + 1)%Z HIN) as (Hn1 & Hreg & BST & BDO & BDJ). unfold U_IMG_LO, U_IMG_END in Hreg.
    resume MD. rewrite Ha0, Ha1, Hra.
    set (sp := getr regs 2) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (munch_refl [(o, o + 24); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl USEGS m) as WM.
    carve_frame 80%nat ST.
    do 11 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (rd_byte0_C8 USEGS _ _ _ _ OBJ) as RD0.
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
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    name_mem m0.
    destruct (long_split USEGS _ _ _ _ _ OBJ) as [OB0 OBA]. clear OBJ.
    set (ob0 := (skipn 1 (le8 (Z_to_bv 64 (c + 2))) ++ le8 (Z_to_bv 64 s) ++ le8 (Z_to_bv 64 p))) in OBA.
    assert (LOB0 : length ob0 = 23%nat) by reflexivity.
    pose proof (bytes_at_sub USEGS m0 p buf 0 (Z.to_nat (s + 1)) (proj1 BUFA) ltac:(lia)) as SRC.
    rewrite Z.add_0_r in SRC. change (skipn 0 buf) with buf in SRC.
    rewrite <- (firstn_skipn (Z.to_nat (s + 1)) ob0) in OBA. apply u8arr_app in OBA. destruct OBA as [DST0 DST1].
    assert (LF0 : length (firstn (Z.to_nat (s + 1)) ob0) = Z.to_nat (s + 1)) by (rewrite firstn_length_le; lia).
    assert (LFb : length (firstn (Z.to_nat (s + 1)) buf) = Z.to_nat (s + 1)) by (rewrite firstn_length_le; lia).
    assert (LS0 : length (skipn (Z.to_nat (s + 1)) ob0) = Z.to_nat (22 - s)) by (rewrite skipn_length, LOB0; lia).
    rewrite LF0 in DST1. rewrite Z2Nat.id in DST1 by lia.
    pose proof (unsigned_lit p ltac:(lia)) as ULp. pose proof (unsigned_lit (o + 1) ltac:(lia)) as ULo.
    pose proof (unsigned_lit (s + 1) ltac:(lia)) as ULs.
    call MEMMOVE.
    1:{ rewrite ULp. exact SRC. }
    1:{ rewrite ULo. exact DST0. }
    1:{ rewrite LF0, LFb. reflexivity. }
    1:{ rewrite LFb, ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULp, ULo, ULs. lia. }
    1:{ rewrite ULo, ULs. lia. }
    1:{ rewrite ULp, ULs. lia. }
    1:{ reflexivity. }
    name_mem m3.
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    exit_rz r1 HR1.
    lazymatch type of MU with ?T => change (keep T) in MU end.
    assert (HP1 : Heap hs m3 md).
    { unfold keep in MU. eapply FRAME; [exact HP | exact MU | exact WM |].
      intros z Hz. cbn [outside] in Hz. destruct (outside_dec (owned hs) z) as [Ho|Ho]; [exact Ho|].
      specialize (O1 z Ho). lia. }
    assert (SP1 : sp_of r1 = (bv_unsigned sp + -80)%Z).
    { unfold sp_of. rewrite HR1. getr_leaf. rewrite unsigned_lit by lia. reflexivity. }
    eapply (DEL _ r1 m3 md hs p (c + 1)%Z (Z_to_bv 64 0x232e4) K HP1 MD).
    - rewrite HR1. getr_leaf. reflexivity.
    - right. exact HIN.
    - rewrite HR1. getr_leaf. reflexivity.
    - reflexivity.
    - rewrite HR1. getr_leaf. exact Hgp.
    - rewrite HR1. getr_leaf. exact Htp.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite SP1. lia.
    - unfold U_FNEED. rewrite SP1. lia.
    - unfold U_FNEED. rewrite SP1. lazymatch goal with H : stk USEGS m3 ?lo ?hi |- _ =>
        destruct (stk_split USEGS m3 lo (bv_unsigned sp + -80 - 8192) hi H ltac:(lia)) as [_ H2];
        replace hi with (bv_unsigned sp + -80)%Z in H2 by lia; exact H2 end.
    - intros fx2 r2 m2 md2 hs2 Hfx2 HP2 MD2 VM2 UB2 KP2 BDEL CS MU2 ST2.
      rewrite (proj2 (Z.eqb_neq p 0) ltac:(lia)) in BDEL.
      rewrite SP1 in MU2, ST2. unfold U_FNEED in MU2, ST2.
      (* [comment removed for export] *)
      lazymatch goal with H : u8arr USEGS m3 (bv_unsigned (Z_to_bv 64 (o + 1))) _ |- _ => rename H into DST0' end.
      rewrite ULo in DST0'.
      assert (DST1' : u8arr USEGS m3 (o + 1 + Z.of_nat (length (firstn (Z.to_nat (s + 1)) buf))) (skipn (Z.to_nat (s + 1)) ob0)).
      { rewrite LFb, Z2Nat.id by lia. exact DST1. }
      pose proof (proj2 (u8arr_app USEGS m3 (o + 1) _ _) (conj DST0' DST1')) as OBA'. clear DST1'.
      clear DST0' DST1.
      assert (AGF : agree_on m3 m2 (bv_unsigned sp + -80)%Z 80).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m3 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
      assert (AGO : agree_on m3 m2 o 24).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m3 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
      lazymatch goal with H : rw_cells USEGS m3 (bv_unsigned sp + -80) _ |- _ => rename H into FR end.
      apply (rw_cells_agree USEGS m3 m2) in FR; [|exact AGF].
      apply (rw_cells_agree USEGS m3 m2) in OB0; [|eapply agree_on_sub; [exact AGO | lia | cbn; lia]].
      apply (u8arr_agree USEGS m3 m2) in OBA'; [|eapply agree_on_sub; [exact AGO | lia | rewrite app_length, LFb, LS0; lia]].
      lazymatch goal with H : stk USEGS m3 (bv_unsigned sp - (80 + (16 + 8192))) _ |- _ => rename H into STlo end.
      destruct (stk_split USEGS m3 _ (bv_unsigned sp + -80 - 8192) _ STlo ltac:(lia)) as [STlo' _]. clear STlo.
      assert (AGS : agree_on m3 m2 (bv_unsigned sp - (80 + (16 + 8192)))%Z 16).
      { eapply (cps_agree USEGS _ _ _ _ _ _ _ _ hs hs2 m3 m2 md md2 _ _ _ BOK HP1 HP2 MU2);
          [cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia | left; lia]. }
      apply (stk_agree USEGS m3 m2) in STlo'; [|eapply agree_on_sub; [exact AGS | lia | lia]].
      clear AGF AGO AGS.
      lazymatch type of MU2 with ?T => change (keep T) in MU2 end.
      resume MD2. cs_resume CS HR1.
      pose proof (munch_refl [(o, o + 24); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m2) as MU'.
      pose proof (wmono_refl USEGS m2) as WM'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 11 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ret_pc_even_w ret Hret).
      exit_rz r3 HR3.
      unfold keep in MU, MU2.
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (mkst _ _ ?mm _) _) _ => rename mm into mF end.
      lazymatch goal with H : rw_cells USEGS mF o [C1 _] |- _ => rename H into OB' end.
      rewrite (unsigned_lit s), Z.shiftl_mul_pow2, (unsigned_lit (s * 2^1)) in OB' by lia. change (2^1)%Z with 2%Z in OB'.
      replace (s * 2)%Z with (2 * s)%Z in OB' by lia.
      lazymatch goal with H : u8arr USEGS mF (o + 1) _ |- _ => rename H into OBA2 end.
      apply (CONT fx1 r3 mF md2 hs2 (firstn (Z.to_nat (s + 1)) buf ++ skipn (Z.to_nat (s + 1)) ob0)); [congruence | | exact MD2 | exact VM2 | exact UB2 | apply (keep_trans U_KEEP m m3 mF); [eapply keep_munch; [|exact MU]; keep_side | apply (keep_trans U_KEEP m3 m2 mF); [exact KP2 | eapply keep_munch; [|exact MU']; keep_side]] | exact BDEL | | | | exact OB' | exact OBA2 | ].
      + eapply FRAME; [exact HP2 | exact MU' | exact WM' |].
        intros z Hz. cbn [outside] in Hz.
        destruct (outside_dec (owned hs2) z) as [Ho|Ho]; [exact Ho|]. destruct (BOK _ _ _ HP2) as [_ O2].
        pose proof (O2 z Ho) as [Hz1 _]. lia.
      + repeat split; rewrite HR3; getr_leaf; reflexivity.
      + intros z Hz. rewrite !outside_app in Hz. destruct Hz as (Hz1 & Hz2 & Hz3). cbn [outside] in Hz3.
        rewrite (MU' z) by (cbn [outside]; repeat split; try exact I; lia).
        rewrite (MU2 z) by (apply outside_app; split; [exact Hz1 | apply outside_app; split; [exact Hz2 | cbn [outside]; repeat split; try exact I; lia]]).
        rewrite (MU z) by (cbn [outside]; repeat split; try exact I; lia). reflexivity.
      + lazymatch goal with H : stk USEGS mF _ (bv_unsigned sp + -80) |- _ => rename H into ST' end.
        lazymatch goal with H : rw_cells USEGS mF (bv_unsigned sp + -80) _ |- _ => rename H into FR' end.
        lazymatch goal with H : stk USEGS mF (bv_unsigned sp - (80 + (16 + 8192))) _ |- _ => rename H into STlo2 end.
        eapply stk_release in FR'; [ | exact ST' | lia ]. cbn [cells_size csize Nat.add] in FR'.
        replace (bv_unsigned sp + -80 + Z.of_nat 80)%Z with (bv_unsigned sp) in FR' by lia.
        eapply stk_merge; [exact STlo2 | exact FR' | lia].
      + rewrite app_length, LFb, LS0. lia.
  Qed.
End SOE1.
End U_h_soe1.

Module U_h_pushback.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation USEGS := Ubsan.M.loaded_segments.

Definition pb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list ivl) (m : word -> option byte) (P : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch W m m' /\ wmono USEGS m m' /\ stk USEGS m' (bv_unsigned sp - 64) (bv_unsigned sp) /\ P m'.

Definition pb_short_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s : Z) (ob : list byte),
    rw_cells USEGS m o [C1 (Z_to_bv 8 (2 * s))] -> u8arr USEGS m (o + 1) ob -> length ob = 23%nat -> (0 <= s < 22)%Z ->
    stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) -> (bv_unsigned sp <= o)%Z -> (o + 24 < 2^64)%Z ->
    (64 <= bv_unsigned sp)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
    evt USEGS (pb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24)]%Z m
                 (fun m' => rw_cells USEGS m' o [C1 (Z_to_bv 8 (2 * (s + 1)))] /\
                            exists ob', length ob' = 23%nat /\ u8arr USEGS m' (o + 1) ob'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x48710) fc None m (seg_rom USEGS)).

Lemma zxb_even : forall s, (0 <= s < 128)%Z -> bv_unsigned (zxb (Z_to_bv 8 (2 * s))) = (2 * s)%Z.
Proof.
  intros s Hs. unfold zxb. rewrite (Z_to_bv_unsigned 8 (2 * s)). rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma le1_exists : forall v : word, exists b : byte, le1 v = [b].
Proof.
  intros v. pose proof (length_le1 v) as L.
  destruct (le1 v) as [|b [|b' l]]; cbn in L; try lia. exists b; reflexivity.
Qed.

Lemma zxb_lit8 : forall z, (0 <= z < 256)%Z -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia. Qed.

Lemma shr1_even : forall s, (0 <= s)%Z -> Z.shiftr (2 * s) 1 = s.
Proof. intros s Hs. rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

Lemma pb_short_spec : pb_short_stmt.
Proof.
  unfold pb_short_stmt. intros until ob. intros OB0 OBA LOB Hs ST Hso Hoe Hsp Hra.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24)]%Z m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  carve_frame 64%nat ST.
  do 8 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (zxb_lit8 (2 * s)) by lia.
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (2 * s)) by lia. rewrite land1_mod2. replace ((2 * s) mod 2)%Z with 0%Z by (Z.div_mod_to_equations; lia).
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_vm.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (2 * s)), (shr1_even s) by lia.
  lazymatch goal with H : rw_cells USEGS _ o [C1 _] |- _ => rename H into OB1 end.
  rewrite (unsigned_lit (2 * s + 2)) in OB1 by lia.
  pose proof (u8arr_store_ok USEGS _ (o + 1) ob s _ OBA ltac:(lia) eq_refl) as SOK.
  step. (* [comment removed for export] *)
  destruct (le1_exists a1) as [cb Hcb]. rewrite Hcb.
  pose proof (u8arr_write USEGS _ (o + 1) ob s cb OBA ltac:(lia)) as OBA'.
  store_done.
  assert (LU : length (upd ob (Z.to_nat s) cb) = 23%nat) by (rewrite upd_length; exact LOB).
  pose proof (u8arr_store_ok USEGS _ (o + 1) _ (s + 1) _ OBA' ltac:(rewrite LU; lia) ltac:(f_equal; lia)) as SOK2.
  step. (* [comment removed for export] *)
  match goal with |- context [write_to_mem _ _ (le1 ?v)] => destruct (le1_exists v) as [cz Hcz]; rewrite Hcz end.
  pose proof (u8arr_write USEGS _ (o + 1) _ (s + 1) cz OBA' ltac:(rewrite LU; lia)) as OBA''.
  replace (o + 1 + s + 1)%Z with (o + 1 + (s + 1))%Z by lia.
  store_done.
  do 9 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  apply evt_done. unfold pb_post. do 16 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split.
  - lazymatch goal with H : stk USEGS _ _ (bv_unsigned sp + -64) |- _ => rename H into ST' end.
    eapply stk_release in FR; [ | exact ST' | lia ]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in FR by lia. exact FR.
  - split; [replace (2 * (s + 1))%Z with (2 * s + 2)%Z by lia; exact OB1|].
    eexists. split; [|exact OBA'']. rewrite !upd_length. exact LOB.
Qed.

Definition pb_long_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o c s p : Z) (buf : list byte),
    rw_cells USEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] ->
    (23 <= c < 2^26)%Z -> (c mod 2 = 1)%Z -> (0 <= s < c)%Z ->
    u8arr USEGS m p buf -> length buf = Z.to_nat (c + 1) -> (0 <= p)%Z -> (p + c + 1 <= bv_unsigned sp - 64)%Z ->
    stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) -> (bv_unsigned sp <= o)%Z -> (o + 24 < 2^64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt USEGS (pb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24); (p, p + c + 1)]%Z m
                 (fun m' => rw_cells USEGS m' o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 (s + 1)); C8 (Z_to_bv 64 p)] /\
                            exists buf', length buf' = length buf /\ u8arr USEGS m' p buf'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x48710) fc None m (seg_rom USEGS)).

Lemma pb_long_spec : pb_long_stmt.
Proof.
  unfold pb_long_stmt. intros until buf. intros OBJ Hc Hodd Hs BUF LB Hp0 Hpsp ST Hso Hoe Hra.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24); (p, p + c + 1)]%Z m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  carve_frame 64%nat ST.
  do 9 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  pose proof (rd_byte0_C8 USEGS _ _ _ _ OBJ) as RD0.
  step. (* [comment removed for export] *)
  clear RD0.
  step. (* [comment removed for export] *)
  rewrite (cap_byte0_odd c) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_vm.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (cap_landm2 c) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite ?(unsigned_lit p), ?(unsigned_lit s) by lia.
  pose proof (u8arr_store_ok USEGS _ p buf s _ BUF ltac:(lia) eq_refl) as SOK.
  step. (* [comment removed for export] *)
  destruct (le1_exists a1) as [cb Hcb]. rewrite Hcb.
  pose proof (u8arr_write USEGS _ p buf s cb BUF ltac:(lia)) as BUF'.
  store_done.
  assert (LU : length (upd buf (Z.to_nat s) cb) = Z.to_nat (c + 1)) by (rewrite upd_length; exact LB).
  pose proof (u8arr_store_ok USEGS _ p _ (s + 1) _ BUF' ltac:(rewrite LU; lia) ltac:(f_equal; lia)) as SOK2.
  step. (* [comment removed for export] *)
  match goal with |- context [write_to_mem _ _ (le1 ?v)] => destruct (le1_exists v) as [cz Hcz]; rewrite Hcz end.
  pose proof (u8arr_write USEGS _ p _ (s + 1) cz BUF' ltac:(rewrite LU; lia)) as BUF''.
  replace (p + s + 1)%Z with (p + (s + 1))%Z by lia.
  store_done.
  do 9 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  apply evt_done. unfold pb_post. do 16 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split.
  - lazymatch goal with H : stk USEGS _ _ (bv_unsigned sp + -64) |- _ => rename H into ST' end.
    eapply stk_release in FR; [ | exact ST' | lia ]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in FR by lia. exact FR.
  - split.
    + lazymatch goal with H : rw_cells USEGS _ o _ |- _ => rename H into OB' end. exact OB'.
    + eexists. split; [|exact BUF'']. rewrite !upd_length. reflexivity.
Qed.
End U_h_pushback.

Module U_h_crls_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe1 OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_pushback.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SHORT.
  Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (o f ptr0 rem0 : Z) (bs0 : list byte).
  Hypothesis Rsp : (64 <= bv_unsigned sp < 2^64)%Z.
  Hypothesis Ho : (bv_unsigned sp + 64 <= o /\ o + 24 < 2^64)%Z.
  Hypothesis Hf : (bv_unsigned sp + 64 <= f /\ f + 16 < 2^64 /\ (o + 24 <= f \/ f + 16 <= o))%Z.
  Hypothesis Hrem0 : (1 <= rem0 <= 2^26)%Z.
  Hypothesis Hlen0 : Z.of_nat (length bs0) = rem0.
  Hypothesis Hpay : (1 <= ptr0 /\ ptr0 + rem0 <= bv_unsigned sp - 64)%Z.
  Notation W0 := [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24); (f, f + 16)]%Z.
  Hypothesis DATAF : forall m, munch W0 m0 m -> bytes_at USEGS m ptr0 bs0.

  Definition loopS_post : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (s' ptr' rem' : Z) (ob' : list byte),
      ms' = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 f) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23100) fc None m' (seg_rom USEGS)
      /\ munch W0 m0 m' /\ wmono USEGS m0 m' /\ stk USEGS m' (bv_unsigned sp - 64) (bv_unsigned sp)
      /\ rw_cells USEGS m' f [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')]
      /\ (ptr' + rem' = ptr0 + rem0 /\ 0 <= rem' <= rem0)%Z
      /\ rw_cells USEGS m' o [C1 (Z_to_bv 8 (2 * s'))] /\ u8arr USEGS m' (o + 1) ob' /\ length ob' = 23%nat
      /\ (0 <= s' <= 22 /\ s' <= rem0 - rem')%Z.

  Definition loopS_ok (k : nat) : Prop :=
    forall (i s rem : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ob : list byte),
      (Z.to_nat (128 - i) < k)%nat -> (1 <= i <= 128)%Z -> (0 <= s <= i - 1)%Z -> (s <= rem0 - rem)%Z ->
      (1 <= rem <= rem0)%Z -> (rem0 <= 22)%Z ->
      rw_cells USEGS m f [C8 (Z_to_bv 64 (ptr0 + rem0 - rem)); C8 (Z_to_bv 64 rem)] ->
      rw_cells USEGS m o [C1 (Z_to_bv 8 (2 * s))] -> u8arr USEGS m (o + 1) ob -> length ob = 23%nat ->
      stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
      munch W0 m0 m -> wmono USEGS m0 m ->
      evt USEGS loopS_post
        (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) (Z_to_bv 64 rem) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x230a4) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  #[using="bs0 Rsp Ho Hf"] Lemma loopS_push : forall k, loopS_ok k ->
    forall (i s rem' : Z) (x1 x5 x6 x7 cv x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x10 : word)
           (m : word -> option byte) (ob : list byte),
      (i = 128%Z \/ (Z.to_nat (128 - (i + 1)) < k)%nat) -> (1 <= i <= 128)%Z -> (0 <= s <= i - 1)%Z -> (s + 1 <= rem0 - rem')%Z ->
      (0 <= rem' < rem0)%Z -> (rem0 <= 22)%Z ->
      rw_cells USEGS m f [C8 (Z_to_bv 64 (ptr0 + rem0 - rem')); C8 (Z_to_bv 64 rem')] ->
      rw_cells USEGS m o [C1 (Z_to_bv 8 (2 * s))] -> u8arr USEGS m (o + 1) ob -> length ob = 23%nat ->
      stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
      munch W0 m0 m -> wmono USEGS m0 m ->
      evt USEGS loopS_post
        (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) x10 cv x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x230e8) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs0 Rsp Ho Hf : LiaFast.U) => LiaFast.u0).
    intros k IH i s rem' x1 x5 x6 x7 cv x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x10 m ob Hk Hi Hs Hsr Hrem Hr22 FDP OB0 OBA LOB ST MU WM.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call pb_short_spec.
    1:{ exact OB0. } 1:{ exact OBA. } 1:{ exact LOB. } 1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. }
    match goal with H : exists ob', _ |- _ => destruct H as (ob1 & LOB1 & OBA1) end.
    lazymatch goal with H : rw_cells USEGS _ o [C1 _] |- _ => rename H into OB1 end.
    lazymatch goal with H : stk USEGS _ (bv_unsigned sp - 64) _ |- _ => rename H into ST1 end.
    step. (* [comment removed for export] *)
    let Hc := fresh "Hc" in if_cases Hc; cond_cleanup Hc.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply evt_done; unfold loopS_post; do 19 eexists; exists mm, (s + 1)%Z, (ptr0 + rem0 - rem')%Z, rem', ob1 end.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FDP|].
      split; [lia|]. split; [exact OB1|]. split; [exact OBA1|]. split; [exact LOB1|]. lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd; cond_cleanup Hd.
      + destruct Hk as [Hk|Hk]; [lia|].
        eapply (IH (i + 1)%Z (s + 1)%Z rem'); try eassumption; try lia.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          apply evt_done; unfold loopS_post; do 19 eexists; exists mm, (s + 1)%Z, (ptr0 + rem0 - rem')%Z, rem', ob1 end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FDP|].
        split; [lia|]. split; [exact OB1|]. split; [exact OBA1|]. split; [exact LOB1|]. lia.
  Qed.

  #[using="bs0 Rsp Ho Hf Hrem0 Hlen0 Hpay DATAF"] Lemma loopS_loop : forall k, loopS_ok k.
  Proof. LiaFast.lf_pins (fun (bs0 Rsp Ho Hf Hrem0 Hlen0 Hpay DATAF : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loopS_ok; intros i s rem x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m ob
      Hk Hi Hs Hsr Hrem Hr22 FDP OB0 OBA LOB ST MU WM; [lia|].
    pose proof (DATAF m MU) as DATA. pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    destruct (nth_error bs0 (Z.to_nat (rem0 - rem))) as [ch|] eqn:Hb.
    2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8ro_read USEGS m ptr0 bs0 (rem0 - rem) ch _ DATA Hb ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with H : rw_cells USEGS _ f _ |- _ => rename H into FDP1 end.
    replace (rem + -1)%Z with (rem - 1)%Z in FDP1 by lia.
    let Hc := fresh "Hc" in if_cases Hc.
    - (* [comment removed for export] *)
      eapply (loopS_push k IH i s (rem - 1)); try eassumption; try lia.
      replace (ptr0 + rem0 - (rem - 1))%Z with (ptr0 + rem0 - rem + 1)%Z by lia. exact FDP1.
    - (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd.
      + cond_cleanup Hd.
        eapply (loopS_push k IH i s (rem - 1)); try eassumption; try lia.
        replace (ptr0 + rem0 - (rem - 1))%Z with (ptr0 + rem0 - rem + 1)%Z by lia. exact FDP1.
      + cond_cleanup Hd.
        destruct (nth_error bs0 (Z.to_nat (rem0 - rem + 1))) as [ch2|] eqn:Hb2.
        2:{ exfalso. apply nth_error_None in Hb2. lia. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
        assert (MU1 : munch W0 m0 m1) by assumption.
        pose proof (DATAF m1 MU1) as DATA1.
        pose proof (u8ro_read USEGS m1 ptr0 bs0 (rem0 - rem + 1) ch2 _ DATA1 Hb2 ltac:(lia) ltac:(f_equal; lia)) as RD2.
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        clear RD2.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        lazymatch goal with H : rw_cells USEGS _ f _ |- _ => rename H into FDP2 end.
        replace (rem + -2)%Z with (rem - 2)%Z in FDP2 by lia.
        let He := fresh "He" in if_cases He.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            apply evt_done; unfold loopS_post; do 19 eexists; exists mm, s, (ptr0 + rem0 - (rem - 2))%Z, (rem - 2)%Z, ob end.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [replace (ptr0 + rem0 - (rem - 2))%Z with (ptr0 + rem0 - rem + 2)%Z by lia; exact FDP2|].
          split; [lia|]. split; [assumption|]. split; [assumption|]. split; [exact LOB|]. lia.
        * eapply (loopS_push k IH i s (rem - 2)); try eassumption; try lia.
          replace (ptr0 + rem0 - (rem - 2))%Z with (ptr0 + rem0 - rem + 2)%Z by lia. exact FDP2.
  Qed.
End SHORT.

Section LONG.
  Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (o f ptr0 rem0 : Z) (bs0 : list byte) (c p : Z).
  Hypothesis Hc : (23 <= c < 2^26 /\ c mod 2 = 1 /\ Z.min 128 rem0 <= c)%Z.
  Hypothesis Hp : (0 <= p /\ p + c + 1 <= bv_unsigned sp - 64 /\ (p + c + 1 <= ptr0 \/ ptr0 + rem0 <= p))%Z.
  Hypothesis Rsp : (64 <= bv_unsigned sp < 2^64)%Z.
  Hypothesis Ho : (bv_unsigned sp + 64 <= o /\ o + 24 < 2^64)%Z.
  Hypothesis Hf : (bv_unsigned sp + 64 <= f /\ f + 16 < 2^64 /\ (o + 24 <= f \/ f + 16 <= o))%Z.
  Hypothesis Hrem0 : (1 <= rem0 <= 2^26)%Z.
  Hypothesis Hlen0 : Z.of_nat (length bs0) = rem0.
  Hypothesis Hpay : (1 <= ptr0 /\ ptr0 + rem0 <= bv_unsigned sp - 64)%Z.
  Notation W0 := [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + 24); (f, f + 16); (p, p + c + 1)]%Z.
  Hypothesis DATAF : forall m, munch W0 m0 m -> bytes_at USEGS m ptr0 bs0.

  Definition loopL_post : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (s' ptr' rem' : Z) (ob' : list byte),
      ms' = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 f) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x23100) fc None m' (seg_rom USEGS)
      /\ munch W0 m0 m' /\ wmono USEGS m0 m' /\ stk USEGS m' (bv_unsigned sp - 64) (bv_unsigned sp)
      /\ rw_cells USEGS m' f [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')]
      /\ (ptr' + rem' = ptr0 + rem0 /\ 0 <= rem' <= rem0)%Z
      /\ rw_cells USEGS m' o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 p)]
      /\ u8arr USEGS m' p ob' /\ length ob' = Z.to_nat (c + 1)
      /\ (0 <= s' <= c /\ s' <= rem0 - rem' /\ s' <= 128)%Z.

  Definition loopL_ok (k : nat) : Prop :=
    forall (i s rem : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ob : list byte),
      (Z.to_nat (128 - i) < k)%nat -> (1 <= i <= 128)%Z -> (0 <= s <= i - 1)%Z -> (s <= rem0 - rem)%Z ->
      (1 <= rem <= rem0)%Z ->
      rw_cells USEGS m f [C8 (Z_to_bv 64 (ptr0 + rem0 - rem)); C8 (Z_to_bv 64 rem)] ->
      rw_cells USEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] -> u8arr USEGS m p ob -> length ob = Z.to_nat (c + 1) ->
      stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
      munch W0 m0 m -> wmono USEGS m0 m ->
      evt USEGS loopL_post
        (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) (Z_to_bv 64 rem) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x230a4) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  #[using="bs0 Hc Hp Ho Hf Hrem0 Hpay"] Lemma loopL_push : forall k, loopL_ok k ->
    forall (i s rem' : Z) (x1 x5 x6 x7 cv x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x10 : word)
           (m : word -> option byte) (ob : list byte),
      (i = 128%Z \/ (Z.to_nat (128 - (i + 1)) < k)%nat) -> (1 <= i <= 128)%Z -> (0 <= s <= i - 1)%Z -> (s + 1 <= rem0 - rem')%Z ->
      (0 <= rem' < rem0)%Z ->
      rw_cells USEGS m f [C8 (Z_to_bv 64 (ptr0 + rem0 - rem')); C8 (Z_to_bv 64 rem')] ->
      rw_cells USEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)] -> u8arr USEGS m p ob -> length ob = Z.to_nat (c + 1) ->
      stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
      munch W0 m0 m -> wmono USEGS m0 m ->
      evt USEGS loopL_post
        (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 128) x10 cv x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x230e8) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs0 Hc Hp Ho Hf Hrem0 Hpay : LiaFast.U) => LiaFast.u0).
    intros k IH i s rem' x1 x5 x6 x7 cv x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x10 m ob Hk Hi Hs Hsr Hrem FDP OB0 OBA LOB ST MU WM.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (pb_long_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o c s p ob).
    1:{ exact OB0. } 1:{ lia. } 1:{ lia. } 1:{ pose proof (Z.le_min_l 128 rem0); pose proof (Z.le_min_r 128 rem0); lia. }
    1:{ exact OBA. } 1:{ exact LOB. } 1:{ lia. } 1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. }
    match goal with H : exists ob', _ |- _ => destruct H as (ob1 & LOB1 & OBA1) end. rewrite LOB in LOB1.
    lazymatch goal with H : rw_cells USEGS _ o _ |- _ => rename H into OB1 end.
    lazymatch goal with H : stk USEGS _ (bv_unsigned sp - 64) _ |- _ => rename H into ST1 end.
    step. (* [comment removed for export] *)
    let Hc := fresh "Hc" in if_cases Hc; cond_cleanup Hc.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply evt_done; unfold loopL_post; do 19 eexists; exists mm, (s + 1)%Z, (ptr0 + rem0 - rem')%Z, rem', ob1 end.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FDP|].
      split; [lia|]. split; [exact OB1|]. split; [exact OBA1|]. split; [exact LOB1|]. pose proof (Z.le_min_l 128 rem0); pose proof (Z.le_min_r 128 rem0); lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd; cond_cleanup Hd.
      + destruct Hk as [Hk|Hk]; [lia|].
        eapply (IH (i + 1)%Z (s + 1)%Z rem'); try eassumption; try lia.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          apply evt_done; unfold loopL_post; do 19 eexists; exists mm, (s + 1)%Z, (ptr0 + rem0 - rem')%Z, rem', ob1 end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FDP|].
        split; [lia|]. split; [exact OB1|]. split; [exact OBA1|]. split; [exact LOB1|]. pose proof (Z.le_min_l 128 rem0); pose proof (Z.le_min_r 128 rem0); lia.
  Qed.

  #[using="bs0 Hc Hp Ho Hf Hrem0 Hlen0 Hpay DATAF"] Lemma loopL_loop : forall k, loopL_ok k.
  Proof. LiaFast.lf_pins (fun (bs0 Hc Hp Ho Hf Hrem0 Hlen0 Hpay DATAF : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loopL_ok; intros i s rem x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m ob
      Hk Hi Hs Hsr Hrem FDP OB0 OBA LOB ST MU WM; [lia|].
    pose proof (DATAF m MU) as DATA. pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    destruct (nth_error bs0 (Z.to_nat (rem0 - rem))) as [ch|] eqn:Hb.
    2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8ro_read USEGS m ptr0 bs0 (rem0 - rem) ch _ DATA Hb ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with H : rw_cells USEGS _ f _ |- _ => rename H into FDP1 end.
    replace (rem + -1)%Z with (rem - 1)%Z in FDP1 by lia.
    let Hc := fresh "Hc" in if_cases Hc.
    - (* [comment removed for export] *)
      eapply (loopL_push k IH i s (rem - 1)); try eassumption; try lia.
      replace (ptr0 + rem0 - (rem - 1))%Z with (ptr0 + rem0 - rem + 1)%Z by lia. exact FDP1.
    - (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      let Hd := fresh "Hd" in if_cases Hd.
      + cond_cleanup Hd.
        eapply (loopL_push k IH i s (rem - 1)); try eassumption; try lia.
        replace (ptr0 + rem0 - (rem - 1))%Z with (ptr0 + rem0 - rem + 1)%Z by lia. exact FDP1.
      + cond_cleanup Hd.
        destruct (nth_error bs0 (Z.to_nat (rem0 - rem + 1))) as [ch2|] eqn:Hb2.
        2:{ exfalso. apply nth_error_None in Hb2. lia. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
        assert (MU1 : munch W0 m0 m1) by assumption.
        pose proof (DATAF m1 MU1) as DATA1.
        pose proof (u8ro_read USEGS m1 ptr0 bs0 (rem0 - rem + 1) ch2 _ DATA1 Hb2 ltac:(lia) ltac:(f_equal; lia)) as RD2.
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        clear RD2.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        lazymatch goal with H : rw_cells USEGS _ f _ |- _ => rename H into FDP2 end.
        replace (rem + -2)%Z with (rem - 2)%Z in FDP2 by lia.
        let He := fresh "He" in if_cases He.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            apply evt_done; unfold loopL_post; do 19 eexists; exists mm, s, (ptr0 + rem0 - (rem - 2))%Z, (rem - 2)%Z, ob end.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [replace (ptr0 + rem0 - (rem - 2))%Z with (ptr0 + rem0 - rem + 2)%Z by lia; exact FDP2|].
          split; [lia|]. split; [assumption|]. split; [assumption|]. split; [exact LOB|]. pose proof (Z.le_min_l 128 rem0); pose proof (Z.le_min_r 128 rem0); lia.
        * eapply (loopL_push k IH i s (rem - 2)); try eassumption; try lia.
          replace (ptr0 + rem0 - (rem - 2))%Z with (ptr0 + rem0 - rem + 2)%Z by lia. exact FDP2.
  Qed.
End LONG.
End U_h_crls_loop.

Module U_h_reserve.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require HIface.
Import OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface OSSVerify.Proofs.fast_float.from_chars.lib.H.U_hbase OSSVerify.Proofs.fast_float.from_chars.lib.H.HIface.Hstr OSSVerify.Proofs.fast_float.from_chars.lib.H.U_h_fuzz_base.U_h_soe.
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
             F (ret_pc ra) fc None m' (seg_rom USEGS) /\ munch [] m m' /\ wmono USEGS m m' /\ True.

Definition reserve_short_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o n : Z),
    rw_cells USEGS m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> (0 <= n <= 22)%Z ->
    evt USEGS (reserve_short_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x486a4) fc None m (seg_rom USEGS)).

Lemma reserve_short_spec : reserve_short_stmt.
Proof.
  unfold reserve_short_stmt. intros until n. intros OBJ Hn.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  pose proof (rd_byte0_C8 USEGS _ _ _ _ OBJ) as RD0.
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
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.
  Hypothesis MEMCPY : memcpy_stmt.
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  (* [comment removed for export] *)
  Definition reserve_long_contract : Prop :=
    forall (fx : FPState) regs m md hs (o n : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE (rec n + 1) <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 n -> (23 <= n <= 128)%Z ->
      rw_cells USEGS m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      (sp_of regs <= o)%Z -> (o + 24 < 2^64)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - SOE_NEED)%Z ->
      stk USEGS m (sp_of regs - SOE_NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (p : Z) (buf : list byte),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE (rec n + 1))%Z -> (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) ->
         blocks_add (blocks hs) (blocks hs') (p, rec n + 1)%Z -> ~ In (p, rec n + 1)%Z (blocks hs) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(o, o + 24); (p, p + rec n + 1); (sp_of regs - SOE_NEED, sp_of regs)]%Z) m m' ->
         stk USEGS m' (sp_of regs - SOE_NEED) (sp_of regs) ->
         rw_cells USEGS m' o [C8 (Z_to_bv 64 (rec n + 2)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 p)] ->
         u8arr USEGS m' p buf -> length buf = Z.to_nat (rec n + 1) ->
         realizes_cfg USEGS cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom USEGS)) md') K) ->
      realizes_cfg USEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x486a4) m (seg_rom USEGS)) md) K.

  #[using="STATIC HOK MEMCPY"] Lemma reserve_long_ok : reserve_long_contract.
  Proof. LiaFast.lf_pins (fun (STATIC HOK MEMCPY : LiaFast.U) => LiaFast.u0).
    pose proof (soe_R_ok cfg HI GP TP HTOP STATIC HOK MEMCPY) as SOE.
    intros fx regs m md hs o n ret K HP MD UB Ha0 Ha1 Hn OBJ Hso Hoe Hra Hret Hgp Htp AL SPB HT ST CONT.
    destruct (rec_bounds n Hn) as (Hr1 & Hr2 & Hr3).
    resume MD. rewrite Ha0, Ha1, Hra.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (rd_byte0_C8 USEGS _ _ _ _ OBJ) as RD0.
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
End U_h_reserve.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition FUZZ_NEED : Z := 128 + from_chars_double_need + 5760.
Definition U_RO : list (Z * Z) := [(0x10000, 0x22000); (U_FMIN, U_FMIN + 4)]%Z.

(* [comment removed for export] *)
Definition str_obj (m : word -> option byte) (o : Z) (b : option (Z * Z)) : Prop :=
  match b with
  | None => exists s, (0 <= s <= 22)%Z /\ rw_cells USEGS m o [C1 (Z_to_bv 8 (2 * s))] /\
              exists ob, length ob = 23%nat /\ u8arr USEGS m (o + 1) ob
  | Some (p, n) => exists c s, n = (c + 1)%Z /\ (23 <= c < 2^26)%Z /\ (c mod 2 = 1)%Z /\ (0 <= s <= c)%Z /\
              rw_cells USEGS m o [C8 (Z_to_bv 64 (c + 2)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 p)]
  end.

Definition opt_list {A} (o : option A) : list A := match o with Some x => [x] | None => [] end.

(* [comment removed for export] *)
Definition u_fmt (k : Z) : Z := match k with 0 => 1 | 1 => 4 | 2 => 4 | _ => 5 end%Z.

Lemma u_fmt_ok : forall k, (u_fmt k = 1 \/ u_fmt k = 4 \/ u_fmt k = 5)%Z.
Proof. intros k. unfold u_fmt. destruct k as [|[[]|[]|]|]; cbn; tauto. Qed.

Lemma stk_of_u8arr : forall m A bs, u8arr USEGS m A bs -> stk USEGS m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs [(Ha & Hl & Hb) (_ & _ & Hw)]. split; [lia|]. split; [lia|].
  intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
    destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
Qed.

Lemma str_obj_stk : forall m o b, str_obj m o b -> stk USEGS m o (o + 24).
Proof.
  intros m o [[p n]|] H; cbn [str_obj] in H.
  - destruct H as (c & s & _ & _ & _ & _ & H). pose proof (stk_of_rw_cells USEGS m o _ H) as S. exact S.
  - destruct H as (s & _ & H1 & ob & Hl & H2).
    pose proof (stk_of_rw_cells USEGS m o _ H1) as S1. pose proof (stk_of_u8arr m (o + 1) ob H2) as S2.
    rewrite Hl in S2. cbn [cells_size csize Nat.add] in S1.
    eapply stk_merge; [exact S1 | replace (o + Z.of_nat 1)%Z with (o + 1)%Z by lia; replace (o + 24)%Z with (o + 1 + Z.of_nat 23)%Z by lia; exact S2 | ].
    pose proof (rw_cells_bound USEGS m o _ H1) as B. cbn [cells_size csize Nat.add] in B. lia.
Qed.

Lemma str_obj_agree : forall m m' o b, str_obj m o b -> agree_on m m' o 24 -> str_obj m' o b.
Proof.
  intros m m' o [[p n]|] H AG; cbn [str_obj] in *.
  - destruct H as (c & s & E & B1 & B2 & B3 & H). exists c, s. split; [exact E|]. split; [exact B1|]. split; [exact B2|].
    split; [exact B3|]. eapply rw_cells_agree; [exact H | exact AG].
  - destruct H as (s & Hs & H1 & ob & Hl & H2). exists s. split; [exact Hs|]. split.
    + eapply rw_cells_agree; [exact H1 | eapply agree_on_sub; [exact AG | lia | cbn; lia]].
    + exists ob. split; [exact Hl|]. eapply u8arr_agree; [exact H2 | eapply agree_on_sub; [exact AG | lia | rewrite Hl; cbn; lia]].
Qed.

Lemma agree_write_other : forall m a bs o k, (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z -> (0 <= o)%Z -> (o + k <= 2^64)%Z ->
  (a + Z.of_nat (length bs) <= o \/ o + k <= a)%Z -> agree_on m (write_to_mem m (wa a) bs) o k.
Proof.
  intros m a bs o k Ha Hl Ho Hk Hd i Hi. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a (o + i)); destruct (Z.ltb_spec0 (o + i) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. lia.
Qed.

Lemma str_obj_write : forall m o b a bs, str_obj m o b -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (a + Z.of_nat (length bs) <= o \/ o + 24 <= a)%Z -> str_obj (write_to_mem m (wa a) bs) o b.
Proof.
  intros m o b a bs H Ha Hl Hd. pose proof (str_obj_stk m o b H) as (S1 & S2 & _).
  eapply str_obj_agree; [exact H|]. apply agree_write_other; lia.
Qed.

Lemma rw_cells_at : forall m A A' cs, rw_cells USEGS m A cs -> A = A' -> rw_cells USEGS m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Lemma stk_at : forall m lo hi lo' hi', stk USEGS m lo hi -> lo = lo' -> hi = hi' -> stk USEGS m lo' hi'.
Proof. intros m lo hi lo' hi' H <- <-. exact H. Qed.
Lemma stk_merge' : forall m lo mid mid' hi, stk USEGS m lo mid -> stk USEGS m mid' hi -> mid = mid' -> (lo <= mid <= hi)%Z -> stk USEGS m lo hi.
Proof. intros m lo mid mid' hi A B <- H. eapply stk_merge; eassumption. Qed.
Lemma str_obj_at : forall m o o' b, str_obj m o b -> o = o' -> str_obj m o' b.
Proof. intros m o o' b H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma ro_munch : forall W m m' (RO : list (Z * Z)),
  Forall (fun r => pristine m (fst r) (snd r)) RO -> munch W m m' ->
  (forall r x, In r RO -> (fst r <= x < snd r)%Z -> outside W x) ->
  Forall (fun r => pristine m' (fst r) (snd r)) RO.
Proof.
  intros W m m' RO H MU HO. induction H as [|r RO Hr H IH]; constructor.
  - destruct Hr as (A & B & C). split; [exact A|]. split; [exact B|].
    intros i Hi. rewrite MU; [apply C, Hi|]. rewrite wa_unsigned by lia. apply (HO r); [left; reflexivity | exact Hi].
  - apply IH. intros r' x Hin Hx. apply (HO r'); [right; exact Hin | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma acc_same : forall (B0 B B' LB : list (Z * Z)),
  (forall y, In y B <-> In y B0 \/ In y LB) -> blocks_same B B' -> (forall y, In y B' <-> In y B0 \/ In y LB).
Proof. intros B0 B B' LB H S y. rewrite (S y). apply H. Qed.

Lemma acc_add : forall (B0 B B' LB : list (Z * Z)) x,
  (forall y, In y B <-> In y B0 \/ In y LB) -> (forall y, In y LB -> ~ In y B0) -> List.NoDup LB ->
  blocks_add B B' x -> ~ In x B ->
  (forall y, In y B' <-> In y B0 \/ In y (x :: LB)) /\ (forall y, In y (x :: LB) -> ~ In y B0) /\ List.NoDup (x :: LB).
Proof.
  intros B0 B B' LB x H F N A X. split; [|split].
  - intros y. rewrite (A y), (H y). cbn. split.
    + intros [<-|[B1|B1]]; [right; left; reflexivity | left; exact B1 | right; right; exact B1].
    + intros [B1|[<-|B1]]; [right; left; exact B1 | left; reflexivity | right; right; exact B1].
  - intros y [<-|Hy]; [intros Hin; apply X, H; left; exact Hin | apply F, Hy].
  - constructor; [intros Hin; apply X, H; right; exact Hin | exact N].
Qed.

Lemma acc_del : forall (B0 B B' LB : list (Z * Z)) x,
  (forall y, In y B <-> In y B0 \/ In y (x :: LB)) -> (forall y, In y (x :: LB) -> ~ In y B0) -> List.NoDup (x :: LB) ->
  blocks_del B B' x ->
  (forall y, In y B' <-> In y B0 \/ In y LB) /\ (forall y, In y LB -> ~ In y B0) /\ List.NoDup LB.
Proof.
  intros B0 B B' LB x H F N D. destruct (proj1 (List.NoDup_cons_iff x LB) N) as [NX N']. split; [|split].
  - intros y. rewrite (D y), (H y). cbn. split.
    + intros [[A1|[A1|A1]] B1]; [left; exact A1 | exfalso; apply B1; symmetry; exact A1 | right; exact A1].
    + intros [A1|A1]; split; [left; exact A1 | intros ->; exact (F x (or_introl eq_refl) A1) | right; right; exact A1 | intros ->; exact (NX A1)].
  - intros y Hy. apply F. right. exact Hy.
  - exact N'.
Qed.

Section FZ.
  Variable cfg : SpuriousCfg.
  Variable HI : heap_iface.
  Variables (GP TP : word) (HTOP : Z) (STATIC : list ivl).
  Local Notation Heap := (hi_Heap HI).
  Local Notation blocks := (hi_blocks HI).
  Local Notation owned := (hi_owned HI).

  (* [comment removed for export] *)
  Record fz_ctx : Type := FZC {
    z_regs : bvmap 5 word; z_m : word -> option byte; z_hs : hi_HS HI; z_K : TSet; z_md : Model }.

  Definition z_sp (c : fz_ctx) : Z := sp_of (z_regs c).
  Definition z_ret (c : fz_ctx) : word := getr (z_regs c) 1.

  (* [comment removed for export] *)
  Definition fz_cont (c : fz_ctx) : Prop :=
    forall (fx' : FPState) regs' m' md' hs',
      Heap hs' m' md' -> md_ok md' -> vm_only (z_md c) md' -> (U md' <= U (z_md c) + FUZZ_CHARGE)%Z ->
      (forall a, ~ outside U_KEEP a -> m' (wa a) = z_m c (wa a)) ->
      getr regs' 10 = Z_to_bv 64 0 -> callee_saved (z_regs c) regs' -> frm0 (@fp_csr fx') ->
      blocks_same (blocks (z_hs c)) (blocks hs') ->
      munch (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP); (z_sp c - FUZZ_NEED, z_sp c)]%Z) (z_m c) m' ->
      (forall p n, In (p, n) (blocks (z_hs c)) -> forall a, (p <= a < p + n)%Z -> m' (wa a) = z_m c (wa a)) ->
      stk USEGS m' (z_sp c - FUZZ_NEED) (z_sp c) ->
      realizes_cfg USEGS cfg (mkCfg (@mkst fx' regs' (z_ret c) m' (seg_rom USEGS)) md') (z_K c).

  (* [comment removed for export] *)
  Definition fz_acc (c : fz_ctx) (hs : hi_HS HI) (m : word -> option byte) (md : Model) (LB : list (Z * Z)) : Prop :=
    Heap hs m md /\ md_ok md /\
    (forall y, In y (blocks hs) <-> In y (blocks (z_hs c)) \/ In y LB) /\
    (forall y, In y LB -> ~ In y (blocks (z_hs c))) /\ List.NoDup LB /\
    munch (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP); (z_sp c - FUZZ_NEED, z_sp c)]%Z) (z_m c) m /\
    (forall q k, In (q, k) (blocks (z_hs c)) -> agree_on (z_m c) m q k) /\
    Forall (fun r => pristine m (fst r) (snd r)) U_RO /\ vm_only (z_md c) md /\ keep_eq U_KEEP (z_m c) m.

  (* [comment removed for export] *)
  Definition ctx_ok (c : fz_ctx) : Prop :=
    (z_sp c mod 16 = 0)%Z /\ (HTOP <= z_sp c - FUZZ_NEED)%Z /\
    getr (z_regs c) 3 = GP /\ getr (z_regs c) 4 = TP /\ (bv_unsigned (z_ret c) mod 2 = 0)%Z /\
    Forall (fun r => forall x, (fst r <= x < snd r)%Z -> outside STATIC x \/ ~ outside U_KEEP x) U_RO /\ (z_sp c <= 2^47)%Z /\
    (U (z_md c) + FUZZ_CHARGE <= UBOUND)%Z.

  (* [comment removed for export] *)
  Definition regs_ok (c : fz_ctx) (regs : bvmap 5 word) : Prop :=
    (sp_of regs + 128 = z_sp c)%Z /\ getr regs 3 = GP /\ getr regs 4 = TP /\
    getr regs 18 = getr (z_regs c) 18 /\ getr regs 19 = getr (z_regs c) 19 /\ getr regs 20 = getr (z_regs c) 20 /\
    getr regs 21 = getr (z_regs c) 21 /\ getr regs 22 = getr (z_regs c) 22 /\ getr regs 23 = getr (z_regs c) 23 /\
    getr regs 24 = getr (z_regs c) 24 /\ getr regs 25 = getr (z_regs c) 25 /\ getr regs 26 = getr (z_regs c) 26 /\
    getr regs 27 = getr (z_regs c) 27.

  (* [comment removed for export] *)
  Definition pay_ok (c : fz_ctx) (ptr rem : Z) : Prop :=
    (0 <= ptr)%Z /\ (0 <= rem <= 2^26)%Z /\ (ptr + rem < 2^64)%Z /\
    (rem = 0%Z \/ exists q k, In (q, k) (blocks (z_hs c)) /\ (q <= ptr)%Z /\ (ptr + rem <= q + k)%Z).

  #[using="Type"] Lemma pay_ok_step : forall c ptr rem ptr' rem', pay_ok c ptr rem -> (ptr' + rem' = ptr + rem)%Z -> (0 <= rem' <= rem)%Z ->
    pay_ok c ptr' rem'.
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros c ptr rem ptr' rem' (H1 & H2 & H3 & H4) E R. split; [lia|]. split; [lia|]. split; [lia|].
    destruct H4 as [E0|(q & k & Hq & A & B)]; [left; lia|].
    destruct (Z.eq_dec rem' 0) as [E0|E0]; [left; exact E0|]. right. exists q, k. split; [exact Hq|]. lia.
  Qed.

  #[using="Type"] Lemma regs_ok_cs : forall c regs regs', regs_ok c regs -> callee_saved regs regs' -> regs_ok c regs'.
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros c regs regs' (A1 & A3 & A4 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27)
      (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
    unfold regs_ok, sp_of in *. rewrite C2, C3, C4, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27. tauto.
  Qed.

  #[using="Type"] Lemma z_sp_range : forall c, (0 <= z_sp c < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. intros c. unfold z_sp, sp_of. pose proof (bv_unsigned_in_range 64 (getr (z_regs c) 2)) as R. unfold bv_modulus in R. lia. Qed.

  Section WithHOK.
  Hypothesis HOK : U_heap_ok cfg HI GP TP HTOP STATIC.

  #[using="cfg HOK"] Lemma ro_out : forall c (L : list ivl) r x, ctx_ok c -> In r U_RO -> (fst r <= x < snd r)%Z ->
    (forall x, ~ outside L x -> (z_sp c - FUZZ_NEED <= x < z_sp c)%Z) ->
    outside (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP)] ++ L)%Z x \/ ~ outside U_KEEP x.
  Proof. LiaFast.lf_pins (fun (cfg HOK : LiaFast.U) => LiaFast.u0).
    destruct HOK as ((HTOPB & SOK) & _). unfold U_IMG_LO, U_IMG_END in HTOPB.
    intros c L r x (_ & HT & _ & _ & _ & SRO & _) Hr Hx HL.
    rewrite Forall_forall in SRO. destruct (SRO r Hr x Hx) as [D|D]; [|right; exact D]. left.
    assert (Hx' : (0x10000 <= x < 0x99000)%Z) by (destruct Hr as [<-|[<-|[]]]; cbn in Hx |- *; unfold U_FMIN in Hx; lia).
    apply outside_app. split; [exact D|].
    cbn [app outside]. unfold U_IMG_LO, U_IMG_END. split; [lia|]. split; [lia|].
    destruct (outside_dec L x) as [A|A]; [exact A|]. specialize (HL x A). unfold FUZZ_NEED, from_chars_double_need in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cfg HOK"] Lemma fz_acc_frame : forall c hs m md LB m' (W : list ivl),
    ctx_ok c -> fz_acc c hs m md LB -> munch W m m' -> wmono USEGS m m' ->
    (forall x, ~ outside W x -> (z_sp c - FUZZ_NEED <= x < z_sp c)%Z) ->
    fz_acc c hs m' md LB.
  Proof. LiaFast.lf_pins (fun (cfg HOK : LiaFast.U) => LiaFast.u0).
    pose proof HOK as HOK'. destruct HOK' as ((HTOPB & SOK) & _ & _ & FRAME & BOK). unfold U_IMG_LO, U_IMG_END in HTOPB.
    intros c hs m md LB m' W CX (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP) MU WM HW.
    pose proof CX as (Hal & HT & _ & _ & _ & SRO & _).
    pose proof (z_sp_range c) as Rsp. unfold FUZZ_NEED, from_chars_double_need in *.
    destruct (BOK _ _ _ HP) as [B1 O1].
    refine (conj _ (conj MD (conj BL (conj FR (conj ND (conj _ (conj _ (conj _ (conj VM _))))))))).
    - eapply FRAME; [exact HP | exact MU | exact WM |].
      intros x Hx. specialize (HW x Hx). destruct (outside_dec (owned hs) x) as [A|A]; [exact A|].
      specialize (O1 x A). unfold FUZZ_NEED, from_chars_double_need in *. lia.
    - eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
      intros x Hx. destruct (outside_dec W x) as [A|A]; [exact A|]. exfalso. specialize (HW _ A).
      rewrite outside_app in Hx. destruct Hx as [_ Hx]. cbn [outside] in Hx. unfold FUZZ_NEED, from_chars_double_need in *. lia.
    - intros q k Hq. eapply agree_on_trans; [exact (AG0 q k Hq)|].
      destruct (B1 q k (proj2 (BL (q, k)) (or_introl Hq))) as (Hk & Hreg & _). unfold U_IMG_LO, U_IMG_END in Hreg.
      intros i Hi. apply MU. rewrite wa_unsigned by lia.
      destruct (outside_dec W (q + i)) as [A|A]; [exact A|]. specialize (HW _ A). unfold FUZZ_NEED, from_chars_double_need in *. lia.
    - eapply ro_munch; [exact RO | exact MU |]. intros r x Hr Hx.
      destruct (outside_dec W x) as [A|A]; [exact A|]. exfalso. specialize (HW _ A).
      assert (Hx' : (x < 0x99000)%Z) by (destruct Hr as [<-|[<-|[]]]; cbn in Hx |- *; unfold U_FMIN in Hx; lia).
      unfold FUZZ_NEED, from_chars_double_need in *. lia.
    - apply (keep_trans _ _ m); [exact KP|]. apply (keep_munch _ W); [|exact MU]. intros a Ha. unfold U_KEEP in Ha. apply not_outside_4 in Ha.
      split; [lia|]. destruct (outside_dec W a) as [A|A]; [exact A|]. exfalso. specialize (HW _ A). unfold FUZZ_NEED, from_chars_double_need in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cfg HOK"] Lemma fz_acc_cps : forall c hs m md LB hs' m' md' (L : list ivl) LB',
    ctx_ok c -> fz_acc c hs m md LB -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> keep_eq U_KEEP m m' ->
    munch (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP)] ++ L)%Z m m' ->
    (forall x, ~ outside L x -> (z_sp c - FUZZ_NEED <= x < z_sp c)%Z) ->
    (forall q k, In (q, k) (blocks (z_hs c)) -> agree_on m m' q k) ->
    (forall y, In y (blocks hs') <-> In y (blocks (z_hs c)) \/ In y LB') ->
    (forall y, In y LB' -> ~ In y (blocks (z_hs c))) -> List.NoDup LB' ->
    fz_acc c hs' m' md' LB'.
  Proof. LiaFast.lf_pins (fun (cfg HOK : LiaFast.U) => LiaFast.u0).
    intros c hs m md LB hs' m' md' L LB' CX (HP & MD & BL & FR & ND & MU0 & AG0 & RO & VM & KP) HP' MD' VM' KP' MU HL AG BL' FR' ND'.
    refine (conj HP' (conj MD' (conj BL' (conj FR' (conj ND' (conj _ (conj _ (conj _ (conj (vm_only_trans _ _ _ VM VM') (keep_trans _ _ _ _ KP KP')))))))))).
    - eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
      intros x Hx. rewrite outside_app in Hx |- *. destruct Hx as [HS Hx]. split; [exact HS|].
      cbn [app outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|].
      destruct (outside_dec L x) as [A|A]; [exact A|]. specialize (HL _ A). lia.
    - intros q k Hq. eapply agree_on_trans; [exact (AG0 q k Hq) | exact (AG q k Hq)].
    - eapply (ro_munch_keep U_KEEP); [exact RO | exact MU | exact KP' |]. intros r x Hr Hx. eapply ro_out; eassumption.
  Qed.

  #[using="Type"] Lemma acc_ro : forall c hs m md LB, fz_acc c hs m md LB -> pristine m 0x10000 0x22000 /\ pristine m U_FMIN (U_FMIN + 4).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros c hs m md LB (_ & _ & _ & _ & _ & _ & _ & RO & _ & _). unfold U_RO in RO.
    apply Forall_cons_iff in RO. destruct RO as [R1 RO]. apply Forall_cons_iff in RO. destruct RO as [R2 _].
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="cfg HOK"] Lemma fz_acc_crls : forall c hs m md LB hs' m' md' (o f sp s : Z),
    ctx_ok c -> fz_acc c hs m md LB -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> keep_eq U_KEEP m m' ->
    munch (STATIC ++ [(0, U_IMG_LO); (U_IMG_END, HTOP); (o, o + 24); (f, f + 16); (sp - CRLS_NEED, sp)]%Z) m m' ->
    (forall q k, In (q, k) (blocks hs) -> In (q, k) (blocks hs') /\ agree_on m m' q k) ->
    (z_sp c - FUZZ_NEED <= sp - CRLS_NEED)%Z -> (sp <= o)%Z -> (o + 24 <= z_sp c)%Z -> (sp <= f)%Z -> (f + 16 <= z_sp c)%Z ->
    (0 <= s)%Z ->
    str_result HI hs hs' m' o s ->
    exists b, str_obj m' o b /\ fz_acc c hs' m' md' (opt_list b ++ LB).
  Proof. LiaFast.lf_pins (fun (cfg HOK : LiaFast.U) => LiaFast.u0).
    intros c hs m md LB hs' m' md' o f sp s CX ACC HP' MD' VM' KP' MU AG H1 H2 H3 H4 H5 Hs STR.
    pose proof ACC as (HP & MD & BL & FR & ND & _).
    assert (AG0 : forall q k, In (q, k) (blocks (z_hs c)) -> agree_on m m' q k).
    { intros q k Hq. apply (AG q k). apply BL. left. exact Hq. }
    assert (HL : forall x, ~ outside [(o, o + 24); (f, f + 16); (sp - CRLS_NEED, sp)]%Z x -> (z_sp c - FUZZ_NEED <= x < z_sp c)%Z).
    { intros x Hx. cbn [outside] in Hx. unfold CRLS_NEED, SOE_NEED, U_MNEED, FUZZ_NEED, from_chars_double_need in *. lia. }
    unfold str_result in STR. destruct STR as [(Hs22 & BS & OB & ob & Lob & OBA) | (cc & p & buf & Hc1 & Hc2 & Hc3 & BADD & FRESH & OB & BUF & LBUF)].
    - exists None. split; [exists s; split; [lia|]; split; [exact OB | exists ob; split; assumption]|].
      eapply (fz_acc_cps c hs m md LB hs' m' md' _ LB CX ACC HP' MD' VM' KP' MU HL AG0); [ | exact FR | exact ND].
      exact (acc_same _ _ _ _ BL BS).
    - exists (Some (p, cc + 1)%Z). split; [exists cc, s; split; [reflexivity|]; split; [exact Hc1|]; split; [exact Hc2|]; split; [lia | exact OB]|].
      destruct (acc_add _ _ _ _ _ BL FR ND BADD FRESH) as (BL' & FR' & ND').
      eapply (fz_acc_cps c hs m md LB hs' m' md' _ _ CX ACC HP' MD' VM' KP' MU HL AG0); [exact BL' | exact FR' | exact ND'].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pay_blocks : forall c hs m md LB ptr rem, fz_acc c hs m md LB -> pay_ok c ptr rem ->
    (rem = 0%Z \/ exists q k, In (q, k) (blocks hs) /\ (q <= ptr)%Z /\ (ptr + rem <= q + k)%Z).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros c hs m md LB ptr rem (_ & _ & BL & _) (_ & _ & _ & [E|(q & k & Hq & H1 & H2)]); [left; exact E|].
    right. exists q, k. split; [apply BL; left; exact Hq|]. split; assumption.
  Qed.

  #[using="cfg GP TP HOK"] Lemma pay_bytes : forall c hs m md LB ptr rem, fz_acc c hs m md LB -> pay_ok c ptr rem ->
    exists bs, bytes_at USEGS m ptr bs /\ Z.of_nat (length bs) = rem.
  Proof. LiaFast.lf_pins (fun (cfg GP TP HOK : LiaFast.U) => LiaFast.u0).
    destruct HOK as (_ & _ & _ & _ & BOK).
    intros c hs m md LB ptr rem ACC PO. pose proof (pay_blocks c hs m md LB ptr rem ACC PO) as PB.
    destruct PO as (Hp & Hr & Hpr & _). destruct ACC as (HP & _).
    destruct PB as [E|(q & k & Hq & H1 & H2)].
    - subst rem. exists []. split; [apply bytes_at_nil; lia | reflexivity].
    - destruct (BOK _ _ _ HP) as [B1 _]. destruct (B1 q k Hq) as (_ & _ & ST & _).
      destruct (stk_split USEGS m q ptr (q + k) ST ltac:(lia)) as [_ S1].
      destruct (stk_split USEGS m ptr (ptr + rem) (q + k) S1 ltac:(lia)) as [S2 _].
      destruct (stk_bytes USEGS m ptr (ptr + rem) S2 ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb | lia].
  Qed.
  End WithHOK.
End FZ.
Arguments FZC {HI}. Arguments z_regs {HI}. Arguments z_m {HI}. Arguments z_hs {HI}. Arguments z_K {HI}. Arguments z_md {HI}.
Arguments z_sp {HI}. Arguments z_ret {HI}.

Lemma agree_blocks_eq : forall m0 m p n, agree_on m0 m p n -> forall a, (p <= a < p + n)%Z -> m (wa a) = m0 (wa a).
Proof. intros m0 m p n AG a Ha. replace a with (p + (a - p))%Z by lia. apply AG. lia. Qed.

(* [comment removed for export] *)
Ltac fz_transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_write_other m lo hi a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : str_obj m ?o ?b |- _ =>
      first [ apply (str_obj_write m o b a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac fz_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  destruct PO as [E [MUc [WMc PO]]];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      cbv delta [from_chars_double_need from_chars_float_need] in MUc;
      repeat match goal with
      | H : str_obj m ?o ?b |- _ =>
          first [ apply (str_obj_agree m m' o b) in H;
                  [| eapply agree_on_of_munch; [exact MUc | cbn [disjoint_from]; repeat split; try exact I; lia | lia | lia] ]
                | clear H ]
      end;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "fz_call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | fz_post_call segs m ]
  end.

(* [comment removed for export] *)
Ltac xport SOK MU :=
  lazymatch type of MU with
  | munch (?ST ++ [(0, U_IMG_LO); (U_IMG_END, ?HT)] ++ ?L)%Z ?m ?m' =>
  let AGT := (eapply (static_agree ST L U_IMG_LO U_IMG_END HT m m' _ _ SOK MU);
              [cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; lia | lia | unfold U_IMG_LO; lia
              | unfold U_IMG_LO, U_IMG_END; lia | simpl_sizes; lia]) in
  repeat match goal with
  | H : rw_cells USEGS m ?A ?cs |- _ =>
      first [ apply (rw_cells_agree USEGS m m' A cs) in H; [|AGT] | clear H ]
  | H : u8arr USEGS m ?A ?bs |- _ =>
      first [ apply (u8arr_agree USEGS m m' A bs) in H; [|AGT] | clear H ]
  | H : stk USEGS m ?lo ?hi |- _ =>
      first [ apply (stk_agree USEGS m m' lo hi) in H; [|AGT] | clear H ]
  | H : str_obj m ?o ?b |- _ =>
      first [ apply (str_obj_agree m m' o b) in H; [|AGT] | clear H ]
  end
  end.
