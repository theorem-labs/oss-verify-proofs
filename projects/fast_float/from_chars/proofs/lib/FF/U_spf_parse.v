(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.

Module U_spf_A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memset.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  Hypothesis C_28114e : K_28114e c.
  Hypothesis C_272dc : K_272dc c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_float_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN; exact PR2|]; split; [exact MU | exact WM].

  (* [comment removed for export] *)
  #[using="PRE C_28114e C_272dc"] Lemma uspf_A :
    evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Zw 0x28fe8) fc None mI (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_28114e C_272dc : LiaFast.U) => LiaFast.u0).
    unfold K_28114e in C_28114e. unfold K_272dc in C_272dc.
    pre_facts.
    pose proof (pre_ST c PRE) as ST. unfold slow_path_float_need in ST.
    pose proof (pre_TXT c PRE) as TXT. pose proof (pre_VAL c PRE) as VAL.
    pose proof (pre_PR1 c PRE) as PR1. pose proof (pre_PR2 c PRE) as PR2. unfold U_FMIN in PR2.
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    pose proof (munch_refl W mI) as MU. cbv beta delta [slow_path_float_W slow_path_float_need] in MU.
    pose proof (wmono_refl USEGS mI) as WM.
    carve_frame 704%nat ST.
    do 14 step.   (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 600 ?j :: _) => set (junk0 := j) in FR; clearbody junk0 end.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z.land (bv_unsigned a4) 255) with DP
      by (change 255%Z with (2^8 - 1)%Z; rewrite zb_land_mask by lia; reflexivity).
    rewrite (pre_A5 c PRE).
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    if_cases Hnull; [| cond_cleanup Hnull; exfalso; lia]. clear Hnull.
    txt_rd TXT 0%Z RD. rewrite wa_P0 in RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) 0%Z. pose proof (tx_range bs 0) as R0.
    assert (UPINV : upinv c junk0 m) by (mk_upinv TXT FR ST VAL PR1 PR2 MU WM).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SIGN : forall x10,
      evt USEGS POST
        (MS (mkR ra (Zw SP) gp tp t0 t1 t2 s0 s1 x10 (Zw DP) (Zw (tx bs 0)) a3 a4 (Zw 0) a6 a7
                 a0 a1 s4 s5 s6 a2 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Zw 0x29098) fc None m (seg_rom USEGS))).
    { intros x10.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
      step. (* [comment removed for export] *)
      if_cases Hend.
      - cond_cleanup Hend.
        (* [comment removed for export] *)
        step. step. step. step. (* [comment removed for export] *)
        step. step. step. (* [comment removed for export] *)
        call_memset27 FR.
        do 5 step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_true.
        to_frameA FR.
        goto (eapply C_28114e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
      - cond_cleanup Hend.
        txt_rd TXT 1%Z RD.
        step. (* [comment removed for export] *)
        clear RD. fold_tx (r_bs c) 1%Z. pose proof (tx_range bs 1) as R1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hdig.
        + clear Hdig.
          step. (* [comment removed for export] *)
          goto (eapply C_272dc with (k3 := 1%Z)); [exact UPINV | lia | lia | intros; reflexivity].
        + clear Hdig.
          step. (* [comment removed for export] *)
          if_cases Hdp.
          * clear Hdp.
            step. (* [comment removed for export] *)
            goto (eapply C_272dc with (k3 := 1%Z)); [exact UPINV | lia | lia | intros; reflexivity].
          * clear Hdp.
            (* [comment removed for export] *)
            step. step. step. step. (* [comment removed for export] *)
            step. step. step. (* [comment removed for export] *)
            call_memset27 FR.
            do 5 step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_true.
            to_frameA FR.
            goto (eapply C_28114e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM. }
    step. (* [comment removed for export] *)
    if_cases Hminus; [apply SIGN|].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hplus.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_272dc with (k3 := 0%Z)); [exact UPINV | lia | lia | intros; reflexivity].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H43.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply C_272dc with (k3 := 0%Z)); [exact UPINV | lia | lia | intros; reflexivity].
      + apply SIGN.
  Qed.
End BLK.
End U_spf_A.


Module U_spf_B.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  Hypothesis C_27658 : K_27658 c.

  #[local] Ltac fin k3v kIv PINV DG :=
    goto (eapply C_27658 with (k3 := k3v) (kI := kIv)); [exact PINV | lia | lia | lia | exact DG].

  (* [comment removed for export] *)
  #[using="PRE C_27658"] Lemma uspf_B_loop : forall (n : nat) (k : Z) junk m
      (x1 x5' x6 x7 x8 x9 x10 x20 x21 x22 x24 x25 x26 x27 x29 x30 x31 : word) (k3 : Z),
      (L + 1 - k <= Z.of_nat n)%Z ->
      upinv c junk m -> (0 <= k3)%Z -> (k3 <= 1)%Z -> (k3 <= k <= L)%Z -> digs bs k3 k ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw 9) x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw 2) (Zw 10) (Zw (P + k)) (Zw (P + k))
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x5' x29 x30 x31)
            F (Zw 0x293a0) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_27658 : LiaFast.U) => LiaFast.u0).
    unfold K_27658 in C_27658.
    induction n as [|n IH]; intros k junk m x1 x5' x6 x7 x8 x9 x10 x20 x21 x22 x24 x25 x26 x27 x29 x30 x31 k3
      Hn PINV K30 K31 HK DG.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore.
      txt_rd TXT k RD. pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      clear RD. fold_tx (r_bs c) k.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hd.
      + cond_cleanup Hd. clear Hd. fin k3 k PINV DG.
      + cond_cleanup Hd. pose proof (dig_yes _ Rk Hd) as D. clear Hd.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
        goto (eapply (IH (k + 1)%Z) with (k3 := k3)); [lia | exact PINV | lia | lia | lia | apply digs_snoc; assumption].
    - cond_cleanup Hmore.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin k3 k PINV DG.
  Qed.

  #[using="PRE C_27658"] Lemma uspf_B : K_272dc c.
  Proof. LiaFast.lf_pins (fun (PRE C_27658 : LiaFast.U) => LiaFast.u0).
    unfold K_27658 in C_27658.
    unfold K_272dc. intros junk m x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3
      PINV K3L K31 X14.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    pose proof (digs_nil bs k3) as DG0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend.
      step. (* [comment removed for export] *)
      fin k3 k3 PINV DG0. }
    cond_cleanup Hend. rewrite (X14 ltac:(lia)).
    pose proof (tx_range bs k3) as R0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd0.
    { cond_cleanup Hd0. clear Hd0. fin k3 k3 PINV DG0. }
    cond_cleanup Hd0. pose proof (dig_yes _ R0 Hd0) as D0. clear Hd0.
    pose proof (digs_snoc _ _ _ DG0 D0) as DG1.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov1; [ | cond_cleanup Hov1; exfalso; lia]. clear Hov1.
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin k3 (k3 + 1)%Z PINV DG1. }
    cond_cleanup He1.
    txt_rd TXT (k3 + 1)%Z RD. pose proof (tx_range bs (k3 + 1)) as R1.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 1)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { cond_cleanup Hd1. clear Hd1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin k3 (k3 + 1)%Z PINV DG1. }
    cond_cleanup Hd1. pose proof (dig_yes _ R1 Hd1) as D1. clear Hd1.
    pose proof (digs_snoc _ _ _ DG1 D1) as DG2. replace (k3 + 1 + 1)%Z with (k3 + 2)%Z in DG2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov2; [ | cond_cleanup Hov2; exfalso; lia]. clear Hov2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2. fin k3 (k3 + 2)%Z PINV DG2. }
    cond_cleanup He2.
    txt_rd TXT (k3 + 2)%Z RD. pose proof (tx_range bs (k3 + 2)) as R2.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 2)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd2.
    { cond_cleanup Hd2. clear Hd2. fin k3 (k3 + 2)%Z PINV DG2. }
    cond_cleanup Hd2. pose proof (dig_yes _ R2 Hd2) as D2. clear Hd2.
    pose proof (digs_snoc _ _ _ DG2 D2) as DG3. replace (k3 + 2 + 1)%Z with (k3 + 3)%Z in DG3 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov3; [ | cond_cleanup Hov3; exfalso; lia]. clear Hov3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3. fin k3 (k3 + 3)%Z PINV DG3. }
    cond_cleanup He3.
    txt_rd TXT (k3 + 3)%Z RD. pose proof (tx_range bs (k3 + 3)) as R3.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 3)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd3.
    { cond_cleanup Hd3. clear Hd3. fin k3 (k3 + 3)%Z PINV DG3. }
    cond_cleanup Hd3. pose proof (dig_yes _ R3 Hd3) as D3. clear Hd3.
    pose proof (digs_snoc _ _ _ DG3 D3) as DG4. replace (k3 + 3 + 1)%Z with (k3 + 4)%Z in DG4 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov4; [ | cond_cleanup Hov4; exfalso; lia]. clear Hov4.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4. fin k3 (k3 + 4)%Z PINV DG4. }
    cond_cleanup He4.
    txt_rd TXT (k3 + 4)%Z RD. pose proof (tx_range bs (k3 + 4)) as R4.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 4)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd4.
    { cond_cleanup Hd4. clear Hd4. fin k3 (k3 + 4)%Z PINV DG4. }
    cond_cleanup Hd4. pose proof (dig_yes _ R4 Hd4) as D4. clear Hd4.
    pose proof (digs_snoc _ _ _ DG4 D4) as DG5. replace (k3 + 4 + 1)%Z with (k3 + 5)%Z in DG5 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov5; [ | cond_cleanup Hov5; exfalso; lia]. clear Hov5.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (uspf_B_loop (S (Z.to_nat (L - (k3 + 5)))) (k3 + 5)%Z) with (k3 := k3));
      [lia | exact PINV | lia | lia | lia | exact DG5].
  Qed.
End BLK.
End U_spf_B.


Module U_spf_C.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  (* [comment removed for export] *)
  #[local] Ltac kill_chk H :=
    exfalso; cond_cleanup H; unsign_chk H;
    repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
    Z.div_mod_to_equations; lia.

  Hypothesis C_277ac : K_277ac c.
  Hypothesis C_28114e : K_28114e c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_float_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN; exact PR2|]; split; [exact MU | exact WM].

  #[using="Type"] Lemma nz_of_mod : forall x M : Z, (x mod M <> 0)%Z -> x <> 0%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. intros x M H E0. apply H. rewrite E0. apply Zmod_0_l. Qed.

  Section C.

  (* [comment removed for export] *)
  #[using="PRE C_28114e"] Lemma UC_err6 : forall junk m (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      upinv c junk m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) x12 x13 x14 x15 x16 x17
                 x18 a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x29958) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    unfold K_28114e in C_28114e.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. step. step. step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    call_memset27 FR.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    to_frameA FR.
    goto (eapply C_28114e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_27984 : forall junk m (x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kp : Z),
      upinv c junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kp <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kp ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kp)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x29938) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kp PINV K3I K31 KIL DPk KP DGI DGF.
    unfold K_277ac in C_277ac.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (P + kI + 1)%Z), ?(unsigned_lit (P + kp)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hchk.
    2:{ kill_chk Hchk. }
    clear Hchk.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - cond_cleanup Hnz.
      goto (eapply C_277ac with (k3 := k3) (kI := kI) (fp := (P + kI + 1)%Z) (fL := (kp - (kI + 1))%Z) (kp := kp));
        [exact PINV | lia | lia | lia | lia | exact DGI | | ].
      + right. split; [reflexivity|]. split; [lia|]. split; [exact DPk|]. split; [lia|].
        replace (kI + 1 + (kp - (kI + 1)))%Z with kp by lia. exact DGF.
      + Z.div_mod_to_equations. lia.
    - cond_cleanup Hnz.
      goto (eapply UC_err6). exact PINV.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_loop1 : forall (n : nat) junk m (x1 x7 x8 x10 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      upinv c junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc < L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (-1)) (Zw 10) x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw 9)
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2990c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x7 x8 x10 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kc Hn PINV K3I K31 KIL DPk KC DGI DGF.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    txt_rd TXT kc RD. pose proof (tx_range bs kc) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd.
      goto (eapply UC_27984 with (kp := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
    - cond_cleanup Hd. pose proof (dig_yes_m _ Rk Hd) as D. clear Hd.
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia]. clear Hov.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (kc := (kc + 1)%Z));
          [lia | exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | apply digs_snoc; assumption].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        goto (eapply UC_27984 with (kp := (kc + 1)%Z));
          [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | apply digs_snoc; assumption].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_27944 : forall j0 j1 m (x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x298f8) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    intros j0 j1 m x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kc PINV K3I K31 KIL DPk KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    to_frameA FR.
    assert (PINVA : upinv c junk_m m) by (mk_upinv TXT FR ST VAL PR1 PR2 MU WM).
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      goto (eapply UC_27984 with (kp := kc)); [exact PINVA | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
    - cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (UC_loop1 (S (Z.to_nat (L - kc))) junk_m m) with (kc := kc));
        [lia | exact PINVA | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
  Qed.

  #[using="Type"] Lemma digs_snoc4 : forall lo k, digs bs lo k ->
    isdig (tx bs k) -> isdig (tx bs (k + 1)) -> isdig (tx bs (k + 2)) -> isdig (tx bs (k + 3)) -> digs bs lo (k + 4).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros lo k H D0 D1 D2 D3.
    replace (k + 4)%Z with (k + 3 + 1)%Z by lia. apply digs_snoc; [|exact D3].
    replace (k + 3)%Z with (k + 2 + 1)%Z by lia. apply digs_snoc; [|exact D2].
    replace (k + 2)%Z with (k + 1 + 1)%Z by lia. apply digs_snoc; [|exact D1].
    apply digs_snoc; [exact H|exact D0].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_4test : forall j0 j1 m (x1 x5 x6 x7 x8 x10 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc Vv : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc)%Z -> (kc + 4 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      (0 <= Vv < 2^64)%Z -> (Vv mod 2^32 = v4 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3)))%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 x23 (Zw Vv) x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2987c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    intros j0 j1 m x1 x5 x6 x7 x8 x10 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 k3 kI kc Vv PINV K3I K31 KIL DPk KC1 KC2 DGI DGF VR VM.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4.
      goto (eapply UC_27944 with (kc := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
    - rewrite ?(unsigned_lit Vv) in H4 by lia.
      destruct (swar4_dig Vv _ _ _ _ R0 R1 R2 R3 VR VM H4) as (D0 & D1 & D2 & D3). clear H4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
      do 16 step. (* [comment removed for export] *)
      goto (eapply UC_27944 with (kc := (kc + 4)%Z)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | ].
      apply digs_snoc4; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_27898 : forall j0 j1 m (x1 x6 x7 x8 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x2984c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    intros j0 j1 m x1 x6 x7 x8 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kc PINV K3I K31 KIL DPk KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4.
      goto (eapply UC_27944 with (kc := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
    - cond_cleanup H4. rewrite signed_lit in H4 by lia.
      pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
      pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
      txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 1)%Z.
      txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 0)%Z. rewrite (Z.add_0_r kc).
      txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 2)%Z.
      txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 3)%Z.
      do 6 step. (* [comment removed for export] *)
      rewrite (ortree4_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))) by (apply tx_range).
      pose proof (v4_range _ _ _ _ R0 R1 R2 R3) as VR.
      goto (eapply UC_4test with (kc := kc) (Vv := v4 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))));
        [exact PINV | lia | lia | lia | exact DPk | lia | lia | exact DGI | exact DGF | lia | apply Z.mod_small; lia].
  Qed.

  #[using="Type"] Lemma v8_facts : forall z0 z1 z2 z3 z4 z5 z6 z7,
    (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
     0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
     0 <= v8 z0 z1 z2 z3 z4 z5 z6 z7 < 2^64 /\ v8 z0 z1 z2 z3 z4 z5 z6 z7 mod 2^32 = v4 z0 z1 z2 z3)%Z.
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros. pose proof (v4_range z0 z1 z2 z3). pose proof (v4_range z4 z5 z6 z7). unfold v8. split; [lia|].
    rewrite (Z.mul_comm (2^32)). rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_277ac C_28114e"] Lemma UC_loop8 : forall (n : nat) j0 j1 m (x1 x8 x10 x20 x21 x22 x24 x25 x26 x27 x30 x31 : word) (k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc)%Z -> (kc + 8 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) (Zw 8) (Zw 14974415777481871312) x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3
                 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 (Zw 7) x24 x25 x26 x27 (Zw 9259542123273814144) (Zw 5063812098665367110) x30 x31)
            F (Zw 0x29690) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros j0 j1 m x1 x8 x10 x20 x21 x22 x24 x25 x26 x27 x30 x31 k3 kI kc
      Hn PINV K3I K31 KIL DPk KC1 KC8 DGI DGF.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_range bs (kc + 4)) as R4. pose proof (tx_range bs (kc + 5)) as R5.
    pose proof (tx_range bs (kc + 6)) as R6. pose proof (tx_range bs (kc + 7)) as R7.
    txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 1)%Z.
    txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 2)%Z.
    txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 3)%Z.
    txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 0)%Z. rewrite (Z.add_0_r kc).
    do 4 step. (* [comment removed for export] *)
    txt_rd TXT (kc + 4)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 4)%Z.
    txt_rd TXT (kc + 5)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 5)%Z.
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 6)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 6)%Z.
    txt_rd TXT (kc + 7)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 7)%Z.
    do 9 step. (* [comment removed for export] *)
    rewrite (ortree8_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))) by (apply tx_range).
    destruct (v8_facts _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7) as [VR VM].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsw.
    - clear Hsw.
      goto (eapply UC_4test with (kc := kc) (Vv := v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))));
        [exact PINV | lia | lia | lia | exact DPk | lia | lia | exact DGI | exact DGF | exact VR | exact VM].
    - rewrite ?(unsigned_lit (v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7)))) in Hsw by lia.
      destruct (swar8_dig _ _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7 eq_refl Hsw) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
      clear Hsw.
      assert (DGF' : digs bs (kI + 1) (kc + 8)).
      { replace (kc + 8)%Z with (kc + 4 + 4)%Z by lia.
        apply digs_snoc4; [apply digs_snoc4; assumption | exact D4 | | |].
        - replace (kc + 4 + 1)%Z with (kc + 5)%Z by lia. exact D5.
        - replace (kc + 4 + 2)%Z with (kc + 6)%Z by lia. exact D6.
        - replace (kc + 4 + 3)%Z with (kc + 7)%Z by lia. exact D7. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
      do 14 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore. rewrite signed_lit in Hmore by lia.
        goto (eapply (IH j0 j1 m) with (kc := (kc + 8)%Z));
          [lia | exact PINV | lia | lia | lia | exact DPk | lia | lia | exact DGI | exact DGF'].
      + cond_cleanup Hmore. rewrite signed_lit in Hmore by lia.
        step. (* [comment removed for export] *)
        goto (eapply UC_27898 with (kc := (kc + 8)%Z));
          [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF'].
  Qed.

  End C.

  #[using="PRE C_277ac C_28114e"] Lemma uspf_C : K_27658 c.
  Proof. LiaFast.lf_pins (fun (PRE C_277ac C_28114e : LiaFast.U) => LiaFast.u0).
    unfold K_277ac in C_277ac.
    unfold K_27658. intros junk m x1 x5 x6 x7 x8 x9 x10 x14 x15 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI
      PINV K3I KIL K31 DG.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI)%Z), (unsigned_lit (P + k3)%Z) by lia.
    (* [comment removed for export] *)
    assert (NODP : forall x15,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (P + kI - (P + k3))) x15 (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x29748) fc None m (seg_rom USEGS))).
    { intros y15.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz.
        goto (eapply UC_err6). exact PINV.
      - cond_cleanup Hz.
        goto (eapply C_277ac with (k3 := k3) (kI := kI) (fp := 0%Z) (fL := 0%Z) (kp := kI));
          [exact PINV | lia | lia | lia | lia | exact DG | left; lia | ].
        Z.div_mod_to_equations. lia. }
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend. apply NODP. }
    cond_cleanup Hend.
    txt_rd TXT kI RD. pose proof (tx_range bs kI) as RkI.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kI.
    step. (* [comment removed for export] *)
    if_cases Hdp.
    { cond_cleanup Hdp. apply NODP. }
    cond_cleanup Hdp.
    assert (DPk : tx bs kI = DP).
    { pose proof (Z.mod_pos_bound (bv_unsigned a4) 256 ltac:(lia)). rewrite ?Z.mod_small in Hdp by lia. exact Hdp. }
    clear Hdp.
    pose proof (digs_nil bs (kI + 1)) as DGF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
    step. (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?a :: C8 _ :: CB 584 ?b :: _) =>
      set (j0 := a) in FR; set (j1 := b) in FR; clearbody j0 j1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (PINVB : upinvB c j0 j1 mm) by (mk_upinv TXT FR ST VAL PR1 PR2 MU WM) end.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI + 1)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H8.
    - cond_cleanup H8. rewrite signed_lit in H8 by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply UC_27898 with (kc := (kI + 1)%Z));
        [exact PINVB | lia | lia | lia | exact DPk | lia | exact DG | exact DGF].
    - cond_cleanup H8. rewrite signed_lit in H8 by lia.
      do 7 step. (* [comment removed for export] *)
      step. step. step. (* [comment removed for export] *)
      do 9 step. (* [comment removed for export] *)
      step. step. (* [comment removed for export] *)
      goto (eapply (UC_loop8 (S (Z.to_nat (L - (kI + 1)))) j0 j1) with (kc := (kI + 1)%Z));
        [lia | exact PINVB | lia | lia | lia | exact DPk | lia | lia | exact DG | exact DGF].
  Qed.
End BLK.
End U_spf_C.


Module U_spf_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  (* [comment removed for export] *)
  #[local] Ltac kill_chk H :=
    exfalso; cond_cleanup H; unsign_chk H;
    repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
    Z.div_mod_to_equations; lia.

  Hypothesis C_27cf8 : K_27cf8 c.
  Hypothesis C_28114e : K_28114e c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_float_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN; exact PR2|]; split; [exact MU | exact WM].

  (* [comment removed for export] *)
  Definition udctx (k3 kI fp fL kp : Z) junk m : Prop :=
    upinv c junk m /\ (0 <= k3 <= kI)%Z /\ (k3 <= 1)%Z /\ (0 <= fL)%Z /\
    (kI <= kp <= L)%Z /\ digs bs k3 kI /\ uspans c k3 kI fp fL kp /\ (0 < (kI - k3) + fL)%Z.

  #[local] Ltac open_udctx DX :=
    destruct DX as (PINV & K3I & K31 & FL0 & KP & DGI & SPANS & DC);
    pre_facts; pose proof PINV as PINV'; open_upinv PINV'.

  Section D.
  Variables x10 x24 x25 x26 x27 : word.

  (* [comment removed for export] *)
  #[local] Notation UDST pc x1 x6 x7 x8 x9 x13 x20 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m :=
    (MS (mkR x1 (Zw SP) gp tp (Zw ((kI - k3) + fL)) x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) x13
             (Zw (kI - k3)) (Zw fp) (Zw (P + kI)) (Zw fL) (Zw (P + k3)) a1 x20
             x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom USEGS)) (only parsing).

  #[local] Ltac fin_cf8 PINV DGI SPANS kpv kqv xnv :=
    goto (eapply C_27cf8 with (kp := kpv) (kq := kqv) (xn := xnv));
    [exact PINV | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].

  (* [comment removed for export] *)
  #[using="PRE C_27cf8"] Lemma UD_27cdc : forall junk m (x1 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn ngx,
      udctx k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x29c90 x1 (Zw ngx) x7 x8 (Zw (P + kq)) (Zw xn) (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp kq xn ngx DX KQ XN NGX. open_udctx DX.
    unfold K_27cf8 in C_27cf8.
    assert (FLK : (kI + fL <= kp)%Z) by (destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; lia).
    step. (* [comment removed for export] *)
    if_cases Hng.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hchk; [kill_chk Hchk|]. clear Hchk.
      step. (* [comment removed for export] *)
      fin_cf8 PINV DGI SPANS kp kq xn.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hchk; [kill_chk Hchk|]. clear Hchk.
      step. (* [comment removed for export] *)
      fin_cf8 PINV DGI SPANS kp kq (- xn)%Z.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8"] Lemma UD_loopx : forall (n : nat) junk m (x1 x8 x9 x22 : word) k3 kI fp fL kp kq xn ngx,
      (L - kq <= Z.of_nat n)%Z ->
      udctx k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x299cc x1 (Zw ngx) (Zw 9) x8 x9 (Zw xn) (Zw (- fL)) (Zw (P + kq)) x22
                           (Zw 10) (Zw 268435455) (Zw 2) (Zw (P + kq)) k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x8 x9 x22 k3 kI fp fL kp kq xn ngx Hn DX KQ XN NGX.
    { exfalso. lia. }
    pose proof DX as DX'. open_udctx DX'.
    txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd.
      step. (* [comment removed for export] *)
      goto (eapply UD_27cdc with (kq := kq) (xn := xn) (ngx := ngx)); [exact DX | lia | lia | lia].
    - clear Hd.
      (* [comment removed for export] *)
      assert (TAIL : forall xn' (x8' x22' : word), (0 <= xn' < 2^32)%Z ->
        evt USEGS POST (UDST 0x299f4 x1 (Zw ngx) (Zw 9) x8' (Zw (Z.land (bv_unsigned (Zw (tx bs kq + -48))) 255)) (Zw xn') (Zw (- fL)) (Zw (P + kq)) x22'
                           (Zw 10) (Zw 268435455) (Zw 2) (Zw (P + kq)) k3 kI fp fL kp m)).
      { intros xn' x8' x22' XN'.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov; [cond_cleanup Hov; exfalso; lia|]. clear Hov.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hmore.
        - cond_cleanup Hmore.
          goto (eapply (IH junk m) with (kq := (kq + 1)%Z) (xn := xn') (ngx := ngx)); [lia | exact DX | lia | lia | lia].
        - cond_cleanup Hmore.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          goto (eapply UD_27cdc with (kq := (kq + 1)%Z) (xn := xn') (ngx := ngx)); [exact DX | lia | lia | lia]. }
      step. (* [comment removed for export] *)
      if_cases Hcl.
      + clear Hcl. apply TAIL. lia.
      + cond_cleanup Hcl. rewrite ?signed_lit in Hcl by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit xn) by lia.
        step. (* [comment removed for export] *)
        if_cases Hchk.
        { exfalso. cond_cleanup Hchk. rewrite ?(unsigned_lit xn) in Hchk by lia. rewrite !signed_lit in Hchk by lia.
          rewrite !Z.shiftr_div_pow2 in Hchk by lia. rewrite !Z.div_small in Hchk by lia. apply Hchk. reflexivity. }
        clear Hchk.
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit (xn * 10)%Z) by lia.
        lazymatch goal with |- context [Zw (xn * 10 + Z.land ?u 255)%Z] =>
          pose proof (land255_range u) as T0; apply (TAIL (xn * 10 + Z.land u 255)%Z); lia
        | |- ?g => idtac "ADDFORM"; idtac g end.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_27a58 : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x29a0c x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX. open_udctx DX.
    unfold K_27cf8 in C_27cf8. unfold K_28114e in C_28114e.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hfx.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin_cf8 PINV DGI SPANS kp kp 0%Z.
    - (* [comment removed for export] *)
      step. step. step. step. (* [comment removed for export] *)
      step. step. step. (* [comment removed for export] *)
      call_memset27 FR.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_true.
      to_frameA FR.
      goto (eapply C_28114e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_279f0 : forall junk m (x1 x7 x8 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq ngx,
      udctx k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x299a4 x1 (Zw ngx) x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) (Zw (P + kq)) x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x22 x28 x29 x30 x31 k3 kI fp fL kp kq ngx DX KQ NGX.
    pose proof DX as DX'. open_udctx DX'.
    txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd. goto (eapply UD_27a58). exact DX.
    - clear Hd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (UD_loopx (S (Z.to_nat (L - kq))) junk m) with (kq := kq) (xn := 0%Z) (ngx := ngx));
        [lia | exact DX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_27840 : forall junk m (x1 x6 x7 x8 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq,
      udctx k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z ->
      evt USEGS POST (UDST 0x297f4 x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) (Zw (P + kq)) x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x22 x28 x29 x30 x31 k3 kI fp fL kp kq DX KQ.
    pose proof DX as DX'. open_udctx DX'.
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hx; cond_cleanup Hx; [exfalso; lia|].
      step. (* [comment removed for export] *)
      goto (eapply UD_27a58). exact DX.
    - cond_cleanup Hend.
      txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
      step. (* [comment removed for export] *)
      clear RD. fold_tx (r_bs c) kq.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hplus.
      + clear Hplus.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov; [cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia|]. clear Hov.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He.
        * clear He. goto (eapply UD_27a58). exact DX.
        * cond_cleanup He. goto (eapply UD_279f0 with (kq := (kq + 1)%Z) (ngx := 0%Z)); [exact DX | lia | lia].
      + clear Hplus.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hminus.
        * clear Hminus.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hx.
          -- clear Hx. goto (eapply UD_279f0 with (kq := kq) (ngx := 0%Z)); [exact DX | lia | lia].
          -- clear Hx. step. (* [comment removed for export] *) goto (eapply UD_27a58). exact DX.
        * clear Hminus.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hov; [ | cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia]. clear Hov.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He.
          -- cond_cleanup He. goto (eapply UD_279f0 with (kq := (kq + 1)%Z) (ngx := 1%Z)); [exact DX | lia | lia].
          -- clear He. step. (* [comment removed for export] *) goto (eapply UD_27a58). exact DX.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_27804 : forall junk m (x1 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m -> (kp < L)%Z ->
      evt USEGS POST (UDST 0x297b8 x1 (Zw (tx bs kp)) x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX KP'.
    pose proof DX as DX'. open_udctx DX'. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    - clear Hs. goto (eapply UD_27840 with (kq := kp)); [exact DX | lia].
    - clear Hs.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hskip.
      + clear Hskip. goto (eapply UD_27840 with (kq := kp)); [exact DX | lia].
      + clear Hskip.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
        goto (eapply UD_27840 with (kq := (kp + 1)%Z)); [exact DX | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_27874 : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x29828 x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX.
    pose proof DX as DX'. open_udctx DX'.
    unfold K_27cf8 in C_27cf8. unfold K_28114e in C_28114e.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsci.
    - (* [comment removed for export] *)
      step. step. step. step. (* [comment removed for export] *)
      step. step. step. (* [comment removed for export] *)
      call_memset27 FR.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_true.
      to_frameA FR.
      goto (eapply C_28114e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin_cf8 PINV DGI SPANS kp kp 0%Z.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_27cf8 C_28114e"] Lemma UD_277c8 : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x2977c x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX.
    pose proof DX as DX'. open_udctx DX'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hf; [clear Hf; goto (eapply UD_27874); exact DX|]. clear Hf.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply UD_27874); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hr; [clear Hr; goto (eapply UD_27874); exact DX|]. clear Hr.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; [clear Hb; goto (eapply UD_27874); exact DX|]. clear Hb.
    goto (eapply UD_27804); [exact DX | lia].
  Qed.

  End D.

  #[using="PRE C_27cf8 C_28114e"] Lemma uspf_D : K_277ac c.
  Proof. LiaFast.lf_pins (fun (PRE C_27cf8 C_28114e : LiaFast.U) => LiaFast.u0).
    unfold K_277ac. intros junk m x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI fp fL kp
      PINV K3I K31 FL0 KP DGI SPANS DC.
    assert (DX : udctx k3 kI fp fL kp junk m).
    { split; [exact PINV|]. split; [exact K3I|]. split; [exact K31|]. split; [exact FL0|].
      split; [exact KP|]. split; [exact DGI|]. split; [exact SPANS| exact DC]. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs; [clear Hs; goto (eapply (UD_277c8 x10 x24 x25 x26 x27)); exact DX|]. clear Hs.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply (UD_277c8 x10 x24 x25 x26 x27)); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hee.
    - clear Hee. goto (eapply (UD_27804 x10 x24 x25 x26 x27)); [exact DX | lia].
    - clear Hee. goto (eapply (UD_277c8 x10 x24 x25 x26 x27)); exact DX.
  Qed.
End BLK.
End U_spf_D.


Module U_spf_E.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spf_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation mI := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -704)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Notation DP := (bv_unsigned (r_a4 c) mod 256)%Z.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[local] Ltac open_upinv H :=
    unfold upinv, upinvB, upinv_with in H;
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold uframeA, uframeB, usaves in FR;
    unfold slow_path_float_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[using="Type"] #[local] Lemma rw_CB_len : forall segs m A n junk rest, rw_cells segs m A (CB n junk :: rest) -> length junk = n.
  Proof. LiaFast.lf_pins LiaFast.u0. intros segs m A n junk rest [[Hwf _] _]. cbn in Hwf. tauto. Qed.

  (* [comment removed for export] *)
  #[local] Ltac to_frameA FR :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A ?cs =>
        let n := eval compute in (Nat.sub (List.length cs) 13) in
        let mid := take_cells n cs in
        let post := drop_cells n cs in
        apply (rw_cells_merge segs m A [] mid post) in FR;
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ _ (CB 600 ?j :: _) => set (junk_m := j) in FR; clearbody junk_m
        end
    end.

  (* [comment removed for export] *)
  #[local] Ltac call_memset27 FR :=
    let LJA := fresh "LJA" in let LJJ := fresh "LJJ" in let OLD := fresh "OLD" in let OBJn := fresh "OBJn" in
    let Ua0 := fresh "Ua0" in let Ua2 := fresh "Ua2" in
    let FRlo := fresh "FRlo" in let FR2 := fresh "FR2" in let OBJ := fresh "OBJ" in let FRhi := fresh "FRhi" in
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (CB 48 ?ja :: ?rest) =>
        pose proof (rw_CB_len segs m A 48 ja rest FR) as LJA;
        apply (rw_cells_split_CB segs m A [] 48 ja rest [16; 27; 5]%nat) in FR; [ | reflexivity ];
        cbn [app mk_CB_cells] in FR
    end;
    chunk_split FR 1%nat FRlo FR2; chunk_split FR2 1%nat OBJ FRhi;
    lazymatch type of OBJ with
    | rw_cells ?segs ?m ?B [CB 27 ?jj] =>
        pose proof (rw_CB_len segs m B 27 jj [] OBJ) as LJJ;
        pose proof (u8arr_of_rw_cells segs m B 27 jj OBJ) as OLD; clear OBJ;
        pose proof (unsigned_lit B ltac:(lia)) as Ua0;
        pose proof (unsigned_lit 27 ltac:(lia)) as Ua2
    end;
    step; (* [comment removed for export] *)
    call memset_spec;
    [ reflexivity
    | rewrite unsigned_lit by lia; exact OLD
    | rewrite unsigned_lit by lia; rewrite LJJ; reflexivity
    | rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
    | ];
    lazymatch goal with
    | HB : bytes_at ?segs ?m' _ (repeat _ _), HW : wr_at _ _ _ _ |- _ =>
        rewrite ?unsigned_lit in HB, HW by lia;
        pose proof (rw_cells_of_u8arr segs m' _ _ (conj HB HW)) as OBJn;
        rewrite repeat_length in OBJn; change (Z.to_nat 27) with 27%nat in OBJn;
        clear HB HW; try clear OLD; try clear Ua0; try clear Ua2;
        chunk_join FRlo OBJn FR2; chunk_join FR2 FRhi FR
    end.

  (* [comment removed for export] *)
  #[local] Ltac ms_leaf_eq ::=
    first [ reflexivity
          | apply (f_equal (Z_to_bv 64)); lia
          | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
          | lazymatch goal with
            | |- ?a = Z_to_bv 64 ?e =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | apply (f_equal (Z_to_bv 64)); lia ]
            | |- Z_to_bv 64 ?e = ?a =>
                transitivity (Z_to_bv 64 (bv_unsigned a)); [ apply (f_equal (Z_to_bv 64)); lia | apply Z_to_bv_bv_unsigned ]
            end ].

  (* [comment removed for export] *)
  #[local] Ltac ms_eq_tac ::=
    cbv beta delta [mkR];
    repeat first [ reflexivity
                 | ms_leaf_eq
                 | lazymatch goal with
                   | |- ?a = _ => lazymatch type of a with
                                  | bv _ => fail
                                  | _ => progress f_equal
                                  end
                   end ].

  (* [comment removed for export] *)
  #[local] Tactic Notation "goto" tactic3(tac) := (eapply evt_eq; [ | tac ]; [ ms_eq_tac; try first [ ms_leaf_eq | lia ] | .. ]).

  (* [comment removed for export] *)
  #[local] Ltac kill_chk H :=
    exfalso; cond_cleanup H; unsign_chk H; rewrite ?signed_lit in H by lia;
    repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
    Z.div_mod_to_equations; lia.

  Hypothesis C_28084 : K_28084 c.

  Definition C19 : Z := 999999999999999999.

  (* [comment removed for export] *)
  Definition uectx (k3 kI fp fL kp kq : Z) junk m : Prop :=
    upinv c junk m /\ (0 <= k3 <= kI)%Z /\ (k3 <= 1)%Z /\ (0 <= fL)%Z /\
    (kI <= kp <= kq)%Z /\ (kq <= L)%Z /\ digs bs k3 kI /\ uspans c k3 kI fp fL kp /\ (0 < (kI - k3) + fL)%Z /\
    (kI + fL <= kp)%Z.

  Definition NZ (k3 kI fL : Z) : Prop := zeros bs k3 kI -> (fL = 0 \/ zeros bs (kI + 1) (kI + 1 + fL))%Z -> False.

  #[local] Ltac open_uectx EX :=
    destruct EX as (PINV & K3I & K31 & FL0 & KPQ & KQL & DGI & SPANS & DC & FLK);
    pre_facts; pose proof PINV as PINV'; open_upinv PINV'.

  Section E.
  Variables x8 x20' x21 x22 x24 x25 x26 x27 : word.

  (* [comment removed for export] *)
  #[local] Notation UEST pc x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m :=
    (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kq)) x10 x11 (Zw (tx bs 0)) x13
             (Zw (kI - k3)) (Zw fp) x16 (Zw fL) (Zw (P + k3)) a1 x20
             x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom USEGS)) (only parsing).

  #[local] Ltac fin84 PINV SPANS tmv :=
    goto (eapply C_28084 with (tm := tmv));
    [ exact PINV | lia | lia | lia | lia
    | destruct SPANS as [(?&?&?)|(?&?&?&?&?)]; [left; lia | right; lia]
    | lia | ].

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_28070 : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn d wv,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (- 2^41 < d < 2^41)%Z -> (0 < wv < 2^64 - 1)%Z ->
      evt USEGS POST (UEST 0x2a024 x1 x5 x6 x7 (Zw wv) (Zw d) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn d wv EX XN DD WV. open_uectx EX.
    unfold K_28084 in C_28084.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hchk; [kill_chk Hchk|]. clear Hchk.
    step. (* [comment removed for export] *)
    fin84 PINV SPANS 1%Z. intros _. rewrite unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_fin0 : forall junk m (x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq,
      uectx k3 kI fp fL kp kq junk m ->
      evt USEGS POST (UEST 0x29d64 x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq EX. open_uectx EX.
    unfold K_28084 in C_28084.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fin84 PINV SPANS 0%Z. intros; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_2806c : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn kf wv,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (fp = P + kI + 1)%Z -> (kI + 1 <= kf <= L)%Z ->
      (0 < wv < 2^64 - 1)%Z ->
      evt USEGS POST (UEST 0x2a020 x1 x5 x6 x7 (Zw wv) (Zw (P + kf)) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn kf wv EX XN FP KF WV.
    pose proof EX as EX'. open_uectx EX'.
    step. (* [comment removed for export] *)
    goto (eapply UE_28070 with (d := (kI + 1 - kf)%Z) (wv := wv)); [exact EX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_loopF : forall (n : nat) junk m (x1 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn kf wv,
      (kI + 1 + fL - kf <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (fp = P + kI + 1)%Z -> (kI + 1 + fL <= L)%Z -> digs bs (kI + 1) (kI + 1 + fL) ->
      (kI + 1 <= kf < kI + 1 + fL)%Z -> (0 <= wv <= C19)%Z ->
      (wv = 0%Z -> zeros bs k3 kI /\ zeros bs (kI + 1) kf) ->
      evt USEGS POST (UEST 0x29da0 x1 (Zw (-1)) (Zw 10) (Zw (kI + fL - kf)) (Zw wv) (Zw (P + kf)) (Zw xn) (Zw C19) x20
                           (Zw (P + kf)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x20 x29 x30 x31 k3 kI fp fL kp kq xn kf wv Hn EX NZH XN FP FEND DGF KF WV ZF.
    { exfalso. lia. }
    pose proof EX as EX'. open_uectx EX'. unfold C19 in *.
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia|]. clear Hov.
    txt_rd TXT kf RD. pose proof (tx_range bs kf) as Rk. pose proof (DGF kf ltac:(lia)) as Dk. unfold isdig in Dk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kf.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs kf)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      goto (eapply UE_2806c with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia | exact FP | lia | lia].
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z));
          [lia | exact EX | exact NZH | lia | exact FP | lia | exact DGF | | unfold C19; lia | ].
        * Z.div_mod_to_equations. lia.
        * intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
          split; [exact Z1|]. apply zeros_snoc; [exact Z2 | lia].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        assert (NZW : (wv * 10 + tx bs kf + -48 <> 0)%Z).
        { intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
          apply (NZH Z1). right. replace (kI + 1 + fL)%Z with (kf + 1)%Z by (Z.div_mod_to_equations; lia).
          apply zeros_snoc; [exact Z2 | lia]. }
        goto (eapply UE_2806c with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia | exact FP | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_27db8 : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn wv,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 kI) ->
      evt USEGS POST (UEST 0x29d6c x1 x5 x6 x7 (Zw wv) (Zw 77052) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn wv EX NZH XN WV ZF.
    pose proof EX as EX'. open_uectx EX'. unfold C19 in *.
    destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)].
    - (* [comment removed for export] *)
      subst fp fL.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; revert Hov; vm_compute; congruence|]. clear Hov.
      step. (* [comment removed for export] *)
      if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (NZW : wv <> 0%Z).
      { intros ->. apply (NZH (ZF eq_refl)). left. reflexivity. }
      goto (eapply UE_28070 with (d := 0%Z) (wv := wv)); [exact EX | lia | lia | lia].
    - (* [comment removed for export] *)
      subst fp.
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (P + kI + 1)%Z), ?(unsigned_lit fL) by lia.
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov.
      { exfalso. cond_cleanup Hov. revert Hov. rewrite ?v_sltu_b2z, ?v_sltiu_b2z. rewrite ?unsigned_lit by lia.
        replace (bv_wrap 64 1) with 1%Z by reflexivity.
        destruct (Z.ltb_spec0 0 (P + kI + 1)); [|lia].
        destruct (Z.ltb_spec0 (fL + (P + kI + 1)) 1); [lia|]. vm_compute. congruence. }
      clear Hov.
      step. (* [comment removed for export] *)
      if_cases Hf0.
      + cond_cleanup Hf0. rewrite ?Z.mod_small in Hf0 by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        assert (NZW : wv <> 0%Z).
        { intros ->. apply (NZH (ZF eq_refl)). left. lia. }
        goto (eapply UE_28070 with (d := 0%Z) (wv := wv)); [exact EX | lia | lia | lia].
      + cond_cleanup Hf0. rewrite ?Z.mod_small in Hf0 by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply (UE_loopF (S (Z.to_nat fL)) junk m) with (kf := (kI + 1)%Z) (wv := wv));
          [lia | exact EX | exact NZH | lia | reflexivity | lia | exact F5 | lia | unfold C19; lia | ].
        intros Hz. split; [exact (ZF Hz) | apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_27d90 : forall junk m (x1 x6 x7 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ki wv,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (k3 <= ki <= kI)%Z -> (0 <= wv < 2^64 - 1)%Z -> (wv <= C19 -> wv = 0 -> zeros bs k3 kI)%Z ->
      evt USEGS POST (UEST 0x29d44 x1 (Zw (P + ki)) x6 x7 (Zw wv) (Zw 77052) (Zw xn) (Zw (P + kI)) x20 (Zw 10) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x20 x29 x30 x31 k3 kI fp fL kp kq xn ki wv EX NZH XN KI WV ZF.
    pose proof EX as EX'. open_uectx EX'. unfold C19 in *.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsmall.
    - cond_cleanup Hsmall.
      goto (eapply UE_27db8 with (wv := wv)); [exact EX | exact NZH | lia | unfold C19; lia | intros; apply ZF; lia].
    - cond_cleanup Hsmall.
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (P + kI)%Z), ?(unsigned_lit (P + ki)%Z) by lia.
      step. (* [comment removed for export] *)
      goto (eapply UE_28070 with (d := (kI - ki)%Z) (wv := wv)); [exact EX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_loopI : forall (n : nat) junk m (x1 x20 x30 x31 : word) k3 kI fp fL kp kq xn ki wv,
      (kI - ki <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (k3 <= ki < kI)%Z -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 ki) ->
      evt USEGS POST (UEST 0x29d1c x1 (Zw (P + ki)) (Zw C19) (Zw 2) (Zw wv) (Zw 77052) (Zw xn) (Zw (P + kI)) x20
                           (Zw 10) (Zw (P + ki + 1)) x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x20 x30 x31 k3 kI fp fL kp kq xn ki wv Hn EX NZH XN KI WV ZF.
    { exfalso. lia. }
    pose proof EX as EX'. open_uectx EX'. unfold C19 in *.
    pose proof (DGI ki ltac:(lia)) as Dk. unfold isdig in Dk. pose proof (tx_range bs ki) as Rk.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    txt_rd TXT ki RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) ki.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs ki)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      goto (eapply UE_27d90 with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
        [exact EX | exact NZH | lia | lia | lia | intros; exfalso; lia].
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
          [lia | exact EX | exact NZH | lia | lia | unfold C19; lia | ].
        intros Hz. assert (wv = 0%Z) as -> by lia. apply zeros_snoc; [exact (ZF eq_refl) | lia].
      + cond_cleanup Hmore.
        goto (eapply UE_27d90 with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
          [exact EX | exact NZH | lia | lia | unfold C19; lia | ].
        intros _ Hz. assert (wv = 0%Z) as -> by lia. replace kI with (ki + 1)%Z by lia.
        apply zeros_snoc; [exact (ZF eq_refl) | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_27d40 : forall junk m (x1 x5 x6 x7 x10 x11 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      evt USEGS POST (UEST 0x29cf4 x1 x5 x6 x7 x10 x11 (Zw xn) (Zw (P + kI)) x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x10 x11 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn EX NZH XN.
    pose proof EX as EX'. open_uectx EX'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hemp.
    - cond_cleanup Hemp.
      goto (eapply UE_27db8 with (wv := 0%Z)); [exact EX | exact NZH | lia | unfold C19; lia | ].
      intros _. replace kI with k3 by (Z.div_mod_to_equations; lia). apply zeros_nil.
    - cond_cleanup Hemp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (UE_loopI (S (Z.to_nat (kI - k3))) junk m) with (ki := k3) (wv := 0%Z));
        [lia | exact EX | exact NZH | lia | Z.div_mod_to_equations; lia | unfold C19; lia | intros _; apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_27d38 : forall junk m (x1 x6 x7 x10 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ks,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (k3 <= ks <= L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = DP) ->
      (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> DP)) ->
      evt USEGS POST (UEST 0x29cec x1 (Zw ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))) x6 x7 x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
                           (Zw (P + ks)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x10 x20 x29 x30 x31 k3 kI fp fL kp kq xn ks EX XN KS SCAN EXIT.
    pose proof EX as EX'. open_uectx EX'.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply UE_fin0). exact EX.
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      goto (eapply UE_27d40); [exact EX | | lia].
      intros ZI ZF.
      assert (SP' : (fL = 0 \/ (kI < L /\ tx bs kI = DP /\ kI + 1 + fL <= L /\ zeros bs (kI + 1) (kI + 1 + fL)))%Z).
      { destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; [left; exact F2|].
        destruct ZF as [F0|ZF]; [left; exact F0 | right].
        split; [exact F2|]. split; [exact F3|]. split; [lia | exact ZF]. }
      exact (strip_contra bs L k3 kI fL ks DP ltac:(lia) ltac:(lia) FL0 KS ZI SP' SCAN EXIT H20).
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_28084"] Lemma UE_loopS : forall (n : nat) junk m (x1 x10 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ks t0v,
      (L - ks <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (k3 <= ks < L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = DP) ->
      t0v = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z ->
      evt USEGS POST (UEST 0x29cc4 x1 (Zw t0v) (Zw 48) (Zw (-1)) x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
                           (Zw (P + ks)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x10 x20 x29 x30 x31 k3 kI fp fL kp kq xn ks t0v Hn EX XN KS SCAN T0V.
    { exfalso. lia. }
    pose proof EX as EX'. open_uectx EX'.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    pose proof (Z.mod_pos_bound (bv_unsigned a4) 256 ltac:(lia)) as DPR.
    txt_rd TXT ks RD. pose proof (tx_range bs ks) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) ks.
    (* [comment removed for export] *)
    assert (TAIL : forall (is0 : Z) (x29' : word),
      (is0 = (if (tx bs ks =? 48)%Z then 1 else 0))%Z -> (tx bs ks = 48%Z \/ tx bs ks = DP) ->
      evt USEGS POST (UEST 0x29ce0 x1 (Zw (t0v - is0)) (Zw 48) (Zw (-1)) x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
                           (Zw (P + ks)) x29' x30 x31 k3 kI fp fL kp kq m)).
    { intros is0 x29' IS0 HB.
      assert (IS0R : (0 <= is0 <= 1)%Z) by (rewrite IS0; destruct (tx bs ks =? 48)%Z; lia).
      assert (SCAN' : forall k, (k3 <= k < ks + 1)%Z -> tx bs k = 48%Z \/ tx bs k = DP).
      { intros k Hk. destruct (Z.eq_dec k ks) as [->|]; [exact HB|]. apply SCAN. lia. }
      assert (T0V' : (t0v - is0 = (kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks + 1 - k3)))%Z).
      { replace (Z.to_nat (ks + 1 - k3)) with (S (Z.to_nat (ks - k3))) by lia.
        rewrite cnt48_step. replace (k3 + Z.of_nat (Z.to_nat (ks - k3)))%Z with ks by lia. rewrite <- IS0. lia. }
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      - cond_cleanup Hmore.
        goto (eapply (IH junk m) with (ks := (ks + 1)%Z) (t0v := (t0v - is0)%Z));
          [lia | exact EX | lia | lia | exact SCAN' | exact T0V'].
      - cond_cleanup Hmore.
        goto (eapply UE_27d38 with (ks := (ks + 1)%Z));
          [exact EX | lia | lia | exact SCAN' | left; lia]. }
    step. (* [comment removed for export] *)
    if_cases H48.
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases Hx; [cond_cleanup Hx; exfalso; lia|]. clear Hx.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hchk; [kill_chk Hchk|]. clear Hchk.
      step. (* [comment removed for export] *)
      goto (eapply (TAIL 1%Z)); [rewrite H48; reflexivity | left; exact H48].
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      + cond_cleanup Hdp.
        goto (eapply UE_27d38 with (ks := ks));
          [exact EX | lia | lia | exact SCAN | right; split; [exact H48 | exact Hdp]].
      + cond_cleanup Hdp.
        step. (* [comment removed for export] *)
        if_cases Hx; [|cond_cleanup Hx; exfalso; lia]. clear Hx.
        goto (eapply (TAIL 0%Z)); [rewrite (proj2 (Z.eqb_neq _ _) H48); reflexivity | right; exact Hdp].
  Qed.

  End E.

  #[using="PRE C_28084"] Lemma uspf_E : K_27cf8 c.
  Proof. LiaFast.lf_pins (fun (PRE C_28084 : LiaFast.U) => LiaFast.u0).
    unfold K_27cf8. intros junk m x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI fp fL kp kq xn
      PINV K3I K31 FL0 KPQ KQL DGI SPANS DC XN.
    assert (EX : uectx k3 kI fp fL kp kq junk m).
    { split; [exact PINV|]. split; [exact K3I|]. split; [exact K31|]. split; [exact FL0|].
      split; [exact KPQ|]. split; [exact KQL|]. split; [exact DGI|]. split; [exact SPANS|]. split; [exact DC|].
      destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; lia. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    assert (FLK : (kI + fL <= kp)%Z) by (destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply UE_fin0). exact EX.
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      step. (* [comment removed for export] *)
      if_cases Hk3.
      { cond_cleanup Hk3. exfalso. lia. }
      cond_cleanup Hk3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (UE_loopS x8 x21 x22 x24 x25 x26 x27 (S (Z.to_nat (L - k3))) junk m)
              with (ks := k3) (t0v := ((kI - k3) + fL)%Z));
        [lia | exact EX | lia | lia | intros; lia | ].
      replace (Z.to_nat (k3 - k3)) with O by lia. cbn [cnt48]. lia.
  Qed.
End BLK.
End U_spf_E.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse.U_spf_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse.U_spf_B OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse.U_spf_C OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse.U_spf_D OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spf_parse.U_spf_E.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Lemma uspf_parse : forall c : spf_ctx, uspf_pre c -> K_28084 c -> K_28114e c ->
  evt USEGS (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c))
      (MS (mkR (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_t0 c) (r_t1 c) (r_t2 c) (r_s0 c) (r_s1 c)
               (r_a0 c) (r_a1 c) (r_a2 c) (r_a3 c) (r_a4 c) (r_a5 c) (r_a6 c) (r_a7 c)
               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c) (r_s10 c) (r_s11 c)
               (r_t3 c) (r_t4 c) (r_t5 c) (r_t6 c))
          (r_F c) (Z_to_bv 64 0x28fe8) (r_fc c) None (r_m0 c) (seg_rom USEGS)).
Proof.
  intros c PRE K6d0 K4b4.
  apply (uspf_A c PRE K4b4).
  apply (uspf_B c PRE).
  apply (uspf_C c PRE); [|exact K4b4].
  apply (uspf_D c PRE); [|exact K4b4].
  apply (uspf_E c PRE). exact K6d0.
Qed.

(* [comment removed for export] *)
Lemma uspf_parse_stmt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (v : word),
    let c := SPF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v in
    uspf_pre c -> K_28084 c -> K_28114e c ->
    evt USEGS (slow_path_float_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned a2) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x28fe8) fc None m (seg_rom USEGS)).
Proof.
  intros. apply (uspf_parse _ H H0 H1).
Qed.
