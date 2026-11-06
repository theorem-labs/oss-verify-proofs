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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_slow_path_double_stmt U_positive_digit_comp_d_stmt U_negative_digit_comp_d_stmt Spf_text U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.

Module U_spd_B.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  Hypothesis C_22c1c : K_22c1c c.

  #[local] Ltac fin k3v kIv PINV DG :=
    goto (eapply C_22c1c with (k3 := k3v) (kI := kIv)); [exact PINV | lia | lia | lia | exact DG].

  (* [comment removed for export] *)
  #[using="PRE C_22c1c"] Lemma uspd_B_loop : forall (n : nat) (k : Z) junk m
      (x1 x5' x6 x7 x8 x9 x10 x20 x21 x22 x24 x25 x26 x27 x29 x30 x31 : word) (k3 : Z),
      (L + 1 - k <= Z.of_nat n)%Z ->
      upinv c junk m -> (0 <= k3)%Z -> (k3 <= 1)%Z -> (k3 <= k <= L)%Z -> digs bs k3 k ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw 9) x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw 2) (Zw 10) (Zw (P + k)) (Zw (P + k))
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x5' x29 x30 x31)
            F (Zw 0x24964) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22c1c : LiaFast.U) => LiaFast.u0).
    unfold K_22c1c in C_22c1c.
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

  #[using="PRE C_22c1c"] Lemma uspd_B : K_228a0 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22c1c : LiaFast.U) => LiaFast.u0).
    unfold K_22c1c in C_22c1c.
    unfold K_228a0. intros junk m x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3
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
    goto (eapply (uspd_B_loop (S (Z.to_nat (L - (k3 + 5)))) (k3 + 5)%Z) with (k3 := k3));
      [lia | exact PINV | lia | lia | lia | exact DG5].
  Qed.
End BLK.
End U_spd_B.


Module U_spd_C.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  Hypothesis C_22d70 : K_22d70 c.
  Hypothesis C_236d8e : K_236d8e c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_double_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN_D; exact PR2|]; split; [exact MU | exact WM].

  #[using="Type"] Lemma nz_of_mod : forall x M : Z, (x mod M <> 0)%Z -> x <> 0%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. intros x M H E0. apply H. rewrite E0. apply Zmod_0_l. Qed.

  Section C.

  (* [comment removed for export] *)
  #[using="PRE C_236d8e"] Lemma UC_err6 : forall junk m (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      upinv c junk m ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) x12 x13 x14 x15 x16 x17
                 x18 a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24f1c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    unfold K_236d8e in C_236d8e.
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
    goto (eapply C_236d8e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_22f48 : forall junk m (x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kp : Z),
      upinv c junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kp <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kp ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kp)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24efc) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kp PINV K3I K31 KIL DPk KP DGI DGF.
    unfold K_22d70 in C_22d70.
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
      goto (eapply C_22d70 with (k3 := k3) (kI := kI) (fp := (P + kI + 1)%Z) (fL := (kp - (kI + 1))%Z) (kp := kp));
        [exact PINV | lia | lia | lia | lia | exact DGI | | ].
      + right. split; [reflexivity|]. split; [lia|]. split; [exact DPk|]. split; [lia|].
        replace (kI + 1 + (kp - (kI + 1)))%Z with kp by lia. exact DGF.
      + Z.div_mod_to_equations. lia.
    - cond_cleanup Hnz.
      goto (eapply UC_err6). exact PINV.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_loop1 : forall (n : nat) junk m (x1 x7 x8 x10 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      upinv c junk m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc < L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (-1)) (Zw 10) x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw 9)
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24ed0) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UC_22f48 with (kp := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
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
        goto (eapply UC_22f48 with (kp := (kc + 1)%Z));
          [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | apply digs_snoc; assumption].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_22f08 : forall j0 j1 m (x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24ebc) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
    intros j0 j1 m x1 x5 x6 x7 x8 x10 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kc PINV K3I K31 KIL DPk KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    to_frameA FR.
    assert (PINVA : upinv c junk_m m) by (mk_upinv TXT FR ST VAL PR1 PR2 MU WM).
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      goto (eapply UC_22f48 with (kp := kc)); [exact PINVA | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
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
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_4test : forall j0 j1 m (x1 x5 x6 x7 x8 x10 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc Vv : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc)%Z -> (kc + 4 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      (0 <= Vv < 2^64)%Z -> (Vv mod 2^32 = v4 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3)))%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 x23 (Zw Vv) x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24e40) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UC_22f08 with (kc := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
    - rewrite ?(unsigned_lit Vv) in H4 by lia.
      destruct (swar4_dig Vv _ _ _ _ R0 R1 R2 R3 VR VM H4) as (D0 & D1 & D2 & D3). clear H4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
      do 16 step. (* [comment removed for export] *)
      goto (eapply UC_22f08 with (kc := (kc + 4)%Z)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | ].
      apply digs_snoc4; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_22e5c : forall j0 j1 m (x1 x6 x7 x8 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (k3 kI kc : Z),
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) x6 x7 x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24e10) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
    intros j0 j1 m x1 x6 x7 x8 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI kc PINV K3I K31 KIL DPk KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4.
      goto (eapply UC_22f08 with (kc := kc)); [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF].
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
  #[using="PRE C_22d70 C_236d8e"] Lemma UC_loop8 : forall (n : nat) j0 j1 m (x1 x8 x10 x20 x21 x22 x24 x25 x26 x27 x30 x31 : word) (k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      upinvB c j0 j1 m -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z -> tx bs kI = DP ->
      (kI + 1 <= kc)%Z -> (kc + 8 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) (Zw 8) (Zw 14974415777481871312) x8 (Zw (P + kc)) x10 (Zw DP) (Zw (tx bs 0)) a3
                 (Zw (kI - k3)) (Zw (P + kI + 1)) (Zw (P + kI)) (Zw (P + kc))
                 (Zw (P + k3)) a1 x20 x21 x22 (Zw 7) x24 x25 x26 x27 (Zw 9259542123273814144) (Zw 5063812098665367110) x30 x31)
            F (Zw 0x24c54) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
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
        goto (eapply UC_22e5c with (kc := (kc + 8)%Z));
          [exact PINV | lia | lia | lia | exact DPk | lia | exact DGI | exact DGF'].
  Qed.

  End C.

  #[using="PRE C_22d70 C_236d8e"] Lemma uspd_C : K_22c1c c.
  Proof. LiaFast.lf_pins (fun (PRE C_22d70 C_236d8e : LiaFast.U) => LiaFast.u0).
    unfold K_22d70 in C_22d70.
    unfold K_22c1c. intros junk m x1 x5 x6 x7 x8 x9 x10 x14 x15 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI
      PINV K3I KIL K31 DG.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI)%Z), (unsigned_lit (P + k3)%Z) by lia.
    (* [comment removed for export] *)
    assert (NODP : forall x15,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 x10 (Zw DP) (Zw (tx bs 0)) a3 (Zw (P + kI - (P + k3))) x15 (Zw (P + kI)) x17
                 (Zw (P + k3)) a1 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24d0c) fc None m (seg_rom USEGS))).
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
        goto (eapply C_22d70 with (k3 := k3) (kI := kI) (fp := 0%Z) (fL := 0%Z) (kp := kI));
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
      goto (eapply UC_22e5c with (kc := (kI + 1)%Z));
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
End U_spd_C.


Module U_spd_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  Hypothesis C_232bc : K_232bc c.
  Hypothesis C_236d8e : K_236d8e c.

  #[local] Ltac mk_upinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [exact FR|]; split; [unfold slow_path_double_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold U_FMIN_D; exact PR2|]; split; [exact MU | exact WM].

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
    goto (eapply C_232bc with (kp := kpv) (kq := kqv) (xn := xnv));
    [exact PINV | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].

  (* [comment removed for export] *)
  #[using="PRE C_232bc"] Lemma UD_232a0 : forall junk m (x1 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn ngx,
      udctx k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x25254 x1 (Zw ngx) x7 x8 (Zw (P + kq)) (Zw xn) (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp kq xn ngx DX KQ XN NGX. open_udctx DX.
    unfold K_232bc in C_232bc.
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
  #[using="PRE C_232bc"] Lemma UD_loopx : forall (n : nat) junk m (x1 x8 x9 x22 : word) k3 kI fp fL kp kq xn ngx,
      (L - kq <= Z.of_nat n)%Z ->
      udctx k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x24f90 x1 (Zw ngx) (Zw 9) x8 x9 (Zw xn) (Zw (- fL)) (Zw (P + kq)) x22
                           (Zw 10) (Zw 268435455) (Zw 2) (Zw (P + kq)) k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UD_232a0 with (kq := kq) (xn := xn) (ngx := ngx)); [exact DX | lia | lia | lia].
    - clear Hd.
      (* [comment removed for export] *)
      assert (TAIL : forall xn' (x8' x22' : word), (0 <= xn' < 2^32)%Z ->
        evt USEGS POST (UDST 0x24fb8 x1 (Zw ngx) (Zw 9) x8' (Zw (Z.land (bv_unsigned (Zw (tx bs kq + -48))) 255)) (Zw xn') (Zw (- fL)) (Zw (P + kq)) x22'
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
          goto (eapply UD_232a0 with (kq := (kq + 1)%Z) (xn := xn') (ngx := ngx)); [exact DX | lia | lia | lia]. }
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
  #[using="PRE C_232bc C_236d8e"] Lemma UD_2301c : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x24fd0 x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX. open_udctx DX.
    unfold K_232bc in C_232bc. unfold K_236d8e in C_236d8e.
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
      goto (eapply C_236d8e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_232bc C_236d8e"] Lemma UD_22fb4 : forall junk m (x1 x7 x8 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq ngx,
      udctx k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= ngx <= 1)%Z ->
      evt USEGS POST (UDST 0x24f68 x1 (Zw ngx) x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) (Zw (P + kq)) x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x22 x28 x29 x30 x31 k3 kI fp fL kp kq ngx DX KQ NGX.
    pose proof DX as DX'. open_udctx DX'.
    txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd. goto (eapply UD_2301c). exact DX.
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
  #[using="PRE C_232bc C_236d8e"] Lemma UD_22e04 : forall junk m (x1 x6 x7 x8 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp kq,
      udctx k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z ->
      evt USEGS POST (UDST 0x24db8 x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) (Zw (P + kq)) x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x22 x28 x29 x30 x31 k3 kI fp fL kp kq DX KQ.
    pose proof DX as DX'. open_udctx DX'.
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hx; cond_cleanup Hx; [exfalso; lia|].
      step. (* [comment removed for export] *)
      goto (eapply UD_2301c). exact DX.
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
        * clear He. goto (eapply UD_2301c). exact DX.
        * cond_cleanup He. goto (eapply UD_22fb4 with (kq := (kq + 1)%Z) (ngx := 0%Z)); [exact DX | lia | lia].
      + clear Hplus.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hminus.
        * clear Hminus.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hx.
          -- clear Hx. goto (eapply UD_22fb4 with (kq := kq) (ngx := 0%Z)); [exact DX | lia | lia].
          -- clear Hx. step. (* [comment removed for export] *) goto (eapply UD_2301c). exact DX.
        * clear Hminus.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hov; [ | cond_cleanup Hov; exfalso; Z.div_mod_to_equations; lia]. clear Hov.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He.
          -- cond_cleanup He. goto (eapply UD_22fb4 with (kq := (kq + 1)%Z) (ngx := 1%Z)); [exact DX | lia | lia].
          -- clear He. step. (* [comment removed for export] *) goto (eapply UD_2301c). exact DX.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_232bc C_236d8e"] Lemma UD_22dc8 : forall junk m (x1 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m -> (kp < L)%Z ->
      evt USEGS POST (UDST 0x24d7c x1 (Zw (tx bs kp)) x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX KP'.
    pose proof DX as DX'. open_udctx DX'. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    - clear Hs. goto (eapply UD_22e04 with (kq := kp)); [exact DX | lia].
    - clear Hs.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hskip.
      + clear Hskip. goto (eapply UD_22e04 with (kq := kp)); [exact DX | lia].
      + clear Hskip.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov; [ | cond_cleanup Hov; exfalso; lia]. clear Hov.
        goto (eapply UD_22e04 with (kq := (kp + 1)%Z)); [exact DX | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_232bc C_236d8e"] Lemma UD_22e38 : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x24dec x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX.
    pose proof DX as DX'. open_udctx DX'.
    unfold K_232bc in C_232bc. unfold K_236d8e in C_236d8e.
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
      goto (eapply C_236d8e). mk_upinv TXT FR ST VAL PR1 PR2 MU WM.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      fin_cf8 PINV DGI SPANS kp kp 0%Z.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_232bc C_236d8e"] Lemma UD_22d8c : forall junk m (x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 : word) k3 kI fp fL kp,
      udctx k3 kI fp fL kp junk m ->
      evt USEGS POST (UDST 0x24d40 x1 x6 x7 x8 (Zw (P + kp)) a3 (Zw (- fL)) x21 x22 x28 x29 x30 x31 k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x8 x21 x22 x28 x29 x30 x31 k3 kI fp fL kp DX.
    pose proof DX as DX'. open_udctx DX'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hf; [clear Hf; goto (eapply UD_22e38); exact DX|]. clear Hf.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply UD_22e38); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hr; [clear Hr; goto (eapply UD_22e38); exact DX|]. clear Hr.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; [clear Hb; goto (eapply UD_22e38); exact DX|]. clear Hb.
    goto (eapply UD_22dc8); [exact DX | lia].
  Qed.

  End D.

  #[using="PRE C_232bc C_236d8e"] Lemma uspd_D : K_22d70 c.
  Proof. LiaFast.lf_pins (fun (PRE C_232bc C_236d8e : LiaFast.U) => LiaFast.u0).
    unfold K_22d70. intros junk m x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI fp fL kp
      PINV K3I K31 FL0 KP DGI SPANS DC.
    assert (DX : udctx k3 kI fp fL kp junk m).
    { split; [exact PINV|]. split; [exact K3I|]. split; [exact K31|]. split; [exact FL0|].
      split; [exact KP|]. split; [exact DGI|]. split; [exact SPANS| exact DC]. }
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs; [clear Hs; goto (eapply (UD_22d8c x10 x24 x25 x26 x27)); exact DX|]. clear Hs.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply (UD_22d8c x10 x24 x25 x26 x27)); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hee.
    - clear Hee. goto (eapply (UD_22dc8 x10 x24 x25 x26 x27)); [exact DX | lia].
    - clear Hee. goto (eapply (UD_22d8c x10 x24 x25 x26 x27)); exact DX.
  Qed.
End BLK.
End U_spd_D.


Module U_spd_E.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  Hypothesis C_23648 : K_23648 c.

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
    goto (eapply C_23648 with (tm := tmv));
    [ exact PINV | lia | lia | lia | lia
    | destruct SPANS as [(?&?&?)|(?&?&?&?&?)]; [left; lia | right; lia]
    | lia | ].

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_23634 : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn d wv,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (- 2^41 < d < 2^41)%Z -> (0 < wv < 2^64 - 1)%Z ->
      evt USEGS POST (UEST 0x255e8 x1 x5 x6 x7 (Zw wv) (Zw d) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn d wv EX XN DD WV. open_uectx EX.
    unfold K_23648 in C_23648.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hchk; [kill_chk Hchk|]. clear Hchk.
    step. (* [comment removed for export] *)
    fin84 PINV SPANS 1%Z. intros _. rewrite unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_fin0 : forall junk m (x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq,
      uectx k3 kI fp fL kp kq junk m ->
      evt USEGS POST (UEST 0x25328 x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x10 x11 x13 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq EX. open_uectx EX.
    unfold K_23648 in C_23648.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fin84 PINV SPANS 0%Z. intros; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_23630 : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn kf wv,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (fp = P + kI + 1)%Z -> (kI + 1 <= kf <= L)%Z ->
      (0 < wv < 2^64 - 1)%Z ->
      evt USEGS POST (UEST 0x255e4 x1 x5 x6 x7 (Zw wv) (Zw (P + kf)) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq xn kf wv EX XN FP KF WV.
    pose proof EX as EX'. open_uectx EX'.
    step. (* [comment removed for export] *)
    goto (eapply UE_23634 with (d := (kI + 1 - kf)%Z) (wv := wv)); [exact EX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_loopF : forall (n : nat) junk m (x1 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn kf wv,
      (kI + 1 + fL - kf <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (fp = P + kI + 1)%Z -> (kI + 1 + fL <= L)%Z -> digs bs (kI + 1) (kI + 1 + fL) ->
      (kI + 1 <= kf < kI + 1 + fL)%Z -> (0 <= wv <= C19)%Z ->
      (wv = 0%Z -> zeros bs k3 kI /\ zeros bs (kI + 1) kf) ->
      evt USEGS POST (UEST 0x25364 x1 (Zw (-1)) (Zw 10) (Zw (kI + fL - kf)) (Zw wv) (Zw (P + kf)) (Zw xn) (Zw C19) x20
                           (Zw (P + kf)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UE_23630 with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia | exact FP | lia | lia].
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
        goto (eapply UE_23630 with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia | exact FP | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_2337c : forall junk m (x1 x5 x6 x7 x16 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn wv,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 kI) ->
      evt USEGS POST (UEST 0x25330 x1 x5 x6 x7 (Zw wv) (Zw 78528) (Zw xn) x16 x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UE_23634 with (d := 0%Z) (wv := wv)); [exact EX | lia | lia | lia].
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
        goto (eapply UE_23634 with (d := 0%Z) (wv := wv)); [exact EX | lia | lia | lia].
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
  #[using="PRE C_23648"] Lemma UE_23354 : forall junk m (x1 x6 x7 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ki wv,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (k3 <= ki <= kI)%Z -> (0 <= wv < 2^64 - 1)%Z -> (wv <= C19 -> wv = 0 -> zeros bs k3 kI)%Z ->
      evt USEGS POST (UEST 0x25308 x1 (Zw (P + ki)) x6 x7 (Zw wv) (Zw 78528) (Zw xn) (Zw (P + kI)) x20 (Zw 10) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x20 x29 x30 x31 k3 kI fp fL kp kq xn ki wv EX NZH XN KI WV ZF.
    pose proof EX as EX'. open_uectx EX'. unfold C19 in *.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsmall.
    - cond_cleanup Hsmall.
      goto (eapply UE_2337c with (wv := wv)); [exact EX | exact NZH | lia | unfold C19; lia | intros; apply ZF; lia].
    - cond_cleanup Hsmall.
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (P + kI)%Z), ?(unsigned_lit (P + ki)%Z) by lia.
      step. (* [comment removed for export] *)
      goto (eapply UE_23634 with (d := (kI - ki)%Z) (wv := wv)); [exact EX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_loopI : forall (n : nat) junk m (x1 x20 x30 x31 : word) k3 kI fp fL kp kq xn ki wv,
      (kI - ki <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      (k3 <= ki < kI)%Z -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 ki) ->
      evt USEGS POST (UEST 0x252e0 x1 (Zw (P + ki)) (Zw C19) (Zw 2) (Zw wv) (Zw 78528) (Zw xn) (Zw (P + kI)) x20
                           (Zw 10) (Zw (P + ki + 1)) x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UE_23354 with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
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
        goto (eapply UE_23354 with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
          [exact EX | exact NZH | lia | lia | unfold C19; lia | ].
        intros _ Hz. assert (wv = 0%Z) as -> by lia. replace kI with (ki + 1)%Z by lia.
        apply zeros_snoc; [exact (ZF eq_refl) | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_23304 : forall junk m (x1 x5 x6 x7 x10 x11 x20 x28 x29 x30 x31 : word) k3 kI fp fL kp kq xn,
      uectx k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (- 2^32 < xn < 2^32)%Z ->
      evt USEGS POST (UEST 0x252b8 x1 x5 x6 x7 x10 x11 (Zw xn) (Zw (P + kI)) x20 x28 x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
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
      goto (eapply UE_2337c with (wv := 0%Z)); [exact EX | exact NZH | lia | unfold C19; lia | ].
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
  #[using="PRE C_23648"] Lemma UE_232fc : forall junk m (x1 x6 x7 x10 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ks,
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (k3 <= ks <= L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = DP) ->
      (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> DP)) ->
      evt USEGS POST (UEST 0x252b0 x1 (Zw ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))) x6 x7 x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
                           (Zw (P + ks)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x10 x20 x29 x30 x31 k3 kI fp fL kp kq xn ks EX XN KS SCAN EXIT.
    pose proof EX as EX'. open_uectx EX'.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply UE_fin0). exact EX.
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      goto (eapply UE_23304); [exact EX | | lia].
      intros ZI ZF.
      assert (SP' : (fL = 0 \/ (kI < L /\ tx bs kI = DP /\ kI + 1 + fL <= L /\ zeros bs (kI + 1) (kI + 1 + fL)))%Z).
      { destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; [left; exact F2|].
        destruct ZF as [F0|ZF]; [left; exact F0 | right].
        split; [exact F2|]. split; [exact F3|]. split; [lia | exact ZF]. }
      exact (strip_contra bs L k3 kI fL ks DP ltac:(lia) ltac:(lia) FL0 KS ZI SP' SCAN EXIT H20).
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23648"] Lemma UE_loopS : forall (n : nat) junk m (x1 x10 x20 x29 x30 x31 : word) k3 kI fp fL kp kq xn ks t0v,
      (L - ks <= Z.of_nat n)%Z ->
      uectx k3 kI fp fL kp kq junk m -> (- 2^32 < xn < 2^32)%Z -> (k3 <= ks < L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = DP) ->
      t0v = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z ->
      evt USEGS POST (UEST 0x25288 x1 (Zw t0v) (Zw 48) (Zw (-1)) x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
                           (Zw (P + ks)) x29 x30 x31 k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
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
      evt USEGS POST (UEST 0x252a4 x1 (Zw (t0v - is0)) (Zw 48) (Zw (-1)) x10 (Zw DP) (Zw xn) (Zw (P + kI)) x20
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
        goto (eapply UE_232fc with (ks := (ks + 1)%Z));
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
        goto (eapply UE_232fc with (ks := ks));
          [exact EX | lia | lia | exact SCAN | right; split; [exact H48 | exact Hdp]].
      + cond_cleanup Hdp.
        step. (* [comment removed for export] *)
        if_cases Hx; [|cond_cleanup Hx; exfalso; lia]. clear Hx.
        goto (eapply (TAIL 0%Z)); [rewrite (proj2 (Z.eqb_neq _ _) H48); reflexivity | right; exact Hdp].
  Qed.

  End E.

  #[using="PRE C_23648"] Lemma uspd_E : K_232bc c.
  Proof. LiaFast.lf_pins (fun (PRE C_23648 : LiaFast.U) => LiaFast.u0).
    unfold K_232bc. intros junk m x1 x6 x7 x8 x10 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 k3 kI fp fL kp kq xn
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
End U_spd_E.


Module U_spd_T0.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_236d0 : K_236d0 c.

  (* [comment removed for export] *)
  #[using="PRE C_236d0"] Lemma uspd_T0 : K_23648 c.
  Proof. LiaFast.lf_pins (fun (PRE C_236d0 : LiaFast.U) => LiaFast.u0).
    unfold K_236d0 in C_236d0.
    unfold K_23648. intros junk m x1 x5 x6 x7 x8 x13 x16 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 w q k3 kI fp fL kq tm
      PINV K3I K31 FL0 KQ FP TM TW.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    pose proof (tx_range bs 0) as R0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite v_sltiu_b2z.
    lazymatch goal with |- context [Zw (Z.b2z ?b)] =>
      pose proof (b2z_range b) as NG; set (ng := Z.b2z b) in *; clearbody ng end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit ng), (unsigned_lit 1), (unsigned_lit tm) in FR by lia.
    eapply C_236d0 with (ng := ng) (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (tm := tm).
    - split; [exact TXT|]. split; [cbv beta delta [frameT usaves app]; exact FR|].
      split; [unfold slow_path_double_need; exact ST|]. split; [exact VAL|].
      split; [exact PR1|]. split; [unfold U_FMIN_D; exact PR2|]. split; [exact MU | exact WM].
    - unfold pnsok. repeat split; try lia; intros H1; apply TW; exact H1.
  Qed.
End BLK.
End U_spd_T0.


Module U_spd_TD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_236f0 : K_236f0 c.
  Hypothesis C_23764 : K_23764 c.

  (* [comment removed for export] *)
  #[using="PRE C_236f0 C_23764"] Lemma uspd_TD : K_236d0 c.
  Proof. LiaFast.lf_pins (fun (PRE C_236f0 C_23764 : LiaFast.U) => LiaFast.u0).
    unfold K_236f0 in C_236f0. unfold K_23764 in C_23764.
    unfold K_236d0. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm TI PN.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      assert (TI2 : tinv c (frameT c j16 q w lm ng tm j5 k3 kI fp fL [C8 (Zw 0); CB 512 (skipn 8 r)]) m')
        by (split; [exact TXT|]; split; [cbv beta delta [frameT usaves app]; exact FR|];
            split; [unfold slow_path_double_need; exact ST|]; split; [exact VAL|];
            split; [exact PR1|]; split; [unfold U_FMIN_D; exact PR2|]; split; [exact MU | exact WM]) end.
    step. (* [comment removed for export] *)
    if_cases Htm3.
    { cond_cleanup Htm3. eapply C_23764; [exact TI2 | exact PN | lia]. }
    cond_cleanup Htm3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hq11.
    { eapply C_23764; [exact TI2 | exact PN | lia]. }
    cond_cleanup Hq11.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw24.
    { eapply C_23764; [exact TI2 | exact PN | lia]. }
    cond_cleanup Hw24.
    clear TI2. chunk_split FR 14%nat FRl FRh.
    eapply C_236f0; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM
                    | lia | | lia].
    - replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
    - (* [comment removed for export] *)
      rewrite SQ. destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
  Qed.
End BLK.
End U_spd_TD.


Module U_spd_PK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  (* [comment removed for export] *)
  #[using="PRE"] Lemma uspd_EPI : K_23ea0 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_23ea0. intros m cells F' fc' v' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 FRM' FRl SZ FRh ST VAL MU WM.
    pre_facts. cbv beta delta [usaves] in FRh. cbv beta delta [slow_path_double_W slow_path_double_need] in MU.
    unfold slow_path_double_need in ST.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRh by lia.
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply stk_release in FRl; [ | exact ST | lia ]. rewrite SZ in FRl. clear ST.
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRl by lia.
    eapply stk_release in FRh; [ | exact FRl | lia ]. cbn [cells_size csize Nat.add] in FRh. clear FRl.
    replace (bv_unsigned sp + -104 + Z.of_nat 104)%Z with (bv_unsigned sp) in FRh by lia.
    unfold slow_path_double_post. finish.
    all: try (unfold slow_path_double_need; exact FRh).
    all: try exact VAL.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE"] Lemma uspd_PK : K_23e64 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_23e64. intros m cells j16 x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 w q ng TXT FRl SZ FRh ST VAL PR1 PR2 MU WM NG.
    pre_facts. unfold slow_path_double_need in ST. unfold U_FMIN_D in PR2.
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    cbv beta delta [usaves] in FRh. cbn [app] in FRl.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      lazymatch goal with FR2 : rw_cells _ m' (bv_unsigned sp + -704) ?cs |- _ =>
        eapply (uspd_EPI m' cs); [exact FRM | exact FR2 | cbn [cells_size csize Nat.add app]; cbn [cells_size csize Nat.add] in SZ; lia
                                 | | exact ST | | exact MU | exact WM]
      end end.
    all: try (replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; first [exact FRh | assumption]).
    all: try assumption.
    all: match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => replace a with V in H by lia; exact H end.
  Qed.
End BLK.
End U_spd_PK.


Module U_spd_CL.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_23ea0 : K_23ea0 c.

  (* [comment removed for export] *)
  #[using="PRE C_23ea0"] Lemma uspd_CL : K_236f0 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23ea0 : LiaFast.U) => LiaFast.u0).
    unfold K_23ea0 in C_23ea0.
    unfold K_236f0. intros m cells x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q ng TXT FRl SZ FRh ST VAL PR1 PR2 MU WM NG Hq Hw.
    pre_facts. unfold slow_path_double_need in ST. unfold U_FMIN_D in PR2.
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU. cbv beta delta [usaves] in FRh.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [feq_s ?a ?b] => replace (feq_s a b) with true by (vm_compute; reflexivity) end.
    step. (* [comment removed for export] *)
    if_false.
    (* [comment removed for export] *)
    assert (TAIL : forall (m' : word -> option byte) (v' : word) (Fq : bvmap 5 word) (fcq : bv 32) (xa0 xa1 xa3 xs4 : word),
      frm0 fcq -> rw_cells USEGS m' SP cells -> rw_cells USEGS m' (bv_unsigned sp + -104)%Z (usaves c) ->
      stk USEGS m' (bv_unsigned sp - (704 + 1872)) SP -> rw_cells USEGS m' V [C8 v'] ->
      munch [((bv_unsigned sp - (704 + 1872))%Z, bv_unsigned sp); (V, (V + 8)%Z)] mI m' -> wmono USEGS mI m' ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 x8 x9 xa0 xa1 (Zw ng) xa3 x14 x15 x16 x17
                 x18 x19 xs4 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            Fq (Zw 0x25dcc) fcq None m' (seg_rom USEGS))).
    { intros m' v' Fq fcq xa0 xa1 xa3 xs4 FRMq FRl' FRh' ST' VAL' MU' WM'. cbv beta delta [usaves] in FRh'.
      pose proof (rw_cells_bound _ _ _ _ VAL') as Bval'. cbn [cells_size csize Nat.add] in Bval'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsgn.
      - eapply C_23ea0; [exact FRMq | exact FRl' | exact SZ | | exact ST' | | exact MU' | exact WM'].
        + replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh'.
        + match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => replace a with V in H by lia; exact H end.
      - step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_23ea0; [exact FRMq | exact FRl' | exact SZ | | exact ST' | | exact MU' | exact WM'].
        + replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh'.
        + match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => replace a with V in H by lia; exact H end. }
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z in FRh by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hneg.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q - 2^64)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      replace (Zw (89008 + bv_unsigned (Zw (0 - bv_unsigned q)) * 2 ^ 3))
        with (Zw (89008 + 8 * (2^64 - bv_unsigned q)))
        by (rewrite unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      lazymatch goal with H : pristine _ 65536 139264 |- _ =>
        pose proof (table_read USEGS _ _ _ _ _ _ _ TBLDU_ok H ltac:(lia) ltac:(cbn; lia) (2^64 - bv_unsigned q)%Z ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRl | exact FRh | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => replace a with V in H by lia; exact H end.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      replace (Zw (89008 + bv_unsigned (Zw (bv_unsigned q * 2 ^ 3))))
        with (Zw (89008 + 8 * bv_unsigned q))
        by (rewrite unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      lazymatch goal with H : pristine _ 65536 139264 |- _ =>
        pose proof (table_read USEGS _ _ _ _ _ _ _ TBLDU_ok H ltac:(lia) ltac:(cbn; lia) (bv_unsigned q) ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRl | exact FRh | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => replace a with V in H by lia; exact H end.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_23ea0"] Lemma uspd_ERRCL : K_236d8e c.
  Proof. LiaFast.lf_pins (fun (PRE C_23ea0 : LiaFast.U) => LiaFast.u0).
    unfold K_236d8e. intros junk m x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. pose proof PINV as PINV'. open_upinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hr; [exfalso; revert Hr; vm_compute; congruence|]. clear Hr.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; [exfalso; revert Hm; vm_compute; congruence|]. clear Hm.
    chunk_split FR 1%nat FRl FRh.
    eapply (uspd_CL m [CB 600 junk]) with (ng := 0%Z);
      [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM
      | lia | rewrite signed_lit by lia; lia | rewrite unsigned_lit by lia; lia].
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
  Qed.
End BLK.
End U_spd_CL.


Module U_spd_CF1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_23964 : K_23964 c.
  Hypothesis C_23e64 : K_23e64 c.

  (* [comment removed for export] *)
  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_23e64; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM | lia];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_23964 C_23e64"] Lemma uspd_CF1 : K_23764 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23964 C_23e64 : LiaFast.U) => LiaFast.u0).
    unfold K_23964 in C_23964. unfold K_23e64 in C_23e64.
    unfold K_23764. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm tf TI PN Htf.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (XF2 : forall (v5 v6 v7 v11 v13 v14 v15 v16 v17 v28 v29 v30 v31 am ap : word), tm = 1%Z ->
      (bv_signed q < -342 -> am = Zw 0 /\ ap = Zw 0)%Z -> (308 < bv_signed q -> am = Zw 0 /\ ap = Zw 2047)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) v13 v14 v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25918) fc None m (seg_rom USEGS))).
    { intros until am. intros ap Htm1 H1 H2. subst tm. eapply C_23964; [exact TI | exact PN | exact H1 | exact H2]. }
    (* [comment removed for export] *)
    assert (X60 : forall (v5 v6 v7 v13 v14 v15 v16 v17 v28 v29 v30 v31 am ap : word),
      (bv_signed q < -342 -> am = Zw 0 /\ ap = Zw 0)%Z -> (308 < bv_signed q -> am = Zw 0 /\ ap = Zw 2047)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw tf) (Zw ng) v13 v14 v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25914) fc None m (seg_rom USEGS))).
    { intros until am. intros ap H1 H2.
      step. (* [comment removed for export] *)
      if_cases Htf0.
      - exitPK.
      - cond_cleanup Htf0. apply XF2; [lia | exact H1 | exact H2]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw0.
    { cond_cleanup Hw0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htm1. { cond_cleanup Htm1. exfalso. lia. }
      step. (* [comment removed for export] *)
      exitPK. }
    cond_cleanup Hw0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo. apply X60; [intros _; split; reflexivity | intros HH; exfalso; lia]. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htm1.
      - cond_cleanup Htm1. apply XF2; [lia | intros HH; exfalso; lia | intros _; split; reflexivity].
      - step. (* [comment removed for export] *)
        exitPK. }
    cond_cleanup Hqhi.
    (* [comment removed for export] *)
    assert (X60' : forall (v5 v6 v7 v13 v14 v15 v16 v17 v28 v29 v30 v31 am ap : word),
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw tf) (Zw ng) v13 v14 v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25914) fc None m (seg_rom USEGS))).
    { intros. apply X60; intros HH; exfalso; lia. }
    clear X60 XF2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ucf_idx q) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    step. step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 9 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J884 : forall v5 v6 v7 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w (Zw tf) (Zw ng) v13 v14 v15 v16 v17
                 (Zw 0) (Zw 0) q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25838) fc None m (seg_rom USEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnorm.
      - clear Hnorm. (* [comment removed for export] *)
        do 12 gstep. (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (J910 : forall u5 u13 u14 u15 u16 u17 : word,
          evt USEGS POST
            (MS (mkR x1 (Zw SP) gp tp u5 v6 v7 x8 x9 w (Zw tf) (Zw ng) u13 u14 u15 u16 u17
                     (Zw 0) (Zw 0) q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
                F (Zw 0x258c4) fc None m (seg_rom USEGS))).
        { intros.
          do 13 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hinf.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply X60'.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply X60'. }
        step. (* [comment removed for export] *)
        if_cases Hre.
        + clear Hre. apply J910.
        + clear Hre.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          apply J910.
      - clear Hnorm. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          step. (* [comment removed for export] *)
          do 7 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htm1.
          * cond_cleanup Htm1. assert (Htm1' : tm = 1%Z) by lia. subst tm.
            eapply C_23964; [exact TI | exact PN | intros HH; exfalso; lia | intros HH; exfalso; lia].
          * step. (* [comment removed for export] *) exitPK.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htm1.
          * cond_cleanup Htm1. assert (Htm1' : tm = 1%Z) by lia. subst tm.
            eapply C_23964; [exact TI | exact PN | intros HH; exfalso; lia | intros HH; exfalso; lia].
          * step. (* [comment removed for export] *) exitPK. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J884. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J884.
  Qed.
End BLK.
End U_spd_CF1.


Module U_spd_CF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_23bb0 : K_23bb0 c.
  Hypothesis C_23e64 : K_23e64 c.

  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_23e64; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM | lia];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_23bb0 C_23e64"] Lemma uspd_CF2 : K_23964 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23bb0 C_23e64 : LiaFast.U) => LiaFast.u0).
    unfold K_23bb0 in C_23bb0. unfold K_23e64 in C_23e64.
    unfold K_23964. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ap ng k3 kI fp fL TI PN Hlo Hhi.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (XCE : forall (v5 v6 v7 v11 v13 v14 v15 v16 v17 v18 v19 v28 v29 v30 v31 : word),
      (-342 <= bv_signed q <= 308)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) v13 v14 v15 v16 v17
                 v18 v19 q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25b64) fc None m (seg_rom USEGS))).
    { intros. eapply C_23bb0; [exact TI | exact PN | assumption]. }
    (* [comment removed for export] *)
    assert (CMPC : forall (v5 v6 v7 v11 v14 v15 v16 v17 v28 v29 v30 v31 bp : word),
      ((ap <> bp) -> -342 <= bv_signed q <= 308)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) bp v14 v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25b60) fc None m (seg_rom USEGS))).
    { intros until bp. intros Hrg.
      step. (* [comment removed for export] *)
      if_cases Heq.
      - exitPK.
      - cond_cleanup Heq. apply XCE. apply Hrg. intros E'. apply Heq. rewrite E'. reflexivity. }
    assert (CMP8 : forall (v5 v6 v7 v11 v15 v16 v17 v28 v29 v30 v31 bm bp : word),
      ((am <> bm \/ ap <> bp) -> -342 <= bv_signed q <= 308)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) bp bm v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25b5c) fc None m (seg_rom USEGS))).
    { intros until bm. intros bp Hrg.
      step. (* [comment removed for export] *)
      if_cases Hne.
      - cond_cleanup Hne. apply XCE. apply Hrg. left. intros E'. apply Hne. rewrite E'. reflexivity.
      - apply CMPC. intros HH. apply Hrg. right. exact HH. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw1. { cond_cleanup Hw1. exfalso. Z.div_mod_to_equations. lia. }
    cond_cleanup Hw1. rewrite ?(unsigned_lit (bv_unsigned w + 1)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo. destruct (Hlo ltac:(lia)) as [-> ->].
      apply CMP8. intros [HH|HH]; exfalso; apply HH; reflexivity. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi. destruct (Hhi ltac:(lia)) as [-> ->].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; [| cond_cleanup Hz; exfalso; apply Hz; reflexivity].
      apply CMPC. intros HH; exfalso; apply HH; reflexivity. }
    cond_cleanup Hqhi. clear Hlo Hhi.
    (* [comment removed for export] *)
    assert (W1 : (0 <= bv_unsigned w + 1 < 2^64)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ucf_idx q) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 5 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J80 : forall v5 v6 v7 v11 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) v13 v14 v15 v16 v17
                 am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25a34) fc None m (seg_rom USEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnorm.
      - clear Hnorm. (* [comment removed for export] *)
        do 12 gstep.
        assert (J58 : forall u11 u13 u14 u15 u16 u17 u5 : word,
          evt USEGS POST
            (MS (mkR x1 (Zw SP) gp tp u5 v6 v7 x8 x9 w u11 (Zw ng) u13 u14 u15 u16 u17
                     am ap q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
                F (Zw 0x25b0c) fc None m (seg_rom USEGS))).
        { intros.
          do 13 gstep.
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hinf.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply CMP8. intros; lia.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            apply CMP8. intros; lia. }
        step. (* [comment removed for export] *)
        if_cases Hre.
        + clear Hre. apply J58.
        + clear Hre.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          apply J58.
      - clear Hnorm. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          step. (* [comment removed for export] *)
          do 7 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He1.
          * apply CMPC. intros; lia.
          * step. (* [comment removed for export] *) apply XCE. lia.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases He1.
          * apply CMPC. intros; lia.
          * step. (* [comment removed for export] *) apply XCE. lia. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J80. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J80.
  Qed.
End BLK.
End U_spd_CF2.


Module U_spd_CE.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : uspd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
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
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
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

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold U_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameT usaves app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_23cf4 : K_23cf4 c.
  Hypothesis C_23e64 : K_23e64 c.

  #[local] Ltac exitPK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -704) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 420760 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 14%nat FRl FRh;
    eapply C_23e64; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM | lia];
    replace (SP + 600)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_23cf4 C_23e64"] Lemma uspd_CE : K_23bb0 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23cf4 C_23e64 : LiaFast.U) => LiaFast.u0).
    unfold K_23cf4 in C_23cf4. unfold K_23e64 in C_23e64.
    unfold K_23bb0. intros m r j16 j5 x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL TI PN Hq.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    if_cases Hw0; [cond_cleanup Hw0; exfalso; lia|]. clear Hw0.
    step. (* [comment removed for export] *)
    rewrite (q342_word q).
    step. (* [comment removed for export] *)
    if_cases Hc1; [kill_chk Hc1|]. clear Hc1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (bv_signed q + 342)%Z) by lia. rewrite (swrap32_small (bv_signed q + 342 + 1073741824)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hc2; [kill_chk Hc2|]. clear Hc2.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (bv_signed q + 342)%Z) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    rewrite (swrap32_small ((bv_signed q + 342) * 2 ^ 1)%Z) by lia.
    replace (Zw ((bv_signed q + 342) * 2 ^ 1)) with (Zw (2 * bv_signed q + 684)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc3; [cond_cleanup Hc3; exfalso; rewrite ?Z.mod_small in Hc3 by lia; lia|]. clear Hc3.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    step. step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 9 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [Some (Zw (Z.shiftr (bv_unsigned ?rv) 56))] =>
      pose proof (bv_unsigned_in_range 64 rv) as Rlz; unfold bv_modulus in Rlz;
      remember (Z.shiftr (bv_unsigned rv) 56) as lz eqn:Hlz end.
    assert (LZ : (0 <= lz < 256)%Z) by (subst lz; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    clear Hlz Rlz.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (Jb4 : forall v5 v6 v7 v11 v13 v14 v15 v28 v29 v30 v31 hi : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 v6 v7 x8 x9 w v11 (Zw ng) v13 v14 v15 hi (Zw lz)
                 x18 x19 q x21 x22 a2 x24 x25 x26 x27 v28 v29 v30 v31)
            F (Zw 0x25c68) fc None m (seg_rom USEGS))).
    { intros.
      pose proof (bv_unsigned_in_range 64 hi) as Rhi. unfold bv_modulus in Rhi.
      step. (* [comment removed for export] *)
      rewrite (Z.add_0_r (bv_unsigned q)). rewrite (swrap32_unsigned q) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc4.
      { exfalso. cond_cleanup Hc4. apply Hc4. unfold bv_swrap, bv_wrap.
        replace (bv_half_modulus 32) with (2^31)%Z by reflexivity. replace (bv_modulus 32) with (2^32)%Z by reflexivity.
        Z.div_mod_to_equations. lia. }
      clear Hc4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Zw (bv_swrap 32 (Z.shiftr ?t 16)))] =>
        remember (bv_swrap 32 (Z.shiftr t 16)) as A eqn:HAe end.
      first [ pose proof (uce_A_range q ltac:(lia)) as HA; rewrite <- HAe in HA
            | pose proof (uce_A_range' q ltac:(lia)) as HA; rewrite <- HAe in HA
            | match type of HAe with ?ty => idtac "AFORM:" ty end ].
      clear HAe.
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit lz) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Zw (Z.shiftr (bv_unsigned ?rv) 63))] =>
        pose proof (bv_unsigned_in_range 64 rv) as Rhz; unfold bv_modulus in Rhz;
        remember (Z.shiftr (bv_unsigned rv) 63) as hz eqn:Hhz end.
      assert (HZ : (0 <= hz <= 1)%Z) by (subst hz; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
      clear Hhz Rhz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit hz) by lia.
      lazymatch goal with |- context [Some (Zw (bv_unsigned ?t - hz)%Z)] =>
        replace (Zw (bv_unsigned t - hz)%Z) with (Zw (A - lz - 31692 - hz))
          by (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia)
      | |- ?g => idtac "SUB2FORM" end.
      step. (* [comment removed for export] *)
      repeat match goal with |- context [Some (Zw (Z.shiftl ?a ?b))] => gen_val (Zw (Z.shiftl a b)) end.
      step. (* [comment removed for export] *)
      if_cases Hpos.
      - exitPK.
      - eapply C_23cf4; [exact TI | exact PN | exact Hq | lia]. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply Jb4. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply Jb4.
  Qed.
End BLK.
End U_spd_CE.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.U_spd_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_B OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_C OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_D OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_E OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_T0 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_TD OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_PK OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_CL OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_CF1 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_CF2 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double.U_spd_CE OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_DC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Main.
  Hypothesis positive_digit_comp_d_spec : positive_digit_comp_d_stmt.
  Hypothesis negative_digit_comp_d_spec : negative_digit_comp_d_stmt.

  #[using="positive_digit_comp_d_spec negative_digit_comp_d_spec"] Lemma slow_path_double_spec : slow_path_double_stmt.
  Proof. LiaFast.lf_pins (fun (positive_digit_comp_d_spec negative_digit_comp_d_spec : LiaFast.U) => LiaFast.u0).
    unfold slow_path_double_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v.
    intros TXT LEN RANGE ENW A5 VAL VAL8 ST AL LO P0 V0 VLO PR1 PR2 FRM SEP1 SEP2 SEP3.
    set (c := SPF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v).
    assert (PRE : uspd_pre c).
    { constructor; cbn; try assumption; try lia. }
    pose proof (uspd_EPI c PRE) as EPI.
    pose proof (uspd_PK c PRE) as PK.
    pose proof (uspd_DC c PRE positive_digit_comp_d_spec negative_digit_comp_d_spec PK) as DC.
    pose proof (uspd_CE c PRE DC PK) as CE.
    pose proof (uspd_CF2 c PRE CE PK) as CF2.
    pose proof (uspd_CF1 c PRE CF2 PK) as CF1.
    pose proof (uspd_CL c PRE EPI) as CL.
    pose proof (uspd_ERRCL c PRE EPI) as ERRCL.
    pose proof (uspd_TD c PRE CL CF1) as TD.
    pose proof (uspd_T0 c PRE TD) as T0.
    pose proof (uspd_E c PRE T0) as BE.
    pose proof (uspd_D c PRE BE ERRCL) as BD.
    pose proof (uspd_C c PRE BD ERRCL) as BC.
    pose proof (uspd_B c PRE BC) as BB.
    exact (uspd_A c PRE ERRCL BB).
  Qed.
End Main.
