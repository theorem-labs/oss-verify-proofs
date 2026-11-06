(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas B_long_mul_stmt B_pow10_stmt B_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_positive_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_hi64_stmt.B_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_f_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length in *) else idtac.      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)
Ltac open_fk5 H :=
  let a := fresh "FK1" in let b := fresh "FK2" in let c := fresh "FK3" in let d := fresh "FK4" in let e := fresh "FK5" in
  destruct H as (a & b & c & d & e); unfold fs_cells_ok in a.
Ltac close_fk5 := unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; eassumption.
Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

(* [comment removed for export] *)
Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
Ltac gen_big :=
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
  | |- context [Some (zx8 ?a)] => gen_val (zx8 a)
  | |- context [Some (zx16 ?a)] => gen_val (zx16 a)
  | |- context [Some (sx32 ?a)] => gen_val (sx32 a)
  end.
Ltac gstep := step; gen_big.

Lemma cb1_c1 : forall m A l, rw_cells BSEGS m A [CB 1 l] -> exists b, rw_cells BSEGS m A [C1 b].
Proof.
  intros m A l [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  destruct l as [|b [|]]; cbn in Hl; try discriminate.
  exists b. split; [split|]; [cbn; tauto | exact Hb | exact Hw].
Qed.

Section Main.
  Hypothesis pow10_spec : pow10_stmt.
  Hypothesis hi64_spec : hi64_stmt.
  Hypothesis ctlz_spec : ctlz_stmt.

  Notation SP' sp := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation BB := (Z_to_bv 64 ASAN_B).

  #[using="pow10_spec hi64_spec ctlz_spec"] Lemma positive_digit_comp_f_spec : positive_digit_comp_f_stmt.
  Proof. LiaFast.lf_pins (fun (pow10_spec hi64_spec ctlz_spec : LiaFast.U) => LiaFast.u0).
    unfold positive_digit_comp_f_stmt. intros until h5. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP CAP2 SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF SHS RTX0.
    pose proof (munch_refl (positive_digit_comp_f_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v)) m) as MU.
    cbv delta [positive_digit_comp_f_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    assert (BC : ro_cells BSEGS m 943736 [C8 (Z_to_bv 64 ASAN_B)]).
    { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app BSEGS m 943736 _ _) RT1)). }
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    open_fk5 FK.
    carve_frame 48%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply pow10_spec with (v := v) (h5 := h5) (ws := ws) (len := len) | post_call BSEGS mc ] end.
    1:{ rewrite ULs. replace (bv_unsigned sp + -48 - 2624)%Z with (bv_unsigned sp - 2672)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ exact He. } 1:{ exact CAP. } 1:{ exact CAP2. }
    1:{ rewrite ULs. lia. }
    1:{ exact TP. } 1:{ exact PRG. } 1:{ exact PRT. }
    1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    1:{ close_fk5. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite ULs. lia. } 1:{ exact SEPF. }
    1:{ rewrite ULs. eapply rt_disj_sub; [exact RD1 | lia | lia]. }
    1:{ exact RD2. } 1:{ exact RD3. }
    1:{ exact SHX. } 1:{ exact SHT. } 1:{ exact RBX. } 1:{ exact RBF. } 1:{ exact RTX0. }
    1:{ rewrite ULs. replace (bv_unsigned sp + -48 - 2624)%Z with (bv_unsigned sp - 2672)%Z by lia. eapply shz_sub; [exact SHS | lia | lia | lia]. }
    rewrite ?ULs in *.
    clear CAP CAP2 NORM.
    match goal with H : u64arr BSEGS _ (bv_unsigned a0) ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : length ws5 = 62%nat |- _ => rename H into L62' end.
    match goal with H : rw_cells BSEGS _ (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : (0 <= len5 <= 62)%Z |- _ => rename H into Hlen5 end.
    match goal with H : bnorm ws5 _ |- _ => rename H into BN5 end.
    match goal with H : stk BSEGS _ (bv_unsigned sp + -48 - 2624) _ |- _ => rename H into ST5 end.
    match goal with H : RT _ v |- _ => rename H into RTH5 end.
    match goal with H : pristine _ IMG_LO ROD_HI |- _ => rename H into PR5 end.
    match goal with H : fk5_inv _ (rt_FS v) ?hh |- _ => rename H into FK5'; rename hh into h5b end.
    try clear FK1; try clear FK2; try clear FK3; try clear FK4; try clear FK5. open_fk5 FK5'.
    name_mem m1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 2672, bv_unsigned sp)]%Z m1) as MU1.
    (* [comment removed for export] *)
    eapply (rw_cells_split_CB BSEGS m1 _ [] 16 _ _ [15; 1]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    chunk_split FR 1%nat FR15 FRr. chunk_split FRr 1%nat TB FRs.
    destruct (cb1_c1 _ _ _ TB) as [tb TB1]. clear TB.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -33) ltac:(lia)) as UL15.
    replace (bv_unsigned sp + -48 - 2624)%Z with (bv_unsigned sp - 2672)%Z in ST5 by lia.
    destruct (stk_split _ _ _ (bv_unsigned sp + -48 - 64)%Z _ ST5 ltac:(lia)) as [STlo SThi]. clear ST5.
    match goal with H : shz BSEGS m1 (ASAN_B + (bv_unsigned sp - 2672) / 8) 334 |- _ => rename H into SHS1 end.
    assert (SHB : shz BSEGS m1 (ASAN_B + (bv_unsigned sp + -33) / 8) 1).
    { eapply shz_sub; [exact SHS1 | | lia | ]; Z.div_mod_to_equations; lia. }
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply hi64_spec with (ws := ws5) (len := len5) (tb := tb) | post_call BSEGS mc ] end.
    1:{ exact XA5. } 1:{ exact L62'. } 1:{ exact LENC5. } 1:{ exact Hlen5. } 1:{ exact BN5. }
    1:{ rewrite UL15. exact TB1. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR5. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite UL15, ULs. lia. }
    1:{ rewrite UL15. lia. }
    1:{ exact PRG. } 1:{ exact BC. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite UL15. lia. } 1:{ rewrite UL15. lia. }
    1:{ exact SHX. }
    1:{ rewrite UL15. exact SHB. }
    rewrite ?ULs, ?UL15 in *.
    rename MI into Ht. rename PC into TB.
    first [ clear SThi; rename POST into SThi | rename POST into SThi ].
    name_mem m2.
    (* [comment removed for export] *)
    destruct (stk_split _ _ _ (bv_unsigned sp + -48 - 16)%Z _ SThi ltac:(lia)) as [STmid SThi2]. clear SThi. rename SThi2 into SThi.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply ctlz_spec with (ws := ws5) (len := len5) | post_call BSEGS mc ] end.
    1:{ exact XA5. } 1:{ exact L62'. } 1:{ exact LENC5. } 1:{ exact Hlen5. } 1:{ exact BN5. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR5. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PRG. } 1:{ exact BC. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ exact SHX. }
    rewrite ?ULs in *.
    rename MI into Hz. first [ clear SThi; rename POST into SThi | rename POST into SThi ].
    name_mem m3.
    pose proof (stk_merge _ _ _ _ _ STmid SThi ltac:(lia)) as SThi'. clear STmid SThi. rename SThi' into SThi.
    try clear ST. pose proof (stk_merge _ _ _ _ _ STlo SThi ltac:(lia)) as ST. clear STlo SThi.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (10:reg)) in
      let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in
      lazymatch v with Z_to_bv 64 ?z => rename z into zc end end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite (zx16_lit len5) by lia.
    step. (* [comment removed for export] *) rewrite (unsigned_lit len5) by lia. rewrite (Z.shiftl_mul_pow2 len5 6) by lia. change (2^6)%Z with 64%Z.
    step. (* [comment removed for export] *) rewrite word_sub_lit2.
    step. (* [comment removed for export] *) rewrite uw_sub2. rewrite (swrap32_id (len5 * 64 - zc)) by lia.
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *) rewrite uw_add, Z.add_0_r. rewrite (swrap32_id (len5 * 64 - zc)) by lia.
    step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (len5 * 64 - zc + -64)) by lia.
    step. (* [comment removed for export] *) trap_dead.
    step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (len5 * 64 - zc + -64 + 150)) by lia.
    step. (* [comment removed for export] *) trap_dead.
    set (P := (len5 * 64 - zc + 86)%Z) in *.
    assert (HP : (-170 <= P <= 4054)%Z) by (subst P; lia).
    step. (* [comment removed for export] *) rewrite (zxb_lit8 _) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) trap_dead.
    step. (* [comment removed for export] *) rewrite uw_sub. rewrite (swrap32_id (0 - P)) by lia.
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (POSTC := positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) v m).
    set (SPW := Z_to_bv 64 (bv_unsigned sp + -48)).
    assert (EPI : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt BSEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9d264) fc None m3 (seg_rom BSEGS))).
    { intros. subst POSTC SPW.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      chunk_join FR15 TB FRa. chunk_join FRa FRs FR.
      release_frame FR ST (bv_unsigned sp).
      unfold positive_digit_comp_f_post. finish.
      all: try eassumption. all: try lia.
      all: try (eapply RT_transport; [exact RTH5 | exact MU1 | solve_W_ok_rt]).
      all: try close_fk5. }
    assert (J5c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt BSEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9d25c) fc None m3 (seg_rom BSEGS))).
    { intros. subst SPW. do 2 gstep. apply EPI. }
    assert (J4c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt BSEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9d24c) fc None m3 (seg_rom BSEGS))).
    { intros. subst SPW. do 4 gstep. apply J5c. }
    assert (J24 : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt BSEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9d224) fc None m3 (seg_rom BSEGS))).
    { intros. subst SPW. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. gstep. gstep. step. apply J5c.
      - clear Hq. step. (* [comment removed for export] *) gstep. gstep. step. apply J5c. }
    assert (Jf8 : forall (q : Z) (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      (-2^20 <= q <= 2^20)%Z ->
      evt BSEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 (Z_to_bv 64 q) x12 x13 x14 x15 x16 x17 BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9d1f8) fc None m3 (seg_rom BSEGS))).
    { intros q. intros. subst SPW.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (q + 1)) by lia.
        step. (* [comment removed for export] *) trap_dead.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J24.
      - clear Hq. gstep. gstep. step. (* [comment removed for export] *) apply J24. }
    step. (* [comment removed for export] *)
    if_cases Hd.
    - (* [comment removed for export] *)
      cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (0 - P + 1)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (J8c : forall (sh : Z) (x1 x5 x6 x7 x8 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        (1 <= sh <= 64)%Z ->
        evt BSEGS POSTC
          (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 (Z_to_bv 64 sh) (Z_to_bv 64 P) (Z_to_bv 64 (0 - P + 1)) x14 x15 x16 x17
                   BB s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x9d18c) fc None m3 (seg_rom BSEGS))).
      { intros sh. intros. subst SPW.
        step. (* [comment removed for export] *) rewrite ?word_add_lit2.
        step. (* [comment removed for export] *) rewrite ?uw_add2. rewrite (swrap32_id (P + sh)) by lia.
        step. (* [comment removed for export] *) if_not_taken.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        do 10 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1. { clear Hb1. apply J4c. }
        clear Hb1. gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb2.
        + clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3. { clear Hb3. apply J4c. }
          clear Hb3. gstep. gstep. apply J4c.
        + clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3. { clear Hb3. step. step. apply J4c. }
          clear Hb3. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hb4. { clear Hb4. gstep. gstep. apply J4c. }
          clear Hb4. step. (* [comment removed for export] *) apply J4c. }
      step. (* [comment removed for export] *)
      if_cases Hs.
      + cond_cleanup Hs. apply J8c. lia.
      + cond_cleanup Hs. step. (* [comment removed for export] *) apply J8c. lia.
    - (* [comment removed for export] *)
      cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (P + 40)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb1. { clear Hb1. apply Jf8. lia. }
      clear Hb1.
      gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb2.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. apply Jf8. lia. }
        clear Hb3. gstep. gstep. apply Jf8. lia.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. step. step. apply Jf8. lia. }
        clear Hb3. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb4. { clear Hb4. gstep. gstep. apply Jf8. lia. }
        clear Hb4. step. (* [comment removed for export] *) apply Jf8. lia.
  Qed.
End Main.
