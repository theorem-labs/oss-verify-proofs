(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma accessible_transport : forall W m m' a n,
  accessible m a n -> munch W m m' ->
  (forall x, a <= x < a + n -> outside W (sh x)) -> accessible m' a n.
Proof.
  intros W m m' a n (A0 & A1 & AA) MU OUT. split; [exact A0|]. split; [exact A1|].
  intros x Hx. destruct (AA x Hx) as (v & Hv & RD & OK). exists v. split; [exact Hv|]. split; [|exact OK].
  unfold mrd in *. rewrite MU; [exact RD|]. unfold wa.
  pose proof (sh_range_app x ltac:(lia)) as SR. unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR.
  rewrite unsigned_lit by lia. apply OUT. exact Hx.
Qed.

Lemma accessible_transport_stack : forall slo shi m m' a n,
  accessible m a n -> munch [(slo, shi)] m m' -> AHI_LO <= slo -> accessible m' a n.
Proof.
  intros slo shi m m' a n ACC MU LO. eapply accessible_transport; [exact ACC | exact MU |].
  intros x Hx. destruct ACC as (A0 & A1 & _). pose proof (sh_range_app x ltac:(lia)) as SR. cbn. split; [|exact I]. lia.
Qed.

Lemma ACONST_transport_stack : forall slo shi m m',
  ACONST m -> munch [(slo, shi)] m m' -> wmono asegs m m' -> AHI_LO <= slo -> ACONST m'.
Proof.
  intros slo shi m m' AC MU WM LO. eapply ACONST_frame; [exact AC | exact MU | exact WM |].
  constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP, AHI_LO in *; rewrite ?ASHADOW_BASE_val; lia.
Qed.

(* [comment removed for export] *)
Lemma ACONST_layout_memset : forall m, ACONST m ->
  rw_cells asegs m 6194080 [C8 (Z_to_bv 64 6993369)] /\ rw_cells asegs m 6993368 [C1 (b8 1); C1 (b8 1)] /\
  rw_cells asegs m 6204016 [C8 (Z_to_bv 64 5676560)].
Proof.
  intros m AC.
  change 6194080 with AGOT_RINTRIN. change 6993369 with ARINTRIN_CELL. change 6993368 with AINITED_CELL.
  change 6204016 with AMEMSETP_CELL. change 1348780 with AREAL_MEMSET.
  repeat split; (eapply ACONST_cell; [exact AC| in_nth]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition amemset_entry := 0x1bdf4c%Z.

Section MEMSET.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (junk : list byte) (lo : Z).
  Hypothesis A1 : a1 = Z_to_bv 64 c.
  Hypothesis Hc : 0 <= c < 256.
  Hypothesis DST : rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
  Hypothesis ACC : accessible m (bv_unsigned a0) (bv_unsigned a2).
  Hypothesis SV : shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : bv_unsigned a2 <= 2^40.
  Hypothesis INM : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis AOK : aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2).
  Hypothesis DJ : bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0.   (* [comment removed for export] *)

  Notation dst := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation POST := (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 c lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2128)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation RST pc x1 x5 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 mm :=
    (MS (mkR x1 SP2 gp tp x5 t1 t2 sp x9 a0 x11 a2 x13 x14 x15 x16 x17 x18 x19 SP2 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 4096, bv_unsigned sp)].

  Section J.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis C6 : rw_cells asegs mm 6204016 [C8 (Z_to_bv 64 5676560)].

    (* [comment removed for export] *)
    Lemma ams_jm : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21,
      evt asegs POST (RST 0x1bdfdc x1 x5 x9 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 mm).
    Proof.
      intros. acb; unfold AINTRIN_STACK in *.
      pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. change (2 ^ Z.of_N 64) with (2^64) in A0R.
      pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. change (2 ^ Z.of_N 64) with (2^64) in A2R.
      do 3 zstep.
      call2 memset_spec; try eassumption.
      match goal with H : rw_cells asegs _ dst _ |- _ => rewrite (Z.mod_small c 256) in H by lia; rename H into DST' end.
      do 10 zstep.
      release_frame FR STm (bv_unsigned sp + -56).
      release_frame FR1 STm (bv_unsigned sp).
      match goal with H : munch W m ?m' |- _ =>
        assert (AC' : ACONST m')
          by (eapply ACONST_frame; [exact AC | exact H | eassumption |];
              constructor; [exact AOK|]; constructor; [|constructor];
              apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia) end.
      unfold amemset_post. finish.
    Qed.
  End J.

  Section JR.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis C6 : rw_cells asegs mm 6204016 [C8 (Z_to_bv 64 5676560)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
    Lemma ams_jr : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21,
      evt asegs POST (RST 0x1be120 x1 x5 x9 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 mm).
    Proof.
      intros. acb; unfold AINTRIN_STACK in *.
      pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. change (2 ^ Z.of_N 64) with (2^64) in A0R.
      pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. change (2 ^ Z.of_N 64) with (2^64) in A2R.
      assert (ACm : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [exact AOK|]; constructor; [|constructor].
        apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      assert (ACCm : accessible mm dst n).
      { eapply accessible_transport; [exact ACC | exact MU |].
        intros x Hx. destruct ACC as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia. }
      do 4 zstep.
      zstep. call2 rip_body_w; try eassumption;
        [ lia
        | rewrite unsigned_lit by lia; exact STm
        | unfold RIP_STACK; rewrite unsigned_lit by lia; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      do 4 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      eapply ams_jm; [exact MI0 | exact DSTm | exact FR1 | exact FR | exact PC | exact MU | exact WM | exact C6].
    Qed.
  End JR.


  Section JQ.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis C6 : rw_cells asegs mm 6204016 [C8 (Z_to_bv 64 5676560)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis N64 : 1 <= bv_unsigned a2 <= 64.

    (* [comment removed for export] *)
    Lemma ams_j5 : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21,
      evt asegs POST (RST 0x1be118 x1 x5 x9 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 mm).
    Proof.
      intros.
      zstep. zstep. if_cases K.
      - eapply ams_jm; [exact MIm | exact DSTm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact C6].
      - eapply ams_jr; [exact MIm | exact DSTm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact C6 | exact G1 | exact C1 | exact G2 | exact G3 | exact G4 | exact C4].
    Qed.

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh dst /\ sh (dst + n - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh dst /\ sh (dst + n - 1) < 17594333495296.

      Lemma q_read : forall x, 8 * q1 <= x < 8 * q1 + Z.of_nat (length qj) ->
        ov_read_bytes asegs mm (wa x) 1 = Some [nth (Z.to_nat (x - 8 * q1)) qj (b8 0)].
      Proof.
        intros x Hx. eapply (u8arr_read asegs mm (8 * q1) qj (x - 8 * q1)); [exact QA | | lia | f_equal; lia].
        apply nth_error_nth'. lia.
      Qed.

      (* [comment removed for export] *)
      Lemma ams_loop : forall (k : nat) (i : Z) x1 x5 x9 x15 x16 x17 x18 x19 x21,
        Z.to_nat (sh (dst + n - 1) - (sh dst + i)) = k -> 0 <= i -> sh dst + i < sh (dst + n - 1) ->
        evt asegs POST (RST 0x1be108 x1 x5 x9 (Z_to_bv 64 c) (Z_to_bv 64 (sh dst + i)) (Z_to_bv 64 (sh (dst + n - 1)))
                            x15 x16 x17 x18 x19 x21 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x9 x15 x16 x17 x18 x19 x21 Hk Hi Hlt.
        pose proof (q_read (sh dst + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh dst + i + 1) with (sh dst + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (dst + n - 1) - (sh dst + (i + 1))))); lia.
        - apply ams_j5.
      Qed.
    End Loop.

    Hypothesis SVm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
    Lemma ams_jq : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21,
      evt asegs POST (RST 0x1bdfa0 x1 x5 x9 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 mm).
    Proof.
      intros. acb; unfold AINTRIN_STACK in *.
      pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. change (2 ^ Z.of_N 64) with (2^64) in A0R.
      destruct (hull_words dst n ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app dst ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (dst + n - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      rewrite HLO, HHI in SVm.
      set (q1 := sh dst / 8) in *. set (q2 := sh (dst + n - 1) / 8) in *.
      do 9 zstep. replace (dst + n + -1) with (dst + n - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      (* [comment removed for export] *)
      assert (QX : exists qj, rw_cells asegs mm (8 * q1) [CB (length qj) qj] /\ 8 * q2 + 8 = 8 * q1 + Z.of_nat (length qj)
                              /\ (length qj = 8%nat \/ length qj = 16%nat)).
      { destruct HQ2 as [E|E]; rewrite E in SVm |- *.
        - destruct (stk_carve asegs mm _ _ 8 SVm ltac:(lia)) as [_ [qj QW]].
          replace (8 * q1 + 8 - Z.of_nat 8) with (8 * q1) in QW by lia.
          pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| left; reflexivity].
        - destruct (stk_carve asegs mm _ _ 16 SVm ltac:(lia)) as [_ [qj QW]].
          replace (8 * (q1 + 1) + 8 - Z.of_nat 16) with (8 * q1) in QW by lia.
          pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| right; reflexivity]. }
      destruct QX as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      assert (QB : 8 * q1 <= sh dst /\ sh (dst + n - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh dst /\ sh (dst + n - 1) < 17594333495296) by lia.
      destruct HQ2 as [E|E]; rewrite E in QL |- *.
      - destruct QL2 as [L|L]; rewrite L in QW, QL; [|exfalso; lia].
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read q1 qj QA (sh (dst + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply ams_j5.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (ams_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply ams_jm; [exact MIm | exact DSTm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact C6].
      - destruct QL2 as [L|L]; rewrite L in QW, QL; [exfalso; lia|].
        replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read q1 qj QA (sh (dst + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply ams_j5.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (ams_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply ams_jm; [exact MIm | exact DSTm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact C6].
    Qed.
  End JQ.

  Lemma amemset_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 amemset_entry) fc None m (seg_rom asegs)).
  Proof.
    unfold amemset_entry. rewrite A1. pose proof LO as LO'. unfold AINTRIN_STACK in LO. pose proof CEIL as CEIL'. acb.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_memset m AC) as (G5 & C5 & C6). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM. rewrite ASHADOW_BASE_val in INM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. change (2 ^ Z.of_N 64) with (2^64) in A0R.
    pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. change (2 ^ Z.of_N 64) with (2^64) in A2R.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof SV as SVm. unfold shvis in SVm.
    assert (SR0 : 2147450880 <= sh (hull_lo dst) /\ sh (hull_hi (dst + n)) <= 17594333495296 + 16).
    { unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    pose proof ST0 as ST. carve_frame 56%nat ST. rename FR into FR1. carve_frame 2072%nat ST.
    do 10 zstep.
    do 3 zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    do 3 zstep.
    zstep. if_cases K1; zify_cond K1; rewrite lxor_ones64 in K1 by lia.
    { exfalso. lia. }
    do 2 zstep.
    zstep. if_cases K2; zify_cond K2; rewrite land_ones64 in K2.
    - zstep. if_cases K3; zify_cond K3.
      + eapply ams_jr; [exact MI | exact DST | exact FR1 | exact FR | exact ST | exact MU | exact WM | exact C6 | exact G1 | exact C1 | exact G2 | exact G3 | exact G4 | exact C4].
      + zstep. eapply ams_jm; [exact MI | exact DST | exact FR1 | exact FR | exact ST | exact MU | exact WM | exact C6].
    - eapply ams_jq; try eassumption. Z.div_mod_to_equations. lia.
  Qed.
End MEMSET.
