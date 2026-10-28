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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_memcpy N6_imm.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac eassum := match goal with H : _ |- _ => exact H end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition amemmove_entry := 0x1be18c%Z.

Section MEMMOVE.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte) (lo : Z).
  Hypothesis SRC : bytes_at asegs m (bv_unsigned a1) src.
  Hypothesis LEN : length src = Z.to_nat (bv_unsigned a2).
  Hypothesis DST : rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
  Hypothesis SEP : bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1.
  Hypothesis ACCS : accessible m (bv_unsigned a1) (bv_unsigned a2).
  Hypothesis ACCD : accessible m (bv_unsigned a0) (bv_unsigned a2).
  Hypothesis SVS : shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2).
  Hypothesis SVD : shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : bv_unsigned a2 <= 2^40.
  Hypothesis INMS : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2).
  Hypothesis INMD : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis AOK : aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2).
  Hypothesis DJD : bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis DJS : bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1.

  Notation dst := (bv_unsigned a0).
  Notation sa := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 src lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation SP4 := (Z_to_bv 64 (bv_unsigned sp + -2136)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 mm :=
    (MS (mkR x1 SP2 gp tp x5 t1 t2 sp x9 a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 SP4 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold AINTRIN_STACK in *;
    pose proof INMS as INMS'; unfold in_app_mem, AHI_LO, AAPP_HI in INMS'; rewrite ASHADOW_BASE_val in INMS';
    pose proof INMD as INMD'; unfold in_app_mem, AHI_LO, AAPP_HI in INMD'; rewrite ASHADOW_BASE_val in INMD';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R;
    pose proof (bv_unsigned_in_range 64 a2) as A2R; unfold bv_modulus in A2R; change (2 ^ Z.of_N 64) with (2^64) in A2R.

  (* [comment removed for export] *)
  Section JM.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
    Lemma amm_jm : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22,
      evt asegs POST (RST 0x1be26c x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 mm).
    Proof.
      prep.
      zstep. call2 imm_spec_sec; try eassum; [lia | lia |].
      do 11 zstep.
      release_frame FR STm (bv_unsigned sp + -64).
      release_frame FR1 STm (bv_unsigned sp).
      match goal with H : munch W m ?m' |- _ =>
        assert (AC' : ACONST m')
          by (eapply ACONST_frame; [exact AC | exact H | eassum |];
              constructor; [exact AOK|]; constructor; [|constructor];
              apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia) end.
      unfold amemmove_post. finish.
    Qed.
  End JM.

  (* [comment removed for export] *)
  Section JRD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    Lemma amm_consts : ACONST mm /\ accessible mm dst n /\ accessible mm sa n.
    Proof.
      prep. split; [|split].
      - eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [exact AOK|]; constructor; [|constructor].
        apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - eapply accessible_transport; [exact ACCD | exact MU |].
        intros x Hx. destruct ACCD as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. (first [clear - SR INMD' ACEILB LO CEIL; lia | lia]).
      - eapply accessible_transport; [exact ACCS | exact MU |].
        intros x Hx. destruct ACCS as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma amm_jrd : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22,
      evt asegs POST (RST 0x1be490 x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 mm).
    Proof.
      prep. destruct amm_consts as (ACm & ACCDm & ACCSm).
      do 4 zstep.
      zstep. call2 rip_body_w; try eassum;
        [ lia
        | rewrite unsigned_lit by lia; exact STm
        | unfold RIP_STACK; rewrite unsigned_lit by lia; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      do 4 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      eapply amm_jm; eassum.
    Qed.
  End JRD.

  (* [comment removed for export] *)
  Section JQD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis N64 : 1 <= bv_unsigned a2 <= 64.

    (* [comment removed for export] *)
    Lemma amm_j5d : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22,
      evt asegs POST (RST 0x1be488 x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply amm_jm; eassum.
      - eapply amm_jrd; eassum.
    Qed.

    Section LoopD.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh dst /\ sh (dst + n - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh dst /\ sh (dst + n - 1) < 17594333495296.
      Lemma amm_loopd : forall (k : nat) (i : Z) x1 x5 x9 x15 x16 x17 x18 x19 x21 x22,
        Z.to_nat (sh (dst + n - 1) - (sh dst + i)) = k -> 0 <= i -> sh dst + i < sh (dst + n - 1) ->
        evt asegs POST (RST 0x1be478 x1 x5 x9 (Z_to_bv 64 (sh dst + i)) (Z_to_bv 64 (sh (dst + n - 1))) x15 x16 x17
                            x18 x19 x21 x22 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x9 x15 x16 x17 x18 x19 x21 x22 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh dst + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh dst + i + 1) with (sh dst + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (dst + n - 1) - (sh dst + (i + 1))))); lia.
        - apply amm_j5d.
      Qed.
    End LoopD.

    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
    Lemma amm_jqd : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22,
      evt asegs POST (RST 0x1be230 x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 mm).
    Proof.
      prep.
      destruct (hull_words dst n ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app dst ltac:(unfold AAPP_HI; (first [clear - A2R INMD'; lia | lia]))) as SR1.
      pose proof (sh_range_app (dst + n - 1) ltac:(unfold AAPP_HI; (first [clear - INMD' N64; lia | lia]))) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm dst n ltac:(lia) N64 ltac:(lia) SVDm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh dst / 8) in *. set (q2 := sh (dst + n - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh dst /\ sh (dst + n - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh dst /\ sh (dst + n - 1) < 17594333495296) by lia.
      do 9 zstep. replace (dst + n + -1) with (dst + n - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
      - do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (dst + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply amm_j5d.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (amm_loopd q1 qj); first [eassum | reflexivity | lia].
        + eapply amm_jm; eassum.
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (dst + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply amm_j5d.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (amm_loopd q1 qj); first [eassum | reflexivity | lia].
        + eapply amm_jm; eassum.
    Qed.
  End JQD.

  (* [comment removed for export] *)
  Section JD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
    Lemma amm_jd : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x21 x22,
      evt asegs POST (RST 0x1be220 x1 x5 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (n + -65)) x21 x22 mm).
    Proof.
      prep.
      zstep. zstep. if_cases K1; zify_cond K1; rewrite lxor_ones64 in K1 by lia.
      { exfalso. lia. }
      zstep. zstep. if_cases K2; zify_cond K2; rewrite land_ones64 in K2.
      - zstep. if_cases K3; zify_cond K3.
        + eapply amm_jrd; eassum.
        + zstep. eapply amm_jm; eassum.
      - eapply amm_jqd; try eassum. Z.div_mod_to_equations. (first [clear - H0 H K2 A2R; lia | lia]).
    Qed.
  End JD.

  (* [comment removed for export] *)
  Section JS.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
    Lemma amm_jrs : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x21 x22,
      evt asegs POST (RST 0x1be3ec x1 x5 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (n + -65)) x21 x22 mm).
    Proof.
      prep. destruct (amm_consts mm MU WM) as (ACm & ACCDm & ACCSm).
      assert (SRV : 2147450880 <= sh (hull_lo dst) /\ sh (hull_hi (dst + n)) <= 17594333495296 + 16).
      { unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. (first [clear - H20 H19 H10 H5 H4 H0 H INMD'; lia | lia]). }
      do 5 zstep.
      zstep. call2 rip_body_w; try eassum;
        [ lia
        | rewrite unsigned_lit by lia; exact STm
        | unfold RIP_STACK; rewrite unsigned_lit by lia; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      do 4 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      eapply amm_jd; eassum.
    Qed.

    Hypothesis N64 : 1 <= bv_unsigned a2 <= 64.

    (* [comment removed for export] *)
    Lemma amm_j5s : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x21 x22,
      evt asegs POST (RST 0x1be3e4 x1 x5 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (n + -65)) x21 x22 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply amm_jd; eassum.
      - eapply amm_jrs; eassum.
    Qed.

    Section LoopS.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + n - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + n - 1) < 17594333495296.
      Lemma amm_loops : forall (k : nat) (i : Z) x1 x5 x9 x15 x16 x17 x18 x21 x22,
        Z.to_nat (sh (sa + n - 1) - (sh sa + i)) = k -> 0 <= i -> sh sa + i < sh (sa + n - 1) ->
        evt asegs POST (RST 0x1be3d4 x1 x5 x9 (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + n - 1))) x15 x16 x17
                            x18 (Z_to_bv 64 (n + -65)) x21 x22 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x9 x15 x16 x17 x18 x21 x22 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (sa + n - 1) - (sh sa + (i + 1))))); lia.
        - apply amm_j5s.
      Qed.
    End LoopS.

    Hypothesis SVSm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + n))).

    (* [comment removed for export] *)
    Lemma amm_jqs : forall x1 x5 x9 x13 x14 x15 x16 x17 x18 x21 x22,
      evt asegs POST (RST 0x1be1e4 x1 x5 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (n + -65)) x21 x22 mm).
    Proof.
      prep.
      destruct (hull_words sa n ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app sa ltac:(unfold AAPP_HI; (first [clear - A2R INMS'; lia | lia]))) as SR1.
      pose proof (sh_range_app (sa + n - 1) ltac:(unfold AAPP_HI; (first [clear - INMS' N64; lia | lia]))) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm sa n ltac:(lia) N64 ltac:(lia) SVSm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh sa / 8) in *. set (q2 := sh (sa + n - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh sa /\ sh (sa + n - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh sa /\ sh (sa + n - 1) < 17594333495296) by lia.
      do 9 zstep. replace (sa + n + -1) with (sa + n - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
      - do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply amm_j5s.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (amm_loops q1 qj); first [eassum | reflexivity | lia].
        + eapply amm_jd; eassum.
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + n - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply amm_j5s.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (amm_loops q1 qj); first [eassum | reflexivity | lia].
        + eapply amm_jd; eassum.
    Qed.
  End JS.

  Lemma amemmove_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 amemmove_entry) fc None m (seg_rom asegs)).
  Proof.
    unfold amemmove_entry. prep.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_flag m AC) as (G5 & C5). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof SVD as SVDm. unfold shvis in SVDm. pose proof SVS as SVSm. unfold shvis in SVSm.
    assert (SRV : 2147450880 <= sh (hull_lo dst) /\ sh (hull_hi (dst + n)) <= 17594333495296 + 16
                  /\ 2147450880 <= sh (hull_lo sa) /\ sh (hull_hi (sa + n)) <= 17594333495296 + 16).
    { unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. (first [clear - H45 H44 H35 H30 H29 H20 H15 H14 H10 H9 H5 H4 H0 H INMD' INMS'; lia | lia]). }
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LEN in SB.
    pose proof ST0 as ST. carve_frame 64%nat ST. rename FR into FR1. carve_frame 2080%nat ST.
    do 11 zstep.
    do 3 zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    do 3 zstep.
    zstep. if_cases K4; zify_cond K4; rewrite lxor_ones64 in K4 by lia. { exfalso. lia. }
    do 2 zstep.
    zstep. if_cases K5; zify_cond K5; rewrite land_ones64 in K5.
    - zstep. if_cases K6; zify_cond K6.
      + eapply amm_jrs; eassum.
      + zstep. eapply amm_jd; eassum.
    - eapply amm_jqs; try eassum. Z.div_mod_to_equations. (first [clear - H0 H K5 A2R; lia | lia]).
  Qed.
End MEMMOVE.
