(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_istrlen N6_strlen N6_iface F_strrchr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_pure SPEC ::=
  eapply evt_cut; [ eapply SPEC | ];
  [ .. | let ms' := fresh "ms'" in let PO := fresh "POST" in
         intros ms' PO;
         (let T := type of PO in let h := head_of T in try unfold h in PO);
         destruct_exs PO; subst ms';
         try (lazymatch goal with
              | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
              end) ].

Definition ASTRRCHR_STUB : Z := 0x1a870c.       (* [comment removed for export] *)
Definition ASTRRCHR_ICPT : Z := 0x1a9b10.
(* [comment removed for export] *)
Definition ASTRRCHR_STACK : Z := 8192.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition astrrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (rfind_ret (bv_unsigned a0) (rfind (str ++ [Z_to_bv 8 0]) (Z_to_bv 8 (bv_unsigned a1)))))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ASTRRCHR_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack)
    /\ ACONST m'.
Definition strrchr_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (str slack : list byte) (lo : Z),
    bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) str ->
    ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) ->
    accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
    shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTRRCHR_STACK ->
    mem_inv asegs m -> ACONST m ->
    Z.of_nat (length str) + 1 <= 2^40 -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
    (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (* [comment removed for export] *)
    rw_cells asegs m ASTRRCHRP_CELL [C8 (Z_to_bv 64 AREAL_STRRCHR)] -> rw_cells asegs m ACF_ISTRCHR_CELL [C1 (Z_to_bv 8 1)] ->
    evt asegs (astrrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRRCHR_STUB) fc None m (seg_rom asegs)).
End HCW.

Section STRRCHR.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z).
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis ACC : accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Hypothesis SV : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ASTRRCHR_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis N40 : Z.of_nat (length str) + 1 <= 2^40.
  Hypothesis INM : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis DJ : bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis RSR : rw_cells asegs m ASTRRCHRP_CELL [C8 (Z_to_bv 64 AREAL_STRRCHR)].
  Hypothesis CFS : rw_cells asegs m ACF_ISTRCHR_CELL [C1 (Z_to_bv 8 1)].

  Notation sa := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (astrrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation CFP := (Z_to_bv 64 0x73c428).
  Notation W := [(bv_unsigned sp - 8192, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (len + 1)) s4 CFP SP2 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold ASTRRCHR_STACK, ASTRRCHRP_CELL, AREAL_STRRCHR, ACF_ISTRCHR_CELL in *;
    pose proof INM as INM'; unfold in_app_mem, AHI_LO, AAPP_HI in INM'; rewrite ASHADOW_BASE_val in INM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R;
    pose proof aceil_range as CLR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JE.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSRm : rw_cells asegs mm 6203496 [C8 (Z_to_bv 64 5678584)].

    Lemma asr_je : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9bc4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (ACm : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      assert (ACCm : accessible mm sa (len + 1)).
      { eapply accessible_transport; [exact ACC | exact MU |].
        intros x Hx. destruct ACC as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia. }
      assert (SVm : shvis mm sa (sa + len + 1)).
      { eapply shvis_transport; [exact SV | exact MU | exact WM |].
        unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]. constructor; [| constructor].
        Z.div_mod_to_equations. lia. }
      do 4 zstep.   (* [comment removed for export] *)
      zstep. call2 (astrrchr_real_body strlen_icpt_ok); try eassumption; rewrite ?unsigned_lit by lia;
        [ exact STm | unfold ASTRRCHR_REAL_STACK, AINTRIN_STACK; lia | lia | ].
      try rewrite unsigned_lit in * by lia.
      do 12 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _ |- _ =>
          release_frame FRx STx (bv_unsigned sp + -72) end;
        match goal with FRx : rw_cells asegs mx (bv_unsigned sp + -72) _, STx : stk asegs mx lo _ |- _ =>
          release_frame FRx STx (bv_unsigned sp) end;
        assert (AC' : ACONST mx) by assumption
      end.
      unfold astrrchr_post. finish.
    Qed.
  End JE.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JR.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSRm : rw_cells asegs mm 6203496 [C8 (Z_to_bv 64 5678584)].

    Lemma asr_jr : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9d28 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (ACm : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      assert (ACCm : accessible mm sa (len + 1)).
      { eapply accessible_transport; [exact ACC | exact MU |].
        intros x Hx. destruct ACC as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia. }
      do 2 zstep.
      zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by lia;
        [ exact ACCm
        | lia
        | replace (sa + (len + 1)) with (sa + len + 1) by lia; exact INM
        | exact STm
        | unfold RIP_STACK; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _,
                         MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203496 _, Sx : bytes_at asegs mx _ _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _ |- _ =>
          eapply (asr_je mx); [exact MIx | exact Sx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx] end
      end.
    Qed.
  End JR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JQ.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSRm : rw_cells asegs mm 6203496 [C8 (Z_to_bv 64 5678584)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis L64 : len + 1 <= 64.

    (* [comment removed for export] *)
    Lemma asr_j5 : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9d20 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply asr_je; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact RSRm].
      - eapply asr_jr; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact RSRm].
    Qed.

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + (len + 1) - 1) < 17594333495296.
      (* [comment removed for export] *)
      Lemma asr_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x28 x29 x30 x31 x12 x13 x14 x15 x16 x17,
        Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + i)) = k -> 0 <= i -> sh sa + i < sh (sa + (len + 1) - 1) ->
        evt asegs POST (RST 0x1a9d10 x1 x5 x6 x7 (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + (len + 1) - 1))) x12
                            x13 x14 x15 x16 x17 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x28 x29 x30 x31 x12 x13 x14 x15 x16 x17 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + (i + 1))))); lia.
        - apply asr_j5.
      Qed.
    End Loop.

    Hypothesis SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + (len + 1)))).

    (* [comment removed for export] *)
    Lemma asr_jq : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9b8c x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (N64 : 1 <= len + 1 <= 64) by lia.
      destruct (hull_words sa (len + 1) ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app sa ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (sa + (len + 1) - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm sa (len + 1) ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh sa / 8) in *. set (q2 := sh (sa + (len + 1) - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh sa /\ sh (sa + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh sa /\ sh (sa + (len + 1) - 1) < 17594333495296) by lia.
      do 8 zstep. replace (len + sa) with (sa + (len + 1) - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
      - do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (len + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asr_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_je; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact RSRm].
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (len + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asr_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_je; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact RSRm].
    Qed.
  End JQ.

  Lemma ACONST_layout_strrchr : ACONST m ->
    rw_cells asegs m 6993368 [C1 (b8 1); C1 (b8 1)] /\ rw_cells asegs m 6191112 [C8 (Z_to_bv 64 7586856)].
  Proof. intros ACx. exact (ACONST_layout_strlen m ACx). Qed.

  (* [comment removed for export] *)
  Lemma astrrchr_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRRCHR_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold ASTRRCHR_STUB. prep.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_strrchr AC) as (C5 & G6). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof SV as SVm. unfold shvis in SVm. replace (sa + len + 1) with (sa + (len + 1)) in SVm by lia.
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
    pose proof ST0 as ST. carve_frame 72%nat ST. rename FR into FR1. carve_frame 2072%nat ST.
    zstep. (* [comment removed for export] *)
    do 12 zstep. (* [comment removed for export] *)
    do 2 zstep.  (* [comment removed for export] *)
    zstep. call_pure asaninited_body; [eassumption .. |].
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|].
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2144 - 16) _ ST ltac:(lia)) as [STlo SThi].
    zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2144 - 16) (bv_unsigned sp + -2144),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2144 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
    do 2 zstep. (* [comment removed for export] *)
    zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 1)) with 1 by reflexivity.   (* [comment removed for export] *)
    zstep. if_cases K2; [exfalso; revert K2; vm_compute; discriminate|].
    do 2 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. call_pure istrlen_spec; [eassumption .. |].
    do 2 zstep. (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3; rewrite ?lxor_ones64 in K3 by lia. { exfalso. lia. }
    zstep. zstep. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5; [| exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _,
                         MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203496 _, Sx : bytes_at asegs mx _ _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _ |- _ =>
          eapply (asr_jr mx); [exact MIx | exact Sx | exact F1x | exact FRx | exact ST | exact MUx | exact WMx | exact Rx] end
      end.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _,
                         MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203496 _, Sx : bytes_at asegs mx _ _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                         G1x : rw_cells asegs mx 6191128 _, C1x : rw_cells asegs mx 6990072 _ |- _ =>
          eapply (asr_jq mx); [exact MIx | exact Sx | exact F1x | exact FRx | exact ST | exact MUx | exact WMx | exact Rx | exact G1x | exact C1x | lia | try eassumption ] end
      end.
      all: lazymatch goal with
           | |- stk asegs ?mx _ _ => replace (sa + (len + 1)) with (sa + len + 1) by lia; unfold shvis in SV;
               eapply stk_transport_disjoint; [exact SV | eassumption | eassumption |];
               unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]; constructor; [| constructor];
               Z.div_mod_to_equations; lia
           end.
  Qed.
End STRRCHR.

Section OK.
  Context {HCEIL : HeapCeil}.
  Lemma strrchr_icpt_ok : strrchr_icpt_stmt.
  Proof. unfold strrchr_icpt_stmt. intros. eapply astrrchr_body; eassumption. Qed.
End OK.
