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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_strlen F_memchr.
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

Definition AMEMCHR_STUB : Z := 0x1a8720.       (* [comment removed for export] *)
Definition AMEMCHR_ICPT : Z := 0x1ab110.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition amemchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) buf
    /\ ACONST m'.
Definition memchr_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list byte) (lo : Z),
    bytes_at asegs m (bv_unsigned a0) buf -> Z.of_nat (length buf) = bv_unsigned a2 -> 1 <= bv_unsigned a2 <= 2^40 -> 0 < bv_unsigned a0 ->
    accessible m (bv_unsigned a0) (bv_unsigned a2) ->
    shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
    mem_inv asegs m -> ACONST m ->
    in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    evt asegs (amemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMEMCHR_STUB) fc None m (seg_rom asegs)).
End HCW.

Lemma hull_hi_mono : forall x y, 0 <= x <= y -> hull_hi x <= hull_hi y.
Proof. intros x y H. unfold hull_hi. Z.div_mod_to_equations. lia. Qed.
Lemma sh_hull_lo_le_hi : forall a b, 0 <= a <= b -> sh (hull_lo a) <= sh (hull_hi b).
Proof. intros a b H. unfold sh, hull_lo, hull_hi. Z.div_mod_to_equations. lia. Qed.
Lemma sh_mono : forall x y, x <= y -> sh x <= sh y.
Proof. intros. unfold sh. Z.div_mod_to_equations. lia. Qed.

Section MEMCHR.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte) (lo : Z).
  Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
  Hypothesis LEN : Z.of_nat (length buf) = bv_unsigned a2.
  Hypothesis N1 : 0 <= bv_unsigned a2 <= 2^40.   (* [comment removed for export] *)
  Hypothesis A0P : 0 < bv_unsigned a0.
  Hypothesis ACC : accessible m (bv_unsigned a0) (bv_unsigned a2).
  Hypothesis SV : shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis INM : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis DJ : bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0.

  Notation sa := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation cc := (bv_unsigned a1 mod 256).
  Notation res := (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf).
  Notation POST := (amemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2128)).
  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x6 x7 kk x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp (Z_to_bv 64 kk) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 a0 a1 SP2 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold AINTRIN_STACK in *;
    pose proof INM as INM'; unfold in_app_mem, AHI_LO, AAPP_HI in INM'; rewrite ASHADOW_BASE_val in INM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R;
    pose proof aceil_range as CLR.

  Lemma res_facts : res = 0 \/ (sa <= res < sa + n).
  Proof.
    unfold memchr_res. destruct (find_byte cc (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [right| left; reflexivity].
    destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). rewrite length_firstn in Hi. pose proof N1. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JE.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis BUFm : bytes_at asegs mm (bv_unsigned a0) buf.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma amc_je : forall x1 x5 x6 x7 x28 x29 x30 x31 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21,
      evt asegs POST (MS (mkR x1 SP2 gp tp x5 x6 x7 sp x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x1ab1cc) fc None mm (seg_rom asegs)).
    Proof.
      prep.
      do 10 zstep.
      release_frame FR STm (bv_unsigned sp + -56).
      release_frame FR1 STm (bv_unsigned sp).
      assert (AC' : ACONST mm)
        by (eapply ACONST_frame; [exact AC | exact MU | exact WM |];
            constructor; [|constructor];
            apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia).
      unfold amemchr_post. finish.
    Qed.
  End JE.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section K.
    Variable k : Z.
    Hypothesis HK : 1 <= k <= n.

    (* [comment removed for export] *)
    Section JR.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis BUFm : bytes_at asegs mm (bv_unsigned a0) buf.
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.

      Lemma amc_jr : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x21,
        evt asegs POST (RST 0x1ab2f4 x1 x5 x6 x7 k x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 mm).
      Proof.
        prep.
        assert (ACm : ACONST mm).
        { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
          constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
        assert (ACCm : accessible mm sa k).
        { eapply accessible_transport; [eapply accessible_sub; [exact ACC | lia | lia | lia] | exact MU |].
          intros x Hx. destruct ACC as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
          unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia. }
        do 3 zstep.
        zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by lia;
          [ exact ACCm
          | lia
          | eapply in_app_mem_sub; [exact INM | lia | lia]
          | exact STm
          | unfold RIP_STACK; lia
          | unfold AHI_LO; lia
          | ].
        try rewrite unsigned_lit in * by lia.
        do 2 zstep.
        zstep. if_cases K; zify_cond K; [| exfalso; lia].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2128) _, STx : stk asegs mx lo _,
                           MUx : munch _ m mx, WMx : wmono asegs m mx, Sx : bytes_at asegs mx _ _, F1x : rw_cells asegs mx (bv_unsigned sp + -56) _ |- _ =>
            eapply (amc_je mx); [exact MIx | exact Sx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx] end
        end.
      Qed.
    End JR.

    (* [comment removed for export] *)
    Section JQ.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis BUFm : bytes_at asegs mm (bv_unsigned a0) buf.
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
      Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis L64 : k <= 64.

      Lemma amc_j5 : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x21,
        evt asegs POST (RST 0x1ab2ec x1 x5 x6 x7 k x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 mm).
      Proof.
        intros. zstep. zstep. if_cases K.
        - eapply amc_je; [exact MIm | exact BUFm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
        - eapply amc_jr; [exact MIm | exact BUFm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      Qed.

      Section Loop.
        Variables (q1 : Z) (qj : list byte).
        Hypothesis QA : u8arr asegs mm (8 * q1) qj.
        Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + k - 1) < 8 * q1 + Z.of_nat (length qj).
        Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + k - 1) < 17594333495296.
        (* [comment removed for export] *)
        Lemma amc_loop : forall (j : nat) (i : Z) x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17 x21,
          Z.to_nat (sh (sa + k - 1) - (sh sa + i)) = j -> 0 <= i -> sh sa + i < sh (sa + k - 1) ->
          evt asegs POST (RST 0x1ab2dc x1 x5 x6 x7 k (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + k - 1))) x13
                              x14 x15 x16 x17 x21 x28 x29 x30 x31 mm).
        Proof.
          induction j as [j IH] using lt_wf_ind; intros i x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17 x21 Hj Hi Hlt.
          pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
          do 3 zstep.
          zstep. if_cases K; zify_cond K.
          - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
            eapply (IH (Z.to_nat (sh (sa + k - 1) - (sh sa + (i + 1))))); lia.
          - apply amc_j5.
        Qed.
      End Loop.

      Hypothesis SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + k))).

      Lemma amc_jq : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x21,
        evt asegs POST (RST 0x1ab190 x1 x5 x6 x7 k x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 mm).
      Proof.
        prep.
        assert (N64 : 1 <= k <= 64) by lia.
        destruct (hull_words sa k ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
        pose proof (sh_range_app sa ltac:(unfold AAPP_HI; lia)) as SR1.
        pose proof (sh_range_app (sa + k - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
        unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
        destruct (hull_chunk mm sa k ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
        pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
        set (q1 := sh sa / 8) in *. set (q2 := sh (sa + k - 1) / 8) in *.
        assert (QB : 8 * q1 <= sh sa /\ sh (sa + k - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
        assert (SR12 : 2147450880 <= sh sa /\ sh (sa + k - 1) < 17594333495296) by lia.
        do 9 zstep. replace (sa + k + -1) with (sa + k - 1) by lia. rewrite !shr3_sh by lia.
        do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
        destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
        - do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (sa + k - 1)) ltac:(lia)) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply amc_j5.
            * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
              eapply (amc_loop q1 qj); first [eassumption | reflexivity | lia].
          + eapply amc_je; [exact MIm | exact BUFm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
        - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
          do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (sa + k - 1)) ltac:(lia)) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply amc_j5.
            * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
              eapply (amc_loop q1 qj); first [eassumption | reflexivity | lia].
          + eapply amc_je; [exact MIm | exact BUFm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      Qed.
    End JQ.

    (* [comment removed for export] *)
    Section J65.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis BUFm : bytes_at asegs mm (bv_unsigned a0) buf.
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2128) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2128).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
      Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + k))).

      Lemma amc_j65 : forall (kw : word) x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x21, kw = Z_to_bv 64 k ->
        evt asegs POST (MS (mkR x1 SP2 gp tp x5 x6 x7 sp kw (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 a0 a1 SP2 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x1ab184) fc None mm (seg_rom asegs)).
      Proof.
        intros kw. intros until x21. intros ->. revert x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x21.
        prep.
        do 2 zstep. zstep. if_cases K0; zify_cond K0.
        - (* [comment removed for export] *)
          zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
          eapply amc_jr; [exact MIm | exact BUFm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
        - eapply amc_jq; try eassumption. revert K0. rewrite ?unsigned_lit_wrap, ?land_ones64. intros K0. Z.div_mod_to_equations. lia.
      Qed.
    End J65.
  End K.

  Lemma ACONST_layout_memchr : ACONST m ->
    rw_cells asegs m 6993368 [C1 (b8 1); C1 (b8 1)] /\ rw_cells asegs m AMEMCHRP_CELL [C8 (wz AREAL_MEMCHR)].
  Proof. intros ACx. split; [exact (proj1 (ACONST_layout_strlen m ACx)) | exact (proj1 (ACONST_drv_reals m ACx))]. Qed.

  (* [comment removed for export] *)
  Lemma amemchr_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMEMCHR_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold AMEMCHR_STUB. prep.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_memchr AC) as (C5 & RM). change (b8 1) with (Z_to_bv 8 1) in C5.
    unfold AMEMCHRP_CELL, AREAL_MEMCHR, wz in RM.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as SB.
    pose proof res_facts as RF.
    pose proof ST0 as ST. carve_frame 56%nat ST. rename FR into FR1. carve_frame 2072%nat ST.
    zstep. (* [comment removed for export] *)
    do 10 zstep. (* [comment removed for export] *)
    do 3 zstep.  (* [comment removed for export] *)
    zstep. call_pure asaninited_body; [eassumption .. |].
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|].
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2128 - 16) _ ST ltac:(lia)) as [STlo SThi].
    zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2128 - 16) (bv_unsigned sp + -2128),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2128 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    do 2 zstep. (* [comment removed for export] *)
    do 4 zstep. (* [comment removed for export] *)
    zstep. call2 memchr_spec; try eassumption;
      [ unfold memchr_ok; rewrite <- LEN, Nat2Z.id, firstn_all;
        destruct (find_byte cc buf); [left; lia | lia] | ].
    try rewrite unsigned_lit in * by lia.
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct RF as [RF|RF]; [exfalso; rewrite RF in K2; apply K2; reflexivity|].
      do 2 zstep. rewrite ?land_ones64.
      try replace ((res - sa) mod 2 ^ 64 + 1) with (res - sa + 1) by (rewrite Z.mod_small by lia; lia).
      do 3 zstep. zstep. if_cases K3; zify_cond K3; rewrite ?lxor_ones64, ?land_ones64 in K3 by lia.
      2:{ exfalso. revert K3. rewrite ?Z.mod_small by lia. lia. }
      eapply (amc_j65 (res - sa + 1)); try eassumption; [lia| |reflexivity].
      replace (sa + (res - sa + 1)) with (res + 1) by lia.
      assert (SVk : stk asegs m (sh (hull_lo sa)) (sh (hull_hi (res + 1)))).
      { unfold shvis in SV. eapply (proj1 (stk_split asegs _ _ _ _ SV _)). Unshelve. split; [apply sh_hull_lo_le_hi; lia | apply sh_mono; apply hull_hi_mono; lia]. }
      eapply stk_transport_disjoint; [exact SVk | eassumption | eassumption |].
      unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]. constructor; [| constructor]. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      do 3 zstep. zstep. if_cases K3; zify_cond K3; rewrite ?lxor_ones64, ?land_ones64 in K3 by lia.
      { exfalso. lia. }
      destruct (Z.eq_dec n 0) as [N0|N0].
      { (* [comment removed for export] *)
        do 2 zstep. zstep. if_cases K5; zify_cond K5.
        2:{ exfalso. revert K5. rewrite ?unsigned_lit_wrap, ?land_ones64. intros K5. Z.div_mod_to_equations. lia. }
        zstep. if_cases K6; zify_cond K6; [exfalso; lia|].
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2128) _, STx : stk asegs mx lo _,
                           MUx : munch _ m mx, WMx : wmono asegs m mx, Sx : bytes_at asegs mx _ _, F1x : rw_cells asegs mx (bv_unsigned sp + -56) _ |- _ =>
            eapply (amc_je mx); [exact MIx | exact Sx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx] end
        end. }
      eapply (amc_j65 n); try eassumption; [lia| |symmetry; apply Z_to_bv_bv_unsigned].
      eapply stk_transport_disjoint; [unfold shvis in SV; exact SV | eassumption | eassumption |].
      unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]. constructor; [| constructor]. Z.div_mod_to_equations. lia.
  Qed.
End MEMCHR.

Section OK.
  Context {HCEIL : HeapCeil}.
  Lemma memchr_icpt_ok : memchr_icpt_stmt.
  Proof. unfold memchr_icpt_stmt. intros. eapply amemchr_body; try eassumption. lia. Qed.
  (* [comment removed for export] *)
  Lemma memchr_icpt0_ok :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a0) buf -> Z.of_nat (length buf) = bv_unsigned a2 -> 0 <= bv_unsigned a2 <= 2^40 -> 0 < bv_unsigned a0 ->
      accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      evt asegs (amemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMEMCHR_STUB) fc None m (seg_rom asegs)).
  Proof. intros. eapply amemchr_body; eassumption. Qed.
End OK.
