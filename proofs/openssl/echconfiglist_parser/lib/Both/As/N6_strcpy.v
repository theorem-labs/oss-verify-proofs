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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_istrlen N6_strlen F_strcpy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac eassum := match goal with H : _ |- _ => exact H end.

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

Definition ASTRCPY_STUB : Z := 0x1a87ec.       (* [comment removed for export] *)
Definition ASTRCPY_ICPT : Z := 0x1b2cc8.
Definition ASTRCPY_STACK : Z := 8192.
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition astrcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - ASTRCPY_STACK, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at asegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack)
    /\ ACONST m'.
Definition strcpy_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (str slack junk : list byte) (lo : Z),
    bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) str ->
    ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) ->
    rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk] ->
    (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0
     \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1) ->
    accessible m (bv_unsigned a1) (Z.of_nat (length str) + 1) -> accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
    shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length str) + 1) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTRCPY_STACK ->
    mem_inv asegs m -> ACONST m ->
    Z.of_nat (length str) + 1 <= 2^40 ->
    in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length str) + 1) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
    aconst_ok (bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1) ->
    (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo) -> (bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo) ->
    rw_cells asegs m ASTRCPYP_CELL [C8 (Z_to_bv 64 AREAL_STRCPY)] -> rw_cells asegs m AF_REPSTR_CELL [C1 (Z_to_bv 8 1)] ->
    evt asegs (astrcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRCPY_STUB) fc None m (seg_rom asegs)).
End HCW.

Section STRCPY.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack junk : list byte) (lo : Z).
  Hypothesis STR : bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis DST : rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk].
  Hypothesis SEP : bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0
                   \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1.
  Hypothesis ACCS : accessible m (bv_unsigned a1) (Z.of_nat (length str) + 1).
  Hypothesis ACCD : accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Hypothesis SVS : shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length str) + 1).
  Hypothesis SVD : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ASTRCPY_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis N40 : Z.of_nat (length str) + 1 <= 2^40.
  Hypothesis INMS : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length str) + 1).
  Hypothesis INMD : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis AOK : aconst_ok (bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis DJS : bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo.
  Hypothesis DJD : bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo.
  Hypothesis RSC : rw_cells asegs m ASTRCPYP_CELL [C8 (Z_to_bv 64 AREAL_STRCPY)].
  Hypothesis CFR : rw_cells asegs m AF_REPSTR_CELL [C1 (Z_to_bv 8 1)].

  Notation dst := (bv_unsigned a0).
  Notation sa := (bv_unsigned a1).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (astrcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 8192, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (len + 1)) x20 s5 SP2 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold ASTRCPY_STACK, ASTRCPYP_CELL, AREAL_STRCPY, AF_REPSTR_CELL in *;
    pose proof INMS as INMS'; unfold in_app_mem, AHI_LO, AAPP_HI in INMS'; rewrite ASHADOW_BASE_val in INMS';
    pose proof INMD as INMD'; unfold in_app_mem, AHI_LO, AAPP_HI in INMD'; rewrite ASHADOW_BASE_val in INMD';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R;
    pose proof aceil_range as CLR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JE.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].

    Lemma asc_je : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b2dcc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (ACm : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [exact AOK|]. constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      do 4 zstep.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [eapply strcpy_spec;
          [ exact STRm| exact NONUL| exact PAD| exact DSTm| exact SEP
          | rewrite unsigned_lit by lia; lia| exact DJD| rewrite unsigned_lit by lia; exact STm
          | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MIm]
        | intros ms' PO; unfold strcpy_post in PO; zsimp_in PO; revert ms' PO; post_call asegs mc ] end.
      try rewrite unsigned_lit in * by lia.
      do 12 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _ |- _ =>
          release_frame FRx STx (bv_unsigned sp + -72) end;
        match goal with FRx : rw_cells asegs mx (bv_unsigned sp + -72) _, STx : stk asegs mx lo _ |- _ =>
          release_frame FRx STx (bv_unsigned sp) end;
        match goal with MUx : munch W m mx, WMx : wmono asegs m mx |- _ =>
          assert (AC' : ACONST mx)
            by (eapply ACONST_frame; [exact AC | exact MUx | exact WMx |];
                constructor; [exact AOK|]; constructor; [|constructor]; apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia) end
      end.
      unfold astrcpy_post. finish.
    Qed.
  End JE.

  Local Ltac goJE :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                       FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _ |- _ =>
        eapply (asc_je mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx] end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JRD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].

    Lemma asc_consts : ACONST mm /\ accessible mm dst (len + 1) /\ accessible mm sa (len + 1).
    Proof.
      prep. split; [|split].
      - eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [exact AOK|]. constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - eapply accessible_transport; [exact ACCD | exact MU |].
        intros x Hx. destruct ACCD as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia.
      - eapply accessible_transport; [exact ACCS | exact MU |].
        intros x Hx. destruct ACCS as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
        unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia.
    Qed.

    Lemma asc_jrd : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b3108 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep. destruct asc_consts as (ACm & ACCDm & ACCSm).
      do 2 zstep.
      zstep. call2 rip_body_w; try eassum; rewrite ?unsigned_lit by lia;
        [ exact ACCDm
        | lia
        | replace (dst + (len + 1)) with (dst + len + 1) by lia; exact INMD
        | exact STm
        | unfold RIP_STACK; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      goJE.
    Qed.
  End JRD.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JQD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis L64 : len + 1 <= 64.

    Local Ltac goJRD :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                         FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _ |- _ =>
          eapply (asc_jrd mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx] end
      end.

    (* [comment removed for export] *)
    Lemma asc_j5d : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b3100 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - goJE.
      - goJRD.
    Qed.

    Section LoopD.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh dst /\ sh (dst + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh dst /\ sh (dst + (len + 1) - 1) < 17594333495296.
      (* [comment removed for export] *)
      Lemma asc_loopd : forall (k : nat) (i : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
        Z.to_nat (sh (dst + (len + 1) - 1) - (sh dst + i)) = k -> 0 <= i -> sh dst + i < sh (dst + (len + 1) - 1) ->
        evt asegs POST (RST 0x1b30f0 x1 x5 x6 x7 (Z_to_bv 64 (sh dst + i)) (Z_to_bv 64 (sh (dst + (len + 1) - 1))) x12
                            x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh dst + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh dst + i + 1) with (sh dst + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (dst + (len + 1) - 1) - (sh dst + (i + 1))))); lia.
        - apply asc_j5d.
      Qed.
    End LoopD.

    Hypothesis SVm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + (len + 1)))).

    (* [comment removed for export] *)
    Lemma asc_jqd : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b2d94 x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (N64 : 1 <= len + 1 <= 64) by lia.
      destruct (hull_words dst (len + 1) ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app dst ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (dst + (len + 1) - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm dst (len + 1) ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh dst / 8) in *. set (q2 := sh (dst + (len + 1) - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh dst /\ sh (dst + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh dst /\ sh (dst + (len + 1) - 1) < 17594333495296) by lia.
      do 8 zstep. replace (len + dst) with (dst + (len + 1) - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
      - do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (dst + (len + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asc_j5d.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (asc_loopd q1 qj); first [eassum | reflexivity | lia].
        + goJE.
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (dst + (len + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asc_j5d.
          * replace (Z_to_bv 64 (sh dst)) with (Z_to_bv 64 (sh dst + 0)) by (f_equal; lia).
            eapply (asc_loopd q1 qj); first [eassum | reflexivity | lia].
        + goJE.
    Qed.
  End JQD.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + (len + 1)))).

    Lemma asc_jd : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b2d84 x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep.
      zstep. zstep. if_cases K1; zify_cond K1; rewrite ?lxor_ones64 in K1 by lia. { exfalso. lia. }
      zstep. zstep. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        zstep. if_cases K3; zify_cond K3; [| exfalso; lia].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                           FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _ |- _ =>
            eapply (asc_jrd mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx] end
        end.
      - eapply asc_jqd; try eassum. lia.
    Qed.
  End JD.

  (* [comment removed for export] *)
  Local Ltac svd_now :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
        let SVx := fresh "SVx" in
        assert (SVx : stk asegs mx (sh (hull_lo dst)) (sh (hull_hi (dst + (len + 1)))))
          by (pose proof SVD as SV0; unfold shvis in SV0; replace (dst + len + 1) with (dst + (len + 1)) in SV0 by lia;
              eapply stk_transport_disjoint; [exact SV0 | exact MUx | exact WMx |];
              unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]; constructor; [| constructor; [| constructor]];
              Z.div_mod_to_equations; lia) end end.
  Local Ltac goJD :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                       FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _,
                       G1x : rw_cells asegs mx 6191128 _, C1x : rw_cells asegs mx 6990072 _, SVx : stk asegs mx (sh (hull_lo dst)) _ |- _ =>
        eapply (asc_jd mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx | exact G1x | exact C1x | exact SVx] end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JRS.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].

    Lemma asc_jrs : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b3028 x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep. destruct (asc_consts mm MU WM) as (ACm & ACCDm & ACCSm).
      do 3 zstep.
      zstep. call2 rip_body_w; try eassum; rewrite ?unsigned_lit by lia;
        [ exact ACCSm
        | lia
        | replace (sa + (len + 1)) with (sa + len + 1) by lia; exact INMS
        | exact STm
        | unfold RIP_STACK; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      zstep. zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; lia].
      svd_now. goJD.
    Qed.
  End JRS.

  Local Ltac goJRS :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                       FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _,
                       G1x : rw_cells asegs mx 6191128 _, C1x : rw_cells asegs mx 6990072 _ |- _ =>
        eapply (asc_jrs mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx | exact G1x | exact C1x] end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JQS.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (S (length str)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis RSCm : rw_cells asegs mm 6203920 [C8 (Z_to_bv 64 5677152)].
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + (len + 1)))).
    Hypothesis L64 : len + 1 <= 64.

    (* [comment removed for export] *)
    Lemma asc_j5s : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b3020 x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - goJD.
      - goJRS.
    Qed.

    Section LoopS.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + (len + 1) - 1) < 17594333495296.
      (* [comment removed for export] *)
      Lemma asc_loops : forall (k : nat) (i : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
        Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + i)) = k -> 0 <= i -> sh sa + i < sh (sa + (len + 1) - 1) ->
        evt asegs POST (RST 0x1b3010 x1 x5 x6 x7 (Z_to_bv 64 len) (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + (len + 1) - 1))) x13
                            x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + (i + 1))))); lia.
        - apply asc_j5s.
      Qed.
    End LoopS.

    Hypothesis SVSm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + (len + 1)))).

    (* [comment removed for export] *)
    Lemma asc_jqs : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
      evt asegs POST (RST 0x1b2d4c x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (N64 : 1 <= len + 1 <= 64) by lia.
      destruct (hull_words sa (len + 1) ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app sa ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (sa + (len + 1) - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm sa (len + 1) ltac:(lia) N64 ltac:(lia) SVSm) as (qj & QW & QL & QL2).
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
          * apply asc_j5s.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asc_loops q1 qj); first [eassum | reflexivity | lia].
        + goJD.
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (len + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asc_j5s.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asc_loops q1 qj); first [eassum | reflexivity | lia].
        + goJD.
    Qed.
  End JQS.

  Lemma ACONST_layout_strcpy : ACONST m ->
    rw_cells asegs m 6993368 [C1 (b8 1); C1 (b8 1)] /\ rw_cells asegs m 6191120 [C8 (Z_to_bv 64 6979832)].
  Proof.
    intros ACx. change 6993368 with AINITED_CELL. change 6191120 with AGOT_FLAGS. change 6979832 with 0x6a80f8.
    split; (eapply ACONST_cell; [exact ACx| in_nth]).
  Qed.

  (* [comment removed for export] *)
  Lemma astrcpy_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRCPY_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold ASTRCPY_STUB. prep.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_strcpy AC) as (C5 & G6). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof ST0 as ST. carve_frame 72%nat ST. rename FR into FR1. carve_frame 2072%nat ST.
    zstep. (* [comment removed for export] *)
    do 12 zstep. (* [comment removed for export] *)
    do 2 zstep.  (* [comment removed for export] *)
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
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS (mkR ?x1 _ _ _ ?x5 ?x6 ?x7 _ _ _ _ _ ?x13 ?x14 ?x15 ?x16 ?x17 _ _ ?x20 _ _ ?x23 _ _ _ _ ?x28 ?x29 ?x30 ?x31) _ _ _ _ ?mc _) =>
      assert (J : forall x11 x12 : word, evt asegs POST (RST 0x1b2d3c x1 x5 x6 x7 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 mc)) end.
    { intros x11 x12.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K5; zify_cond K5; rewrite ?lxor_ones64 in K5 by lia. { exfalso. lia. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K6; zify_cond K6.
      - (* [comment removed for export] *)
        zstep. if_cases K7; zify_cond K7; [| exfalso; lia].
        goJRS.
      - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          match goal with MIx : mem_inv asegs mx, Sx : bytes_at asegs mx _ _, Dx : rw_cells asegs mx (bv_unsigned a0) _, F1x : rw_cells asegs mx (bv_unsigned sp + -72) _,
                           FRx : rw_cells asegs mx (bv_unsigned sp + -2144) _, STx : stk asegs mx lo _, MUx : munch _ m mx, WMx : wmono asegs m mx, Rx : rw_cells asegs mx 6203920 _,
                           G1x : rw_cells asegs mx 6191128 _, C1x : rw_cells asegs mx 6990072 _ |- _ =>
            eapply (asc_jqs mx); [exact MIx | exact Sx | exact Dx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx | exact Rx | exact G1x | exact C1x | | lia | ] end
        end.
        all: lazymatch goal with
             | |- stk asegs ?mx (sh (hull_lo dst)) _ =>
                 pose proof SVD as SV0; unfold shvis in SV0; replace (dst + len + 1) with (dst + (len + 1)) in SV0 by lia;
                 eapply stk_transport_disjoint; [exact SV0 | eassumption | eassumption |];
                 unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]; constructor; [| constructor; [| constructor]];
                 Z.div_mod_to_equations; lia
             | |- stk asegs ?mx (sh (hull_lo sa)) _ =>
                 pose proof SVS as SV0; unfold shvis in SV0; replace (sa + len + 1) with (sa + (len + 1)) in SV0 by lia;
                 eapply stk_transport_disjoint; [exact SV0 | eassumption | eassumption |];
                 unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]; constructor; [| constructor; [| constructor]];
                 Z.div_mod_to_equations; lia
             end. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases K3; zify_cond K3; [apply J|].
    zstep. zstep. if_cases K4; zify_cond K4; [exfalso; lia| apply J].
  Qed.
End STRCPY.

Section OK.
  Context {HCEIL : HeapCeil}.
  Lemma strcpy_icpt_ok : strcpy_icpt_stmt.
  Proof. unfold strcpy_icpt_stmt. intros. eapply astrcpy_body; eassumption. Qed.
End OK.
