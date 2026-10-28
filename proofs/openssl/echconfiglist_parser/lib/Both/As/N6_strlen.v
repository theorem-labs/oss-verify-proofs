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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset F_strlen.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asaninited_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (ret_pc ra) fc None m (seg_rom asegs).
Lemma asaninited_body : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv asegs m -> rw_cells asegs m 6993368 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)] ->
  evt asegs (asaninited_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c5a98) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI C5.
  do 6 zstep.
  match goal with |- context [Z_to_bv 64 (Z.b2z ?e)] =>
    replace (Z_to_bv 64 (Z.b2z e)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity) end.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tryinit_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp).
Lemma tryinit_body : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv asegs m -> rw_cells asegs m 6993368 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)] ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) -> 17594333495296 <= bv_unsigned sp - 16 ->
  evt asegs (tryinit_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c69a8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI C5 ST0 LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST0 as ST. carve_frame 16%nat ST.
  do 8 zstep.
  zstep. if_cases K; [exfalso|].
  { revert K. vm_compute. discriminate. }
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold tryinit_post. finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section STRLEN.
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
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : Z.of_nat (length str) + 1 <= 2^40.
  Hypothesis INM : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis DJ : bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis RSL : rw_cells asegs m ASTRLENP_CELL [C8 (Z_to_bv 64 AREAL_STRLEN)].
  Hypothesis CFI : rw_cells asegs m ACF_ISTRLEN_CELL [C1 (Z_to_bv 8 1)].

  Notation sa := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (astrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation SP4 := (Z_to_bv 64 (bv_unsigned sp + -2136)).
  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 a0 x19 SP4 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold AINTRIN_STACK, ASTRLENP_CELL, AREAL_STRLEN, ACF_ISTRLEN_CELL in *;
    pose proof INM as INM'; unfold in_app_mem, AHI_LO, AAPP_HI in INM'; rewrite ASHADOW_BASE_val in INM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R.

  (* [comment removed for export] *)
  Section JE.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
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
    Lemma asl_je : forall x1 x5 x6 x7 x28 x29 x30 x31 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22,
      evt asegs POST (RST 0x1a88b0 x1 x5 x6 x7 x9 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 mm).
    Proof.
      prep.
      do 11 zstep.
      release_frame FR STm (bv_unsigned sp + -64).
      release_frame FR1 STm (bv_unsigned sp).
      assert (AC' : ACONST mm)
        by (eapply ACONST_frame; [exact AC | exact MU | exact WM |];
            constructor; [|constructor];
            apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia).
      unfold astrlen_post. finish.
    Qed.

    (* [comment removed for export] *)
    Lemma asl_j3b8 : forall x1 x5 x6 x7 x28 x29 x30 x31 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22,
      evt asegs POST (RST 0x1a8a84 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 len) x22 x28 x29 x30 x31 mm).
    Proof. intros. zstep. zstep. apply asl_je. Qed.
  End JE.

  (* [comment removed for export] *)
  Section JR.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
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
    Lemma asl_jr : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22,
      evt asegs POST (RST 0x1a89c0 x1 x5 x6 x7 (Z_to_bv 64 (len + 1)) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 len) x22 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (ACm : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [|constructor].
        apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
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
      eapply asl_j3b8; [exact MI0 | exact STRm | exact FR1 | exact FR | exact PC | exact MU | exact WM].
    Qed.
  End JR.

  (* [comment removed for export] *)
  Section JQ.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
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
    Hypothesis L64 : len + 1 <= 64.

    (* [comment removed for export] *)
    Lemma asl_j5 : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22,
      evt asegs POST (RST 0x1a89b8 x1 x5 x6 x7 (Z_to_bv 64 (len + 1)) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 len) x22 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply asl_j3b8; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - eapply asl_jr; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact C1 | exact G2 | exact G3 | exact G4 | exact C4].
    Qed.

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + (len + 1) - 1) < 17594333495296.
      Lemma asl_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x28 x29 x30 x31 x10 x13 x14 x15 x16 x17 x19 x22,
        Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + i)) = k -> 0 <= i -> sh sa + i < sh (sa + (len + 1) - 1) ->
        evt asegs POST (RST 0x1a89a8 x1 x5 x6 x7 (Z_to_bv 64 (len + 1)) x10 (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + (len + 1) - 1)))
                            x13 x14 x15 x16 x17 x19 (Z_to_bv 64 len) x22 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x28 x29 x30 x31 x10 x13 x14 x15 x16 x17 x19 x22 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (sa + (len + 1) - 1) - (sh sa + (i + 1))))); lia.
        - apply asl_j5.
      Qed.
    End Loop.

    Hypothesis SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + (len + 1)))).

    (* [comment removed for export] *)
    Lemma asl_jq : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22,
      evt asegs POST (RST 0x1a8878 x1 x5 x6 x7 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 mm).
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
          do 7 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asl_j5.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asl_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply asl_je; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (len + 1) - 1)) ltac:(lia)) as RD.
          do 7 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asl_j5.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asl_loop q1 qj); first [eassumption | reflexivity | lia].
        + eapply asl_je; [exact MIm | exact STRm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
    Qed.
  End JQ.

  Lemma ACONST_layout_strlen : ACONST m ->
    rw_cells asegs m 6993368 [C1 (b8 1); C1 (b8 1)] /\ rw_cells asegs m 6191112 [C8 (Z_to_bv 64 7586856)].
  Proof.
    intros ACx. change 6993368 with AINITED_CELL. change 6191112 with AGOT_CFLAGS.
    split; (eapply ACONST_cell; [exact ACx| in_nth]).
  Qed.

  Lemma astrlen_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRLEN_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold ASTRLEN_STUB. prep.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_strlen AC) as (C5 & G6). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof SV as SVm. unfold shvis in SVm. replace (sa + len + 1) with (sa + (len + 1)) in SVm by lia.
    assert (SRV : 2147450880 <= sh (hull_lo sa) /\ sh (hull_hi (sa + (len + 1))) <= 17594333495296 + 16).
    { unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
    pose proof ST0 as ST. carve_frame 64%nat ST. rename FR into FR1. carve_frame 2080%nat ST.
    zstep. (* [comment removed for export] *)
    do 11 zstep.
    zstep. zstep. call_pure asaninited_body; [eassumption .. |].
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|].
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2144 - 16) _ ST ltac:(lia)) as [STlo SThi].
    zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2144 - 16) (bv_unsigned sp + -2144),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2144 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    do 4 zstep.
    zstep. call2 strlen_spec; try eassumption.
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
    do 3 zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 1)) with 1 by reflexivity.
    zstep. if_cases K2; [exfalso; revert K2; vm_compute; discriminate|].
    do 4 zstep.
    zstep. if_cases K3; zify_cond K3; rewrite lxor_ones64 in K3 by lia. { exfalso. lia. }
    zstep. zstep. if_cases K4; zify_cond K4.
    - zstep. zstep. if_cases K5; zify_cond K5; [| exfalso; lia].
      eapply asl_jr; [exact MI | exact POST | exact FR1 | exact FR | exact ST | exact MU | exact WM | exact G1 | exact C1 | exact G2 | exact G3 | exact G4 | exact C4].
    - eapply asl_jq; try eassumption. lia.
  Qed.

End STRLEN.
