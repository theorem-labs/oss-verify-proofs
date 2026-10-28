(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_istrlen N6_strlen N6_iface F_strspn.
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

Definition ASTRSPN_STUB : Z := 0x1a8710.       (* [comment removed for export] *)
Definition ASTRSPN_ICPT : Z := 0x1a9df0.
Definition ASTRSPN_STACK : Z := 8192.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition astrspn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (str acc : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (spn str acc))) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ASTRSPN_STACK, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ACONST m'.

(* [comment removed for export] *)
Definition strspn_icpt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (str sslack acc aslack : list byte) (lo can : Z),
    bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: sslack) -> ~ In (Z_to_bv 8 0) str ->
    bytes_at asegs m (bv_unsigned a1) (acc ++ Z_to_bv 8 0 :: aslack) -> ~ In (Z_to_bv 8 0) acc -> (2 <= length acc)%nat ->
    accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) -> accessible m (bv_unsigned a1) (Z.of_nat (length acc) + 1) ->
    shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) -> shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length acc) + 1) ->
    in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) -> in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length acc) + 1) ->
    Z.of_nat (length str) + 1 <= 2^40 -> Z.of_nat (length acc) + 1 <= 2^40 ->
    (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length sslack) <= lo) ->
    (bv_unsigned a1 + Z.of_nat (length acc) + 1 + Z.of_nat (length aslack) <= lo) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTRSPN_STACK -> bv_unsigned sp + 8 <= 2^64 ->
    mem_inv asegs m -> ACONST m ->
    rw_cells asegs m AGOT_SSP_CELL [C8 (wz ACANARY_CELL)] -> rw_cells asegs m ACANARY_CELL [C8 (wz can)] -> 0 <= can < 2^64 ->
    evt asegs (astrspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str acc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRSPN_STUB) fc None m (seg_rom asegs)).
End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STRSPN.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str sslack acc aslack : list byte) (lo can : Z).
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: sslack).
  Hypothesis SNONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis ACS : bytes_at asegs m (bv_unsigned a1) (acc ++ Z_to_bv 8 0 :: aslack).
  Hypothesis ANONUL : ~ In (Z_to_bv 8 0) acc.
  Hypothesis ALEN : (2 <= length acc)%nat.
  Hypothesis ACC1 : accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Hypothesis ACC2 : accessible m (bv_unsigned a1) (Z.of_nat (length acc) + 1).
  Hypothesis SV1 : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis SV2 : shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length acc) + 1).
  Hypothesis INM1 : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis INM2 : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length acc) + 1).
  Hypothesis N40a : Z.of_nat (length str) + 1 <= 2^40.
  Hypothesis N40b : Z.of_nat (length acc) + 1 <= 2^40.
  Hypothesis DJ1 : bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length sslack) <= lo.
  Hypothesis DJ2 : bv_unsigned a1 + Z.of_nat (length acc) + 1 + Z.of_nat (length aslack) <= lo.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ASTRSPN_STACK.
  Hypothesis SPH : bv_unsigned sp + 8 <= 2^64.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis GOTC : rw_cells asegs m AGOT_SSP_CELL [C8 (wz ACANARY_CELL)].
  Hypothesis CAN : rw_cells asegs m ACANARY_CELL [C8 (wz can)].
  Hypothesis CANR : 0 <= can < 2^64.

  Notation sa := (bv_unsigned a0).
  Notation ca := (bv_unsigned a1).
  Notation L := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length acc)).
  Notation r := (Z.of_nat (spn str acc)).
  Notation POST := (astrspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str acc lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2160)).
  Notation S6V := (Z_to_bv 64 (bv_unsigned sp + -2152)).
  Notation CFP := (Z_to_bv 64 0x73c428).
  Notation W := [(bv_unsigned sp - 8192, bv_unsigned sp)].
  Notation RST pc x1 x5 x6 x7 xs1 x10 x11 x12 x13 x14 x15 x16 x17 xs2 xs3 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp xs1 x10 x11 x12 x13 x14 x15 x16 x17 xs2 xs3 s4 (Z_to_bv 64 r) S6V CFP s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold ASTRSPN_STACK, ASTRSPNP_CELL, AREAL_STRSPN, ACF_ISTRSPN_CELL, ACF_STRICT_CELL in *;
    pose proof INM1 as INM1'; unfold in_app_mem, AHI_LO, AAPP_HI in INM1'; rewrite ASHADOW_BASE_val in INM1';
    pose proof INM2 as INM2'; unfold in_app_mem, AHI_LO, AAPP_HI in INM2'; rewrite ASHADOW_BASE_val in INM2';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R;
    pose proof (spn_le str acc) as RLE;
    pose proof aceil_range as CLR.

  (* [comment removed for export] *)
  Section MM.
    Variable mm : word -> option byte.
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Lemma ACm : ACONST mm.
    Proof.
      prep. eapply ACONST_frame; [exact AC | exact MU | exact WM |].
      constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
    Qed.
    Lemma ACC1m : accessible mm sa (L + 1).
    Proof.
      prep. eapply accessible_transport; [exact ACC1 | exact MU |].
      intros x Hx. destruct ACC1 as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
      unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia.
    Qed.
    Lemma ACC2m : accessible mm ca (N + 1).
    Proof.
      prep. eapply accessible_transport; [exact ACC2 | exact MU |].
      intros x Hx. destruct ACC2 as (? & ? & _). pose proof (sh_range_app x ltac:(lia)) as SR.
      unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. lia.
    Qed.
    Lemma SV1m : shvis mm sa (sa + L + 1).
    Proof.
      prep. eapply shvis_transport; [exact SV1 | exact MU | exact WM |].
      unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]. constructor; [| constructor].
      Z.div_mod_to_equations. lia.
    Qed.
    Lemma SV2m : shvis mm ca (ca + N + 1).
    Proof.
      prep. eapply shvis_transport; [exact SV2 | exact MU | exact WM |].
      unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]. constructor; [| constructor].
      Z.div_mod_to_equations. lia.
    Qed.
  End MM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section EPI.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma asr_epi : forall x1 x5 x6 x7 xs1 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 xs2 xs3,
      evt asegs POST (RST 0x1a9f18 x1 x5 x6 x7 xs1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 xs2 xs3 x28 x29 x30 x31 mm).
    Proof.
      prep. pose proof (ACm mm MU WM) as AC'.
      do 13 zstep.
      release_frame FR STm (bv_unsigned sp + -80).
      lazymatch goal with STx : stk asegs mm lo _ |- _ => release_frame FR1 STx (bv_unsigned sp) end.
      unfold astrspn_post. finish.
    Qed.
  End EPI.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JR2.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma asr_jr2 : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17 xs3,
      evt asegs POST (RST 0x1aa158 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (r + 1)) xs3 x28 x29 x30 x31 mm).
    Proof.
      prep. pose proof (ACm mm MU WM) as AC'. pose proof (ACC1m mm MU) as ACCm.
      assert (ACCr : accessible mm sa (r + 1)) by (eapply accessible_sub; [exact ACCm| lia| lia| lia]).
      do 2 zstep.
      zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by lia;
        [ exact ACCr
        | lia
        | eapply in_app_mem_sub; [exact INM1| lia| lia]
        | exact STm
        | unfold RIP_STACK; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2160) _, STx : stk asegs mx lo _,
                         MUx : munch _ m mx, WMx : wmono asegs m mx, F1x : rw_cells asegs mx (bv_unsigned sp + -80) _ |- _ =>
          eapply (asr_epi mx); [exact MIx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx] end
      end.
    Qed.
  End JR2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JQ2.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis L64 : r + 1 <= 64.

    (* [comment removed for export] *)
    Lemma asr_j5b : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 xs3,
      evt asegs POST (RST 0x1aa150 x1 x5 x6 x7 a0 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (r + 1)) xs3 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply asr_epi; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - eapply asr_jr2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
    Qed.

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + (r + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + (r + 1) - 1) < 17594333495296.
      (* [comment removed for export] *)
      Lemma asr_loop2 : forall (k : nat) (i : Z) x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17 xs3,
        Z.to_nat (sh (sa + (r + 1) - 1) - (sh sa + i)) = k -> 0 <= i -> sh sa + i < sh (sa + (r + 1) - 1) ->
        evt asegs POST (RST 0x1aa140 x1 x5 x6 x7 a0 (Z_to_bv 64 r) (Z_to_bv 64 (sh sa + i)) (Z_to_bv 64 (sh (sa + (r + 1) - 1))) x13
                            x14 x15 x16 x17 (Z_to_bv 64 (r + 1)) xs3 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17 xs3 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh sa + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh sa + i + 1) with (sh sa + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (sa + (r + 1) - 1) - (sh sa + (i + 1))))); lia.
        - apply asr_j5b.
      Qed.
    End Loop.

    (* [comment removed for export] *)
    Lemma asr_jq2 : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9ee0 x1 x5 x6 x7 a0 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (r + 1)) (Z_to_bv 64 r) x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + (r + 1))))).
      { pose proof (SV1m mm MU WM) as SV. eapply (shvis_sub mm sa (sa + L + 1)); [exact SV| lia| lia| lia| lia| lia]. }
      assert (N64 : 1 <= r + 1 <= 64) by lia.
      destruct (hull_words sa (r + 1) ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app sa ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (sa + (r + 1) - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm sa (r + 1) ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh sa / 8) in *. set (q2 := sh (sa + (r + 1) - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh sa /\ sh (sa + (r + 1) - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh sa /\ sh (sa + (r + 1) - 1) < 17594333495296) by lia.
      destruct (ACONST_layout mm (ACm mm MU WM)) as (G1 & C1 & _).
      do 8 zstep. replace (r + sa) with (sa + (r + 1) - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E LQ]|[E LQ]]; rewrite E in QL |- *; rewrite LQ in QW, QL.
      - do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (r + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5b.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asr_loop2 q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_epi; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 3 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (sa + (r + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5b.
          * replace (Z_to_bv 64 (sh sa)) with (Z_to_bv 64 (sh sa + 0)) by (f_equal; lia).
            eapply (asr_loop2 q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_epi; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
    Qed.
  End JQ2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section J2.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma asr_j2 : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 xs2 xs3,
      evt asegs POST (RST 0x1a9ec0 x1 x5 x6 x7 a0 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 xs2 xs3 x28 x29 x30 x31 mm).
    Proof.
      prep. pose proof (ACm mm MU WM) as AC'. destruct (ACONST_cflags mm AC') as [_ CS]. change (b8 0) with (Z_to_bv 8 0) in CS.
      unfold ACF_STRICT_CELL in CS.
      zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 0)) with 0 by reflexivity.   (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. if_cases K2; try (exfalso; revert K2; vm_compute; discriminate).
      do 2 zstep. (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3; rewrite ?lxor_ones64 in K3 by lia. { exfalso. lia. }
      zstep. zstep. if_cases K4; zify_cond K4.
      - (* [comment removed for export] *)
        zstep. if_cases K5; zify_cond K5; [| exfalso; lia].
        eapply asr_jr2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - eapply asr_jq2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM | lia].
    Qed.
  End J2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JR1.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma asr_jr1 : forall x1 x5 x6 x7 x28 x29 x30 x31 x10 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1aa084 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (N + 1)) a1 x28 x29 x30 x31 mm).
    Proof.
      prep. pose proof (ACm mm MU WM) as AC'. pose proof (ACC2m mm MU) as ACCm.
      do 2 zstep.
      zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by lia;
        [ exact ACCm
        | lia
        | replace (ca + (N + 1)) with (ca + N + 1) by lia; exact INM2
        | exact STm
        | unfold RIP_STACK; lia
        | unfold AHI_LO; lia
        | ].
      try rewrite unsigned_lit in * by lia.
      zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2160) _, STx : stk asegs mx lo _,
                         MUx : munch _ m mx, WMx : wmono asegs m mx, F1x : rw_cells asegs mx (bv_unsigned sp + -80) _ |- _ =>
          eapply (asr_j2 mx); [exact MIx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx] end
      end.
    Qed.
  End JR1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JQ1.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis L64 : N + 1 <= 64.

    (* [comment removed for export] *)
    Lemma asr_j5a : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1aa07c x1 x5 x6 x7 a0 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (N + 1)) a1 x28 x29 x30 x31 mm).
    Proof.
      intros. zstep. zstep. if_cases K.
      - eapply asr_j2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - eapply asr_jr1; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
    Qed.

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh ca /\ sh (ca + (N + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh ca /\ sh (ca + (N + 1) - 1) < 17594333495296.
      (* [comment removed for export] *)
      Lemma asr_loop1 : forall (k : nat) (i : Z) x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17,
        Z.to_nat (sh (ca + (N + 1) - 1) - (sh ca + i)) = k -> 0 <= i -> sh ca + i < sh (ca + (N + 1) - 1) ->
        evt asegs POST (RST 0x1aa06c x1 x5 x6 x7 a0 (Z_to_bv 64 r) (Z_to_bv 64 (sh ca + i)) (Z_to_bv 64 (sh (ca + (N + 1) - 1))) x13
                            x14 x15 x16 x17 (Z_to_bv 64 (N + 1)) a1 x28 x29 x30 x31 mm).
      Proof.
        induction k as [k IH] using lt_wf_ind; intros i x1 x5 x6 x7 x28 x29 x30 x31 x13 x14 x15 x16 x17 Hk Hi Hlt.
        pose proof (q_read mm q1 qj QA (sh ca + i) ltac:(lia)) as RD.
        do 3 zstep.
        zstep. if_cases K; zify_cond K.
        - replace (sh ca + i + 1) with (sh ca + (i + 1)) by lia.
          eapply (IH (Z.to_nat (sh (ca + (N + 1) - 1) - (sh ca + (i + 1))))); lia.
        - apply asr_j5a.
      Qed.
    End Loop.

    (* [comment removed for export] *)
    Lemma asr_jq1 : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17,
      evt asegs POST (RST 0x1a9e84 x1 x5 x6 x7 a0 (Z_to_bv 64 N) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (N + 1)) a1 x28 x29 x30 x31 mm).
    Proof.
      prep.
      assert (SVm : stk asegs mm (sh (hull_lo ca)) (sh (hull_hi (ca + (N + 1))))).
      { pose proof (SV2m mm MU WM) as SV. unfold shvis in SV. replace (ca + N + 1) with (ca + (N + 1)) in SV by lia. exact SV. }
      assert (N64 : 1 <= N + 1 <= 64) by lia.
      destruct (hull_words ca (N + 1) ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
      pose proof (sh_range_app ca ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (ca + (N + 1) - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      destruct (hull_chunk mm ca (N + 1) ltac:(lia) N64 ltac:(lia) SVm) as (qj & QW & QL & QL2).
      pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
      set (q1 := sh ca / 8) in *. set (q2 := sh (ca + (N + 1) - 1) / 8) in *.
      assert (QB : 8 * q1 <= sh ca /\ sh (ca + (N + 1) - 1) < 8 * q1 + Z.of_nat (length qj)) by lia.
      assert (SR12 : 2147450880 <= sh ca /\ sh (ca + (N + 1) - 1) < 17594333495296) by lia.
      destruct (ACONST_layout mm (ACm mm MU WM)) as (G1 & C1 & _).
      do 8 zstep. replace (N + ca) with (ca + (N + 1) - 1) by lia. rewrite !shr3_sh by lia.
      do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
      destruct QL2 as [[E LQ]|[E LQ]]; rewrite E in QL |- *; rewrite LQ in QW, QL.
      - do 4 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (ca + (N + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5a.
          * replace (Z_to_bv 64 (sh ca)) with (Z_to_bv 64 (sh ca + 0)) by (f_equal; lia).
            eapply (asr_loop1 q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_j2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
        do 4 zstep. zstep. if_cases K0.
        + pose proof (q_read mm q1 qj QA (sh (ca + (N + 1) - 1)) ltac:(lia)) as RD.
          do 6 zstep.
          zstep. if_cases K1; zify_cond K1.
          * apply asr_j5a.
          * replace (Z_to_bv 64 (sh ca)) with (Z_to_bv 64 (sh ca + 0)) by (f_equal; lia).
            eapply (asr_loop1 q1 qj); first [eassumption | reflexivity | lia].
        + eapply asr_j2; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
    Qed.
  End JQ1.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section J1.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2160) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2160).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma asr_j1 : forall x1 x5 x6 x7 x28 x29 x30 x31 x11 x12 x13 x14 x15 x16 x17 xs2,
      evt asegs POST (RST 0x1a9e70 x1 x5 x6 x7 a0 (Z_to_bv 64 N) x11 x12 x13 x14 x15 x16 x17 xs2 a1 x28 x29 x30 x31 mm).
    Proof.
      prep.
      do 2 zstep. (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3; rewrite ?lxor_ones64 in K3 by lia. { exfalso. lia. }
      zstep. zstep. if_cases K4; zify_cond K4.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K5; zify_cond K5; [| exfalso; lia].
        eapply asr_jr1; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      - eapply asr_jq1; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM | lia].
    Qed.
  End J1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma astrspn_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRSPN_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold ASTRSPN_STUB. prep.
    destruct (ACONST_layout_flag m AC) as [_ C5]. change (b8 1) with (Z_to_bv 8 1) in C5.
    destruct (ACONST_icpt m AC) as (_ & RSR & _ & _ & _ & CF1 & _). change (b8 1) with (Z_to_bv 8 1) in CF1. unfold wz in RSR.
    unfold ASTRSPNP_CELL, AREAL_STRSPN, ACF_ISTRSPN_CELL in RSR, CF1.
    pose proof (ACONST_cell m AGOT_CFLAGS [C8 (wz 0x73c428)] AC ltac:(in_nth)) as G6. unfold AGOT_CFLAGS, wz in G6.
    pose proof GOTC as GOTC'. pose proof CAN as CAN'. unfold AGOT_SSP_CELL, ACANARY_CELL, wz in GOTC', CAN'.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
    pose proof (bytes_at_bound _ _ _ _ ACS) as CB0. rewrite length_app in CB0. cbn [length] in CB0.
    pose proof ST0 as ST. carve_frame 80%nat ST. rename FR into FR1. carve_frame 2080%nat ST.
    zstep. (* [comment removed for export] *)
    do 13 zstep. (* [comment removed for export] *)
    do 2 zstep.  (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2160 - 16) _ ST ltac:(lia)) as [STlo SThi].
    zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2160 - 16) (bv_unsigned sp + -2160),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2160 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    do 2 zstep. (* [comment removed for export] *)
    do 3 zstep. (* [comment removed for export] *)
    zstep. call2 astrspn_real_body; try eassumption; rewrite ?unsigned_lit by lia.
    all: try lazymatch goal with |- stk asegs _ _ _ => exact ST end.
    all: try lazymatch goal with
         | |- ~ In _ _ => assumption
         | |- (_ <= length acc)%nat => exact ALEN
         | |- _ + Z.of_nat (length (_ ++ _)) <= _ => rewrite length_app; cbn [length]; lia
         | |- 0 <= can < _ => exact CANR
         | |- _ <= _ => lia
         end.
    try rewrite unsigned_lit in * by lia.
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|].   (* [comment removed for export] *)
    do 2 zstep. (* [comment removed for export] *)
    zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 1)) with 1 by reflexivity.   (* [comment removed for export] *)
    zstep. if_cases K2; [exfalso; revert K2; vm_compute; discriminate|].
    zstep. (* [comment removed for export] *)
    do 2 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. call_pure istrlen_spec; [eassumption .. |].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MIx : mem_inv asegs mx, FRx : rw_cells asegs mx (bv_unsigned sp + -2160) _, STx : stk asegs mx lo _,
                       MUx : munch _ m mx, WMx : wmono asegs m mx, F1x : rw_cells asegs mx (bv_unsigned sp + -80) _ |- _ =>
        eapply (asr_j1 mx); [exact MIx | exact F1x | exact FRx | exact STx | exact MUx | exact WMx] end
    end.
  Qed.
End STRSPN.

Section OK.
  Context {HCEIL : HeapCeil}.
  Lemma strspn_icpt_ok : strspn_icpt_stmt.
  Proof. unfold strspn_icpt_stmt. intros. eapply astrspn_body; eassumption. Qed.
End OK.
