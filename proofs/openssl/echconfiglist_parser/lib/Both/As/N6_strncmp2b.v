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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_strlen N6_strncmp_spec N6_strncmp N6_strncmp2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section STRNCMP.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e t rest1 rest2 : list Z) (n lo : Z).
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis N0 : 0 <= n.
  Hypothesis LEN : Z.of_nat (length e) <= n.
  Hypothesis E1 : bytes_at asegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)).
  Hypothesis FE : Forall (fun c => 0 < c < 256) e.
  Hypothesis E2 : bytes_at asegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)).
  Hypothesis FT : Forall (fun c => 0 < c < 256) t.
  Hypothesis ACC1 : accessible m (bv_unsigned a0) (Z.min n (Z.of_nat (length e) + 1)).
  Hypothesis ACC2 : accessible m (bv_unsigned a1) (Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis SV1 : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1).
  Hypothesis SV2 : shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : n <= 2^40.
  Hypothesis INM1 : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.min n (Z.of_nat (length e) + 1)).
  Hypothesis INM2 : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis DJ1 : bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis DJ2 : bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1.
  Hypothesis CFS : rw_cells asegs m ACF_STRICT_CELL [C1 (Z_to_bv 8 0)].

  Notation p1 := (bv_unsigned a0).
  Notation p2 := (bv_unsigned a1).
  Notation lne := (Z.of_nat (length e)).
  Notation lnt := (Z.of_nat (length t)).
  Notation POST := (astrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zstrncmp e t (Z.to_nat n)) lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2176)).
  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 mm :=
    (MS (mkR x1 SP2 gp tp x5 t1 t2 sp a2 x10 x11 x12 x13 x14 x15 x16 x17 a1 a0 ra x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -104)
                         [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; pose proof (Z.le_trans _ _ _ (proj1 (proj1 aceil_facts)) CEIL) as CEILN; unfold AINTRIN_STACK, ACF_STRICT_CELL in *;
    pose proof DJ1 as DJ1'; rewrite <- (length_map b8 (e ++ 0 :: rest1)) in DJ1';
    pose proof DJ2 as DJ2'; rewrite <- (length_map b8 (t ++ 0 :: rest2)) in DJ2';
    pose proof INM1 as INM1'; unfold in_app_mem, AHI_LO, AAPP_HI in INM1'; rewrite ASHADOW_BASE_val in INM1';
    pose proof INM2 as INM2'; unfold in_app_mem, AHI_LO, AAPP_HI in INM2'; rewrite ASHADOW_BASE_val in INM2';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R.

  Lemma len1 : Z.of_nat (length (e ++ 0 :: rest1)) = lne + 1 + Z.of_nat (length rest1).
  Proof. rewrite length_app. cbn [length]. lia. Qed.
  Lemma len2 : Z.of_nat (length (t ++ 0 :: rest2)) = lnt + 1 + Z.of_nat (length rest2).
  Proof. rewrite length_app. cbn [length]. lia. Qed.

  (* [comment removed for export] *)
  Section K.
    Variables (i C1 C2 : Z).
    Hypothesis HC : 0 <= C1 < 256 /\ 0 <= C2 < 256.
    Hypothesis HI : 0 <= i <= n /\ i <= lne /\ i <= lnt.
    Hypothesis SIGN : (zstrncmp e t (Z.to_nat n) = 0 <-> C1 = C2) /\ (zstrncmp e t (Z.to_nat n) < 0 <-> C1 < C2).

    Notation NN := (Z.min (i + 1) n).
    Lemma NN_facts2 : 0 <= NN <= n /\ NN <= Z.min n (lne + 1) /\ NN <= Z.min n (lnt + 1) /\ NN <= 2^40 /\ NN <= i + 1.
    Proof using e t rest1 rest2 n N0 N40 i C1 C2 HI SIGN. pose proof HI. pose proof N40. (first [clear - H0 H; lia | lia]). Qed.

    Lemma SR_facts1 : 1 <= NN ->
      (2147450880 <= sh p1 < 17594333495296) /\ (2147450880 <= sh (p1 + NN - 1) < 17594333495296) /\ 0 <= p1 /\ p1 + NN + 8 <= 2^47.
    Proof using a0 e t rest1 rest2 n N40 INM1 i C1 C2 HI SIGN.
      intros H1. pose proof HI. pose proof N40.
      pose proof INM1 as X. unfold in_app_mem, AHI_LO, AAPP_HI in X. rewrite ASHADOW_BASE_val in X.
      pose proof (bv_unsigned_in_range 64 a0) as A0R.
      assert (R1 : 0 <= p1 < AAPP_HI) by (unfold AAPP_HI; (first [clear - X H; lia | lia])).
      assert (R2 : 0 <= p1 + NN - 1 < AAPP_HI) by (unfold AAPP_HI; (first [clear - X H H1; lia | lia])).
      pose proof (sh_range_app p1 R1) as S1. pose proof (sh_range_app (p1 + NN - 1) R2) as S2.
      unfold AHI_LO in S1, S2. rewrite ASHADOW_BASE_val in S1, S2. (first [clear - S2 S1 X H; lia | lia]).
    Qed.

    (* [comment removed for export] *)
    Section CHK0.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis E1m : bytes_at asegs mm (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)).
      Hypothesis E2m : bytes_at asegs mm (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)).
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2176) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2176).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
      Hypothesis CB1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
      Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
      Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
      Hypothesis CB4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
      Hypothesis SV2m : stk asegs mm (sh (hull_lo p2)) (sh (hull_hi (p2 + Z.min n (lnt + 1)))).
      Hypothesis SV1m : stk asegs mm (sh (hull_lo p1)) (sh (hull_hi (p1 + lne + 1))).
      Hypothesis G6 : rw_cells asegs mm 6191112 [C8 (Z_to_bv 64 7586856)].
      Hypothesis CFSm : rw_cells asegs mm 7587101 [Cells.C1 (Z_to_bv 8 0)].

      (* [comment removed for export] *)
      Lemma asn_j368 : forall w21 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26, w21 = Z_to_bv 64 NN ->
        evt asegs POST (RST 0x1a9408 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 w21 x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 (Z_to_bv 64 i) mm).
      Proof.
        intros w21. intros until x26. intros ->. revert x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26.
        prep. pose proof NN_facts2 as NF.
        zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite land_ones64 in K2.
        - zstep. if_cases K3; zify_cond K3.
          + eapply asn_jr1; [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | exact HC | exact HI | exact SIGN | exact MIm | exact E1m | exact E2m | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m].
          + zstep. eapply asn_j3b0; [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | exact HC | exact HI | exact SIGN | exact MIm | exact E2m | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m].
        - eapply asn_jq1; try eassumption.
          first [ solve [ clear - K2 NF N0; Z.div_mod_to_equations; lia ] | (Z.div_mod_to_equations; lia) ].   (* [comment removed for export] *)
      Qed.

      (* [comment removed for export] *)
      Lemma asn_j248 : forall w27 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26, w27 = Z_to_bv 64 i ->
        evt asegs POST (RST 0x1a92e8 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 w27 mm).
      Proof.
        intros w27. intros until x26. intros ->. revert x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26.
        prep. pose proof NN_facts2 as NF.
        assert (NA2 : bv_unsigned a2 = n) by (rewrite A2; apply unsigned_lit; lia).
        pose proof (bytes_at_bound _ _ _ _ E1m) as B1. rewrite length_map, length_app in B1. cbn [length] in B1.
        zstep. if_cases K1; zify_cond K1.
        - zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
          do 4 zstep. zstep. if_cases K3; zify_cond K3; rewrite lxor_ones64 in K3 by lia; [| exfalso; (first [clear - K3 K2 NA2 NF INM1'; lia | lia])].
          eapply asn_j368; try eassumption. rewrite A2. f_equal. (first [clear - K2 NA2; lia | lia]).
        - do 3 zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 0)) with 0 by reflexivity.
          do 2 zstep. change (Z.land 0 1) with 0.
          zstep. if_cases K2; [| exfalso; revert K2; vm_compute; discriminate].
          zstep. zstep. if_cases K3; zify_cond K3.
          + do 4 zstep. zstep. if_cases K4; zify_cond K4; rewrite lxor_ones64 in K4 by lia; [| exfalso; (first [clear - K4 K3 NA2 NF INM1'; lia | lia])].
            eapply asn_j368; try eassumption. rewrite A2. f_equal. (first [clear - K3 NA2; lia | lia]).
          + do 3 zstep. zstep. if_cases K4; zify_cond K4; rewrite lxor_ones64 in K4 by lia; [exfalso; (first [clear - K4 K3 NA2 NF INM1'; lia | lia])|].
            eapply asn_j368; try eassumption. f_equal. (first [clear - K3 NA2; lia | lia]).
      Qed.
    End CHK0.
  End K.
End STRNCMP.
