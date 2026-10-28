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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_strlen N6_strncmp_spec N6_strncmp N6_strncmp2 N6_strncmp2b.
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
    intros; acb; unfold AINTRIN_STACK, ACF_STRICT_CELL in *;
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
  Lemma nthZ_range_e : forall j, (j <= length e)%nat -> 0 <= nthZ j e < 256.
  Proof.
    intros j Hj. destruct (Nat.lt_ge_cases j (length e)) as [L|G].
    - rewrite nthZ_lt by lia. pose proof (proj1 (Forall_nth _ _) FE j 0 L). cbn in H. lia.
    - assert (j = length e) as -> by lia. rewrite nthZ_len. lia.
  Qed.
  Lemma nthZ_range_t : forall j, (j <= length t)%nat -> 0 <= nthZ j t < 256.
  Proof.
    intros j Hj. destruct (Nat.lt_ge_cases j (length t)) as [L|G].
    - rewrite nthZ_lt by lia. pose proof (proj1 (Forall_nth _ _) FT j 0 L). cbn in H. lia.
    - assert (j = length t) as -> by lia. rewrite nthZ_len. lia.
  Qed.

  Lemma sign_at_break : forall (j : nat) (X1 X2 : Z),
    (j <= Z.to_nat n)%nat -> (j <= length e)%nat -> (j <= length t)%nat ->
    (forall j', (j' < j)%nat -> nth j' e 0 = nth j' t 0) ->
    (j = Z.to_nat n \/ nthZ j e = 0 \/ nthZ j e <> nthZ j t) ->
    ((j < Z.to_nat n)%nat -> X1 = nthZ j e /\ X2 = nthZ j t) -> ((j >= Z.to_nat n)%nat -> X1 = X2) ->
    (zstrncmp e t (Z.to_nat n) = 0 <-> X1 = X2) /\ (zstrncmp e t (Z.to_nat n) < 0 <-> X1 < X2).
  Proof.
    intros j X1 X2 Hn He Ht PRE STOP HX1 HX2.
    pose proof (cmpi_charact (Z.to_nat n) e t j Hn He Ht PRE STOP FE) as CC.
    pose proof (zstrncmp_sign (Z.to_nat n) e t X1 X2 FE FT) as SG. cbn beta in SG. rewrite CC in SG.
    exact (SG HX1 HX2).
  Qed.

  (* [comment removed for export] *)
  Lemma cstr_read : forall mm p l rest (j : Z),
    bytes_at asegs mm p (map b8 (l ++ 0 :: rest)) -> 0 <= j <= Z.of_nat (length l) ->
    ov_read_bytes asegs mm (wa (p + j)) 1 = Some [b8 (nthZ (Z.to_nat j) l)].
  Proof.
    intros mm p l rest j B Hj.
    eapply (u8ro_read asegs mm p (map b8 (l ++ 0 :: rest)) j); [exact B | | lia | reflexivity].
    rewrite nth_error_map. rewrite (nth_error_nth' _ 0) by (rewrite length_app; cbn; lia). cbn [option_map].
    f_equal. f_equal. apply nthZ_app_rest. lia.
  Qed.

  Section MAIN.
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
    Hypothesis CFSm : rw_cells asegs mm 7587101 [C1 (Z_to_bv 8 0)].

    (* [comment removed for export] *)
    Lemma asn_cl : forall (k : nat) (j : Z) x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26,
      Z.to_nat (n - j) = k -> 0 <= j < n -> j <= lne -> j <= lnt ->
      (forall j', (j' < Z.to_nat j)%nat -> nth j' e 0 = nth j' t 0) ->
      evt asegs POST (RST 0x1a92c0 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 j) mm).
    Proof.
      induction k as [k IH] using lt_wf_ind; intros j x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 Hk Hj Hje Hjt PRE.
      prep. assert (NA2 : bv_unsigned a2 = n) by (rewrite A2; apply unsigned_lit; lia).
      pose proof (cstr_read mm p1 e rest1 j E1m ltac:(lia)) as RD1.
      pose proof (cstr_read mm p2 t rest2 j E2m ltac:(lia)) as RD2.
      pose proof (nthZ_range_e (Z.to_nat j) ltac:(lia)) as R1. pose proof (nthZ_range_t (Z.to_nat j) ltac:(lia)) as R2.
      zstep. zstep. cbv beta. rewrite (b8_unsigned (nthZ (Z.to_nat j) e)) by lia.
      zstep. zstep. cbv beta. rewrite (b8_unsigned (nthZ (Z.to_nat j) t)) by lia.
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        eapply asn_j248 with (i := j) (C1 := nthZ (Z.to_nat j) e) (C2 := nthZ (Z.to_nat j) t); [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | idtac | idtac | idtac | exact MIm | exact E1m | exact E2m | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m | exact SV1m | exact G6 | exact CFSm | idtac]; try reflexivity; [lia | lia |].
        apply (sign_at_break (Z.to_nat j)); [lia | lia | lia | exact PRE | right; left; exact K1 | intros; split; reflexivity | intros; (first [clear - H Hj; lia | lia])].
      - zstep. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
          eapply asn_j248 with (i := j) (C1 := nthZ (Z.to_nat j) e) (C2 := nthZ (Z.to_nat j) t); [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | idtac | idtac | idtac | exact MIm | exact E1m | exact E2m | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m | exact SV1m | exact G6 | exact CFSm | idtac]; try reflexivity; [lia | lia |].
          apply (sign_at_break (Z.to_nat j)); [lia | lia | lia | exact PRE | right; right; exact K2 | intros; split; reflexivity | intros; lia].
        + (* [comment removed for export] *)
          assert (JE : j < lne).
          { destruct (Z.eq_dec j lne) as [E|]; [exfalso| lia].
            rewrite E, Nat2Z.id, nthZ_len in K1. lia. }
          assert (JT : j < lnt).
          { destruct (Z.eq_dec j lnt) as [E|]; [exfalso| lia].
            rewrite K2, E, Nat2Z.id, nthZ_len in K1. lia. }
          assert (PRE' : forall j', (j' < Z.to_nat (j + 1))%nat -> nth j' e 0 = nth j' t 0).
          { intros j' Hj'. destruct (Nat.eq_dec j' (Z.to_nat j)) as [->|NE]; [| apply PRE; (first [clear - NE Hj'; lia | lia])].
            rewrite <- !nthZ_lt by (first [clear - Hj' JE JT; lia | lia]). exact K2. }
          zstep. zstep. if_cases K3; zify_cond K3.
          * (* [comment removed for export] *)
            eapply (IH (Z.to_nat (n - (j + 1))) ltac:(lia) (j + 1)); try eassumption; (first [clear - K3 NA2 Hj JE JT; lia | lia]).
          * (* [comment removed for export] *) zstep. zstep.
            eapply asn_j248 with (i := n) (C1 := nthZ (Z.to_nat j) e) (C2 := nthZ (Z.to_nat j) e); [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | idtac | idtac | idtac | exact MIm | exact E1m | exact E2m | exact FR1 | exact FR | exact STm | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m | exact SV1m | exact G6 | exact CFSm | exact A2]; [lia | lia |].
            apply (sign_at_break (Z.to_nat n)); [lia | lia | lia | | left; reflexivity | intros; lia | intros; reflexivity].
            intros j' Hj'. apply PRE'. lia.
    Qed.
  End MAIN.

  Lemma astrncmp_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTRNCMP_STUB) fc None m (seg_rom asegs)).
  Proof.
    unfold ASTRNCMP_STUB. prep.
    assert (NA2 : bv_unsigned a2 = n) by (rewrite A2; apply unsigned_lit; lia).
    destruct (ACONST_layout m AC) as (G1 & CB1 & G2 & G3 & G4 & CB4).
    destruct (ACONST_layout_strlen m AC) as (C5 & G6). change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof SV1 as SV1m. unfold shvis in SV1m. pose proof SV2 as SV2m. unfold shvis in SV2m.
    assert (SRV : 2147450880 <= sh (hull_lo p1) /\ sh (hull_hi (p1 + lne + 1)) <= 17594333495296 + 16
                  /\ 2147450880 <= sh (hull_lo p2) /\ sh (hull_hi (p2 + Z.min n (lnt + 1))) <= 17594333495296 + 16).
    { unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. (first [clear - H45 H44 H35 H30 H29 H20 H15 H14 H10 H9 H5 H4 H0 H INM2' INM1' LEN; lia | lia]). }
    pose proof (bytes_at_bound _ _ _ _ E1) as B1. rewrite length_map in B1.
    pose proof (bytes_at_bound _ _ _ _ E2) as B2. rewrite length_map in B2.
    pose proof ST0 as ST. carve_frame 104%nat ST. rename FR into FR1. carve_frame 2072%nat ST.
    zstep. (* [comment removed for export] *)
    do 16 zstep.
    do 4 zstep.
    zstep. call_pure asaninited_body; [eassumption .. |].
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|].
    destruct (stk_split asegs _ _ (bv_unsigned sp + -2176 - 16) _ ST ltac:(lia)) as [STlo SThi].
    zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
    try rewrite unsigned_lit in * by lia.
    match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2176 - 16) (bv_unsigned sp + -2176),
                    Hlo : stk asegs ?mx lo (bv_unsigned sp + -2176 - 16) |- _ =>
      pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      do 4 zstep. zstep. zstep. if_cases K3; zify_cond K3; [| exfalso; lia].
      do 4 zstep. zstep. if_cases K4; zify_cond K4; rewrite lxor_ones64 in K4 by lia; [| exfalso; lia].
      eapply asn_j368 with (i := 0) (C1 := 0) (C2 := 0); [exact A2 | exact N0 | exact LEN | exact ACC1 | exact ACC2 | exact CEIL | exact LO | exact AC | exact N40 | exact INM1' | exact INM2' | exact DJ1 | exact DJ2 | idtac | idtac | idtac | exact MI0 | exact E1 | exact E2 | exact FR1 | exact FR | exact ST | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m | exact SV1m | idtac]; [lia | lia | | rewrite A2; f_equal; lia].
      replace (Z.to_nat n) with 0%nat by lia. cbn. lia.
    - zstep.
      eapply asn_cl; [exact MI0 | exact E1 | exact E2 | exact FR1 | exact FR | exact ST | exact MU | exact WM | exact G1 | exact CB1 | exact G2 | exact G3 | exact G4 | exact CB4 | exact SV2m | exact SV1m | exact G6 | exact CFS | idtac | idtac | idtac | idtac | idtac]; try reflexivity; try (first [clear - K2 NA2 LEN; lia | lia]).
      all: intros j' Hj'; exfalso; lia.
  Qed.
End STRNCMP.
