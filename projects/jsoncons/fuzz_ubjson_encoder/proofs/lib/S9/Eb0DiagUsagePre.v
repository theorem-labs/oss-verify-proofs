(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA Eb0RegionPoisoned Eb0AsanMemcpy Eb0DiagKit Eb0DiagChk Eb0DiagMemcpy Eb0DiagStrnlen Eb0DiagGlue Eb0DiagUPS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUP.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Lemma u8s_of_u32 (M : word -> option byte) a w b0 b1 b2 b3 : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a w ->
  map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 w)) = [b0; b1; b2; b3] ->
  L5.u8_at RSEGS M a b0 /\ L5.u8_at RSEGS M (a + 1) b1 /\ L5.u8_at RSEGS M (a + 2) b2 /\ L5.u8_at RSEGS M (a + 3) b3.
Proof.
  intros Ha Hb C E. unfold L5.u32_at in C. unfold L5.u8_at.
  destruct (word_to_le_bytes 4 (Z_to_bv 64 w)) as [|c0 [|c1 [|c2 [|c3 [|]]]]] eqn:EL; try discriminate E.
  cbn [map] in E. injection E as E0 E1 E2 E3.
  assert (X : forall c b, bv_unsigned c = b -> (c : byte) = Z_to_bv 8 b) by (intros c b <-; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (Eb0DiagStrlen.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as R0. pose proof (Eb0DiagStrlen.rdn_byte_at M a _ _ 1%nat C ltac:(lia) Ha ltac:(lia)) as R1.
  pose proof (Eb0DiagStrlen.rdn_byte_at M a _ _ 2%nat C ltac:(lia) Ha ltac:(lia)) as R2. pose proof (Eb0DiagStrlen.rdn_byte_at M a _ _ 3%nat C ltac:(lia) Ha ltac:(lia)) as R3.
  cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ] in R0, R1, R2, R3. rewrite Z.add_0_r in R0.
  rewrite (X c0 b0 E0) in R0. rewrite (X c1 b1 E1) in R1. rewrite (X c2 b2 E2) in R2. rewrite (X c3 b3 E3) in R3.
  repeat split; assumption.
Qed.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 691812.
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1319120.
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91005.
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1306624.
  Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
  Hypothesis Hn : n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
  Hypothesis HFMT : L5KA.zeros_at M 2147462248 16.
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.

  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1172444 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Definition usage_mid (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    (forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M' x = M x) /\ mem_grows M M'
    /\ getr R' (reg 1) = Z_to_bv 64 1212472
    /\ getr R' (reg 10) = Z_to_bv 64 p
    /\ getr R' (reg 11) = Z_to_bv 64 n
    /\ getr R' (reg 12) = Z_to_bv 64 1319120
    /\ getr R' (reg 13) = Z_to_bv 64 (S - 457)
    /\ getr R' (reg 14) = Z_to_bv 64 0
    /\ getr R' (reg 15) = Z_to_bv 64 3
    /\ getr R' (reg 18) = Z_to_bv 64 0
    /\ getr R' (reg 24) = Z_to_bv 64 0
    /\ getr R' (reg 25) = Z_to_bv 64 n
    /\ getr R' (reg 26) = Z_to_bv 64 n
    /\ getr R' (reg 27) = Z_to_bv 64 n
    /\ L5.u64_at RSEGS M' 1319160 (S - 457)
    /\ L5.u64_at RSEGS M' (S - 1016) 0
    /\ L5.u64_at RSEGS M' (S - 992) n
    /\ L5.u64_at RSEGS M' (S - 1008) n
    /\ L5.u64_at RSEGS M' (S - 1024) 69161
    /\ L5.u64_at RSEGS M' (S - 1000) 0
    /\ getr R' (reg 2) = Z_to_bv 64 (S - 1024)
    /\ getr R' (reg 8) = Z_to_bv 64 37
    /\ getr R' (reg 9) = Z_to_bv 64 2147483647
    /\ getr R' (reg 19) = Z_to_bv 64 7
    /\ getr R' (reg 20) = Z_to_bv 64 1319120
    /\ getr R' (reg 21) = Z_to_bv 64 91014
    /\ getr R' (reg 22) = Z_to_bv 64 0
    /\ getr R' (reg 23) = Z_to_bv 64 p
    /\ getr R' (reg 3) = getr R (reg 3)
    /\ getr R' (reg 4) = getr R (reg 4)
    /\ L5.u64_at RSEGS M' (S - 120) 431388
    /\ L5.u64_at RSEGS M' (S - 128) 91005
    /\ L5.u64_at RSEGS M' (S - 136) 1319120
    /\ L5.u64_at RSEGS M' (S - 144) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 152) (U R 19)
    /\ L5.u64_at RSEGS M' (S - 160) (U R 20)
    /\ L5.u64_at RSEGS M' (S - 168) (U R 21)
    /\ L5.u64_at RSEGS M' (S - 176) can
    /\ L5.u64_at RSEGS M' (S - 472) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 184) 0
    /\ L5.u64_at RSEGS M' (S - 216) 0
    /\ L5.u64_at RSEGS M' (S - 208) 0
    /\ L5.u64_at RSEGS M' (S - 200) 0
    /\ L5.u64_at RSEGS M' (S - 192) 0
    /\ L5.u64_at RSEGS M' 1319208 (S - 464)
    /\ L5.u64_at RSEGS M' 1319216 80
    /\ L5.u64_at RSEGS M' 1319176 (S - 464)
    /\ L5.u64_at RSEGS M' 1319128 0
    /\ L5.u64_at RSEGS M' 1319136 0
    /\ L5.u64_at RSEGS M' 1319152 (S - 384)
    /\ L5.u64_at RSEGS M' (S - 488) 1209680
    /\ L5.u64_at RSEGS M' (S - 496) 1319120
    /\ L5.u64_at RSEGS M' (S - 504) 91005
    /\ L5.u64_at RSEGS M' (S - 512) 6922688
    /\ L5.u64_at RSEGS M' (S - 520) 1
    /\ L5.u64_at RSEGS M' (S - 528) 6924696
    /\ L5.u64_at RSEGS M' (S - 536) 5
    /\ L5.u64_at RSEGS M' (S - 544) (U R 22)
    /\ L5.u64_at RSEGS M' (S - 552) (U R 23)
    /\ L5.u64_at RSEGS M' (S - 560) (U R 24)
    /\ L5.u64_at RSEGS M' (S - 568) (U R 25)
    /\ L5.u64_at RSEGS M' (S - 576) (U R 26)
    /\ L5.u64_at RSEGS M' (S - 584) (U R 27)
    /\ L5.u64_at RSEGS M' (S - 960) (S - 216)
    /\ L5.u64_at RSEGS M' (S - 968) (S - 384)
    /\ L5.u64_at RSEGS M' (S - 952) (S - 480)
    /\ L5.u64_at RSEGS M' (S - 936) 0
    /\ L5.u64_at RSEGS M' (S - 928) 6922688
    /\ L5.u64_at RSEGS M' (S - 592) can
    /\ L5.u64_at RSEGS M' (S - 944) 75913
    /\ L5.u64_at RSEGS M' (S - 920) 214748364
    /\ L5.u64_at RSEGS M' (S - 976) 18446744073709486079
    /\ L5.u64_at RSEGS M' (S - 480) (S - 40)
    /\ L5.u64_at RSEGS M' (S - 912) p
    /\ L5.u64_at RSEGS M' (S - 56) 691812
    /\ L5.u64_at RSEGS M' (S - 64) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' (S - 72) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' (S - 80) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' (S - 16) (bv_unsigned (getr R (reg 16)))
    /\ L5.u64_at RSEGS M' (S - 8) (bv_unsigned (getr R (reg 17)))
    /\ L5.u64_at RSEGS M' (S - 48) p
    /\ L5.u64_at RSEGS M' (S - 40) (bv_unsigned (getr R (reg 13)))
    /\ L5.u64_at RSEGS M' (S - 32) (bv_unsigned (getr R (reg 14)))
    /\ L5.u64_at RSEGS M' (S - 24) (bv_unsigned (getr R (reg 15)))
    /\ L5.u64_at RSEGS M' (S - 104) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 88) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 96) (S - 48)
    /\ L5.u64_at RSEGS M' 2147462248 0
    /\ L5.u64_at RSEGS M' 2147462256 0
    /\ L5.u64_at RSEGS M' 1319192 1205504
    /\ L5.u64_at RSEGS M' 6922688 can
    /\ L5.u64_at RSEGS M' 1308880 1244208
    /\ L5.u64_at RSEGS M' 1308504 1209416
    /\ L5.u64_at RSEGS M' 1335544 2147450880
    /\ L5.u64_at RSEGS M' (S + 8) m8
    /\ L5.u64_at RSEGS M' (S + 16) m7
    /\ L5.u64_at RSEGS M' (S + 24) m6
    /\ L5.u64_at RSEGS M' (S + 32) m5
    /\ L5.u64_at RSEGS M' (S + 40) m4
    /\ L5.u64_at RSEGS M' (S + 48) m3
    /\ L5.u64_at RSEGS M' (S + 56) m2
    /\ L5.u64_at RSEGS M' (S + 64) m1
    /\ L5.u64_at RSEGS M' (S + 72) 1172444
    /\ L5.u32_at RSEGS M' 1319120 5
    /\ L5.u32_at RSEGS M' 1319256 18446744073709551615
    /\ L5.u32_at RSEGS M' 1319240 2
    /\ L5.u32_at RSEGS M' 1319264 4294967295
    /\ L5.u32_at RSEGS M' 1319260 4294967295
    /\ L5.u8_at RSEGS M' 1319120 5
    /\ L5.u8_at RSEGS M' (p + n) 0
    /\ L5.u8_at RSEGS M' (S - 464) 117
    /\ L5.u8_at RSEGS M' (S - 463) 115
    /\ L5.u8_at RSEGS M' (S - 462) 97
    /\ L5.u8_at RSEGS M' (S - 461) 103
    /\ L5.u8_at RSEGS M' (S - 460) 101
    /\ L5.u8_at RSEGS M' (S - 459) 58
    /\ L5.u8_at RSEGS M' (S - 458) 32
    /\ L5.u8_at RSEGS M' 1932412 1
    /\ L5.u8_at RSEGS M' 1338841 1
    /\ L5.u8_at RSEGS M' 1338840 1.

  Theorem usage_pre : exists fx5 R5 M5, msteps RSEGS (st fx R 0x64568 M) (st fx5 R5 0x12815c M5) /\ usage_mid R5 M5.
  Proof.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    destruct HMF as (MF72 & MF64 & MF56 & MF48 & MF40 & MF32 & MF24 & MF16 & MF8).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (HFMTa : L5KA.zeros_at M 2147462248 8) by (intros i Hi; apply HFMT; lia). pose proof (u64_of_zeros M 2147462248 HFMTa ltac:(lia) ltac:(lia)) as HFMT64.
    assert (HFMTb : L5KA.zeros_at M 2147462256 8) by (intros i Hi; replace (2147462256 + i) with (2147462248 + (8 + i)) by lia; apply HFMT; lia). pose proof (u64_of_zeros M 2147462256 HFMTb ltac:(lia) ltac:(lia)) as HFMT64b.
    assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.

    pose proof (duA_conc fx R M (fun j => match j with 2%nat => S | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.

    assert (AG1 : forall x : word, bv_unsigned x < S - 2352 \/ S <= bv_unsigned x -> M1 x = M x) by (intros x Hx; apply FR1; lia).
    assert (STR1 : cstr M1 p bs t8) by (apply (cstr_ext M M1); [lia | lia | intros x Hx; apply AG1; lia | exact HSTR]).
    assert (HSN1 : sn_cells M1) by (apply (sn_cells_ext M M1); [intros x Hx; apply AG1; lia | exact HSN]).
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (HSH1 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M1 x = Some (Z_to_bv 8 0)).
    { intros x Hx. rewrite AG1; [apply HSH; exact Hx|]. left. unfold SB in Hx. lia. }
    assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (CP1 : chk_pre M1 p (n + 1) (S - 2352)).
    { apply chk_pre_intro; try lia. apply (L5.writable_sub RSEGS M1 (S - 5440) 5440); [exact W1 | lia | lia]. destruct HSN1 as (_ & _ & _ & G & _); exact G. exact HSH1. }
    assert (r10 : getr R1 10%bv = Z_to_bv 64 p) by (rewrite <- (getr_reg R1 10 10%bv eq_refl); sc).
    assert (r22 : getr R1 22%bv = Z_to_bv 64 p) by (rewrite <- (getr_reg R1 22 22%bv eq_refl); sc).
    assert (r2 : getr R1 2%bv = Z_to_bv 64 (S - 2352)) by (rewrite <- (getr_reg R1 2 2%bv eq_refl); sc).
    destruct (strlen_chk1 M1 (seg_rom RSEGS) p (S - 2352) bs R1 (cstr_rd1 _ _ _ _ STR1) (cs_nz _ _ _ _ STR1) CP1 r10 r22 r2) as (R2 & M2 & RUN2 & K2 & (AG2 & MG2)).

    assert (AG02 : forall x : word, bv_unsigned x < S - 5440 \/ S <= bv_unsigned x -> M2 x = M x) by (intros x Hx; rewrite AG2 by lia; apply AG1; lia).
    assert (AG12 : forall x : word, bv_unsigned x < S - 2424 \/ S - 2352 <= bv_unsigned x -> M2 x = M1 x) by (intros x Hx; apply AG2; lia).
    assert (W2 : L5.writable RSEGS M2 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D2 : L5.defined M2 (S - 5440) 5440) by (eapply defined_grows; [exact MG2 | eapply defined_grows; eassumption]).
    assert (IMG2 : L5.img_clear M2 65536 1306624) by (apply (imgc_ext M M2); [intros x Hx; apply AG02; lia | lia | lia | exact HIMG]).
    assert (FW2 : L5.writable RSEGS M2 1319120 152) by (eapply writable_grows; [exact MG2 | eapply writable_grows; eassumption]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (SK2 : L5KA.zeros_at M2 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M2); [intros x Hx; apply AG02; unfold SB in Hx; lia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    pose proof (duB_conc fx1 R2 M2 (fun j => match j with 2%nat => S - 2352 | 33%nat => p | 34%nat => n | 40%nat => can
       | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 120%nat => U R2 20 | 121%nat => U R2 21 | 122%nat => U R2 22 | 123%nat => U R2 23 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx3 R3 M3 MG3 FR3 FZ3 MS3 KS3.

    assert (AG23 : forall x : word, bv_unsigned x < S - 3248 \/ S - 112 <= bv_unsigned x -> ~ filew (bv_unsigned x) -> M3 x = M2 x) by (intros x Hx Hf; unfold filew in Hf; apply FR3; lia).
    assert (A03 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M3 x = M x) by (intros x Hx Hf; rewrite AG23 by (first [exact Hf | lia]); apply AG02; lia).
    assert (MG03 : mem_grows M M3) by (eapply mem_grows_trans; [exact MG1|]; eapply mem_grows_trans; [exact MG2 | exact MG3]).
    assert (W3 : L5.writable RSEGS M3 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D3 : L5.defined M3 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG3 : L5.img_clear M3 65536 1306624) by (apply (imgc_ext M M3); [intros x Hx; apply A03; flia | lia | lia | exact HIMG]).
    assert (STR3 : cstr M3 p bs t8) by (apply (cstr_ext M M3); [lia | lia | intros x Hx; apply A03; flia | exact HSTR]).
    assert (HSN3 : sn_cells M3) by (apply (sn_cells_agree M M3 S); [lia | exact A03 | exact HSN]).
    assert (HSH3 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M3 x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold SB in Hx. rewrite A03 by flia. apply HSH. exact Hx. }
    destruct (wrap_strnlen_run fx3 R3 M3 (S - 1024) p bs t8) as (fx4 & R4 & M4 & MS4 & V4 & KS4 & FR4 & MG4);
      [ sc | sc | sc | sc | lia | (replace (S - 1024) with (S + (-64) * 16) by lia); rewrite Z_mod_plus_full; exact Hal
      | dk_gmem | dk_gmem | exact IMG3 | lia | lia | exact STR3 | exact HSH3 | exact HSN3 | ].

    assert (AG34 : forall x : word, bv_unsigned x < S - 5424 \/ S - 1024 <= bv_unsigned x -> M4 x = M3 x) by (intros x Hx; apply FR4; lia).
    assert (A04 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M4 x = M x) by (intros x Hx Hf; rewrite AG34 by lia; apply A03; assumption).
    assert (MG04 : mem_grows M M4) by (eapply mem_grows_trans; eassumption).
    assert (W4 : L5.writable RSEGS M4 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D4 : L5.defined M4 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG4 : L5.img_clear M4 65536 1306624) by (apply (imgc_ext M M4); [intros x Hx; apply A04; flia | lia | lia | exact HIMG]).
    assert (STR4 : cstr M4 p bs t8) by (apply (cstr_ext M M4); [lia | lia | intros x Hx; apply A04; flia | exact HSTR]).
    assert (FW4 : L5.writable RSEGS M4 1319120 152) by (eapply writable_grows; eassumption).
    pose proof (cstr_nul M4 p bs t8 ltac:(lia) ltac:(lia) STR4) as NUL4.
    assert (F84 : L5.u8_at RSEGS M4 1319120 5).
    { apply u8_of_u32_5; [lia | lia|]. scc. }
    pose proof (duD_conc fx4 R4 M4 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx5 R5 M5 MG5 FR5 FZ5 MS5 KS5.

    assert (AG45 : forall x : word, bv_unsigned x < S - 3248 \/ S - 976 <= bv_unsigned x -> ~ (1319160 <= bv_unsigned x < 1319168) -> M5 x = M4 x) by (intros x Hx Hf; apply FR5; lia).
    assert (AG35 : forall x : word, bv_unsigned x < S - 5424 \/ S - 976 <= bv_unsigned x -> ~ (1319160 <= bv_unsigned x < 1319168) -> M5 x = M3 x) by (intros x Hx Hf; rewrite AG45 by (first [exact Hf | lia]); apply AG34; lia).
    assert (A05 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M5 x = M x) by (intros x Hx Hf; rewrite AG45 by (unfold filew in Hf; lia); apply A04; assumption).
    assert (AG13h : forall x : word, S - 112 <= bv_unsigned x -> M3 x = M1 x) by (intros x Hx; rewrite AG23 by (unfold filew; lia); apply AG12; lia).
    assert (AG15 : forall x : word, S - 112 <= bv_unsigned x -> M5 x = M1 x) by (intros x Hx; rewrite AG35 by lia; apply AG13h; lia).
    clear AG1 AG2 AG02 AG12 AG23 A03 AG34 A04 AG45 AG13h.
    eassert (E2 : getr R5 (reg 2) = Z_to_bv 64 _) by sc. eassert (E8 : getr R5 (reg 8) = Z_to_bv 64 _) by sc. eassert (E9 : getr R5 (reg 9) = Z_to_bv 64 _) by sc.
    eassert (E19 : getr R5 (reg 19) = Z_to_bv 64 _) by sc. eassert (E20 : getr R5 (reg 20) = Z_to_bv 64 _) by sc. eassert (E21 : getr R5 (reg 21) = Z_to_bv 64 _) by sc.
    eassert (E22 : getr R5 (reg 22) = Z_to_bv 64 _) by sc. eassert (E23 : getr R5 (reg 23) = Z_to_bv 64 _) by sc.
    assert (E3 : getr R5 (reg 3) = getr R (reg 3)).
    { rewrite (KS5 3%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (KS4 3%nat) by (cbn; tauto). rewrite (KS3 3%nat) by (apply L5K.in_b; vm_compute; reflexivity).
      transitivity (getr R1 (reg 3)); [rkb K2; reflexivity | apply KS1; apply L5K.in_b; vm_compute; reflexivity]. }
    assert (E4 : getr R5 (reg 4) = getr R (reg 4)).
    { rewrite (KS5 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (KS4 4%nat) by (cbn; tauto). rewrite (KS3 4%nat) by (apply L5K.in_b; vm_compute; reflexivity).
      transitivity (getr R1 (reg 4)); [rkb K2; reflexivity | apply KS1; apply L5K.in_b; vm_compute; reflexivity]. }
    dk_export M5 ltac:(unfold filew; dk_qlia).
    replace (0x6865c%bv : word) with (Z_to_bv 64 0x6865c) in RUN2 by (apply bv_eq; reflexivity).
    replace (0x685c0%bv : word) with (Z_to_bv 64 0x685c0) in RUN2 by (apply bv_eq; reflexivity).
    exists fx5, R5, M5. split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4|]. exact MS5. }

    unfold usage_mid. split; [exact A05|]. split; [eapply mem_grows_trans; [exact MG04 | exact MG5]|]. repeat split; assumption.
  Qed.
End UA.
End DUP.
