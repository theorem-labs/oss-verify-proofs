(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagKit_b Ba0DiagChk_b Ba0DiagMemcpy_b Ba0DiagStrnlen_b Ba0DiagGlue_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DiagRP_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DRP.
Import DK. Import DSN. Import DG. Import AS0DIAGRP.

Lemma u8s_of_u32 (M : word -> option byte) a w b0 b1 b2 b3 : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a w ->
  map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 w)) = [b0; b1; b2; b3] ->
  L5.u8_at RSEGS M a b0 /\ L5.u8_at RSEGS M (a + 1) b1 /\ L5.u8_at RSEGS M (a + 2) b2 /\ L5.u8_at RSEGS M (a + 3) b3.
Proof.
  intros Ha Hb C E. unfold L5.u32_at in C. unfold L5.u8_at.
  destruct (word_to_le_bytes 4 (Z_to_bv 64 w)) as [|c0 [|c1 [|c2 [|c3 [|]]]]] eqn:EL; try discriminate E.
  cbn [map] in E. injection E as E0 E1 E2 E3.
  assert (X : forall c b, bv_unsigned c = b -> (c : byte) = Z_to_bv 8 b) by (intros c b <-; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (Ba0DiagStrlen_b.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as R0. pose proof (Ba0DiagStrlen_b.rdn_byte_at M a _ _ 1%nat C ltac:(lia) Ha ltac:(lia)) as R1.
  pose proof (Ba0DiagStrlen_b.rdn_byte_at M a _ _ 2%nat C ltac:(lia) Ha ltac:(lia)) as R2. pose proof (Ba0DiagStrlen_b.rdn_byte_at M a _ _ 3%nat C ltac:(lia) Ha ltac:(lia)) as R3.
  cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ] in R0, R1, R2, R3. rewrite Z.add_0_r in R0.
  rewrite (X c0 b0 E0) in R0. rewrite (X c1 b1 E1) in R1. rewrite (X c2 b2 E2) in R2. rewrite (X c3 b3 E3) in R3.
  repeat split; assumption.
Qed.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 687464.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1293512.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 127251.      (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1282048.
  Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
  Hypothesis Hn : n = 1.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147466776 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Definition read_mid (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    (forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M' x = M x) /\ mem_grows M M'
    /\ getr R' (reg 1) = Z_to_bv 64 1187080
    /\ getr R' (reg 10) = Z_to_bv 64 p
    /\ getr R' (reg 11) = Z_to_bv 64 1
    /\ getr R' (reg 12) = Z_to_bv 64 1293512
    /\ getr R' (reg 13) = Z_to_bv 64 (S - 445)
    /\ getr R' (reg 14) = Z_to_bv 64 0
    /\ getr R' (reg 15) = Z_to_bv 64 3
    /\ getr R' (reg 18) = Z_to_bv 64 0
    /\ getr R' (reg 24) = Z_to_bv 64 0
    /\ getr R' (reg 25) = Z_to_bv 64 1
    /\ getr R' (reg 26) = Z_to_bv 64 1
    /\ getr R' (reg 27) = Z_to_bv 64 1
    /\ L5.u64_at RSEGS M' 1293552 (S - 445)
    /\ L5.u64_at RSEGS M' (S - 1016) 0
    /\ L5.u64_at RSEGS M' (S - 992) 1
    /\ L5.u64_at RSEGS M' (S - 1008) 1
    /\ L5.u64_at RSEGS M' (S - 1024) 69053
    /\ L5.u64_at RSEGS M' (S - 1000) 0
    /\ getr R' (reg 2) = Z_to_bv 64 (S - 1024)
    /\ getr R' (reg 8) = Z_to_bv 64 37
    /\ getr R' (reg 9) = Z_to_bv 64 2147483647
    /\ getr R' (reg 19) = Z_to_bv 64 19
    /\ getr R' (reg 20) = Z_to_bv 64 1293512
    /\ getr R' (reg 21) = Z_to_bv 64 127272
    /\ getr R' (reg 22) = Z_to_bv 64 0
    /\ getr R' (reg 23) = Z_to_bv 64 p
    /\ getr R' (reg 3) = getr R (reg 3)
    /\ getr R' (reg 4) = getr R (reg 4)
    /\ L5.u64_at RSEGS M' (S - 120) 426864
    /\ L5.u64_at RSEGS M' (S - 128) 127251
    /\ L5.u64_at RSEGS M' (S - 136) 1293512
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
    /\ L5.u64_at RSEGS M' 1293600 (S - 464)
    /\ L5.u64_at RSEGS M' 1293608 80
    /\ L5.u64_at RSEGS M' 1293568 (S - 464)
    /\ L5.u64_at RSEGS M' 1293520 0
    /\ L5.u64_at RSEGS M' 1293528 0
    /\ L5.u64_at RSEGS M' 1293544 (S - 384)
    /\ L5.u64_at RSEGS M' (S - 488) 1184288
    /\ L5.u64_at RSEGS M' (S - 496) 1293512
    /\ L5.u64_at RSEGS M' (S - 504) 127251
    /\ L5.u64_at RSEGS M' (S - 512) 6896960
    /\ L5.u64_at RSEGS M' (S - 520) 1
    /\ L5.u64_at RSEGS M' (S - 528) 6898968
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
    /\ L5.u64_at RSEGS M' (S - 928) 6896960
    /\ L5.u64_at RSEGS M' (S - 592) can
    /\ L5.u64_at RSEGS M' (S - 944) 75913
    /\ L5.u64_at RSEGS M' (S - 920) 214748364
    /\ L5.u64_at RSEGS M' (S - 976) 18446744073709486079
    /\ L5.u64_at RSEGS M' (S - 480) (S - 40)
    /\ L5.u64_at RSEGS M' (S - 912) p
    /\ L5.u64_at RSEGS M' (S - 56) 687464
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
    /\ L5.u64_at RSEGS M' 2147466784 0
    /\ L5.u64_at RSEGS M' 2147466776 0
    /\ L5.u64_at RSEGS M' 1293584 1180112
    /\ L5.u64_at RSEGS M' 6896960 can
    /\ L5.u64_at RSEGS M' 1283272 1218816
    /\ L5.u64_at RSEGS M' 1282896 1184024
    /\ L5.u64_at RSEGS M' 1309752 2147450880
    /\ L5.u32_at RSEGS M' 1293512 5
    /\ L5.u32_at RSEGS M' 1293648 18446744073709551615
    /\ L5.u32_at RSEGS M' 1293632 2
    /\ L5.u32_at RSEGS M' 1293656 4294967295
    /\ L5.u32_at RSEGS M' 1293652 4294967295
    /\ L5.u8_at RSEGS M' 1293512 5
    /\ L5.u8_at RSEGS M' (p + 1) 0
    /\ L5.u8_at RSEGS M' (S - 464) 99
    /\ L5.u8_at RSEGS M' (S - 463) 108
    /\ L5.u8_at RSEGS M' (S - 462) 105
    /\ L5.u8_at RSEGS M' (S - 461) 58
    /\ L5.u8_at RSEGS M' (S - 460) 32
    /\ L5.u8_at RSEGS M' (S - 459) 114
    /\ L5.u8_at RSEGS M' (S - 458) 101
    /\ L5.u8_at RSEGS M' (S - 457) 97
    /\ L5.u8_at RSEGS M' (S - 456) 100
    /\ L5.u8_at RSEGS M' (S - 455) 32
    /\ L5.u8_at RSEGS M' (S - 454) 101
    /\ L5.u8_at RSEGS M' (S - 453) 114
    /\ L5.u8_at RSEGS M' (S - 452) 114
    /\ L5.u8_at RSEGS M' (S - 451) 111
    /\ L5.u8_at RSEGS M' (S - 450) 114
    /\ L5.u8_at RSEGS M' (S - 449) 32
    /\ L5.u8_at RSEGS M' (S - 448) 111
    /\ L5.u8_at RSEGS M' (S - 447) 110
    /\ L5.u8_at RSEGS M' (S - 446) 32
    /\ L5.u8_at RSEGS M' 1906620 1
    /\ L5.u8_at RSEGS M' 1313049 1
    /\ L5.u8_at RSEGS M' 1313048 1.

  Theorem read_pre : exists fx5 R5 M5, msteps RSEGS (st fx R 0x633bc M) (st fx5 R5 0x121e2c M5) /\ read_mid R5 M5.
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    pose proof (u64_of_zeros M 2147466776 (L5KA.zeros_at_sub M 2147466776 16 2147466776 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64.
    pose proof (u64_of_zeros M 2147466784 (L5KA.zeros_at_sub M 2147466776 16 2147466784 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64b.
    assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    LeanFeed.pfeed P (drA_conc fx R M (fun j => match j with 2%nat => S | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    assert (AG02 : forall x : word, bv_unsigned x < S - 5440 \/ S <= bv_unsigned x -> M2 x = M x) by (intros x Hx; rewrite AG2 by lia; apply AG1; lia).
    assert (AG12 : forall x : word, bv_unsigned x < S - 2424 \/ S - 2352 <= bv_unsigned x -> M2 x = M1 x) by (intros x Hx; apply AG2; lia).
    assert (W2 : L5.writable RSEGS M2 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D2 : L5.defined M2 (S - 5440) 5440) by (eapply defined_grows; [exact MG2 | eapply defined_grows; eassumption]).
    assert (IMG2 : L5.img_clear M2 65536 1282048) by (apply (imgc_ext M M2); [intros x Hx; apply AG02; lia | lia | lia | exact HIMG]).
    assert (FW2 : L5.writable RSEGS M2 1293512 152) by (eapply writable_grows; [exact MG2 | eapply writable_grows; eassumption]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (SK2 : L5KA.zeros_at M2 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M2); [intros x Hx; apply AG02; unfold SB in Hx; lia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    LeanFeed.pfeed P (drB_conc fx1 R2 M2 (fun j => match j with 2%nat => S - 2352 | 33%nat => p | 34%nat => n | 40%nat => can
       | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 120%nat => U R2 20 | 121%nat => U R2 21 | 122%nat => U R2 22 | 123%nat => U R2 23 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx3 R3 M3 MG3 FR3 FZ3 MS3 KS3.
    (* [comment removed for export] *)
    assert (AG23 : forall x : word, bv_unsigned x < S - 3248 \/ S - 112 <= bv_unsigned x -> ~ filew (bv_unsigned x) -> M3 x = M2 x) by (intros x Hx Hf; unfold filew in Hf; apply FR3; lia).
    assert (A03 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M3 x = M x) by (intros x Hx Hf; rewrite AG23 by (first [exact Hf | lia]); apply AG02; lia).
    assert (MG03 : mem_grows M M3) by (eapply mem_grows_trans; [exact MG1|]; eapply mem_grows_trans; [exact MG2 | exact MG3]).
    assert (W3 : L5.writable RSEGS M3 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D3 : L5.defined M3 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG3 : L5.img_clear M3 65536 1282048) by (apply (imgc_ext M M3); [intros x Hx; apply A03; flia | lia | lia | exact HIMG]).
    assert (STR3 : cstr M3 p bs t8) by (apply (cstr_ext M M3); [lia | lia | intros x Hx; apply A03; flia | exact HSTR]).
    assert (HSN3 : sn_cells M3) by (apply (sn_cells_agree M M3 S); [lia | exact A03 | exact HSN]).
    assert (HSH3 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M3 x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold SB in Hx. rewrite A03 by flia. apply HSH. exact Hx. }
    destruct (wrap_strnlen_run fx3 R3 M3 (S - 1024) p bs t8) as (fx4 & R4 & M4 & MS4 & V4 & KS4 & FR4 & MG4);
      [ sc | sc | sc | sc | lia | (replace (S - 1024) with (S + (-64) * 16) by lia); rewrite Z_mod_plus_full; exact Hal
      | dk_gmem | dk_gmem | exact IMG3 | lia | lia | exact STR3 | exact HSH3 | exact HSN3 | ].
    (* [comment removed for export] *)
    assert (AG34 : forall x : word, bv_unsigned x < S - 5424 \/ S - 1024 <= bv_unsigned x -> M4 x = M3 x) by (intros x Hx; apply FR4; lia).
    assert (A04 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M4 x = M x) by (intros x Hx Hf; rewrite AG34 by lia; apply A03; assumption).
    assert (MG04 : mem_grows M M4) by (eapply mem_grows_trans; eassumption).
    assert (W4 : L5.writable RSEGS M4 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D4 : L5.defined M4 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG4 : L5.img_clear M4 65536 1282048) by (apply (imgc_ext M M4); [intros x Hx; apply A04; flia | lia | lia | exact HIMG]).
    assert (STR4 : cstr M4 p bs t8) by (apply (cstr_ext M M4); [lia | lia | intros x Hx; apply A04; flia | exact HSTR]).
    assert (FW4 : L5.writable RSEGS M4 1293512 152) by (eapply writable_grows; eassumption).
    pose proof (cstr_nul M4 p bs t8 ltac:(lia) ltac:(lia) STR4) as NUL4. rewrite Hn in NUL4.
    assert (F84 : L5.u8_at RSEGS M4 1293512 5).
    { apply u8_of_u32_5; [lia | lia|]. scc. }
    LeanFeed.pfeed P (drD_conc fx4 R4 M4 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx5 R5 M5 MG5 FR5 FZ5 MS5 KS5.
    (* [comment removed for export] *)
    assert (AG45 : forall x : word, bv_unsigned x < S - 3248 \/ S - 976 <= bv_unsigned x -> ~ (1293552 <= bv_unsigned x < 1293560) -> M5 x = M4 x) by (intros x Hx Hf; apply FR5; lia).
    assert (AG35 : forall x : word, bv_unsigned x < S - 5424 \/ S - 976 <= bv_unsigned x -> ~ (1293552 <= bv_unsigned x < 1293560) -> M5 x = M3 x) by (intros x Hx Hf; rewrite AG45 by (first [exact Hf | lia]); apply AG34; lia).
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
    replace (0x674b0%bv : word) with (Z_to_bv 64 0x674b0) in RUN2 by (apply bv_eq; reflexivity).
    replace (0x67414%bv : word) with (Z_to_bv 64 0x67414) in RUN2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    destruct (u8s_of_u32 M5 (S - 464) 979987555 99 108 105 58) as (Y0 & Y1 & Y2 & Y3); [lia | lia | assumption | vm_compute; reflexivity|].
    destruct (u8s_of_u32 M5 (S - 460) 1634038304 32 114 101 97) as (Y4 & Y5 & Y6 & Y7); [lia | lia | assumption | vm_compute; reflexivity|].
    destruct (u8s_of_u32 M5 (S - 456) 1919230052 100 32 101 114) as (Y8 & Y9 & Y10 & Y11); [lia | lia | assumption | vm_compute; reflexivity|].
    destruct (u8s_of_u32 M5 (S - 452) 544370546 114 111 114 32) as (Y12 & Y13 & Y14 & Y15); [lia | lia | assumption | vm_compute; reflexivity|].
    cbn [Z.add] in Y1, Y2, Y3, Y5, Y6, Y7, Y9, Y10, Y11, Y13, Y14, Y15.
    exists fx5, R5, M5. split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4|]. exact MS5. }
    unfold read_mid. split; [exact A05|]. split; [eapply mem_grows_trans; [exact MG04 | exact MG5]|].
    repeat split; try assumption;
      lazymatch goal with |- L5.u8_at _ _ ?a _ => first [ replace a with (S - 464 + 1) by lia; assumption | replace a with (S - 464 + 2) by lia; assumption | replace a with (S - 464 + 3) by lia; assumption
        | replace a with (S - 460 + 1) by lia; assumption | replace a with (S - 460 + 2) by lia; assumption | replace a with (S - 460 + 3) by lia; assumption
        | replace a with (S - 456 + 1) by lia; assumption | replace a with (S - 456 + 2) by lia; assumption | replace a with (S - 456 + 3) by lia; assumption
        | replace a with (S - 452 + 1) by lia; assumption | replace a with (S - 452 + 2) by lia; assumption | replace a with (S - 452 + 3) by lia; assumption ] end.
  Qed.
End UA.
End DRP.
