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

Module DRF.
Import DK. Import DSN. Import DG. Import AS0DIAGRP.

(* [comment removed for export] *)
Definition MSGR : list byte := map (Z_to_bv 8)
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].

(* [comment removed for export] *)
Ltac rdn_bytes :=
  repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
  reflexivity.

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

Ltac shz0 := lazymatch goal with |- L5KA.zeros_at ?M (?S / 8 + ?d) ?l => unfold SB in *; dk_gmem end.

Section RF.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S can : Z).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 687464.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1293512.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 108788.      (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 67108864.    (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1282048.
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
  Hypothesis HFMT : L5KA.zeros_at M 2147464472 16.               (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.

  Theorem refuse_run :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x633bc M) (st fxE RE 0x120258 ME)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1293512 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE (reg 22) = Z_to_bv 64 38
      /\ L5.u64_at RSEGS ME (S - 584) (S - 464) /\ L5.u64_at RSEGS ME (S - 576) 38 /\ L5.u64_at RSEGS ME (S - 568) 0 /\ L5.u64_at RSEGS ME (S - 560) 0
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 38 = Some MSGR
      /\ L5.u32_at RSEGS ME 1293632 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxF RF MF,
              msteps RSEGS (st fx' RX 0x120264 MX) (st fxF RF 0x118878 MF)
              /\ getr RF (reg 10) = Z_to_bv 64 2 /\ getr RF (reg 2) = Z_to_bv 64 S
              /\ agree0 M MF S /\ mem_grows M MF
              /\ L5.u32_at RSEGS MF 1293512 5 /\ L5.u64_at RSEGS MF 1293608 0 /\ L5.u64_at RSEGS MF 1293600 6898968
              /\ L5.u64_at RSEGS MF 1293568 0 /\ L5.u64_at RSEGS MF 1293552 0 /\ L5.u64_at RSEGS MF 1293544 0 /\ L5.u64_at RSEGS MF 1293520 0 /\ L5.u64_at RSEGS MF 1293528 0 /\ getr RF (reg 4) = getr R (reg 4)).
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    pose proof (u64_of_zeros M 2147464472 (L5KA.zeros_at_sub M 2147464472 16 2147464472 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64.
    pose proof (u64_of_zeros M 2147464480 (L5KA.zeros_at_sub M 2147464472 16 2147464480 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64b.
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    LeanFeed.pfeed P (dfA_conc fx R M (fun j => match j with 2%nat => S | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz | shz0]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
    assert (A01 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M1 x = M x) by (intros x Hx Hf; unfold filew in Hf; apply FR1; lia).
    assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    (* [comment removed for export] *)
    assert (NE : Z.eqb (S - 426) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx1 R1 M1 1293512 (S - 592) 0 0 (S - 426) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG1W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG1W by lia; apply A01; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    (* [comment removed for export] *)
    assert (BUF1 : rdn RSEGS M1 (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (unfold MSGR; cbn [map]; rdn_bytes).
    assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (apply (rdn_xfer M1 MW); [intros x Hx; apply AG1W; cbn in Hx; lia | lia | cbn; lia | exact BUF1]).
    exists fx1, RW, MW.
    split. { eapply msteps_trans; [exact MS1|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact I0|]. split; [replace (S - 426 - (S - 464)) with 38 in I1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact I1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact I2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact I3|].
    split; [exact BUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    (* [comment removed for export] *)
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX1 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M1 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG1W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R1 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1282048) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1293512 152) by (eapply writable_grows; eassumption).
    LeanFeed.pfeed P (dfG_conc fx' RX MX (fun j => match j with 2%nat => S - 592 | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 118%nat => U RX 18 | 119%nat => U RX 19 | 120%nat => U RX 20 | 122%nat => U RX 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|]. split; [sc|]. split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGX0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0X | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M1); [intros x Hx; rewrite FRF by lia; apply AGX1; lia | lia | lia | eassumption])
                       | (rewrite (KSF 4%nat), (KX 4%nat), (KS1 4%nat) by (first [apply L5K.in_b; vm_compute; reflexivity | cbn; tauto]); reflexivity)].
  Qed.
End RF.
End DRF.
