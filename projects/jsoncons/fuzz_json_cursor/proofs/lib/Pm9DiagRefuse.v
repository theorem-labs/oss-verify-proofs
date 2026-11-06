(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
     Pm9RegionPoisoned Pm9AsanMemcpy Pm9DiagKit Pm9DiagChk Pm9DiagMemcpy Pm9DiagStrnlen Pm9DiagGlue Pm9DiagFix Pm9DiagRP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DRF.
Import DK. Import DSN. Import DG. Import AS0DIAGRP.

Definition MSGR : list byte := map (Z_to_bv 8)
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].

Ltac rdn_bytes :=
  repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
  reflexivity.

Ltac shz0 := lazymatch goal with |- L5KA.zeros_at ?M (?S / 8 + ?d) ?l => unfold SB in *; dk_gmem end.

Section RF.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S can : Z).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 717576.
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1412392.
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 111136.
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 67108864.
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1400832.
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
  Hypothesis HFMT : L5KA.zeros_at M 2147464768 16.
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.

  Theorem refuse_run :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6a95c M) (st fxE RE 0x13ce18 ME)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1412392 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE (reg 22) = Z_to_bv 64 38
      /\ L5.u64_at RSEGS ME (S - 584) (S - 464) /\ L5.u64_at RSEGS ME (S - 576) 38 /\ L5.u64_at RSEGS ME (S - 568) 0 /\ L5.u64_at RSEGS ME (S - 560) 0
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 38 = Some MSGR
      /\ L5.u32_at RSEGS ME 1412512 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxF RF MF,
              msteps RSEGS (st fx' RX 0x13ce24 MX) (st fxF RF 0x135394 MF)
              /\ getr RF (reg 10) = Z_to_bv 64 2 /\ getr RF (reg 2) = Z_to_bv 64 S
              /\ agree0 M MF S /\ mem_grows M MF
              /\ L5.u32_at RSEGS MF 1412392 5 /\ L5.u64_at RSEGS MF 1412488 0 /\ L5.u64_at RSEGS MF 1412480 7021992
              /\ L5.u64_at RSEGS MF 1412448 0 /\ L5.u64_at RSEGS MF 1412432 0 /\ L5.u64_at RSEGS MF 1412424 0 /\ L5.u64_at RSEGS MF 1412400 0 /\ L5.u64_at RSEGS MF 1412408 0 /\ getr RF (reg 4) = getr R (reg 4)).
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    pose proof (u64_of_zeros M 2147464768 (L5KA.zeros_at_sub M 2147464768 16 2147464768 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64.
    pose proof (u64_of_zeros M 2147464776 (L5KA.zeros_at_sub M 2147464768 16 2147464776 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64b.
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).

    pose proof (dfA_conc fx R M (fun j => match j with 2%nat => S | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz | shz0]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
    assert (A01 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M1 x = M x) by (intros x Hx Hf; unfold filew in Hf; apply FR1; lia).
    assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).

    assert (NE : Z.eqb (S - 426) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx1 R1 M1 1412392 (S - 592) 0 0 (S - 426) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG1W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG1W by lia; apply A01; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).

    assert (RB464_0 : L5.u8_at RSEGS M1 (S - 464) 99) by (apply (DFX.u8_of_u32 M1 (S - 464) (S - 464) 979987555 0%nat 99); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB464_1 : L5.u8_at RSEGS M1 (S - 463) 108) by (apply (DFX.u8_of_u32 M1 (S - 464) (S - 463) 979987555 1%nat 108); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB464_2 : L5.u8_at RSEGS M1 (S - 462) 105) by (apply (DFX.u8_of_u32 M1 (S - 464) (S - 462) 979987555 2%nat 105); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB464_3 : L5.u8_at RSEGS M1 (S - 461) 58) by (apply (DFX.u8_of_u32 M1 (S - 464) (S - 461) 979987555 3%nat 58); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB460_0 : L5.u8_at RSEGS M1 (S - 460) 32) by (apply (DFX.u8_of_u32 M1 (S - 460) (S - 460) 1886284064 0%nat 32); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB460_1 : L5.u8_at RSEGS M1 (S - 459) 105) by (apply (DFX.u8_of_u32 M1 (S - 460) (S - 459) 1886284064 1%nat 105); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB460_2 : L5.u8_at RSEGS M1 (S - 458) 110) by (apply (DFX.u8_of_u32 M1 (S - 460) (S - 458) 1886284064 2%nat 110); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB460_3 : L5.u8_at RSEGS M1 (S - 457) 112) by (apply (DFX.u8_of_u32 M1 (S - 460) (S - 457) 1886284064 3%nat 112); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB456_0 : L5.u8_at RSEGS M1 (S - 456) 117) by (apply (DFX.u8_of_u32 M1 (S - 456) (S - 456) 1042314357 0%nat 117); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB456_1 : L5.u8_at RSEGS M1 (S - 455) 116) by (apply (DFX.u8_of_u32 M1 (S - 456) (S - 455) 1042314357 1%nat 116); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB456_2 : L5.u8_at RSEGS M1 (S - 454) 32) by (apply (DFX.u8_of_u32 M1 (S - 456) (S - 454) 1042314357 2%nat 32); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (RB456_3 : L5.u8_at RSEGS M1 (S - 453) 62) by (apply (DFX.u8_of_u32 M1 (S - 456) (S - 453) 1042314357 3%nat 62); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (BUF1 : rdn RSEGS M1 (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (unfold MSGR; cbn [map]; rdn_bytes).
    assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (apply (rdn_xfer M1 MW); [intros x Hx; apply AG1W; cbn in Hx; lia | lia | cbn; lia | exact BUF1]).
    exists fx1, RW, MW.
    split. { eapply msteps_trans; [exact MS1|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact I0|]. split; [replace (S - 426 - (S - 464)) with 38 in I1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact I1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact I2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact I3|].
    split; [exact BUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].

    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX1 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M1 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG1W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R1 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1400832) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1412392 152) by (eapply writable_grows; eassumption).
    pose proof (dfG_conc fx' RX MX (fun j => match j with 2%nat => S - 592 | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 118%nat => U RX 18 | 119%nat => U RX 19 | 120%nat => U RX 20 | 122%nat => U RX 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
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
