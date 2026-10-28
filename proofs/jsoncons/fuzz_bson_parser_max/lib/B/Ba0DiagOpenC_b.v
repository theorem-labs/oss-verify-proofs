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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagKit_b Ba0DiagChk_b Ba0DiagMemcpy_b Ba0DiagStrnlen_b Ba0DiagGlue_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DiagOP_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DiagOpenPre_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DOC.
Import DK. Import DSN. Import DG. Import AS0DIAGOP.

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
(* [comment removed for export] *)
Ltac rdn_bytes :=
  repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
  reflexivity.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 687464.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1293512.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 127230.      (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1282048.
  Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
  Hypothesis Hn : 64 <= n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147466776 16.               (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Definition PRE17 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127230) 17 with Some l => l | None => [] end.
  Definition SUF1 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127249) 1 with Some l => l | None => [] end.
  Lemma suf1_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 127249) 1 = Some SUF1.  Proof. vm_compute. reflexivity. Qed.
  Lemma PRE17_eq : PRE17 = map (Z_to_bv 8) [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].
  Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
  Lemma SUF1_len : length SUF1 = 1%nat.  Proof. reflexivity. Qed.

  Theorem open_C_tail : forall fx5 R5 M5, DOP.open_mid R M S p can bs R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x121e2c M5) (st fxE RE 0x120258 ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1293512 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 17)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 17 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 17 = Some PRE17 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1293632 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x120264 MX) (st fxE2 RE2 0x120258 ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1293512 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 1
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 1 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 1 = Some SUF1
              /\ L5.u32_at RSEGS ME2 1293632 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x120264 MY) (st fxF RF 0x118878 MF)
                      /\ getr RF (reg 10) = Z_to_bv 64 2 /\ getr RF (reg 2) = Z_to_bv 64 S
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1293512 5 /\ L5.u64_at RSEGS MF 1293608 0 /\ L5.u64_at RSEGS MF 1293600 6898968
                      /\ L5.u64_at RSEGS MF 1293568 0 /\ L5.u64_at RSEGS MF 1293552 0 /\ L5.u64_at RSEGS MF 1293544 0 /\ L5.u64_at RSEGS MF 1293520 0 /\ L5.u64_at RSEGS MF 1293528 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    intros fx5 R5 M5 INV.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.
    (* [comment removed for export] *)
    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1282048) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    LeanFeed.pfeed P (doDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
    (* [comment removed for export] *)
    assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (NE : Z.eqb (S - 447) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx8 R8 M8 1293512 (S - 1136) p n (S - 447) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
    assert (P17_5 : rdn RSEGS M5 (Z_to_bv 64 (S - 464)) 17 = Some PRE17).
    { rewrite PRE17_eq. cbn [map].
      rdn_bytes. }
    assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 17 = Some PRE17) by (apply (rdn_xfer M5 MW); [intros x Hx; apply AG5W; cbn in Hx; lia | lia | cbn; lia | exact P17_5]).
    assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
    assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STRW as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    exists fx8, RW, MW.
    split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 447 - (S - 464)) with 17 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
    split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
    split; [exact P7W|]. split; [exact RDSW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    (* [comment removed for export] *)
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1282048) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1293512 152) by (eapply writable_grows; eassumption).
    assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
    { apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (F8X : L5.u8_at RSEGS MX 1293512 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
    assert (FMTX : L5KA.zeros_at MX 2147466776 16) by (apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HFMT]).
    pose proof (u64_of_zeros MX 2147466776 (L5KA.zeros_at_sub MX 2147466776 16 2147466776 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X1.
    pose proof (u64_of_zeros MX 2147466784 (L5KA.zeros_at_sub MX 2147466776 16 2147466784 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X2.
    LeanFeed.pfeed P (doEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
    (* [comment removed for export] *)
    assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1293544 <= bv_unsigned x < 1293560) -> ~ (1293568 <= bv_unsigned x < 1293576) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1293544 <= bv_unsigned x < 1293560) -> ~ (1293568 <= bv_unsigned x < 1293576) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
    assert (NE2 : Z.eqb (S - 463) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx9 R9 M9 1293512 (S - 592) 0 0 (S - 463) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE2 in X11, X12, X18, X19.
    assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
    assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
    assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 1 = Some SUF1).
    { replace SUF1 with [Z_to_bv 8 10 : byte] by (symmetry; apply list_bv_eq; vm_compute; reflexivity).
      assert (C10 : L5.u8_at RSEGS MW2 (S - 464) 10) by (eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]; match goal with |- _ _ _ ?a _ => try (progress (ring_simplify a)) end; assumption).
      exact C10. }
    exists fx9, RW2, MW2.
    split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
    split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
    split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 463 - (S - 464)) with 1 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
    split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
    (* [comment removed for export] *)
    intros fx'' RY MY AGYW MGYW KYW.
    assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
    assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
    assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
    assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
    assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1293544 <= bv_unsigned x < 1293560) -> ~ (1293568 <= bv_unsigned x < 1293576) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
    assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
    assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
    assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGY : L5.img_clear MY 65536 1282048) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
    assert (FWY : L5.writable RSEGS MY 1293512 152) by (eapply writable_grows; eassumption).
    LeanFeed.pfeed P (doGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split; [sc|].
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.

  Theorem open_C :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x633bc M) (st fxE RE 0x120258 ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1293512 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 17)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 17 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 17 = Some PRE17 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1293632 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x120264 MX) (st fxE2 RE2 0x120258 ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1293512 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 1
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 1 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 1 = Some SUF1
              /\ L5.u32_at RSEGS ME2 1293632 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x120264 MY) (st fxF RF 0x118878 MF)
                      /\ getr RF (reg 10) = Z_to_bv 64 2 /\ getr RF (reg 2) = Z_to_bv 64 S
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1293512 5 /\ L5.u64_at RSEGS MF 1293608 0 /\ L5.u64_at RSEGS MF 1293600 6898968
                      /\ L5.u64_at RSEGS MF 1293568 0 /\ L5.u64_at RSEGS MF 1293552 0 /\ L5.u64_at RSEGS MF 1293544 0 /\ L5.u64_at RSEGS MF 1293520 0 /\ L5.u64_at RSEGS MF 1293528 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    destruct (DOP.open_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (open_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DOC.
