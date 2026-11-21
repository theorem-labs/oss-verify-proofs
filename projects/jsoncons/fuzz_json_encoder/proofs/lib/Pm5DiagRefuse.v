(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed refuse_run; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9DiagRefuse.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 66-125. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
     Pm5RegionPoisoned Pm5AsanMemcpy Pm5DiagKit Pm5DiagChk Pm5DiagMemcpy Pm5DiagStrnlen Pm5DiagGlue Pm5DiagFix Pm5DiagRP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.L5FastLia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagGlue; @DG; @diag_cells]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u8_at]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @AsanUbsan; @M; @loaded_segments]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u32_at]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @writable]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Datatypes; @list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagRefuse; @DRF; @MSGR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagGlue; @DG; @agree0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @u64_of_zeros]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_upper_bound]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DiagRP; @AS0DIAGRP; @dfA_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DiagRP; @AS0DIAGRP; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @img_clear]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5KnA; @L5KA; @zeros_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DiagRP; @AS0DIAGRP; @KS_dfA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @writable_sub]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5KnA; @L5KA; @zeros_at_sub]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagGlue; @DG; @filew]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @writable_grows]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagGlue; @DG; @wv_entry_stage]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma2]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Corelib; @Init; @Logic; @I]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEeval]; [@Stdlib; @setoid_ring; @Ring_theory; @IDphi]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pphi_pow]; [@Stdlib; @setoid_ring; @InitialRing; @get_signZ]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pc]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @u32_ext]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagFix; @DFX; @u8_of_u32]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Lists; @ListDef; @nth]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @rdn_cons]; [@Stdlib; @setoid_ring; @Ring_polynom; @PX]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Corelib; @Lists; @ListDef; @map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @rdn_xfer]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps_trans]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @defined_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @imgc_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DiagRP; @AS0DIAGRP; @dfG_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @U]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DiagRP; @AS0DIAGRP; @KS_dfG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @UR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Kn; @L5K; @in_b]; [@Stdlib; @Lists; @List; @existsb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @U_to]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagKit; @DK; @u64_ext]].
 Local Ltac lia := L5FastLia.plia.
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

Ltac shz0 := lazymatch goal with |- L5KA.zeros_at ?M (?S / 8 + ?d) ?l => unfold SB in *; dk_gmem end.

Section RF.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S can : Z).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 723940.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1477960.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 112088.      (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 67108864.    (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1466368.
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
  Hypothesis HFMT : L5KA.zeros_at M 2147464888 8.               (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.

  Theorem refuse_run :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6c238 M) (st fxE RE 0x14ce10 ME)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1477960 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE (reg 22) = Z_to_bv 64 38
      /\ L5.u64_at RSEGS ME (S - 584) (S - 464) /\ L5.u64_at RSEGS ME (S - 576) 38 /\ L5.u64_at RSEGS ME (S - 568) 0 /\ L5.u64_at RSEGS ME (S - 560) 0
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 38 = Some MSGR
      /\ L5.u32_at RSEGS ME 1478080 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxF RF MF,
              msteps RSEGS (st fx' RX 0x14ce1c MX) (st fxF RF 0x14538c MF)
              /\ getr RF (reg 10) = Z_to_bv 64 2 /\ getr RF (reg 2) = Z_to_bv 64 S
              /\ agree0 M MF S /\ mem_grows M MF
              /\ L5.u32_at RSEGS MF 1477960 5 /\ L5.u64_at RSEGS MF 1478056 0 /\ L5.u64_at RSEGS MF 1478048 7086248
              /\ L5.u64_at RSEGS MF 1478016 0 /\ L5.u64_at RSEGS MF 1478000 0 /\ L5.u64_at RSEGS MF 1477992 0 /\ L5.u64_at RSEGS MF 1477968 0 /\ L5.u64_at RSEGS MF 1477976 0 /\ getr RF (reg 4) = getr R (reg 4)).
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    pose proof (u64_of_zeros M 2147464888 HFMT ltac:(lia) ltac:(lia)) as HFMT64.
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    pose proof (dfA_conc fx R M (fun j => match j with 2%nat => S | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz | shz0]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
    assert (A01 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M1 x = M x) by (intros x Hx Hf; unfold filew in Hf; apply FR1; lia).
    assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    (* [comment removed for export] *)
    assert (NE : Z.eqb (S - 426) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx1 R1 M1 1477960 (S - 592) 0 0 (S - 426) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG1W & MGW);
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
    (* [comment removed for export] *)
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX1 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M1 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG1W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R1 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1466368) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1477960 152) by (eapply writable_grows; eassumption).
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
