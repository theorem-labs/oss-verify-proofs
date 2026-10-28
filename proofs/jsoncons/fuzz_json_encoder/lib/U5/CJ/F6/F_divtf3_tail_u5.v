(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers3.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_wide.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_core2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_multf3_core_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_multf3_tail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_core_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_wide_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_round_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Numbers; @BinNums; @Z]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_u5; @rsegs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Datatypes; @nil]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_round_u5; @saved12]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @div_core]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_wide_u5; @divtf3_midC]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_u5; @divtf3_post]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@Corelib; @Init; @Datatypes; @None]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_wide_u5; @divtf3_core12]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @ex]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @divc_tail]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_expM1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_aSigHiI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_bSigHiI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_aHi2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_aLoTop]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_core_u5; @E_a2Lo]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Corelib; @Numbers; @BinNums; @xH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @eq_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_divtf3_tail_u5; @Walk; @L5r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lor]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Logic; @proj1]; [@Corelib; @Init; @Datatypes; @bool]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Walk.
  Variables (sp sgw w6 : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation sgn := (bv_unsigned sgw).
  Notation bLo := (bv_unsigned w6).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  Ltac exact_HR :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

  (* [comment removed for export] *)
  Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
      y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
    (0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
    (-100000 <= wE <= 32766)%Z ->
    R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
          F (Z_to_bv 64 0xb7b60) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K; sgn_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
      + join Lzero. rewrite HR. apply DC6_tiny. lia.
      + do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
        zstep. if_cases K3; zify_cond K3; sgn_cond K3.
        * (* [comment removed for export] *)
          do 5 zstep. unland.
          model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
                                   (Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
          rng absLo.
          zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4.
          -- (* [comment removed for export] *)
             do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
              zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
          -- (* [comment removed for export] *)
             do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
              zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
        * (* [comment removed for export] *)
          do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
          zstep. unland.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
          do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
           zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
           zstep.
           zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
           zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
           zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
           zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
           zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
           zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
           zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
           zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
           zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
           zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
           do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
           zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
           zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
           zstep. model_reg 17 odd (Z.land absLo 1).
           zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
           zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
           zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
           zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
           all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
           all: join Lround.
           all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
    - (* [comment removed for export] *)
      assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
      do 2 zstep. unland.
      model_reg 14 fracHi (Z.land q1Hi 281474976710655).
      do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
      zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
      zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
      zstep. model_reg 17 odd (Z.land q1Lo 1).
      zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
      zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
      zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
      zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
        flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
        (join Lround;
         rewrite HR, DC6_normal, div_round_DRr by lia; unland;
         change (Z.land q1Hi 281474976710655) with fracHi;
         change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
         change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
         change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
         fold_model_lets2; reflexivity).
  Time Qed.

  (* [comment removed for export] *)
  Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
      y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
    (0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
    (-20000 <= expM1 <= 60000)%Z ->
    R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
               (Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
          F (Z_to_bv 64 0xb7a24) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
      zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
      zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
      zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
      zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
      zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
      zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
      zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
      zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
      zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
      zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
      zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
      zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
      do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
      + rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
        rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
      + join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
    - (* [comment removed for export] *)
      assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
      { rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
      zstep. name_as bit112 (Z.shiftr q_hi 48).
      zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
      assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
      zstep. rewrite (land63_id sh) by lia.
      zstep. zstep.
      assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
      rewrite Hamt.
      zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
      zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
      zstep. if_cases Kb; zify_cond Kb.
      * (* [comment removed for export] *)
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        + (* [comment removed for export] *) join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
      * (* [comment removed for export] *)
        zstep.
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        + (* [comment removed for export] *) join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
  Time Qed.

  (* [comment removed for export] *)
  Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
      y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 0xb7754) fc None m1 (seg_rom rsegs)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "Sd80|600;!1,10!1+01|21;|500;|30;!1+0!1,15%~R2!1+46!2+:+2+2!2'=1/sp;|630;!2'<9!1,>:!2'B9!1,C:|<000;!2'F,H#^0|?0000;!1,>?!2+G>!2'I#^0@|:000;!1,CB!1,>B!2'=1/sgw;!2'=1/w6;|10;!1,>G!1,>0!2'MHI!2+G!2'F,H9!2'I9J!2+G!2'F,HE!2'IEJ!2'=1#^:!2+G!2'F,HM!2'IMJvd!1'L#^:N!2+G!2'F,HF!2'IFJ!2'P1<|^27fffffffffff;!2'P1!1,>R!2'P1#^:!2'P1#^9!2'P1#^;!1,T2!1'U'7!2'=1#^Q!2'=1#^P!2'=1#^O!2+G!2'F,H#@!2'I#@J!2+G!2'F,H#?!2'I#?J!3'[#^M#^L#^K!1,>|511;!2'P1!2'^4#@^2!2'P1#@!1,>,^5!2'P1#?!2'P1!1,>|C37a24;!2'=1#^S!2'=1#^R!3'[#^P#^O#^N!1'\^8!1'^0Y!1'^1^8!1'^2^9!1'^3^9!3'[#^O#^N#^M!2'=1#^T!2'=1#^V!2'=1#^U!3'[#^S#^R#^Q!1'\^B!1'^0^A!1'^1^B!1'^2^C!1'^3^C!2+G!2'F,H#C!2'I#CJ!3'[#^R#^Q#^P!2'P1#C!2'=1#^W!2'=1#^Y!2'=1#^X!3'[#^V#^U#^T!1'\^N!1'^0^M!1'^1^N!1'^2^O!1'^3^O!2+G!2'F,H#F!2'I#FJ!3'[#^U#^T#^S!2'P1#F!2'=1#^Z!2'=1#^\!2'=1#^[!3'[#^Y#^X#^W!1'\^Z!1'^0^Y!1'^1^Z!1'^2^[!1'^3^[!2+G!2'F,H#I!2'I#IJ!3'[#^X#^W#^V!2'P1#I!2'=1#_0!2'=1#_2!2'=1#_1!3'[#^\#^[#^Z!1'\_9!1'^0_8!1'^1_9!1'^2_:!1'^3_:!2+G!2'F,H#L!2'I#LJ!3'[#^[#^Z#^Y!2'P1#L!2'=1#_3!2'=1#_5!2'=1#_4!3'[#_2#_1#_0!1'\_E!1'^0_D!1'^1_E!1'^2_F!1'^3_F!2+G!2'F,H#O!2'I#OJ!3'[#_1#_0#^\!2'P1#O!2'=1#_6!2'=1#_8!2'=1#_7!3'[#_5#_4#_3!1'\_Q!1'^0_P!1'^1_Q!1'^2_R!1'^3_R!2+G!2'F,H#R!2'I#RJ!3'[#_4#_3#_2!2'P1#R!2'=1#_9!2'=1#_;!2'=1#_:!3'[#_8#_7#_6!1'\`0!1'^0_\!1'^1`0!1'^2`1!1'^3`1!2+G!2'F,H#U!2'I#UJ!3'[#_7#_6#_5!2'P1#U!2'=1#_<!2'=1#_>!2'=1#_=!3'[#_;#_:#_9!1'\`<!1'^0`;!1'^1`<!1'^2`=!1'^3`=!2+G!2'F,H#X!2'I#XJ!3'[#_:#_9#_8!2'P1#X!2'=1#_?!2'=1#_A!2'=1#_@!3'[#_>#_=#_<!1'\`H!1'^0`G!1'^1`H!1'^2`I!1'^3`I!2+G!2'F,H#[!2'I#[J!3'[#_=#_<#_;!2'P1#[!2'=1#_B!2'=1#_D!2'=1#_C!3'[#_A#_@#_?!1'\`T!1'^0`S!1'^1`T!1'^2`U!1'^3`U!2+G!2'F,H#^1!2'I#^1J!3'[#_@#_?#_>!2'P1#^1!2'=1#_E!2'=1#_G!2'=1#_F!3'[#_D#_C#_B!1'\a3!1'^0a2!1'^1a3!1'^2a4!1'^3a4!2+G!2'F,H#^4!2'I#^4J!3'[#_C#_B#_A!2'P1#^4!2'=1#_H!2'=1#_J!2'=1#_I!3'[#_G#_F#_E!1'\a?!1'^0a>!1'^1a?!1'^2a@!1'^3a@!2+G!2'F,H#^7!2'I#^7J!3'[#_F#_E#_D!2'P1#^7!2'=1#_K!2'=1#_M!2'=1#_L!3'[#_J#_I#_H!1'\aK!1'^0aJ!1'^1aK!1'^2aL!1'^3aL!2+G!2'F,H#^:!2'I#^:J!3'[#_I#_H#_G!2'=1#_N!2'=1#_P!2'=1#_O!3'[#_M#_L#_K!1'\aV!1'^0aU!1'^1aV!1'^2aW!1'^3aW!2+G!2'F,H#^=!2'I#^=J!3'[#_L#_K#_J!2'P1#^=!2'=1#_Q!2'=1#_S!2'=1#_R!3'[#_P#_O#_N!1'\b5!1'^0b4!1'^1b5!1'^2b6!1'^3b6!2+G!2'F,H#^@!2'I#^@J!3'[#_O#_N#_M!2'P1#^@!2'=1#_T%sgn;R+2!3+J+2!8'K#1#_P#_Ob@b5b6F#_Q!;'Z#1!3'[#_Q#_P#_O#^B#^>b5!1'\b@!1'^0b6F!1'^1b@!1'^2b5!1'^3b5!2+G!2'F,H#^A!2'I#^AJ!2'P1#^A!2'=1#_V!2'=1#_U!3'[#_S#_R#_Q!1'\bD!1'^0b@!1'^1bD!1'^2bE!1'^3bE!2+G!2'F,H#^D!2'I#^DJ!2'P1#^D!2+G!2'F,H#^E!2'I#^EJ!3'[#_T#_S#_R!2'=1#_W!2'P1#^E!2+G!2'F,H#^G!2'I#^GJ!3'[#_W#_V#_U!2'=1#_Y!2'=1#_Z!2'P1#^H!3'[#_X#_W#_V!2'=1#_[!2'P1#^I!3'[#_[#_Z#_Y!2'=1#`0!2'=1#`1!3'[#_\#_[#_Z!1'^2b\!2'=1#`2!1'^1c2!1'^0b[!1'^3b\!1'\c2!;'ZEc0#^M#^Ib\c6c4Fc3c1c5!3'[#`0#_\#_[!2'=1#`3!1'\c9!1'^0b\!1'^1c9!1'^2c2!1'^3c2!1,>|^3000000000000;!2'F,Hc?!2'Ic?J!3+J+^?!2'^@,Hc?,^A!2,^C+^?,^A!3+J+^?!2'^Dc?J,^A!2'^<c?!4,^=c@cA!4'^>%~RcBc@%~Rc@cB!2'^B,Hc?cC!4'^>%~RcDcA%~RcAcD!2'^Ec?JcC!1,>|^B7fffffffffffffff;!2'F,HcF!2'IcFJ!3+J+^?!2'^@,HcF,^A!3+J+^?!2'^DcFJ,^A!4,^=cGcH!4'^>%~RcIcG%~RcGcI!2'^B,HcFcC!4'^>%~RcJcH%~RcHcJ!2'^EcFJcC|51f;!1,>cL!3+J+^?!2'^@,HcM,^A!2'F,HcM!2'F,HH}5}4}1!2,^P+2,^Q}3}2!1+^W+2!2,_3+2,^5!1,T+^Y!2,_1+2,H|11;!2,_3+2c[!2,_1+2@!2,_3+2G!1,C|>0e20;!1,>|=1ffe;!3,_6+2!3,_6+2cX!2,_1+2d3!3,_7+2d1c\!1,>|?6a60;!2+G!2'F,H#4!2'I#4@!2'B!2'B#4d3!2'<#5#6$ra;R2$gp;R2$tp;R2$w3;R2$w4;R2$w5;R2$scale;R+2$ea;R+2$eb;R+2$s0;R2$s1;R2$a3;R2$a4;R2$a5;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$t4;R2$t5;R2$t6;R2$y1;R2$y8;R2$y9;R2$y18;R2$y19;R2$y20;R2$y21;R2$y22;R2$y23;R2$y24;R2$y25;R2$y26;R2$y27;R2$F;R!2'3!1,132$fc;R!1+0!1,14$m;R7$m1;R7$j;R!1+56$R;R+2$MI;R!2'6'7#3$MU;R!3'8!3,98!4,;+2+2;9!1,?8#5#4$WM;R!3'@'7#6#5$ST;R!4'A'7#6;<$FR;R!4'D'7#7<!>'E#K#L#M#N#O#P#Q#R#S#T#X#Y#^5#6$SPLO;R!2'F!1,>=9$Ra;RA$Rb;RA$Rsc;R!2+G!2'FC#^3!2'F#^3D$HR;R!3+J+2#:!8'KE#^3#^2!2'=1#^7!2'=1#^6!2'=1#^5F#^4&H;Rvd!1'L/sp;KK&H0;Rvd!1'L/sgw;LL&H1;RON&H2;RON&H3;RON&H4;Rvd!1'L/w6;PP!6'N'7!?'O#^>#^=#^</w6;#^:#^9#^;Q#^@#^?/sgw;S#F#E#C!D'Q#^A/sp;#^@#^?#^8#^7#^3#^2#^1#^0#\#[#Z#Y#X#W#F#E#A#D!7'R!O'S#SQ#^@#^?#^<TU#R#Q#^=/sgw;/w6;#^6#^5#^4S#^>#P#O#N#M#L#K#J#I#H#GV#V#U#T#F!2'P1!1,>|C37754;#EW#CX!V'V#^>#^=#^</w6;#^:#^9#^;#SQ#^@#^?#R#Q/sgw;#^6#^5#^4S#P#O#N#M#L#K#J#I#H#G#V#U#T#F#E#C#@#:#9#8$ms';R+W$P;R!@'O#^?#^>#^=/w6;#^;#^:#^<Q#^A#^@/sgw;S#G#F#D#1!5'X+2$q_hi;R+2!2+Y+2$q_lo;R+2!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^M#^LYZ[F#^N!;'Z#1!3'[#^N#^M#^L#A#@Z!1'\Y!1'^0[F!1'^1Y!1'^2Z!1'^3Z!2+G\!2+G^0!3+J+W#B!7'R!O'S#>Q#^R#^Q!2'P1^1!2'P1!1'^2[!2'P1!1'^1Z#=#<#^O/sgw;/w6;!2'P1!1'^0!2'=1#^N!2'P1!1'^3[^3S!2'P1!1'\Z#;#:#9#8#7#6#5#4#3#2^4!2'P1!2'B^1^5^6#1#X^7#WW#UX!3'^6'7!D'Q#^C/sp;#^B#^A#^:#^9#^5#^4#^3#^2#^1#^0#\#[#Z#Y#H#G#C#F#2$x;R+2$~R!1$q_hi;R+2!2+Y+2$q_lo;R+2!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^N#^M!2'=1#^R!2'=1#^Q!2'=1#^PF#^O!;'Z#1!3'[#^O#^N#^M#A#@!2'=1#^Q!1'\!2'=1#^R!1'^0!2'=1#^PF!1'^1!2'=1#^R!1'^2!2'=1#^Q!1'^3!2'=1#^Q!2+G\!2+G^0!3+J+W#C!7'R!O'S#>Q#^S#^R!2'P1!3'[#^N#^M#^L!2'P1!1'^2!2'=1#^P!2'P1!1'^1!2'=1#^Q#=#<#^P/sgw;/w6;!2'P1!1'^0!2'=1#^O!2'P1!1'^3!2'=1#^P^3S!2'P1!1'\!2'=1#^Q#;#:#9#8#7#6#5#4#3#2^4!2'P1!2'B!3'[#^N#^M#^L^5^6#1#Y^7#XW#VX#1!2$q_hi;R+2$H5;R!2+Y+2$q_lo;R+2!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^O#^N^8^9YF#^P!;'Z#1^:#A#@^9^;^<F^=^>^?!2+G\!2+G^0!3+J+W#D!7'R!O'S#>Q#^T#^S!2'P1^@!2'P1!1'^2Y!2'P1!1'^1^9#=#<#^Q/sgw;/w6;!2'P1!1'^0Z!2'P1!1'^3Y^3S!2'P1!1'\^9#;#:#9#8#7#6#5#4#3#2^4!2'P1!2'B^@^5^6#1#Z^7#YW#WX!5'X+2$q_lo;R+2!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^P#^O^A^8^9F#^Q!;'Z#1!3'[#^Q#^P#^O#B#@^8!1'\^A!1'^0^9F!1'^1^A!1'^2^8!1'^3^8!2+G!2+G!2'F,H#A!2'I#AJ!2+G^0!3+J+W#E!7'R!O'S#>Q#^U#^T!2'P1^:!2'P1^>!2'P1^=#=#<#^R/sgw;/w6;!2'P1^<!2'P1^?!2'P1!2'^4#A^2S!2'P1^;#;#:#9#8#7#6#5#4#3#2!2'P1#A!2'P1!2'B^:^5^6#1#[^7#ZW#XX!3'^6'7!D'Q#^G/sp;#^F#^E#^>#^=#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#L#K#G#J#6$x;R+2$~R!1$q_lo;R+2!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^Q#^P!2'=1#^U!2'=1#^T!2'=1#^SF#^R!;'Z#1!3'[#^R#^Q#^P#C#@!2'=1#^T!1'\!2'=1#^U!1'^0!2'=1#^SF!1'^1!2'=1#^U!1'^2!2'=1#^T!1'^3!2'=1#^T!2+G!2+G!2'F,H#B!2'I#BJ!2+G^0!3+J+W#F!7'R!O'S#>Q#^V#^U!2'P1!3'[#^Q#^P#^O!2'P1!1'^2!2'=1#^S!2'P1!1'^1!2'=1#^T#=#<#^S/sgw;/w6;!2'P1!1'^0!2'=1#^R!2'P1!1'^3!2'=1#^S!2'P1!2'^4#B^2S!2'P1!1'\!2'=1#^T#;#:#9#8#7#6#5#4#3#2!2'P1#B!2'P1!2'B!3'[#^Q#^P#^O^5^6#1#\^7#[W#YX#1!2$q_lo;R+2$H5;R!2+Y2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^R#^Q^B^C^AF#^S!;'Z#1^D#D#@^C^E^FF^G^H^I!2+G^J!2+G^0!3+J+W#G!7'R!O'S#>Q#^W#^V!2'P1^K!2'P1!1'^2^A!2'P1!1'^1^C#=#<#^T/sgw;/w6;!2'P1!1'^0^8!2'P1!1'^3^A!2'P1!2'^4#C^2S!2'P1!1'\^C#;#:#9#8#7#6#5#4#3#2^L!2'P1!2'B^K^5^6#1#^0^7#\W#ZX!5'X2$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^S#^R^M^B^CF#^T!;'Z#1!3'[#^T#^S#^R#E#A^B!1'\^M!1'^0^CF!1'^1^M!1'^2^B!1'^3^B!2+G!2+G!2'F,H#D!2'I#DJ!2+G\!3+J+W#H!7'R!O'S#>Q#^X#^W!2'P1^D!2'P1^H!2'P1^G#=#<#^U/sgw;/w6;!2'P1^F!2'P1^I!2'P1!2'^4#D^2S!2'P1^E#;#:#9#8#7#6#5#4#3#2!2'P1#D!2'P1!2'B^D^5^4#1#^1^7#^0W#[X!3'^6'7!D'Q#^K/sp;#^J#^I#^B#^A#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#P#O#K#N#:$x;R2$~R!1$y1;R2!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^T#^S!2'=1#^X!2'=1#^W!2'=1#^VF#^U!;'Z#1!3'[#^U#^T#^S#F#B!2'=1#^W!1'\!2'=1#^X!1'^0!2'=1#^VF!1'^1!2'=1#^X!1'^2!2'=1#^W!1'^3!2'=1#^W!2+G!2+G!2'F,H#E!2'I#EJ!2+G!2+G!2'F,H#A!2'I#AJ!3+J+W#I!7'R!O'S#>Q#^Y#^X!2'P1!3'[#^T#^S#^R!2'P1!1'^2!2'=1#^V!2'P1!1'^1!2'=1#^W#=#<#^V/sgw;/w6;!2'P1!1'^0!2'=1#^U!2'P1!1'^3!2'=1#^V!2'P1!2'^4#E^2S!2'P1!1'\!2'=1#^W#;#:#9#8#7#6#5#4#3#2!2'P1#E!2'P1!2'B!3'[#^T#^S#^R^5!2'P1#A#1#^2^7#^1W#\X#1!2$z1;R2$H5;R!2+Y2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^U#^T^N^O^MF#^V!;'Z#1^P#G#C^O^Q^RF^S^T^U!2+G^V!2+G!2+G!2'F,H#B!2'I#BJ!3+J+W#J!7'R!O'S#>Q#^Z#^Y!2'P1^W!2'P1!1'^2^M!2'P1!1'^1^O#=#<#^W/sgw;/w6;!2'P1!1'^0^B!2'P1!1'^3^M!2'P1!2'^4#F^2S!2'P1!1'\^O#;#:#9#8#7#6#5#4#3#2^X!2'P1!2'B^W^5!2'P1#B#1#^3^7#^2W#^0X!5'X2$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^V#^U^Y^N^OF#^W!;'Z#1!3'[#^W#^V#^U#H#D^N!1'\^Y!1'^0^OF!1'^1^Y!1'^2^N!1'^3^N!2+G!2+G!2'F,H#G!2'I#GJ!2+G^J!3+J+W#K!7'R!O'S#?Q#^[#^Z!2'P1^P!2'P1^T!2'P1^S#=#<#^X/sgw;/w6;!2'P1^R!2'P1^U!2'P1!2'^4#G^2S!2'P1^Q#;#:#9#8#7#6#5#4#3#2!2'P1#G!2'P1!2'B^P^5^L#1#^4^7#^3W#^1X!3'^6'7!D'Q#^O/sp;#^N#^M#^F#^E#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#T#S#O#R#>$x;R2$~R!1$y8;R2!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^W#^V!2'=1#^[!2'=1#^Z!2'=1#^YF#^X!;'Z#1!3'[#^X#^W#^V#I#E!2'=1#^Z!1'\!2'=1#^[!1'^0!2'=1#^YF!1'^1!2'=1#^[!1'^2!2'=1#^Z!1'^3!2'=1#^Z!2+G!2+G!2'F,H#H!2'I#HJ!2+G!2+G!2'F,H#D!2'I#DJ!3+J+W#L!7'R!O'S#@Q#^\#^[!2'P1!3'[#^W#^V#^U!2'P1!1'^2!2'=1#^Y!2'P1!1'^1!2'=1#^Z#=#<#^Y/sgw;/w6;!2'P1!1'^0!2'=1#^X!2'P1!1'^3!2'=1#^Y!2'P1!2'^4#H^2S!2'P1!1'\!2'=1#^Z#;#:#9#8#7#6#5#4#3#2!2'P1#H!2'P1!2'B!3'[#^W#^V#^U^5!2'P1#D#1#^5^7#^4W#^2X#1!2$z8;R2$H5;R!2+Y2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^X#^W^Z^[^YF#^Y!;'Z#1^\#J#F^[_0_1F_2_3_4!2+G_5!2+G!2+G!2'F,H#E!2'I#EJ!3+J+W#M!7'R!O'S#AQ#_0#^\!2'P1_6!2'P1!1'^2^Y!2'P1!1'^1^[#=#<#^Z/sgw;/w6;!2'P1!1'^0^N!2'P1!1'^3^Y!2'P1!2'^4#I^2S!2'P1!1'\^[#;#:#9#8#7#6#5#4#3#2_7!2'P1!2'B_6^5!2'P1#E#1#^6^7#^5W#^3X!5'X2$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^Y#^X_8^Z^[F#^Z!;'Z#1!3'[#^Z#^Y#^X#K#G^Z!1'\_8!1'^0^[F!1'^1_8!1'^2^Z!1'^3^Z!2+G!2+G!2'F,H#J!2'I#JJ!2+G^V!3+J+W#N!7'R!O'S#BQ#_1#_0!2'P1^\!2'P1_3!2'P1_2#>#<#^[/sgw;/w6;!2'P1_1!2'P1_4!2'P1!2'^4#J^2S!2'P1_0#;#:#9#8#7#6#5#4#3#2!2'P1#J!2'P1!2'B^\^5^X#1#^7^7#^6W#^4X!3'^6'7!D'Q#^S/sp;#^R#^Q#^J#^I#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#X#W#S#V#B$x;R2$~R!1$y9;R2!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^Z#^Y!2'=1#_1!2'=1#_0!2'=1#^\F#^[!;'Z#1!3'[#^[#^Z#^Y#L#H!2'=1#_0!1'\!2'=1#_1!1'^0!2'=1#^\F!1'^1!2'=1#_1!1'^2!2'=1#_0!1'^3!2'=1#_0!2+G!2+G!2'F,H#K!2'I#KJ!2+G!2+G!2'F,H#G!2'I#GJ!3+J+W#O!7'R!O'S#CQ#_2#_1!2'P1!3'[#^Z#^Y#^X!2'P1!1'^2!2'=1#^\!2'P1!1'^1!2'=1#_0#?#<#^\/sgw;/w6;!2'P1!1'^0!2'=1#^[!2'P1!1'^3!2'=1#^\!2'P1!2'^4#K^2S!2'P1!1'\!2'=1#_0#;#:#9#8#7#6#5#4#3#2!2'P1#K!2'P1!2'B!3'[#^Z#^Y#^X^5!2'P1#G#1#^8^7#^7W#^5X#1!2$z9;R2$H5;R!2+Y2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^[#^Z_9_:_8F#^\!;'Z#1_;#M#I_:_<_=F_>_?_@!2+G_A!2+G!2+G!2'F,H#H!2'I#HJ!3+J+W#P!7'R!O'S#DQ#_3#_2!2'P1_B!2'P1!1'^2_8!2'P1!1'^1_:#@#<#_0/sgw;/w6;!2'P1!1'^0^Z!2'P1!1'^3_8!2'P1!2'^4#L^2S!2'P1!1'\_:#;#:#9#8#7#6#5#4#3#2_C!2'P1!2'B_B^5!2'P1#H#1#^9^7#^8W#^6X!5'X2$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#^\#^[_D_9_:F#_0!;'Z#1!3'[#_0#^\#^[#N#J_9!1'\_D!1'^0_:F!1'^1_D!1'^2_9!1'^3_9!2+G!2+G!2'F,H#M!2'I#MJ!2+G_5!3+J+W#Q!7'R!O'S#EQ#_4#_3!2'P1_;!2'P1_?!2'P1_>#A#=#_1/sgw;/w6;!2'P1_=!2'P1_@!2'P1!2'^4#M^2S!2'P1_<#;#:#9#8#7#6#5#4#3#2!2'P1#M!2'P1!2'B_;^5_7#1#^:^7#^9W#^7X!3'^6'7!D'Q#^W/sp;#^V#^U#^N#^M#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#\#[#W#Z#F$x;R2$~R!1$y18;R2!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_0#^\!2'=1#_4!2'=1#_3!2'=1#_2F#_1!;'Z#1!3'[#_1#_0#^\#O#K!2'=1#_3!1'\!2'=1#_4!1'^0!2'=1#_2F!1'^1!2'=1#_4!1'^2!2'=1#_3!1'^3!2'=1#_3!2+G!2+G!2'F,H#N!2'I#NJ!2+G!2+G!2'F,H#J!2'I#JJ!3+J+W#R!7'R!O'S#FQ#_5#_4!2'P1!3'[#_0#^\#^[!2'P1!1'^2!2'=1#_2!2'P1!1'^1!2'=1#_3#B#>#_2/sgw;/w6;!2'P1!1'^0!2'=1#_1!2'P1!1'^3!2'=1#_2!2'P1!2'^4#N^2S!2'P1!1'\!2'=1#_3#;#:#9#8#7#6#5#4#3#2!2'P1#N!2'P1!2'B!3'[#_0#^\#^[^5!2'P1#J#1#^;^7#^:W#^8X#1!2$z18;R2$H5;R!2+Y2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_1#_0_E_F_DF#_2!;'Z#1_G#P#L_F_H_IF_J_K_L!2+G_M!2+G!2+G!2'F,H#K!2'I#KJ!3+J+W#S!7'R!O'S#GQ#_6#_5!2'P1_N!2'P1!1'^2_D!2'P1!1'^1_F#C#?#_3/sgw;/w6;!2'P1!1'^0_9!2'P1!1'^3_D!2'P1!2'^4#O^2S!2'P1!1'\_F#;#:#9#8#7#6#5#4#3#2_O!2'P1!2'B_N^5!2'P1#K#1#^<^7#^;W#^9X!5'X2$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_2#_1_P_E_FF#_3!;'Z#1!3'[#_3#_2#_1#Q#M_E!1'\_P!1'^0_FF!1'^1_P!1'^2_E!1'^3_E!2+G!2+G!2'F,H#P!2'I#PJ!2+G_A!3+J+W#T!7'R!O'S#HQ#_7#_6!2'P1_G!2'P1_K!2'P1_J#D#@#_4/sgw;/w6;!2'P1_I!2'P1_L!2'P1!2'^4#P^2S!2'P1_H#<#:#9#8#7#6#5#4#3#2!2'P1#P!2'P1!2'B_G^5_C#1#^=^7#^<W#^:X!3'^6'7!D'Q#^[/sp;#^Z#^Y#^R#^Q#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^3#^2#[#^1#J$x;R2$~R!1$y19;R2!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_3#_2!2'=1#_7!2'=1#_6!2'=1#_5F#_4!;'Z#1!3'[#_4#_3#_2#R#N!2'=1#_6!1'\!2'=1#_7!1'^0!2'=1#_5F!1'^1!2'=1#_7!1'^2!2'=1#_6!1'^3!2'=1#_6!2+G!2+G!2'F,H#Q!2'I#QJ!2+G!2+G!2'F,H#M!2'I#MJ!3+J+W#U!7'R!O'S#IQ#_8#_7!2'P1!3'[#_3#_2#_1!2'P1!1'^2!2'=1#_5!2'P1!1'^1!2'=1#_6#E#A#_5/sgw;/w6;!2'P1!1'^0!2'=1#_4!2'P1!1'^3!2'=1#_5!2'P1!2'^4#Q^2S!2'P1!1'\!2'=1#_6#=#:#9#8#7#6#5#4#3#2!2'P1#Q!2'P1!2'B!3'[#_3#_2#_1^5!2'P1#M#1#^>^7#^=W#^;X#1!2$z19;R2$H5;R!2+Y2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_4#_3_Q_R_PF#_5!;'Z#1_S#S#O_R_T_UF_V_W_X!2+G_Y!2+G!2+G!2'F,H#N!2'I#NJ!3+J+W#V!7'R!O'S#JQ#_9#_8!2'P1_Z!2'P1!1'^2_P!2'P1!1'^1_R#F#B#_6/sgw;/w6;!2'P1!1'^0_E!2'P1!1'^3_P!2'P1!2'^4#R^2S!2'P1!1'\_R#>#:#9#8#7#6#5#4#3#2_[!2'P1!2'B_Z^5!2'P1#N#1#^?^7#^>W#^<X!5'X2$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_5#_4_\_Q_RF#_6!;'Z#1!3'[#_6#_5#_4#T#P_Q!1'\_\!1'^0_RF!1'^1_\!1'^2_Q!1'^3_Q!2+G!2+G!2'F,H#S!2'I#SJ!2+G_M!3+J+W#W!7'R!O'S#KQ#_:#_9!2'P1_S!2'P1_W!2'P1_V#G#C#_7/sgw;/w6;!2'P1_U!2'P1_X!2'P1!2'^4#S^2S!2'P1_T#?#;#9#8#7#6#5#4#3#2!2'P1#S!2'P1!2'B_S^5_O#1#^@^7#^?W#^=X!3'^6'7!D'Q#_2/sp;#_1#_0#^V#^U#^Q#^P#^O#^N#^M#^L#^K#^J#^I#^H#^7#^6#^2#^5#N$x;R2$~R!1$y20;R2!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_6#_5!2'=1#_:!2'=1#_9!2'=1#_8F#_7!;'Z#1!3'[#_7#_6#_5#U#Q!2'=1#_9!1'\!2'=1#_:!1'^0!2'=1#_8F!1'^1!2'=1#_:!1'^2!2'=1#_9!1'^3!2'=1#_9!2+G!2+G!2'F,H#T!2'I#TJ!2+G!2+G!2'F,H#P!2'I#PJ!3+J+W#X!7'R!O'S#LQ#_;#_:!2'P1!3'[#_6#_5#_4!2'P1!1'^2!2'=1#_8!2'P1!1'^1!2'=1#_9#H#D#_8/sgw;/w6;!2'P1!1'^0!2'=1#_7!2'P1!1'^3!2'=1#_8!2'P1!2'^4#T^2S!2'P1!1'\!2'=1#_9#@#<#9#8#7#6#5#4#3#2!2'P1#T!2'P1!2'B!3'[#_6#_5#_4^5!2'P1#P#1#^A^7#^@W#^>X#1!2$z20;R2$H5;R!2+Y2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_7#_6`0`1_\F#_8!;'Z#1`2#V#R`1`3`4F`5`6`7!2+G`8!2+G!2+G!2'F,H#Q!2'I#QJ!3+J+W#Y!7'R!O'S#MQ#_<#_;!2'P1`9!2'P1!1'^2_\!2'P1!1'^1`1#I#E#_9/sgw;/w6;!2'P1!1'^0_Q!2'P1!1'^3_\!2'P1!2'^4#U^2S!2'P1!1'\`1#A#=#9#8#7#6#5#4#3#2`:!2'P1!2'B`9^5!2'P1#Q#1#^B^7#^AW#^?X!5'X2$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_8#_7`;`0`1F#_9!;'Z#1!3'[#_9#_8#_7#W#S`0!1'\`;!1'^0`1F!1'^1`;!1'^2`0!1'^3`0!2+G!2+G!2'F,H#V!2'I#VJ!2+G_Y!3+J+W#Z!7'R!O'S#NQ#_=#_<!2'P1`2!2'P1`6!2'P1`5#J#F#_:/sgw;/w6;!2'P1`4!2'P1`7!2'P1!2'^4#V^2S!2'P1`3#B#>#:#8#7#6#5#4#3#2!2'P1#V!2'P1!2'B`2^5_[#1#^C^7#^BW#^@X!3'^6'7!D'Q#_6/sp;#_5#_4#^Z#^Y#^U#^T#^S#^R#^Q#^P#^O#^N#^M#^L#^;#^:#^6#^9#R$x;R2$~R!1$y21;R2!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_9#_8!2'=1#_=!2'=1#_<!2'=1#_;F#_:!;'Z#1!3'[#_:#_9#_8#X#T!2'=1#_<!1'\!2'=1#_=!1'^0!2'=1#_;F!1'^1!2'=1#_=!1'^2!2'=1#_<!1'^3!2'=1#_<!2+G!2+G!2'F,H#W!2'I#WJ!2+G!2+G!2'F,H#S!2'I#SJ!3+J+W#[!7'R!O'S#OQ#_>#_=!2'P1!3'[#_9#_8#_7!2'P1!1'^2!2'=1#_;!2'P1!1'^1!2'=1#_<#K#G#_;/sgw;/w6;!2'P1!1'^0!2'=1#_:!2'P1!1'^3!2'=1#_;!2'P1!2'^4#W^2S!2'P1!1'\!2'=1#_<#C#?#;#8#7#6#5#4#3#2!2'P1#W!2'P1!2'B!3'[#_9#_8#_7^5!2'P1#S#1#^D^7#^CW#^AX#1!2$z21;R2$H5;R!2+Y2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_:#_9`<`=`;F#_;!;'Z#1`>#Y#U`=`?`@F`A`B`C!2+G`D!2+G!2+G!2'F,H#T!2'I#TJ!3+J+W#\!7'R!O'S#PQ#_?#_>!2'P1`E!2'P1!1'^2`;!2'P1!1'^1`=#L#H#_</sgw;/w6;!2'P1!1'^0`0!2'P1!1'^3`;!2'P1!2'^4#X^2S!2'P1!1'\`=#D#@#<#8#7#6#5#4#3#2`F!2'P1!2'B`E^5!2'P1#T#1#^E^7#^DW#^BX!5'X2$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_;#_:`G`<`=F#_<!;'Z#1!3'[#_<#_;#_:#Z#V`<!1'\`G!1'^0`=F!1'^1`G!1'^2`<!1'^3`<!2+G!2+G!2'F,H#Y!2'I#YJ!2+G`8!3+J+W#^0!7'R!O'S#QQ#_@#_?!2'P1`>!2'P1`B!2'P1`A#M#I#_=/sgw;/w6;!2'P1`@!2'P1`C!2'P1!2'^4#Y^2S!2'P1`?#E#A#=#9#7#6#5#4#3#2!2'P1#Y!2'P1!2'B`>^5`:#1#^F^7#^EW#^CX!3'^6'7!D'Q#_:/sp;#_9#_8#_1#_0#^Y#^X#^W#^V#^U#^T#^S#^R#^Q#^P#^?#^>#^:#^=#V$x;R2$~R!1$y22;R2!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_<#_;!2'=1#_@!2'=1#_?!2'=1#_>F#_=!;'Z#1!3'[#_=#_<#_;#[#W!2'=1#_?!1'\!2'=1#_@!1'^0!2'=1#_>F!1'^1!2'=1#_@!1'^2!2'=1#_?!1'^3!2'=1#_?!2+G!2+G!2'F,H#Z!2'I#ZJ!2+G!2+G!2'F,H#V!2'I#VJ!3+J+W#^1!7'R!O'S#RQ#_A#_@!2'P1!3'[#_<#_;#_:!2'P1!1'^2!2'=1#_>!2'P1!1'^1!2'=1#_?#N#J#_>/sgw;/w6;!2'P1!1'^0!2'=1#_=!2'P1!1'^3!2'=1#_>!2'P1!2'^4#Z^2S!2'P1!1'\!2'=1#_?#F#B#>#:#7#6#5#4#3#2!2'P1#Z!2'P1!2'B!3'[#_<#_;#_:^5!2'P1#V#1#^G^7#^FW#^DX#1!2$z22;R2$H5;R!2+Y2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_=#_<`H`I`GF#_>!;'Z#1`J#\#X`I`K`LF`M`N`O!2+G`P!2+G!2+G!2'F,H#W!2'I#WJ!3+J+W#^2!7'R!O'S#SQ#_B#_A!2'P1`Q!2'P1!1'^2`G!2'P1!1'^1`I#O#K#_?/sgw;/w6;!2'P1!1'^0`<!2'P1!1'^3`G!2'P1!2'^4#[^2S!2'P1!1'\`I#G#C#?#;#7#6#5#4#3#2`R!2'P1!2'B`Q^5!2'P1#W#1#^H^7#^GW#^EX!5'X2$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_>#_=`S`H`IF#_?!;'Z#1!3'[#_?#_>#_=#^0#Y`H!1'\`S!1'^0`IF!1'^1`S!1'^2`H!1'^3`H!2+G!2+G!2'F,H#\!2'I#\J!2+G`D!3+J+W#^3!7'R!O'S#TQ#_C#_B!2'P1`J!2'P1`N!2'P1`M#P#L#_@/sgw;/w6;!2'P1`L!2'P1`O!2'P1!2'^4#\^2S!2'P1`K#H#D#@#<#8#6#5#4#3#2!2'P1#\!2'P1!2'B`J^5`F#1#^I^7#^HW#^FX!3'^6'7!D'Q#_>/sp;#_=#_<#_5#_4#_0#^\#^[#^Z#^Y#^X#^W#^V#^U#^T#^C#^B#^>#^A#Z$x;R2$~R!1$y23;R2!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_?#_>!2'=1#_C!2'=1#_B!2'=1#_AF#_@!;'Z#1!3'[#_@#_?#_>#^1#Z!2'=1#_B!1'\!2'=1#_C!1'^0!2'=1#_AF!1'^1!2'=1#_C!1'^2!2'=1#_B!1'^3!2'=1#_B!2+G!2+G!2'F,H#^0!2'I#^0J!2+G!2+G!2'F,H#Y!2'I#YJ!3+J+W#^4!7'R!O'S#UQ#_D#_C!2'P1!3'[#_?#_>#_=!2'P1!1'^2!2'=1#_A!2'P1!1'^1!2'=1#_B#Q#M#_A/sgw;/w6;!2'P1!1'^0!2'=1#_@!2'P1!1'^3!2'=1#_A!2'P1!2'^4#^0^2S!2'P1!1'\!2'=1#_B#I#E#A#=#9#6#5#4#3#2!2'P1#^0!2'P1!2'B!3'[#_?#_>#_=^5!2'P1#Y#1#^J^7#^IW#^GX#1!2$z23;R2$H5;R!2+Y2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_@#_?`T`U`SF#_A!;'Z#1`V#^2#[`U`W`XF`Y`Z`[!2+G`\!2+G!2+G!2'F,H#Z!2'I#ZJ!3+J+W#^5!7'R!O'S#VQ#_E#_D!2'P1a0!2'P1!1'^2`S!2'P1!1'^1`U#R#N#_B/sgw;/w6;!2'P1!1'^0`H!2'P1!1'^3`S!2'P1!2'^4#^1^2S!2'P1!1'\`U#J#F#B#>#:#6#5#4#3#2a1!2'P1!2'Ba0^5!2'P1#Z#1#^K^7#^JW#^HX!5'X2$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_A#_@a2`T`UF#_B!;'Z#1!3'[#_B#_A#_@#^3#\`T!1'\a2!1'^0`UF!1'^1a2!1'^2`T!1'^3`T!2+G!2+G!2'F,H#^2!2'I#^2J!2+G`P!3+J+W#^6!7'R!O'S#WQ#_F#_E!2'P1`V!2'P1`Z!2'P1`Y#S#O#_C/sgw;/w6;!2'P1`X!2'P1`[!2'P1!2'^4#^2^2S!2'P1`W#K#G#C#?#;#7#5#4#3#2!2'P1#^2!2'P1!2'B`V^5`R#1#^L^7#^KW#^IX!3'^6'7!D'Q#_B/sp;#_A#_@#_9#_8#_4#_3#_2#_1#_0#^\#^[#^Z#^Y#^X#^G#^F#^B#^E#^1$x;R2$~R!1$y24;R2!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_B#_A!2'=1#_F!2'=1#_E!2'=1#_DF#_C!;'Z#1!3'[#_C#_B#_A#^4#^0!2'=1#_E!1'\!2'=1#_F!1'^0!2'=1#_DF!1'^1!2'=1#_F!1'^2!2'=1#_E!1'^3!2'=1#_E!2+G!2+G!2'F,H#^3!2'I#^3J!2+G!2+G!2'F,H#\!2'I#\J!3+J+W#^7!7'R!O'S#XQ#_G#_F!2'P1!3'[#_B#_A#_@!2'P1!1'^2!2'=1#_D!2'P1!1'^1!2'=1#_E#T#P#_D/sgw;/w6;!2'P1!1'^0!2'=1#_C!2'P1!1'^3!2'=1#_D!2'P1!2'^4#^3^2S!2'P1!1'\!2'=1#_E#L#H#D#@#<#8#5#4#3#2!2'P1#^3!2'P1!2'B!3'[#_B#_A#_@^5!2'P1#\#1#^M^7#^LW#^JX#1!2$z24;R2$H5;R!2+Y2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_C#_Ba3a4a2F#_D!;'Z#1a5#^5#^1a4a6a7Fa8a9a:!2+Ga;!2+G!2+G>!2'I#^0J!3+J+W#^8!7'R!O'S#YQ#_H#_G!2'P1a<!2'P1!1'^2a2!2'P1!1'^1a4#U#Q#_E/sgw;/w6;!2'P1!1'^0`T!2'P1!1'^3a2!2'P1!2'^4#^4^2S!2'P1!1'\a4#M#I#E#A#=#9#5#4#3#2a=!2'P1!2'Ba<^5!2'P1#^0#1#^N^7#^MW#^KX!5'X2$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_D#_Ca>a3a4F#_E!;'Z#1!3'[#_E#_D#_C#^6#^2a3!1'\a>!1'^0a4F!1'^1a>!1'^2a3!1'^3a3!2+G!2+G!2'F,H#^5!2'I#^5J!2+G`\!3+J+W#^9!7'R!O'S#ZQ#_I#_H!2'P1a5!2'P1a9!2'P1a8#V#R#_F/sgw;/w6;!2'P1a7!2'P1a:!2'P1!2'^4#^5^2S!2'P1a6#N#J#F#B#>#:#6#4#3#2!2'P1#^5!2'P1!2'Ba5^5a1#1#^O^7#^NW#^LX!3'^6'7!D'Q#_F/sp;#_E#_D#_=#_<#_8#_7#_6#_5#_4#_3#_2#_1#_0#^\#^K#^J#^F#^I#^5$x;R2$~R!1$y25;R2!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_E#_D!2'=1#_I!2'=1#_H!2'=1#_GF#_F!;'Z#1!3'[#_F#_E#_D#^7#^3!2'=1#_H!1'\!2'=1#_I!1'^0!2'=1#_GF!1'^1!2'=1#_I!1'^2!2'=1#_H!1'^3!2'=1#_H!2+G!2+G!2'F,H#^6!2'I#^6J!2+G!2+G!2'F,H#^2!2'I#^2J!3+J+W#^:!7'R!O'S#[Q#_J#_I!2'P1!3'[#_E#_D#_C!2'P1!1'^2!2'=1#_G!2'P1!1'^1!2'=1#_H#W#S#_G/sgw;/w6;!2'P1!1'^0!2'=1#_F!2'P1!1'^3!2'=1#_G!2'P1!2'^4#^6^2S!2'P1!1'\!2'=1#_H#O#K#G#C#?#;#7#4#3#2!2'P1#^6!2'P1!2'B!3'[#_E#_D#_C^5!2'P1#^2#1#^P^7#^OW#^MX#1!2$z25;R2$H5;R!2+Y2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_F#_Ea?a@a>F#_G!;'Z#1aA#^8#^4a@aBaCFaDaEaF!2+GaG!2+G!2+G!2'F,H#^3!2'I#^3J!3+J+W#^;!7'R!O'S#\Q#_K#_J!2'P1aH!2'P1!1'^2a>!2'P1!1'^1a@#X#T#_H/sgw;/w6;!2'P1!1'^0a3!2'P1!1'^3a>!2'P1!2'^4#^7^2S!2'P1!1'\a@#P#L#H#D#@#<#8#4#3#2aI!2'P1!2'BaH^5!2'P1#^3#1#^Q^7#^PW#^NX!5'X2$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_G#_FaJa?a@F#_H!;'Z#1!3'[#_H#_G#_F#^9#^5a?!1'\aJ!1'^0a@F!1'^1aJ!1'^2a?!1'^3a?!2+G!2+G!2'F,H#^8!2'I#^8J!2+Ga;!3+J+W#^<!7'R!O'S#^0Q#_L#_K!2'P1aA!2'P1aE!2'P1aD#Y#U#_I/sgw;/w6;!2'P1aC!2'P1aF!2'P1!2'^4#^8^2S!2'P1aB#Q#M#I#E#A#=#9#5#3#2!2'P1#^8!2'P1!2'BaA^5a=#1#^R^7#^QW#^OX!3'^6'7!D'Q#_J/sp;#_I#_H#_A#_@#_<#_;#_:#_9#_8#_7#_6#_5#_4#_3#^O#^N#^J#^M#^9$x;R2$~R!1$y26;R2!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_H#_G!2'=1#_L!2'=1#_K!2'=1#_JF#_I!;'Z#1!3'[#_I#_H#_G#^:#^6!2'=1#_K!1'\!2'=1#_L!1'^0!2'=1#_JF!1'^1!2'=1#_L!1'^2!2'=1#_K!1'^3!2'=1#_K!2+G!2+G!2'F,H#^9!2'I#^9J!2+G!2+G!2'F,H#^5!2'I#^5J!3+J+W#^=!7'R!O'S#^1Q#_M#_L!2'P1!3'[#_H#_G#_F!2'P1!1'^2!2'=1#_J!2'P1!1'^1!2'=1#_K#Z#V#_J/sgw;/w6;!2'P1!1'^0!2'=1#_I!2'P1!1'^3!2'=1#_J!2'P1!2'^4#^9^2S!2'P1!1'\!2'=1#_K#R#N#J#F#B#>#:#6#3#2!2'P1#^9!2'P1!2'B!3'[#_H#_G#_F^5!2'P1#^5#1#^S^7#^RW#^PX#1!2$z26;R2$H5;R!2+Y2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_I#_HaKaLaJF#_J!;'Z#1aM#^;#^7aLaNaOFaPaQaR!2+GaS!2+G!2+G!2'F,H#^6!2'I#^6J!3+J+W#^>!7'R!O'S#^2Q#_N#_M!2'P1aT!2'P1!1'^2aJ!2'P1!1'^1aL#[#W#_K/sgw;/w6;!2'P1!1'^0a?!2'P1!1'^3aJ!2'P1!2'^4#^:^2S!2'P1!1'\aL#S#O#K#G#C#?#;#7#3#2T!2'P1!2'BaT^5!2'P1#^6#1#^T^7#^SW#^QX!5'X2$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_J#_IaUaKaLF#_K!;'Z#1!3'[#_K#_J#_I#^<#^8aK!1'\aU!1'^0aLF!1'^1aU!1'^2aK!1'^3aK!2+G!2+G!2'F,H#^;!2'I#^;J!2+GaG!3+J+W#^?!7'R!O'S#^3Q#_O#_N!2'P1aM!2'P1aQ!2'P1aP#\#X#_L/sgw;/w6;!2'P1aO!2'P1aR!2'P1!2'^4#^;^2S!2'P1aN#T#P#L#H#D#@#<#8#4#2V!2'P1!2'BaM^5aI#1#^U^7#^TW#^RX!3'^6'7!D'Q#_N/sp;#_M#_L#_E#_D#_@#_?#_>#_=#_<#_;#_:#_9#_8#_7#^S#^R#^N#^Q#^=$x;R2$~R!1$y27;R2!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_K#_J!2'=1#_O!2'=1#_N!2'=1#_MF#_L!;'Z#1!3'[#_L#_K#_J#^=#^9!2'=1#_N!1'\!2'=1#_O!1'^0!2'=1#_MF!1'^1!2'=1#_O!1'^2!2'=1#_N!1'^3!2'=1#_N!2+G!2+G!2'F,H#^<!2'I#^<J!2+G!2+G!2'F,H#^8!2'I#^8J!3+J+W#^@!7'R!O'S#^4Q#_P#_O!2'P1!3'[#_K#_J#_I!2'P1!1'^2!2'=1#_M!2'P1!1'^1!2'=1#_N#^0#Y#_M/sgw;/w6;!2'P1!1'^0!2'=1#_L!2'P1!1'^3!2'=1#_M!2'P1!2'^4#^<^2S!2'P1!1'\!2'=1#_N#U#Q#M#I#E#A#=#9#5#2!2'P1#^<!2'P1!2'B!3'[#_K#_J#_I^5!2'P1#^8#1#^V^7#^UW#^SX#1!2$z27;R2$H5;R!2+Y2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_L#_KaVaWaUF#_M!;'Z#1aX#^>#^:aWaYaZFa[a\b0!2+Gb1!2+G!2+G!2'F,H#^9!2'I#^9J!3+J+W#^A!7'R!O'S#^5Q#_Q#_P!2'P1b2!2'P1!1'^2aU!2'P1!1'^1aW#^1#Z#_N/sgw;/w6;!2'P1!1'^0aK!2'P1!1'^3aU!2'P1!2'^4#^=^2S!2'P1!1'\aW#V#R#N#J#F#B#>#:#6#2b3!2'P1!2'Bb2^5U#1#^W^7#^VW#^TX!5'X2$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_M#_Lb4aVaWF#_N!;'Z#1!3'[#_N#_M#_L#^?#^;aV!1'\b4!1'^0aWF!1'^1b4!1'^2aV!1'^3aV!2+G!2+G!2'F,H#^>!2'I#^>J!2+GaS!3+J+W#^B!7'R!O'S#^6Q#_R#_Q!2'P1aX!2'P1a\!2'P1a[#^2#[#_O/sgw;/w6;!2'P1aZ!2'P1b0!2'P1!2'^4#^>^2S!2'P1aY#W#S#O#K#G#C#?#;#7#3!2'P1#^>!2'P1!2'BaX^5T#1#^X^7#^WW#^UX!3'^6'7!D'Q#_R/sp;#_Q#_P#_I#_H#_D#_C#_B#_A#_@#_?#_>#_=#_<#_;#^W#^V#^R#^U#^A$x;R2$~R!1$y31;R2!2+G%sgn;R+2!3+J+2!8'K#1#_N#_M!2'=1#_R!2'=1#_Q!2'=1#_PF#_O!;'Z#1!3'[#_O#_N#_M#^@#^<!2'=1#_Q!1'\!2'=1#_R!1'^0!2'=1#_PF!1'^1!2'=1#_R!1'^2!2'=1#_Q!1'^3!2'=1#_Q!2+G!2+G!2'F,H#^?!2'I#^?J!2+G!2+G!2'F,H#^;!2'I#^;J!3+J+W#^C!7'R!O'S#^7Q#_S#_R!2'P1!3'[#_N#_M#_L!2'P1!1'^2!2'=1#_P!2'P1!1'^1!2'=1#_Q#^3#\#_P/sgw;/w6;!2'P1!1'^0!2'=1#_O!2'P1!1'^3!2'=1#_P!2'P1!2'^4#^?^2S!2'P1!1'\!2'=1#_Q#X#T#P#L#H#D#@#<#8#4!2'P1#^?!2'P1!2'B!3'[#_N#_M#_L^5!2'P1#^;#1#^Y^7#^XW#^VX#1!2$z31;R2$H5;R!2+G%sgn;R+2!3+J+2!8'K#1#_O#_Nb5b6b4F#_P!;'Z#1b7#^A#^=b6b8b9Fb:b;b<!2+Gb=!2+G!2+G!2'F,H#^<!2'I#^<J!3+J+W#^D!7'R!O'S#^8Q#_T#_S!2'P1b>!2'P1!1'^2b4!2'P1!1'^1b6#^4#^0#_Q/sgw;/w6;!2'P1!1'^0aV!2'P1!1'^3b4!2'P1!2'^4#^@^2S!2'P1!1'\b6#Y#U#Q#M#I#E#A#=#9#5b?!2'P1!2'Bb>^5!2'P1#^<#1#^Z^7#^YW#^WX!5'^7bA!2+GbB!2+Gb1!3+J+W#^E!7'R!O'S#^9Q#_U#_T!2'P1b7!2'P1b;!2'P1b:#^5#^1#_R/sgw;/w6;!2'P1b9!2'P1b<!2'P1!2'^4#^A^2S!2'P1b8#Z#V#R#N#J#F#B#>#:#6bC!2'P1!2'Bb7^5b3#2#^[^7#^ZW#^XX!3'^6'7!D'Q#_V/sp;#_U#_T#_M#_L#_H#_G#_F#_E#_D#_C#_B#_A#_@#_?#^[#^Z#^V#^Y#^E$~RbA$~R!2+G!2+G!2'F,H#^B!2'I#^BJ!2+G!2+G!2'F,H#^>!2'I#^>J!3+J+W#^F!7'R!O'S#^:Q#_V#_U!2'P1!3'[#_Q#_P#_O!2'P1!1'^2!2'=1#_S!2'P1!1'^1!2'=1#_T#^6#^2#_S/sgw;/w6;!2'P1!1'^0!2'=1#_R!2'P1!1'^3!2'=1#_S!2'P1!2'^4#^B^2S!2'P1!1'\!2'=1#_T#[#W#S#O#K#G#C#?#;#7!2'P1#^B!2'P1!2'B!3'[#_Q#_P#_O^5!2'P1#^>#3#^\^7#^[W#^YX!2$EQ;R%sgn;R+2!3+J+2!8'K#1#_R#_QbDbEb@F#_S!;'Z#1bF#^D#^@bEbGbHFbIbJbK$H5;R!2+GbL!2+Gb=!3+J+W#^H!7'R!O'S#^<Q#_X#_W!2'P1bF!2'P1bJ!2'P1bI#^8#^4#_U/sgw;/w6;!2'P1bH!2'P1bK!2'P1!2'^4#^D^2S!2'P1bG#^0#Y#U#Q#M#I#E#A#=#9bM!2'P1!2'BbF^5b?#5#_1^7#_0W#^[X!5'^7bN!2+GbB!3+J+W#^I!7'R!O'S#^=Q#_Y#_X!2'P1bO!2'P1!1'^2bD!2'P1!1'^1bP#^9#^5#_V/sgw;/w6;!2'P1!1'^0bE!2'P1!1'^3bD!2'P1!2'^4#^E^2S!2'P1!1'\bP#^1#Z#V#R#N#J#F#B#>#:bQ!2'P1!2'BbO^5bC#6#_2^7#_1W#^\X!3'^6'7!D'Q#_Z/sp;#_Y#_X#_Q#_P#_L#_K#_J#_I#_H#_G#_F#_E#_D#_C#_2#_1#^Z#_0#^I$~RbN$~R!2+G!2+G!2'F,H#^B!2'I#^BJ!3+J+W#^J!7'R!O'S#^>Q#_Z#_Y!2'P1!3'[#_U#_T#_S!2'P1!1'^2!2'=1#_W!2'P1!1'^1!2'=1#_X#^:#^6#_W/sgw;/w6;!2'P1!1'^0!2'=1#_V!2'P1!1'^3!2'=1#_W!2'P1!2'^4#^F^2S!2'P1!1'\!2'=1#_X#^2#[#W#S#O#K#G#C#?#;!2'P1#^F!2'P1!2'B!3'[#_U#_T#_S^5!2'P1#^B#7#_3^7#_2W#_0X!2$Rqh;RbR$H5;R!2+GbL!3+J+W#^L!7'R!O'S#^@Q#_\#_[!2'P1bS!2'P1!1'^2bT!2'P1!1'^1bU#^<#^8#_Y/sgw;/w6;!2'P1!1'^0!2'=1#_X!2'P1!1'^3bT!2'P1!2'^4#^H^2S!2'P1!1'\bU#^4#^0#Y#U#Q#M#I#E#A#=bV!2'P1!2'BbS^5bM#9#_5^7#_4W#_2X!5'^7bN!3+J+W#^M!7'R!O'S#^AQ#`0#_\!2'P1bW!2'P1!1'^2bU!2'P1!1'^1bX#^=#^9#_Z/sgw;/w6;!2'P1!1'^0bT!2'P1!1'^3bU!2'P1!2'^4#^I^2S!2'P1!1'\bX#^5#^1#Z#V#R#N#J#F#B#>bY!2'P1!2'BbW^5bQ#:#_6^7#_5W#_3X!3'^6'7!D'Q#`1/sp;#`0#_\#_U#_T#_P#_O#_N#_M#_L#_K#_J#_I#_H#_G#_6#_5#_1#_4#^M$~RbN$~R!3+J+W#^N!7'R!O'S#^BQ#`1#`0!2'P1!3'[#_Y#_X#_W!2'P1!1'^2!2'=1#_[!2'P1!1'^1!2'=1#_\#^>#^:#_[/sgw;/w6;!2'P1!1'^0!2'=1#_Z!2'P1!1'^3!2'=1#_[!2'P1!2'^4#^J^2S!2'P1!1'\!2'=1#_\#^6#^2#[#W#S#O#K#G#C#?!2'P1#^J!2'P1!2'B!3'[#_Y#_X#_W^5!2'P1#^F#;#_7^7#_6W#_4X!2$Rql;RbR$H5;R!3+J+W#^P!7'R!O'S#^DQ#`3#`2!2'P1bZ!2'P1!1'^2b[!2'P1!1'^1b\#^@#^<#`0/sgw;/w6;!2'P1!1'^0!2'=1#_\!2'P1!1'^3b[!2'P1!2'^4#^L^2S!2'P1!1'\b\#^8#^4#^0#Y#U#Q#M#I#E#A!2'P1#^L!2'P1!2'BbZ^5bV#=#_9^7#_8W#_6X!6'^8+W!7'R!O'S#^EQ#`4#`3!2'P1c0!2'P1c1!2'P1c3#^A#^=#`1/sgw;/w6;!2'P1c4!2'P1c5!2'P1!2'^4#^M^2S!2'P1c6#^9#^5#^1#Z#V#R#N#J#F#B!2'P1#^M!2'P1!2'Bc0^5bY#>#_:^7#_9W#_7X$ms';R+W!3'^6'7!D'Q#`6/sp;#`5#`4#_Z#_Y#_U#_T#_S#_R#_Q#_P#_O#_N#_M#_L#_;#_:#_6#_9#1&HR;R!6'^9+2!8'KE#_[#_Zc2b\b[F#_\$z;R+2!3+J+2#_6#1#^Xc7!1#:E!3+J+2#_5c7!^>'^:#`6#`5#`4#_Z#_Y#_U#_T#_S#_R#_Q#_P#_O#_N#_M#_L#`2c8#^N#^Jc:c;c<c=c>#^F#^B#^>#^:#^6#^2#[#W#S#O#K#G#C#?#_;#_:#_9#_8#_7#_6#_5#_4#_3#_2#_1#_0#7#3vd!4'^;c9c?!1'L#`3cE!2+G!2'F,Hc:!2'Ic:Jvd!4'^;b\c?!1'L#`1cE!2+G!2'F,Hc;!2'Ic;Jvd!3'^F!2'^G!2'^Hc9c?^5cFcK!2+G!2'F,Hc<!2'Ic<Jvd!4'^Ic2cM!1'L#`2!4'^>%~RcNcO%~RcOcN!2'^B,HcMcC!2+G!2'F,Hc=!2'Ic=Jvd!3'^F!2'^Gc2^5cFcK!2+G!2'F,Hc>!2'Ic>Jvd&__sat33;R!2'^JHI%~R!2'I,HH%~R!2'F,HI!2'I,HJ&__sat32;R$Ha;RcP$~R+^K!3'^LHI#2%Ha;RcP%~R+^K!2'F,HJ&__arith;R$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,9+^M!2,^N!3,^O+2!2,^P+2cQ!3,^O+2!2,^P+2cR!3,^O+2!2,^P+2cScT,^R!3,9+^M!2,^N!3,^O+2!2,^P+2}6!3,^O+2!2,^P+2cU!3,^O+2!2,^P+2cVcT,^R!1,?+^M!1+5+^M&__varmap;R!4,^S+2!2,^T+2#3#2!2,^T+2#4!1+^U+2&__ff;R!8,^VcW'^X+^Y+^Y,^Z!7,^[cW'^X+^Y+^Y,^Z!7,^\cW'^X+^Y+^Y,^Z!4,_0+2!2,_1+2C,_2cX,_4!7,^\cW'^X+^Y+^Y,^Z!4,_0+2cX,_2!2,_1+2D,_4cY!8,^VcW'^X+^Y+^Y,^Z!7,^[cW'^X+^Y+^Y,^Z!7,^\cW'^X+^Y+^Y,^Z!4,_0+2cZ,_2c\,_4!7,^\cW'^X+^Y+^Y,^Z!4,_0+2c\,_5d0,_4cY!8,^VcW'^X+^Y+^Y,^Z!7,^[cW'^X+^Y+^Y,^Z!7,^\cW'^X+^Y+^Y,^Z!4,_0+2cZ,_2d1,_4!7,^\cW'^X+^Y+^Y,^Z!4,_0+2d1,_5d0,_4cY!7,^[cW'^X+^Y+^Y,^Z!7,^\cW'^X+^Y+^Y,^Z!4,_0+2!2,_1+2d2,_2d4,_4!7,^\cW'^X+^Y+^Y,^Z!4,_0+2d4,_2!2,_1+2d5,_4!2'_8cW,^Z!4'_9#1#3vvcC!3+J+^?!2'_:#1#3,^A!3'_;+2,H#2%__x3;R+2%__x2;R+2%__x1;R+2%~R!2+G!2'FC#1!2'F#1D%~Rd6%~Rd6!2+G!2'Fd2d7!2'Fd7d5!6#1#`1#`2#`3#_0#_1#_2!2+G!2'Fd2c8!2'Fc8d5#1#^Q#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1").
Qed.
End Walk.
