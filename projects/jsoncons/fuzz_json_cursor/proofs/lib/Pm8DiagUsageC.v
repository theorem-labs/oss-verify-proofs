(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the nine-byte string read-ahead): the premise Hp at slack 9, and the recorded proofs of usage_C, usage_C_tail replaced by the text proofs of jsoncons/fuzz_bigint's As0DiagUsageC.v with this unit's addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
     Pm8RegionPoisoned Pm8AsanMemcpy Pm8DiagKit Pm8DiagChk Pm8DiagMemcpy Pm8DiagStrnlen Pm8DiagGlue Pm8DiagFix Pm8DiagUP Pm8DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5FastLia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.FPState"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Npos"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagUsagePre.DUP.usage_mid"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Numbers.BinNums.Z0"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Logic.ex"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps"; "OSSVerify.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.mkst"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u64_at"; "Corelib.Init.Datatypes.list"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.PRE7"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u32_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.agree0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.SUF7"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.diag_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u8_at"; "Corelib.Numbers.BinNums.xH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.writable"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Corelib.Init.Logic.True"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "Corelib.Numbers.BinNums.Z"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEc"; "Stdlib.micromega.RingMicromega.OpLe"; "Stdlib.micromega.EnvRing.PEX"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.Tauto.X"; "Corelib.Init.Datatypes.None"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.EnvRing.PEpow"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Logic.eq_refl"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "Corelib.Init.Logic.conj"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.div_pos"; "Stdlib.micromega.VarMap.Empty"; "Stdlib.micromega.RingMicromega.OpLt"; "Stdlib.ZArith.BinInt.Z.div_le_upper_bound"; "Stdlib.micromega.EnvRing.PEmul"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.filew"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.U"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.writable_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.defined_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.imgc_ext"; "Stdlib.micromega.Tauto.NOT"; "Stdlib.micromega.EnvRing.PEsub"; "Corelib.Init.Logic.False"; "Stdlib.micromega.Tauto.OR"; "Corelib.Init.Logic.or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.img_clear"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.duDl_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.aligned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.KS_duDl"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "Corelib.Numbers.BinNums.Zneg"; "Stdlib.micromega.RingMicromega.OpEq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.writable_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined_sub"; "Corelib.Init.Logic.eq_ind"; "Corelib.Init.Datatypes.prod"; "Stdlib.setoid_ring.Ring_polynom.PExpr"; "Stdlib.setoid_ring.Ring_polynom.Mon"; "Stdlib.setoid_ring.Ring_polynom.Pol"; "Stdlib.setoid_ring.Ring_polynom.mk_monpol_list"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.quotrem"; "Stdlib.setoid_ring.ZArithRing.Zr_ring_lemma2"; "Stdlib.setoid_ring.Ring_tac.ring_subst_niter"; "Corelib.Init.Logic.I"; "Stdlib.setoid_ring.Ring_polynom.norm_subst"; "Stdlib.setoid_ring.Ring_polynom.PEeval"; "Stdlib.setoid_ring.Ring_theory.IDphi"; "Stdlib.ZArith.BinInt.Z.of_N"; "Stdlib.setoid_ring.Ring_polynom.Pphi_pow"; "Stdlib.setoid_ring.InitialRing.get_signZ"; "Stdlib.setoid_ring.Ring_polynom.PX"; "Stdlib.setoid_ring.Ring_polynom.Pc"; "Stdlib.setoid_ring.Ring_polynom.PEsub"; "Stdlib.setoid_ring.Ring_polynom.PEX"; "Stdlib.setoid_ring.Ring_polynom.PEc"; "Corelib.Init.Logic.eq_ind_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows_trans"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.eqb_neq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.wv_entry_stage"; "Stdlib.setoid_ring.Ring_polynom.PEadd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.u64_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.u32_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.rdn_7"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.u8_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.PRE7_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagStrnlen.DSN.cstr_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagStrnlen.DSN.cstr"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Peano.lt"; "Corelib.Lists.ListDef.nth"; "Corelib.Lists.ListDef.firstn"; "stdpp.tactics.f_equal_help"; "Corelib.Init.Nat.sub"; "Stdlib.Lists.List.app_nil_r"; "Stdlib.Arith.PeanoNat.Nat.sub"; "Stdlib.Arith.PeanoNat.Nat.sub_diag"; "Stdlib.Lists.List.firstn_all2"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Corelib.Init.Peano.le"; "Stdlib.micromega.ZifyClasses.mkrel"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Stdlib.Lists.List.firstn_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.rdn_firstn"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.Arith.PeanoNat.Nat.add"; "Stdlib.ZArith.Znat.Nat2Z.inj_add"; "Corelib.Init.Logic.ex_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps_trans"; "Corelib.Init.Logic.and_ind"; "Corelib.Init.Logic.or_intror"; "Corelib.Init.Logic.or_introl"; "Corelib.Init.Logic.or_ind"; "Corelib.Init.Logic.False_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.zeros_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8RegionPoisoned.SB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5KnA.L5KA.zeros_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.u8_of_u32_5"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.duEc_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.KS_duEc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.UR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Kn.L5K.in_b"; "Stdlib.Lists.List.existsb"; "Stdlib.Arith.PeanoNat.Nat.eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagKit.DK.U_to"; "Stdlib.micromega.EnvRing.PEopp"; "Stdlib.ZArith.Zdiv.Z_div_plus_full"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5KnA.L5KA.zeros_at_sub"; "Corelib.Init.Logic.eq_trans"; "Corelib.Init.Logic.f_equal"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagGlue.DG.list_bv_eq"; "Corelib.Lists.ListDef.map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.duGc_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DiagUP.AS0DIAGUP.KS_duGc"; "Corelib.Init.Logic.eq_sym"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagUsagePre.DUP.usage_pre"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagUsageC.DUC.UA.usage_C_tail"].
 Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUC.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 716440.
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1407328.
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91464.
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1392640.
  (* SLACK 16 -> 9, old beside new: was [p + n + 1 + 16 <= 2 ^ 47]; see Pm8DrvEntryK.ent_str_hi.  lia margin UNCHECKED. *)
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : 74 <= n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
  Hypothesis HFMT : L5KA.zeros_at M 2147462312 8.
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.

  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1259184 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Theorem usage_C_tail : forall fx5 R5 M5, DUP.usage_mid R M S p can bs m1 m2 m3 m4 m5 m6 m7 m8 R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x13d430 M5) (st fxE RE 0x13b85c ME)

      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1407328 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1407448 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13b868 MX) (st fxE2 RE2 0x13b85c ME2)

              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1407328 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1407448 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13b868 MY) (st fxF RF 0x133e78 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1407328 5 /\ L5.u64_at RSEGS MF 1407424 0 /\ L5.u64_at RSEGS MF 1407416 7017064
                      /\ L5.u64_at RSEGS MF 1407384 0 /\ L5.u64_at RSEGS MF 1407368 0 /\ L5.u64_at RSEGS MF 1407360 0 /\ L5.u64_at RSEGS MF 1407336 0 /\ L5.u64_at RSEGS MF 1407344 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    intros fx5 R5 M5 INV.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    (* [Hp] (nine bytes past the NUL) gives [p <= 2^47 - 10], the [V 33] bound of the
       widened segment walks' premises ([asan/Pm8DiagUP]); stated at that bound so [scc] closes it
       by [assumption]. *)
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.
    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1392640) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    pose proof (duDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
    assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (NE : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx8 R8 M8 1407328 (S - 1136) p n (S - 457) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
    assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
    { rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
        (eapply (u8_ext M5); [intros x Hx; apply AG5W; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
    assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
    assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STRW as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    exists fx8, RW, MW.
    split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 457 - (S - 464)) with 7 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
    split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
    split; [exact P7W|]. split; [exact RDSW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1392640) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1407328 152) by (eapply writable_grows; eassumption).
    assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
    { apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (F8X : L5.u8_at RSEGS MX 1407328 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
    pose proof (duEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
    assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1407360 <= bv_unsigned x < 1407376) -> ~ (1407384 <= bv_unsigned x < 1407392) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1407360 <= bv_unsigned x < 1407376) -> ~ (1407384 <= bv_unsigned x < 1407392) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
    assert (NE2 : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx9 R9 M9 1407328 (S - 592) 0 0 (S - 457) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE2 in X11, X12, X18, X19.
    assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
    assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
    assert (SUF32 : L5.u32_at RSEGS M9 (S - 464) 1347307808) by (apply (DFX.u32_of_u8s M9 (S - 464) (S - 463) (S - 462) (S - 461) 1347307808 32 73 78 80); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7).
    { rewrite SUF7_eq. apply rdn_43; [lia | lia | ..];
        first [ (eapply (u32_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]) | (eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]) ];
        match goal with |- _ _ _ ?a _ => ring_simplify a end; assumption. }
    exists fx9, RW2, MW2.
    split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
    split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
    split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 457 - (S - 464)) with 7 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
    split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
    intros fx'' RY MY AGYW MGYW KYW.
    assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
    assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
    assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
    assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
    assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1407360 <= bv_unsigned x < 1407376) -> ~ (1407384 <= bv_unsigned x < 1407392) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
    assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
    assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
    assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGY : L5.img_clear MY 65536 1392640) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
    assert (FWY : L5.writable RSEGS MY 1407328 152) by (eapply writable_grows; eassumption).
    pose proof (duGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
       | 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.

  Theorem usage_C :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6a59c M) (st fxE RE 0x13b85c ME)

      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1407328 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1407448 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13b868 MX) (st fxE2 RE2 0x13b85c ME2)

              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1407328 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1407448 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13b868 MY) (st fxF RF 0x133e78 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1407328 5 /\ L5.u64_at RSEGS MF 1407424 0 /\ L5.u64_at RSEGS MF 1407416 7017064
                      /\ L5.u64_at RSEGS MF 1407384 0 /\ L5.u64_at RSEGS MF 1407368 0 /\ L5.u64_at RSEGS MF 1407360 0 /\ L5.u64_at RSEGS MF 1407336 0 /\ L5.u64_at RSEGS MF 1407344 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (usage_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DUC.
