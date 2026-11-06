(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require ZBridge.     (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptB_guard2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptB_guard2 ()) [] "h02Hah16__sat1h24__x1h31zh47__arithh54__ffh66__sat0h76__sat3h88__varmaph95__with:2Hzh;6__sat2p;1p;2p;3p;4p;6p;7p;8g0000j12Tg000Uj15Tg0013j2:Tg001Pj21Tg001lj29Tg002Gj1?Tg002ej1JTg003Hj2;Tg003hj24Tg004Nj33Tg004hj28Tg005Bj2BTg005jj3CTg006Nj2WTg006oj1VTg007Oj1UTg007oj2TTg008Mj1QTg008kj1NTg009Vj2@Tg00:9j2MTg00:\j46Tg00;Gj3>Tg00;jj1ITg00<Lj2HTg00<nj2KTg00=Zj3LTg00>9j4GTg00>kj3FTg00?Nj6ATg00?lj2ETg00@Vj2OTg00AUj1PTg00BIj2DTg00Bej7RTg00CIj7STg00Cmj8XTg00DQR0f0R1'Dp=0f1R2g00DoR3g00ENR4P4g00EnR5P1g00FNFRp=7f2R6P3P4P4P5P2P1FSp=<f3P3P4P4P5P6P2P1GXp==g00FnR3%01g00GLR7#2R8#5R9%28#2#2#2R8#5R:':R;,11'9R<P3P2%28R=#?R>#JR?1;1;,4>14>6R@33X33P3P214>1=3?@X3314>2R@,8?1;2;1B9:RA1109RB%0:110;[RC[RD%09REg00H1RFAC9:2UW0R:%0;\F^0ERGP2g00HM1W09'8PBeRHO1RIPCg00I3RJ#VRK%UJRJ1T32RL%Q3RM%N3RNP31@30g00I_1M37R7C6,7NROP3P7g00JFRP1@39RQ%?85>3C6,7N5<NR8%I4R4P8C=1HN5R5P1P6g00JmRRg00KMRS'81K16=3RSdAL302CGRSb5b8b9X23%02RR112;'9\<^23P1f5f4R6O2b4b1b6b19F2;EA1E>@PAPDP:PG%5=R=,B9%0=1:9=RG,10[R0\BAC9=2VFX0E%0G\F^0EPIP0P6PHO1PCPKPJPLPMPNP8P4P3P7PPA>3Q>C6,7N9<NOC=P5PSb5b8b9X23112G,9R\<^23P1f8f7O2b4b7b1b6b1b;b7,O2EA%P@=3?@eW:W3o"). Qed.

Ltac mulh_fix2 :=
  lazymatch goal with
  | |- context [bv_signed (Z_to_bv 64 _) * bv_signed (zx32 _) / 18446744073709551616] =>
      repeat match goal with |- context [zx32 (Z_to_bv 64 ?z)] => rewrite (zx32_small z) by lia end;
      repeat match goal with
      | |- context [bv_signed (Z_to_bv 64 (_ mod 18446744073709551616 * bv_unsigned (Z_to_bv 64 ?b)))] => rewrite (unsigned_lit b) by lia
      end;
      mulh_fix
  end.
(* [comment removed for export] *)
Ltac shbr ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru _ _ =>
                (* [comment removed for export] *)
                let szm1 := constr:(0%Z) in
                let S4 := eval vm_compute in (SLOW + 4)%Z in
                instr_at segs S4 ltac:(fun i2 =>
                  let szm1 := lazymatch i2 with
                              | OpImm ALU_ADD _ _ ?imm => eval vm_compute in (bv_unsigned imm)
                              | _ => constr:(0%Z) end in
                  let sz := eval vm_compute in (szm1 + 1)%Z in
                  let OK := fresh "SHOK" in
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        assert (OK : sh_ok b (X + sz - 1)) by (apply (shk_ok m a n X sz b ACC K); lia)
                    end
                  | fail 1 "shbr: cannot prove the access addressable:" X sz ];
                  let BB := fresh "BB" in
                  assert (BB : 0 <= bv_unsigned b < 8)
                    by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                  rewrite ?(sxb_small b) by lia;
                  shbr_merge ru FAST OK; clear K BB)
            | _ =>
                (* [comment removed for export] *)
                let OK := fresh "SHOK" in
                first [
                  match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr: cannot prove the 8-byte access addressable:" X ];
                apply sh_ok_8 in OK; [ | lia ];
                rewrite ?(sxb_small b) by lia;
                brF; rewrite ?OK; clear K OK      (* [comment removed for export] *)
            end)
      | _ => fail "shbr: no shk fact for" b
      end
  end.

(* [comment removed for export] *)
Ltac po_neg_fix :=
  repeat match goal with
  | |- context [bv_ltu (Z_to_bv 64 (Zneg ?k)) (Z_to_bv 64 ?x)] =>
      replace (bv_ltu (Z_to_bv 64 (Zneg k)) (Z_to_bv 64 x)) with false
        by (symmetry; unfold bv_ltu; rewrite (unsigned_lit x) by lia;
            let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 (Zneg k))) in change (bv_unsigned (Z_to_bv 64 (Zneg k))) with v;
            apply Z.ltb_ge; lia)
  end.
(* [comment removed for export] *)
Ltac po_not_fix :=
  repeat match goal with
  | |- context [bv_ltu (Z_to_bv 64 (Z.lxor ?x 18446744073709551615)) (Z_to_bv 64 ?y)] =>
      replace (bv_ltu (Z_to_bv 64 (Z.lxor x 18446744073709551615)) (Z_to_bv 64 y)) with false
        by (symmetry; unfold bv_ltu; rewrite (ZBridge.zb_lxor_ones x) by lia; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia)
  end.
(* [comment removed for export] *)
Ltac al_or_fix :=
  repeat match goal with |- context [Z.land (Z.lor ?a ?b) 3] => rewrite (Z.land_lor_distr_l a b 3) end;
  al_fix; change (Z.lor 0 0) with 0.
Ltac guard_fix ::= try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix; try mulh_fix2; po_neg_fix; po_not_fix; try al_or_fix.

(* [comment removed for export] *)
Ltac gwalk1 ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br | progress guard_fix; try br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
