(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ea0RegionPoisoned Ea0AsanMemset Ea0AsanMemcpy Ea0StrlenIcpt Ea0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r48448_48dd8 Ea0_code_r4dae8_4daec Ea0FakeStack1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Ea0FakeStack2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_ind".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].

Lemma land_mask2 : forall a, Z.land a 4095 = (a mod 4096)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStack2 ()) ["FPX_1"] "h07__arithh14__ffh28__varmaph35__with41ah51zp;1p;2p;3p;4p;7p;6g0000j11Tg000Uj12Tg0013j1=Tg001Xj2HTg0025j23Tg002Uj34Tg002oj25Tg003Ij1;Tg003gj2:Tg004Ej17Tg004ej18Tg005Ej19Tg005cj1GTg006Aj1FTg006lj26Tg007Oj4CTg008:j7BTg008^j2?Tg009@j2>Tg009lj3@Tg00:Kj4ATg00;=j2<Tg00;Yj3DTg00<<j6ETf0R0#1#1p=0g00<ZR1P1g00=8R2#1R3#2%=2#0#2R2'H,30f1R4%13#0#0#0#0#0#2R3'39410X511303,51%;2,:0g00=]R3#7%83%91%G1%F1R3g00>Ig00>hR5P5g00?HR5P1g00?hR6,61g00@F1612CCg00@mFB1?35P0f2R5g00AMR3g00AmR7'51>05=437dA@164CAb1b2b31<62P0b09D02EEW4o"). Qed.

Section FSM2.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra a0v : word.
  (* [comment removed for export] *)
  Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  (* [comment removed for export] *)
  Variables fs h pos ff : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.          (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
    tls_cells tpv 0x139f50 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
  (* [comment removed for export] *)
  Hypothesis Hfs : (0x678000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
  Hypothesis Hpos_def : pos = (h mod 4096)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2097152 + 256 * pos)%Z.
  Definition tls_rc : Z := tls_res off ent.
  Hypothesis Hr : (0 <= tls_rc /\ tls_rc + 8 < 2 ^ 64)%Z /\ (tls_rc + 8 <= s - 208 \/ s <= tls_rc)%Z /\ (tls_rc + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_rc)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_rc) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].                     (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).   (* [comment removed for export] *)
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)). (* [comment removed for export] *)
  Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 24576 + pos)) 1%nat = Some [Z_to_bv 8 0].      (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.   (* [comment removed for export] *)
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 32%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 32 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 32 <= 0x139158 \/ 0x1426b8 <= SB + ff / 8)%Z.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.

  (* [comment removed for export] *)
  Definition F4c (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).

  (* [comment removed for export] *)
  Definition fsm2_mem (Mj : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
      (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))
      (Z_to_bv 64 (fs + 4096 + 24576 + pos)) [Z_to_bv 8 1])
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (ff + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 24576 + pos))))
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma sp_sc : sp = Z_to_bv 64 s.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStack2 ()) ["FPX_1"; "FSM2"] "h01sp;1p;2p;3p;4p;6g0000j10Tg00BMj18Tg00Bkj23Tg00CUj12Tg00D8j21Tg002Uj37Tg00D^j26Tg00EPj44Tg00Elj65Tg00<ZR0g00=8#0#0#0#0#0#0#8R1p,2spR2'3R3%21R4f0,11772X00P41113P21612C4p,1sp,6Hs_defE5o"). Qed.

(* [comment removed for export] *)
End FSM2.
End FPX_1.
