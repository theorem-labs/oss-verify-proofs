(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "rw"; "obj_range"; "sv_eqb"; "SLit"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "ranges_disjoint"; "@Corelib.Init.Datatypes"; "false"; "andb"; "bool"; "fst"; "snd"; "true"; "orb"; "prod"; "None"; "list"; "nat"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "le"; "pow"; "add"; "lt"; "max"; "opp"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "robj_tracked"; "@Stdlib.Lists.List"; "In"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLow"; "robj_low"; "robjs_low"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundL SymSoundR SymFrame SymEntail SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition robj_low (tv : list (sv * sv)) (o : sobj) : bool := ltac2:(tb__ "0|14|
SeSeL_;S2aVtv;S14S16A1Vo;A3S11S0SeLx;M0SaVo;A1S18G0S9Vo;A1S18S12S12SdSdSdS5S8Vo;A1M1S7P1M2A1A2S1bS21S1dZ2Z28A2A1M3R2A2A2S1bR2R1A2M4A2S1bR1Z0M5A2M6A2G0G1S18ScLz;M7S19ScLi;M8S27S0S0S27SeLop;R3S0SeLa;R2G7S19S0SeLb;R2S18SdSdSdSdSdS2fR2G2A2S1bG3R1A2A2G6A2S1bG3R7A2A2S1bR7R6A2A2S1bS1eR1R6A2G5A2A2Lc;S19ScLi0;S27S0S0ScLb0;La0;M9Lop0;MaGaS28G9Lop0;MbGbSeS1aS0ScLa0;Lw;Lsgn;McS19S0S18ScLk;MdLi0;Ll0;X0x8Li;GaGaGbGbGcS19S0GdLi;MeLl0;MfX0x8ScScScScScScScScScX27xaLb;La;Lop;S27S0S0ScLb;La;M10Lop;M11S28G10Lop;M12G12SeS1aS0ScLa;Lw;Lsgn;M13GfX0x8A2SdSdSdS5G1S6G5A1A2S1bG5R2A2A2G4A2S1bR1S29A2A2A2Lh;G8G11G11G12G12G13GfX0x8Ll;G8G11G11G12G12G13S19GeLl;X0x8Xex2").
Definition robjs_low (tv : list (sv * sv)) (objs : list sobj) : bool := forallb (robj_low tv) objs.

Section S.
Variable tv : list (sv * sv).
Variable rho : valuation.
Hypothesis Hsp : ltac2:(tb__ "0|2|
S24S1cS1dZ2M0Z2eA2S22Q40S3Vrho;P1A2A2M1A2S1fG1S1dG0Z38A2A2A2").

Variable T : Z.
Hypothesis HT : ltac2:(tb__ "0|0|
S24S1cS29VT;A2S1fVT;S1dZ2Z3fA2A2A2").

Hypothesis Hgeo : ltac2:(tb__ "0|2|
S13S0S0A2M0S2bG0R1Vtv;A3S25S23S18S22Q40M1S1Vrho;SfS0S0R2A3A2A2Z0A3A1S1cS1eS1eS22G1S1Vrho;SfS0S0R3A3A2A2S22G1S1Vrho;S10S0S0R3A3A2A2A2Z4A2VT;A2F_;F_;Ft;").
Hypothesis Hz : ltac2:(tb__ "0|3|
S13S0S0A2M0S2bG0R1Vtv;A3S23S18S22Q40M1S1Vrho;SfS0S0R2A3A2A2Z0M2A3S23S18S22G1S1Vrho;S10S0S0R3A3A2A2G2A3F_;F_;Ft;").

Lemma robj_low_sound : ltac2:(tb__ "0|2|
S2S23SeS2dVtv;R1A2S11A3S26S1cS10S18S18S4Vrho;R2A2M0A3M1S20S22Q40S3Vrho;P1A2A2VT;A2A2S1cG1SfS18S18G0A3A2A2F_;Fo;").
Proof using HT Hgeo Hsp Hz.
  intros o H. unfold robj_low in H. assert (A63 : aceil < 2 ^ 63) by (unfold aceil; lia).
  apply lazy_orb_prop in H as [H|H].
  -
    destruct (robj_tracked_sound tv None o H) as (j & t & Hj & _ & Hb & Hl & Hh).
    pose proof (nth_error_In _ _ Hj) as Hin.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. cbn [fst snd]. rewrite soff_lit_small by lia.
    pose proof (bv_urange (eval rho (snd t))) as Us.
    destruct (Z.eq_dec (bv_unsigned (eval rho (fst t))) 0) as [Z0|NZ].
    + right. unfold soff. rewrite bv_signed_U. rewrite (Hz t Hin Z0). cbn. lia.
    + left. pose proof (Hgeo t Hin NZ) as G. unfold soff. rewrite bv_signed_U.
      destruct (Zsigned_spec (bv_unsigned (eval rho (snd t)))) as [[_ X]|[Y X]]; rewrite X; lia.
  - destruct (ob_lo o) as [l| | | | | | |] eqn:El; try discriminate.
    destruct (ob_hi o) as [h| | | | | | |] eqn:Eh; try discriminate.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite El, Eh. cbn [fst snd].
    apply orb_prop in H as [H|H3]; [apply orb_prop in H as [H1|H2]|].
    + apply andb_prop in H1 as [H1 Hc]. apply andb_prop in H1 as [H1 Hb]. apply andb_prop in H1 as [H1 Ha].
      apply sv_eqb_sound in H1. rewrite H1. apply Z.leb_le in Ha. apply Z.leb_le in Hb. apply Z.leb_le in Hc.
      cbn [eval]. rewrite !soff_lit_small by lia. left. lia.
    + destruct (ob_base o) as [|i0|op a b| | | | |] eqn:Eb; try discriminate. destruct op; try discriminate.
      destruct a as [|i| | | | | |]; try discriminate. destruct b as [c| | | | | | |]; try discriminate.
      apply andb_prop in H2 as [H2 He]. apply andb_prop in H2 as [H2 Hd]. apply andb_prop in H2 as [H2 Hc]. apply andb_prop in H2 as [H2 Hb]. apply andb_prop in H2 as [Hi Ha].
      apply Pos.eqb_eq in Hi. subst i. apply Z.leb_le in Ha. apply Z.leb_le in Hb. apply Z.leb_le in Hc. apply Z.leb_le in Hd. apply Z.leb_le in He.
      cbn [eval]. rewrite add_lit_val, (snorm_small c) by lia. rewrite Z.mod_small by lia. rewrite !soff_lit_small by lia. left. lia.
    + apply andb_prop in H3 as [H3 Hc]. apply andb_prop in H3 as [H3 Hb]. apply andb_prop in H3 as [H3 Ha].
      apply sv_eqb_sound in H3. rewrite H3. apply Z.leb_le in Ha. apply Z.leb_le in Hb. apply Z.leb_le in Hc.
      cbn [eval]. rewrite Z_to_bv_small by (rewrite two64; lia). rewrite !soff_lit_small by lia. left. lia.
Qed.

Lemma robjs_low_disjoint : ltac2:(tb__ "0|0|
S15S2A1S18S18S23SeS2eVtv;R3A2S11A3S1cS20S22Q40S3Vrho;P1A2A2VT;A2R3A2S2cS2S2SbS4Vrho;R1A2S17S18S18R5R4A4A2Lo;R5A3F_;F_;Fhi;Flo;Fobjs;").
Proof using HT Hgeo Hsp Hz.
  intros objs lo hi H Hlo. apply Forall_forall. intros o Ho.
  pose proof (robj_low_sound o (proj1 (forallb_forall _ _) H o Ho)) as R.
  unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.
End S.
