(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "binfo"; "BRd"; "byte_info"; "BLit"; "BNone"; "BImg"; "all_lit_offs"; "cell_byte"; "find_cov"; "lit_small"; "obj_byte"; "@Corelib.Init.Datatypes"; "option"; "bool"; "false"; "list"; "true"; "Some"; "None"; "andb"; "orb"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "cell"; "odefault"; "c_off"; "c_width"; "ob_cells"; "ob_dflt"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB"; "range_cov"; "cells_clear"; "range_info"; "range_present"; "range_zero"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint range_cov (L : list sobj) (base : sv) (a b : Z) : option sobj :=
  match L with
  | [] => None
  | o :: r =>
      if sv_eqb (ob_base o) base && dflt_writable (ob_dflt o) then
        match lit_small (ob_lo o), lit_small (ob_hi o) with
        | Some lo, Some hi => if (lo <=? a) && (b <=? hi) then Some o
                              else if (hi <=? a) || (b <=? lo) then range_cov r base a b else None
        | _, _ => range_cov r base a b
        end
      else range_cov r base a b
  end.

Lemma range_cov_spec : ltac2:(tb__ "0|1|
S10S17A1S18S0S0S17S20SdS17A1M0S27R5R4R3R2A4S12S17R1A2A3S0S21S23R5R1A2S24R1R4A2A2S20G0SaR8R7R2A3S12S17R4A2A3F_;Foff;F_;Fo;Fb;Fa;Fbase;FL;").
Proof.
  induction L as [|o' L IH]; intros base a b o H off Hoff; cbn [range_cov] in H; [discriminate|].
  cbn [find_cov]. unfold covers_b.
  destruct (sv_eqb (ob_base o') base) eqn:Eb; cbn [andb] in H |- *; [|exact (IH base a b o H off Hoff)].
  destruct (dflt_writable (ob_dflt o')) eqn:Ed; cbn [andb] in H.
  2: { rewrite andb_false_r. exact (IH base a b o H off Hoff). }
  destruct (lit_small (ob_lo o')) as [lo|] eqn:El; [|cbn [andb]; exact (IH base a b o H off Hoff)].
  destruct (lit_small (ob_hi o')) as [hi|] eqn:Eh; [|cbn [andb]; exact (IH base a b o H off Hoff)].
  destruct ((lo <=? a) && (b <=? hi)) eqn:Ein.
  - injection H as <-. apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    replace ((lo <=? off) && (off <? hi)) with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - destruct ((hi <=? a) || (b <=? lo)) eqn:Eout; [|discriminate].
    replace ((lo <=? off) && (off <? hi)) with false; [cbn [andb]; exact (IH base a b o H off Hoff)|].
    symmetry. apply orb_prop in Eout as [E|E]; apply Z.leb_le in E.
    + apply andb_false_intro2. apply Z.ltb_ge. lia.
    + apply andb_false_intro1. apply Z.leb_gt. lia.
Qed.

Definition cells_clear (cells : list cell) (a b : Z) : bool := ltac2:(tb__ "0|1|
S2cS19S19SdS0A1SeLx;SbS1bR1A1A1S0S14S25S1cR2A1M0Z8A2S15S25S26R1G0A2Va;A2S25Vb;R1A2A2A2Lco;SfXdx2Lc;Vcells;A3").

Lemma cells_clear_spec : ltac2:(tb__ "0|1|
S10S19A1S0S0S20SeS28R3R2R1A3S11A3S21S20SeS8R4A1S11A3S0S21S23R4R1A2S24R1R3A2A2S20SdSdS0A1M0A1S9R6R2A2S13G0A1A3F_;Foff;A2F_;Fb;Fa;Fcells;").
Proof.
  induction cells as [|c r IH]; intros a b H; [split; [reflexivity | intros; reflexivity]|].
  cbn [cells_clear forallb] in H. apply andb_prop in H as [Hc Hr]. destruct (IH a b Hr) as [IA IB].
  destruct (lit_small (c_off c)) as [co|] eqn:Eo; [|discriminate]. apply andb_prop in Hc as [Hw Hd]. split.
  - cbn [all_lit_offs forallb]. rewrite Eo, Hw. exact IA.
  - intros off Hoff. cbn [cell_byte]. rewrite Eo.
    replace ((co <=? off) && (off <? co + c_width c) && (c_width c <=? 8)) with false; [exact (IB off Hoff)|].
    symmetry. apply andb_false_intro1. apply orb_prop in Hd as [E|E]; apply Z.leb_le in E.
    + apply andb_false_intro2. apply Z.ltb_ge. lia.
    + apply andb_false_intro1. apply Z.leb_gt. lia.
Qed.

Definition range_info (L : list sobj) (base : sv) (a b : Z) : option binfo := ltac2:(tb__ "0|3|
SdS17A1SdS2A1M0Lx;S27VL;Vbase;Va;Vb;A4S17SeG0L_;S28S1dR1A1Va;Vb;A3S12S2S1aS2Lx;S1eR1A1S3S5Z0A1S7S1S3Ll;M1G1S0S18S10S16S0S0A2A1S10S1fA1S3Ltmpl;Lflds;Lcnt;Lesz;X1ax6A2S13S2A1M2Xex2Lo;G2Xdx2").

Theorem range_info_spec : ltac2:(tb__ "0|0|
S10S17A1S18S0S0S2S20SdS2A1S29R5R4R3R2A4S12S2R1A2A3S0S21S23R5R1A2S24R1R4A2A2S20S2S4R8R7R2A3R4A3F_;Foff;F_;Fbi;Fb;Fa;Fbase;FL;").
Proof.
  intros L base a b bi H off Hoff. unfold range_info in H.
  destruct (range_cov L base a b) as [o|] eqn:Ec; [|discriminate].
  destruct (cells_clear (ob_cells o) a b) eqn:Ecl; [|discriminate]. injection H as <-.
  unfold byte_info. rewrite (range_cov_spec L base a b o Ec off Hoff). unfold obj_byte.
  destruct (cells_clear_spec _ _ _ Ecl) as [HA HB]. rewrite (HB off Hoff), HA. reflexivity.
Qed.

Definition range_zero (L : list sobj) (base : sv) (a b : Z) : bool := ltac2:(tb__ "0|1|
SdS2A1SeLx;S29VL;Vbase;Va;Vb;A4S2S2SeLb0;R1SfSfS0S0SeLv;R1S11S1SfLp;M0G0X0x3Lv;SfX2x4Lb0;SfXdx2").

Definition range_present (L : list sobj) (base : sv) (a b : Z) : bool := ltac2:(tb__ "0|0|
SdS17A1SeLx;S27VL;Vbase;Va;Vb;A4S17S11Ls;SfXdx2").
Lemma range_zero_spec : ltac2:(tb__ "0|0|
S10S17A1S18S0S0S20SeS2bR4R3R2R1A4S11A3S0S21S23R4R1A2S24R1R3A2A2S20S2S4R7R6R2A3S5Z0A1A3F_;Foff;F_;Fb;Fa;Fbase;FL;").
Proof.
  intros L base a b H off Hoff. unfold range_zero in H. destruct (range_info L base a b) as [bi|] eqn:E; [|discriminate].
  rewrite (range_info_spec L base a b bi E off Hoff). destruct bi as [| |v|]; try discriminate. destruct v; try discriminate. reflexivity.
Qed.
Lemma obj_byte_not_none : ltac2:(tb__ "0|0|
S17S0S22S20S2ScR2R1A2S6A3A1Foff;Fo;").
Proof.
  intros o off. unfold obj_byte. destruct (cell_byte (ob_cells o) off) as [[v|]|]; try discriminate.
  destruct (all_lit_offs (ob_cells o)); [destruct (ob_dflt o); discriminate | discriminate].
Qed.
Lemma range_present_spec : ltac2:(tb__ "0|0|
S10S17A1S18S0S0S20SeS2aR4R3R2R1A4S11A3S0S21S23R4R1A2S24R1R3A2A2S22S20S2S4R7R6R2A3S6A3A1F_;Foff;F_;Fb;Fa;Fbase;FL;").
Proof.
  intros L base a b H off Hoff. unfold range_present in H. destruct (range_cov L base a b) as [o|] eqn:E; [|discriminate].
  unfold byte_info. rewrite (range_cov_spec L base a b o E off Hoff). apply obj_byte_not_none.
Qed.
