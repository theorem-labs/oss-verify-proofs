(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "cell"; "SLit"; "c_off"; "soff"; "sv_below"; "ob_cells"; "ob_hi"; "ob_lo"; "obj_range"; "c_width"; "eval"; "obj_holds"; "obj_wf"; "valuation"; "c_val"; "ob_base"; "odefault"; "agree_below"; "enc_bytes"; "ob_dflt"; "rm"; "tfact"; "@Corelib.Init.Datatypes"; "bool"; "true"; "false"; "app"; "option"; "Some"; "andb"; "fst"; "prod"; "snd"; "list"; "nat"; "None"; "pair"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit.Kit"; "m'"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "of_nat"; "pow"; "to_nat"; "opp"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "lit_ok"; "covers"; "fully_covered"; "obj_lits_ok"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue ObjBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cell_lit (c : cell) : option (Z * Z) := ltac2:(tb__ "0|5|
S7S23S27S0S0A2M0A1Lx;SbVc;A1S0S24G0S2cS0S0R1S32R1S12Vc;A1A2A4A2Lo;S1S2bG0A1M1Li;S3cS7S7G1Lb;La;M2Lop;M3G3S3dG2Lop;M4G4S1fS2S7G1La;Lw;Lsgn;S1S7S0G1Lk;Li;Ll;X7x8").
Fixpoint covers (cs : list cell) (off : Z) : bool :=
  match cs with
  | [] => false
  | c :: t => match cell_lit c with Some (a, b) => ((a <=? off) && (off <? b)) || covers t off | None => covers t off end
  end.
Definition fully_covered (o : sobj) : bool := ltac2:(tb__ "0|7|
S7S1fLx;M0S10Vo;A1S0G0SfVo;A1S0S2eS2aS2aS45SeVo;A1S32R3S34R1A1A2A2Lk;S42U0S36S38R1R2A2A1A2A3Lhi;S1S21Li;M1S3cS7S7S21Lb;La;M2Lop;M3G3S3dG2Lop;M4G4S1fS2S7S21La;Lw;Lsgn;M5S1S7S0S21Lk;Li;Ll;M6X7x8Llo;G1G3G3G4G4G5G6X7x8").

Definition lit_ok (z : Z) : bool := ltac2:(tb__ "0|1|
S25S33S37S35Z2Z3eA2M0A1Vz;A2S33Vz;G0A2A2").
Definition obj_lits_ok (o : sobj) : bool := ltac2:(tb__ "0|b|
S25S7S1fLx;M0S10Vo;A1S0G0SfVo;A1S0S25S44R2A1S44R1A1M1A2Lhi;S1S21Li;M2S3cS7S7S21Lb;La;M3Lop;M4G4S3dG3Lop;M5G5S1fS2S7S21La;Lw;Lsgn;M6S1S7S0S21Lk;Li;Ll;M7X7x8Llo;G2G4G4G5G5G6G7X7x8S2eS9S9G0SbR1A1S0G1Lz;S1S20Li;S3cS7S7S20Lb;La;M8Lop;M9G9S3dG8Lop;MaGaS1fS2S7S20La;Lw;Lsgn;S1S7S0S20Lk;Li;Ll;X7x8Lc;SeVo;A1A3A2").

Lemma lit_ok_soff rho z : ltac2:(tb__ "0|0|
S3S1fS44Vz;A1S20A3S3S0ScVrho;SaVz;A1A2Vz;A3F_;").
Proof. intros H. unfold lit_ok in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply soff_lit_small. lia. Qed.

Lemma covers_In cs off : ltac2:(tb__ "0|0|
S3S1fS45Vcs;Voff;A2S20A3S5S9S9S5S0S0S4S2dS9R2Vcs;A3S4S3S7SbR2A1SaR1A1A3S4S30R1Voff;A2S31Voff;S32R1S12R2A1A2A2A2A2A2Lo;A2Lc;A2F_;").
Proof.
  induction cs as [|c t IH]; cbn; intros H; [discriminate|].
  destruct (cell_lit c) as [[a b]|] eqn:E.
  - apply Bool.orb_true_iff in H as [H|H].
    + apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      unfold cell_lit in E. destruct (c_off c) eqn:Eo; try discriminate. injection E as <- <-.
      exists c, z. cbn. rewrite Eo. auto.
    + destruct (IH H) as (c' & o & Hin & Ho & R). exists c', o. auto.
  - destruct (IH H) as (c' & o & Hin & Ho & R). exists c', o. auto.
Qed.

Lemma fully_covered_In o lo hi off : ltac2:(tb__ "0|0|
S3S1fS46Vo;A1S20A3S3S7S10Vo;A1SaVlo;A1A3S3S7SfVo;A1SaVhi;A1A3S4S30Vlo;Voff;A2S31Voff;Vhi;A2A2S5S9S9S5S0S0S4S2dS9R2SeVo;A1A3S4S3S7SbR2A1SaR1A1A3S4S30R1Voff;A2S31Voff;S32R1S12R2A1A2A2A2A2A2Lco;A2Lc;A2F_;F_;F_;F_;").
Proof.
  intros H Hlo Hhi Hoff. unfold fully_covered in H. rewrite Hlo, Hhi in H.
  apply covers_In. pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (off - lo)) ltac:(apply in_seq; lia)) as X.
  cbn beta in X. rewrite Z2Nat.id in X by lia. replace (lo + (off - lo)) with off in X by lia. exact X.
Qed.

Section Kit.
Variable segs : list Segment.
Variables (rhoW rhoF : valuation) (ms msF : machine_state) (mW : word -> option byte).
Hypothesis Hrom : rom_ok segs ms.
Hypothesis HromF : rom_ok segs msF.
Variables (UNCH CHG : list sobj).
Hypothesis HU_entry : ltac2:(tb__ "0|0|
S40S8S14Vsegs;VrhoW;S4aVms;VmW;A2A3VUNCH;A3").
Hypothesis HU_leaf : ltac2:(tb__ "0|0|
S40S8S14Vsegs;VrhoF;VmsF;A3VUNCH;A3").
Hypothesis HC_leaf : ltac2:(tb__ "0|0|
S40S8S14Vsegs;VrhoF;VmsF;A3VCHG;A3").

Variable NX : positive.
Hypothesis Hag : ltac2:(tb__ "0|0|
S1aVNX;VrhoW;VrhoF;A3").
Hypothesis Hvars : ltac2:(tb__ "0|0|
S3S1fS2eS8S15VNX;A1S22S8VUNCH;VCHG;A3A3S20A3").
Hypothesis HU_cov : ltac2:(tb__ "0|0|
S3S1fS2eS8S46VUNCH;A3S20A3").
Hypothesis Hlits : ltac2:(tb__ "0|0|
S3S1fS2eS8S47S22S8VUNCH;VCHG;A3A3S20A3").
Hypothesis HU_dunk : ltac2:(tb__ "0|1|
S3S1fS2eS8S8S19S1fLx;S1cR1A1S20S21S21S1S21Ll;M0G0S0S7S29S27S0S0A2A1S29S1eA1S21Ltmpl;Lflds;Lcnt;Lesz;X19x6Lo;S22S8VUNCH;VCHG;A3A3S20A3").

Definition m' : word -> option byte := ltac2:(tb__ "0|0|
S4bVrhoF;S22S8VUNCH;VCHG;A3VmsF;A3").

Lemma obj_below o : ltac2:(tb__ "0|0|
S2dS8Vo;S22S8VUNCH;VCHG;A3A3S3S1fS15VNX;Vo;A2S20A3F_;").
Proof using Hvars. intros Ho. exact (proj1 (forallb_forall _ _) Hvars o Ho). Qed.

Lemma eval_ag e : ltac2:(tb__ "0|0|
S3S1fSdVNX;Ve;A2S20A3S3S39Q40A1S13VrhoF;Ve;A2S13VrhoW;Ve;A2A3F_;").
Proof using Hag. intros He. symmetry. apply (eval_agree NX); assumption. Qed.

Lemma soff_ag e : ltac2:(tb__ "0|0|
S3S1fSdVNX;Ve;A2S20A3S3S0ScVrhoF;Ve;A2ScVrhoW;Ve;A2A3F_;").
Proof using Hag. intros He. unfold soff. rewrite eval_ag by exact He. reflexivity. Qed.

Lemma obj_wf_parts o : ltac2:(tb__ "0|0|
S3S1fS15VNX;Vo;A2S20A3S4S3S1fSdVNX;S18Vo;A1A2S20A3S4S3S1fSdVNX;S10Vo;A1A2S20A3S4S3S1fSdVNX;SfVo;A1A2S20A3S9S2dS9R1SeVo;A1A3S4S3S1fSdVNX;SbR2A1A2S20A3S3S1fSdVNX;S17R2A1A2S20A3A2F_;Fc;A2A2A2F_;").
Proof using .
  intros H. unfold obj_wf in H. apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hh]. apply andb_prop in H as [Hb Hl].
  split; [exact Hb|]. split; [exact Hl|]. split; [exact Hh|].
  intros c Hin. pose proof (proj1 (forallb_forall _ _) Hc c Hin) as W. unfold cell_wf in W.
  apply andb_prop in W as [W Wv]. apply andb_prop in W as [W Wo]. auto.
Qed.

Lemma range_ag o : ltac2:(tb__ "0|0|
S2dS8Vo;S22S8VUNCH;VCHG;A3A3S3S27S0S0A2S11VrhoF;Vo;A2S11VrhoW;Vo;A2A3F_;").
Proof using Hag Hvars.
  intros Ho. destruct (obj_wf_parts o (obj_below o Ho)) as (B & L & H & _).
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite (eval_ag _ B), (soff_ag _ L), (soff_ag _ H). reflexivity.
Qed.

Lemma kit_out a : ltac2:(tb__ "0|0|
S6S43VrhoF;S22S8VUNCH;VCHG;A3Va;A3A1S3S23S39Q8A1A1S2fVa;A1S1dVrhoF;Va;A2A3F_;").
Proof using . intros H. unfold m'. apply release_out. exact H. Qed.
Lemma kit_in a : ltac2:(tb__ "0|0|
S43VrhoF;S22S8VUNCH;VCHG;A3Va;A3S3S23S39Q8A1A1S2fVa;A1S49VmsF;Va;A2A3F_;").
Proof using . intros H. unfold m'. apply release_in. exact H. Qed.

Lemma in_ranges_of o x : ltac2:(tb__ "0|2|
S2dS8Vo;S22S8VUNCH;VCHG;A3M0A3S4S30S26S0S0S11VrhoF;Vo;A2M1A3Vx;A2S31Vx;S28S0S0G1A3A2A2S4S30Z0Vx;A2S31Vx;S35Z2Z40A2A2A2S43VrhoF;G0S3aQ40Vx;A2A3F_;F_;F_;").
Proof using . intros Ho Hx R. exists o. split; [exact Ho|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hx. Qed.

Lemma lits_of o lo hi : ltac2:(tb__ "0|2|
S2dS8Vo;S22S8VUNCH;VCHG;A3A3S3S7S10Vo;A1M0SaVlo;A1A3S3S7SfVo;A1M1SaVhi;A1A3S4S16S3S0ScR1G0A2Vlo;A3Frho;S4S16S3S0ScR1G1A2Vhi;A3Frho;S9S0S2dS9R2SeVo;A1A3S3S7SbR3A1SaR2A1A3S16S3S0ScR1SbR5A1A2R4A3Frho;F_;F_;Fz;Fc;A2A2F_;F_;F_;").
Proof using Hlits.
  intros Ho Elo Ehi. pose proof (proj1 (forallb_forall _ _) Hlits o Ho) as HL. unfold obj_lits_ok in HL.
  rewrite Elo, Ehi in HL. apply andb_prop in HL as [HL HC]. apply andb_prop in HL as [H1 H2].
  split; [intros rho; rewrite Elo; apply lit_ok_soff; exact H1|].
  split; [intros rho; rewrite Ehi; apply lit_ok_soff; exact H2|].
  intros c z Hc Ez rho. pose proof (proj1 (forallb_forall _ _) HC c Hc) as X. cbn beta in X. rewrite Ez in X. rewrite Ez. apply lit_ok_soff. exact X.
Qed.

Theorem unch_same o x : ltac2:(tb__ "0|2|
S2dS8Vo;VUNCH;A3S4S30S26S0S0S11VrhoF;Vo;A2M0A3Vx;A2S31Vx;S28S0S0G0A3A2A2S4S3S23S39Q8A1A1S3eVsegs;S2fS3aQ40Vx;A2M1A3S3eVsegs;VmW;G1A3A3S3S1fS3fVsegs;S2fG1A3S3fVsegs;VmW;G1A3A3A2F_;F_;").
Proof using HU_cov HU_dunk HU_entry HU_leaf Hag Hlits Hrom HromF Hvars.
  intros Ho Hx.
  assert (HoA : In o (UNCH ++ CHG)) by (apply in_app_iff; left; exact Ho).
  pose proof (proj1 (forallb_forall _ _) HU_cov o Ho) as COV.
  pose proof (proj1 (forallb_forall _ _) HU_dunk o HoA) as DK.
  pose proof (proj1 (Forall_forall _ _) HU_entry o Ho) as HE.
  pose proof (proj1 (Forall_forall _ _) HU_leaf o Ho) as HF.
  destruct (obj_wf_parts o (obj_below o HoA)) as (Bb & Bl & Bh & Bc).
  pose proof (range_ag o HoA) as RA. pose proof Hx as HxF. rewrite RA in Hx.
  assert (DK' : ob_dflt o = DUnknown) by (cbn beta in DK; destruct (ob_dflt o); try discriminate; reflexivity).
  unfold fully_covered in COV. destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  destruct (lits_of o lo hi HoA Elo Ehi) as (Slo & Shi & Sc).
  unfold obj_range, obj_lo_of, obj_hi_of in Hx, HxF. rewrite Slo, Shi in Hx, HxF. cbn [fst snd] in Hx, HxF.
  destruct (fully_covered_In o lo hi (x - bv_unsigned (eval rhoW (ob_base o))) ltac:(unfold fully_covered; rewrite Elo, Ehi; exact COV) Elo Ehi ltac:(lia))
    as (c & co & Hc & Eco & Rc).
  destruct (Bc c Hc) as [Boff Bval]. pose proof (Sc c co Hc Eco) as Soff.
  set (j := Z.to_nat (x - bv_unsigned (eval rhoW (ob_base o)) - co)).
  assert (Wc : (j < Z.to_nat (c_width c))%nat) by (subst j; lia).
  pose proof (cell_bytes_sym segs rhoF msF o c j HF Hc Wc) as BF.
  pose proof (cell_bytes_sym segs rhoW (with_mem ms mW) o c j HE Hc Wc) as BE.
  rewrite (eval_ag _ Bb), (eval_ag _ Bval) in BF. rewrite !Soff in BF, BE.
  subst j. rewrite Z2Nat.id in BF, BE by lia.
  replace (bv_unsigned (eval rhoW (ob_base o)) + co + (x - bv_unsigned (eval rhoW (ob_base o)) - co)) with x in BF, BE by lia.
  rewrite (rd_with_mem segs ms mW _ Hrom) in BE.
  assert (RX : 0 <= x < 2 ^ 64).
  { pose proof HE as ((R0 & R1 & _) & _). unfold obj_lo_of, obj_hi_of in R0, R1. rewrite Slo in R0. rewrite Shi in R1. lia. }
  assert (IN : in_ranges rhoF (UNCH ++ CHG) (Z_to_bv 64 x)).
  { apply (in_ranges_of o x HoA); [|exact RX]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Slo, Shi. cbn [fst snd]. lia. }
  split.
  - rewrite (rd_of_at segs m' msF _ HromF (kit_in _ IN)). rewrite BF, BE. reflexivity.
  - destruct (dunk_byte segs rhoF msF o x HF DK' ltac:(unfold obj_range, obj_lo_of, obj_hi_of; rewrite Slo, Shi; cbn [fst snd]; lia)) as [_ WF].
    destruct (dunk_byte segs rhoW (with_mem ms mW) o x HE DK' ltac:(unfold obj_range, obj_lo_of, obj_hi_of; rewrite Slo, Shi; cbn [fst snd]; lia)) as [_ WE].
    rewrite (wok_of_at segs m' msF _ (kit_in _ IN) WF). symmetry. apply wok_of_wview. exact WE.
Qed.

Theorem chg_byte o x : ltac2:(tb__ "0|3|
S2dS8Vo;VCHG;A3S4S30S26S0S0S11VrhoF;Vo;A2M0A3Vx;A2S31Vx;S28S0S0G0A3A2A2S4S3S1fS3fVsegs;S2fS3aQ40Vx;A2M1A3S20A3S5S39Q8A1M2G2S3S23G2A1S3eVsegs;S2fG1A3S24G2R1A2A3Lb;A2A2F_;F_;").
Proof using HC_leaf HU_dunk HromF.
  intros Ho Hx.
  assert (HoA : In o (UNCH ++ CHG)) by (apply in_app_iff; right; exact Ho).
  pose proof (proj1 (forallb_forall _ _) HU_dunk o HoA) as DK.
  pose proof (proj1 (Forall_forall _ _) HC_leaf o Ho) as HF.
  assert (DK' : ob_dflt o = DUnknown) by (cbn beta in DK; destruct (ob_dflt o); try discriminate; reflexivity).
  pose proof HF as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hx, R0, R1 |- . cbn [fst snd] in Hx.
  assert (RX : 0 <= x < 2 ^ 64) by lia.
  assert (IN : in_ranges rhoF (UNCH ++ CHG) (Z_to_bv 64 x)) by (apply (in_ranges_of o x HoA); [unfold obj_range, obj_lo_of, obj_hi_of; cbn [fst snd]; lia | exact RX]).
  destruct (dunk_byte segs rhoF msF o x HF DK' ltac:(unfold obj_range, obj_lo_of, obj_hi_of; cbn [fst snd]; lia)) as [[b Hb] WF].
  split; [exact (wok_of_at segs m' msF _ (kit_in _ IN) WF)|].
  exists b. rewrite (rd_of_at segs m' msF _ HromF (kit_in _ IN)). exact Hb.
Qed.

Theorem chg_cell o c j : ltac2:(tb__ "0|4|
S2dS8Vo;VCHG;A3S2dS9Vc;SeVo;A1A3S48Vj;S36S12Vc;A1A1M0A2S3S23S39Q8M1A1M2A1S3eVsegs;S2fS3aQ40M3S32S32S3bG3S13VrhoW;S18Vo;A1A2A2ScVrhoW;SbVc;A1A2A2S34Vj;A1A2A2A3S24G2S41G2Vj;S1bG0S13VrhoF;S17Vc;A1A2A2S3aG1Z0A2A4A2A3F_;F_;F_;").
Proof using HC_leaf Hag HromF Hvars.
  intros Ho Hc Hj.
  assert (HoA : In o (UNCH ++ CHG)) by (apply in_app_iff; right; exact Ho).
  pose proof (proj1 (Forall_forall _ _) HC_leaf o Ho) as HF.
  destruct (obj_wf_parts o (obj_below o HoA)) as (Bb & Bl & Bh & Bc). destruct (Bc c Hc) as [Boff Bval].
  pose proof (cell_bytes_sym segs rhoF msF o c j HF Hc Hj) as BF.
  rewrite (eval_ag _ Bb), (soff_ag _ Boff) in BF.
  pose proof HF as ((R0 & R1 & _) & _ & HC & _). pose proof (proj1 (Forall_forall _ _) HC c Hc) as (C1 & C2 & _).
  unfold obj_lo_of, obj_hi_of in *. rewrite (eval_ag _ Bb) in R0, R1. rewrite (soff_ag _ Bl) in R0, C1. rewrite (soff_ag _ Bh) in R1, C2. rewrite (soff_ag _ Boff) in C1, C2.
  assert (IN : in_ranges rhoF (UNCH ++ CHG) (Z_to_bv 64 (bv_unsigned (eval rhoW (ob_base o)) + soff rhoW (c_off c) + Z.of_nat j))).
  { apply (in_ranges_of o _ HoA); [|lia]. rewrite (range_ag o HoA). unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. lia. }
  rewrite (rd_of_at segs m' msF _ HromF (kit_in _ IN)). exact BF.
Qed.

End Kit.
