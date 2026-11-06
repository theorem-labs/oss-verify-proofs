(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "layout"; "LMem"; "MCell"; "WF"; "cell_range"; "layout_ok"; "VZ"; "image"; "byteview"; "cell_holds"; "in_user_block"; "ranges_disjoint"; "alloc_owned"; "block_range"; "crange"; "footprint"; "frame_ptr"; "frames"; "implb"; "loc"; "range_incl"; "repr"; "rsv_code"; "used_metas"; "user_blocks"; "zseq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "astate"; "frame"; "padd"; "IB"; "fr_n"; "stride_of"; "UNIT"; "am_last"; "fkind"; "fr_off"; "am_mem"; "fr_kind"; "nth_slot"; "slot_start"; "ss_fr"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "andb"; "cons"; "option"; "app"; "pair"; "None"; "list"; "nil"; "snd"; "true"; "@Stdlib.Lists.List"; "In"; "flat_map"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "eqb"; "le"; "leb"; "add"; "mul"; "ltb"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reserved_of"; "reprO"; "reprP"; "slot_end"; "trailing_loc"; "NV"; "frame_footer_cells"; "group_footer_cells"; "nominal_asserts"; "nominal_view_of"; "nv_at_end"; "nv_at_end_minus_reserved"; "nv_code"; "nv_end5"; "nv_end_minus_p"; "nv_u32"; "owned_mapped"; "trailing_cell"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Init.Specif"; "sumbool"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocWfMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Infix "==>" := implb (at level 55, right associativity).

Definition slot_end (am : ameta) (i : Z) : sptr := ltac2:(tb__ "0|0|
S20S2bVam;Vi;A2S3bS23Vam;A1S21A2A2").

Definition reserved_of (am : ameta) (fr : frame) : Z := ltac2:(tb__ "0|0|
S3bS3bS3bS23Vam;A1S21A2S40S24S27Vfr;A1A2A2S22Vfr;A1A2").

Definition trailing_loc (am : ameta) : sptr := ltac2:(tb__ "0|0|
S20S28Vam;A1S3bS3fS24S40S23Vam;A1S3fS25Vam;A1Z1A2A2A2S21A2A2").

Definition trailing_cell (am : ameta) : mcell := ltac2:(tb__ "0|0|
S3S2S4cVam;A1A1U1S7Z0A1A3").

Lemma trailing_is_last_end : ltac2:(tb__ "0|0|
S1dS43S1cS4cR1A1S4bR1S25R1A1A2A3Fam;").
Proof.
  intros am. unfold trailing_loc, slot_end, slot_start, padd. destruct (am_mem am) as [r o].
  f_equal. lia.
Qed.

Definition frame_footer_cells (am : ameta) (i : Z) (fr : frame) : list mcell := ltac2:(tb__ "0|7|
S26S35S0A1M0Lx;S29Vfr;A1S11Vam;Vi;Vfr;A3S1cS4bVam;Vi;A2S1cS48Vam;Vfr;A2S1bS32S0S2dG0L_;M1S41Z0M2R1A2S30S0S3S2S20R3S22Vfr;A1A2A1U1M3S7G2A1M4A3S36S0A1M5A3G5X2dx2S32S0G1S3eZ5M6R1A2S30S0S3S2S20R2N4A2A1U4S7R1A1A3G5A3G5X2dx2G1S41G6R1A2S30S0S3S2S20R2N5A2A1G3G4A3G5A3G5X2dx2A3A3Tr;Te;Tp;G5X26x2").

Definition group_footer_cells (am : ameta) : list mcell := ltac2:(tb__ "0|0|
S30S0S59Vam;A1S3aS1bS0S1bS31S1fA1S35S0A1Lx;S2cS2aVam;R1A2A1S1fS4eVam;R2R1A3Lfr;S36S0A1X31x2Li;S1aZ0S3fS25Vam;A1Z1A2A2A4A3").

Definition footer_cells (s : astate) : list mcell := ltac2:(tb__ "0|1|
S3aS2eS1cS1dA2M0S0G0S4fS37S1cS1dR1A3A1Lgm;S18Vs;A1A4").

Definition imageP (s : astate) : list mcell := ltac2:(tb__ "0|0|
S32S0S8Vs;A1S47Vs;A1A3").

Definition reprP (L : layout) (s : astate) (m : byteview) : Prop := ltac2:(tb__ "0|0|
S42S16VL;Vs;Vm;A3S5aS0SaVL;Vm;A2S47Vs;A1A3A2").

Definition owned_mapped (L : layout) (s : astate) (m : byteview) : Prop := ltac2:(tb__ "0|0|
S1bSdVL;Vs;R1A3S44S43S31S1bA1Vm;R2A1S34S1bA1A3A1F_;Fx;").

Definition reprO (L : layout) (s : astate) (m : byteview) : Prop := ltac2:(tb__ "0|1|
S42S42S6VL;Vs;A2S42S5aS0SaVL;Vm;A2M0S8Vs;A1A3S58VL;Vs;Vm;A3A2A2S5aS0G0S47Vs;A1A3A2").

Lemma reprP_reprO : ltac2:(tb__ "0|0|
S1S1eS9S4aR3R2R1A3S49R4R3R2A3F_;Fm;Fs;FL;").
Proof.
  intros L s m [[HL [HI HR]] HF]. split; [|exact HF]. split; [exact HL|]. split; [exact HI|].
  intros x [(rg & Hrg & Hx) _]. exact (proj1 (Forall_forall _ _) HR rg Hrg x Hx).
Qed.

Lemma in_user_block_dec : ltac2:(tb__ "0|1|
S1S1eS1bS5bSbR3R2R1A3M0S44G0A1A2Fx;Fs;FL;").
Proof.
  intros L s x.
  destruct (existsb (fun b : sptr * Z => (loc_addr L (LMem (fst b)) <=? x) && (x <? loc_addr L (LMem (fst b)) + snd b)) (user_blocks s)) eqn:E.
  - left. apply existsb_exists in E as (b & Hb & Hx). apply andb_prop in Hx as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists b. split; [exact Hb | lia].
  - right. intros (b & Hb & Hx). apply Bool.not_true_iff_false in E. apply E. apply existsb_exists. exists b. split; [exact Hb|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma reprO_reprP : ltac2:(tb__ "0|0|
S1S1eS9S49R3R2R1A3S1bSbR5R4R1A3S44S43S31S1bA1R4R2A1S34S1bA1A3A1F_;Fx;S4aR5R4R3A3F_;F_;Fm;Fs;FL;").
Proof.
  intros L s m [[HL [HI HO]] HF] HB. split; [|exact HF]. split; [exact HL|]. split; [exact HI|].
  apply Forall_forall. intros rg Hrg x Hx.
  destruct (in_user_block_dec L s x) as [H|H].
  - exact (HB x H).
  - apply HO. split; [exists rg; split; [exact Hrg | exact Hx] | exact H].
Qed.

Record nominal_view := NV {
  nv_code : Z; nv_u32 : Z; nv_end5 : Z; nv_at_end_minus_reserved : Z; nv_at_end : Z; nv_end_minus_p : Z }.

Definition nominal_asserts (v : nominal_view) : bool := ltac2:(tb__ "0|5|
S2dS1bL_;S3eZ5M0S54Vv;A1M1A2M2S57Vv;A1M3G1X2dx2S1bS2fS2fS2fS13G2S2fS2fS3cG1G0A2S3eG0G3A2A2S3cS55Vv;A1Z0M4A2A2A2S3eR1S56Vv;A1A2A2S3cS53Vv;A1G4A2A2S3cS52Vv;A1G4A2A2Treserved;").

Definition nominal_view_of (am : ameta) (i : Z) (fr : frame) : nominal_view := ltac2:(tb__ "0|1|
S48Vam;Vfr;A2S1bS4dS17Vam;Vfr;A2R1Z0M0G0G0S3bS3bS23Vam;A1S21A2S40S24S27Vfr;A1A2A2A6Tr;").

Lemma nominal_asserts_ok_arith : ltac2:(tb__ "0|1|
S1dS1bS1fS3dZ0M0S22R1A1A2S3dG0S48R4R2A2A2S43S2dS50S51R5R4R3A3A1S38A3F_;F_;Ffr;Fi;Fam;").
Proof.
  intros am i fr Hn Hr. unfold nominal_asserts, nominal_view_of, rsv_code.
  cbn [nv_code nv_u32 nv_end5 nv_at_end_minus_reserved nv_at_end nv_end_minus_p].
  change (stride_of am - IB - UNIT * fr_off fr - fr_n fr) with (reserved_of am fr).
  set (r := reserved_of am fr) in *.
  assert (Hst : r + fr_n fr = stride_of am - IB - UNIT * fr_off fr) by (subst r; unfold reserved_of; lia).
  destruct (5 <=? r) eqn:E5.
  - apply Z.leb_le in E5. unfold implb. cbn [negb Z.leb Z.eqb andb orb].
    replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia).
    change (5 <=? 5) with true. change ((5 =? 5)%positive) with true. cbn [negb orb andb].
    replace (r <=? stride_of am - IB - UNIT * fr_off fr) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
  - apply Z.leb_gt in E5. unfold implb. rewrite E5 || idtac.
    replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb orb andb].
    replace (r <=? stride_of am - IB - UNIT * fr_off fr) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

Definition footer_in_footprint_stmt : Prop := ltac2:(tb__ "0|1|
S1eS1S0S4R3A1S6R3R4A2S39S0R3S47R5A1A3S45S2eS14S1bA2M0G0S42S39G0R1S10R7A1A3S15S5R6R5A2SfR6R1A2A2A2Lrg;A2F_;F_;F_;Fc;FL;Fs;").

Definition footer_outside_user_blocks_stmt : Prop := ltac2:(tb__ "0|1|
S1eS1S0S2eS1cS1bA2M0S4R4A1S6R4R5A2S39S0R4S47R6A1A3S39G0R4S19R7A1A3ScS5R7R6A2SeR7R5A2A2F_;F_;F_;F_;Fb;Fc;FL;Fs;").

Definition footer_compatible_stmt : Prop := ltac2:(tb__ "0|0|
S1eS1S0S0S4R4A1S6R4R5A2S39S0R4S47R6A1A3S39S0R4S8R7A1A3S46ScS5R7R6A2S5R7R5A2A2S43S0R6R5A3A2F_;F_;F_;F_;Fc';Fc;FL;Fs;").

Definition reserved_nonneg_stmt : Prop := ltac2:(tb__ "0|3|
S1eS1cS1dS1bS1fS4R5A1S39S2eS2eS2eS1cS1dA2M0S1bA2M1S1fA2S33G1S1fS33G0S1bS33S1cS1dR5R4A4R3A4R2A4S12R6A1A3S42S3dZ0M2S22R3A1A2S3dG2S48R5R3A2A2A2F_;F_;Ffr;Fi;Fam;Fg;Fs;").

Lemma reserved_nonneg_holds : reserved_nonneg_stmt.
Proof.
  intros s g am i fr HWF Hin.
  destruct (frames_inv s g am i fr HWF Hin) as [Hused [Hi Hfr]].
  pose proof (inv_groups HWF g am Hused) as HG.
  destruct HG as [_ [_ [Hslots _]]].
  specialize (Hslots i Hi). unfold slot_ok in Hslots.
  rewrite Hfr in Hslots. destruct Hslots as [_ [_ C]]. destruct C as [_ [_ [Hfrok _]]].
  unfold frame_ok in Hfrok. unfold reserved_of. lia.
Qed.
