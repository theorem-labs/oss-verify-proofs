(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "unit"; "nat"; "Some"; "false"; "option"; "bool"; "nil"; "list"; "tt"; "negb"; "None"; "andb"; "app"; "cons"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "region"; "ameta"; "frame"; "RkMap"; "kreq"; "mkRegion"; "NEST_FUEL"; "am_avail"; "am_freed"; "bit"; "free"; "nontrivial_free"; "KMunmap"; "am_last"; "bind"; "ones"; "rg_len"; "st_regions"; "FUser"; "IRet"; "M"; "ask"; "find_frame"; "fkind"; "fr_kind"; "fr_n"; "itree"; "lupd"; "ret"; "set_regions"; "upd_region"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "frame_ptr"; "frames"; "region_of"; "user_blocks"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "lor"; "add"; "land"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease"; "rs1"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfGeom MallocWfRepr MallocWfMain MallocWfFree
  FreeQuickModel FreeQuickPost FreeRelease MallocFastPost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma user_block_of_frame : ltac2:(tb__ "0|2|
S12S13S15S0S16S3aS1S1S1S13S15A2M0S0A2M1S16A2S2G1S16S2G0S0S2S13S15R4R3A4R2A4R1A4S37R5A1A3S33S2bS2cR2A1S26A3S3aS1S13S0A2S2S13S0S36R5R4R3A3S2dR3A1A4S39R7A1A3F_;F_;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr Hfr Hk. destruct (in_frames_inv s g am i fr Hfr) as (Hg & Hi & Hsl).
  unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hg|]. cbn [snd].
  apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hsl, Hk. left. reflexivity.
Qed.

Section Y.
  Variables (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame).
  Hypothesis HW : WF s.
  Hypothesis Hfr : ltac2:(tb__ "0|2|
S3aS1S1S1S13S15A2M0S0A2M1S16A2S2G1S16S2G0S0S2S13S15Vg;Vam;A4Vi;A4Vfr;A4S37Vs;A1A3").
  Hypothesis Hkind : fr_kind fr = FUser.
  Hypothesis Hslow : ltac2:(tb__ "0|1|
S34S33S0S1cVam;A1M0Z0A3S33S0S3dS3cG0S1bVam;A1A2S1dVi;A1A2S23S21Vam;A1A1A3A2").

  Let FFx : frame_facts s g am i fr := ltac2:(tb__ "0|0|
S40Vs;Vg;Vam;Vi;Vfr;VHW;VHfr;A7").
  Let p : sptr := ltac2:(tb__ "0|0|
S36Vam;Vi;Vfr;A3").
  Let s1 : astate := ltac2:(tb__ "0|0|
S41Vs;Vg;Vam;Vi;A4").

  Lemma find_frame_eq : ltac2:(tb__ "0|2|
S33S2eS12S1S1S13S0A2M0S12A2M1A2S2aVp;Vs;A2S27S12G1S2G0S12S2S13S0Vg;Vi;A4Vs;A4A3A3").
  Proof using FFx.
    unfold p, find_frame, bind, get. cbn [ibind].
    rewrite (find_frame_in_spec [] None U0 s HW g am i fr (ff_used _ _ _ _ _ FFx) (ff_i _ _ _ _ _ FFx) (ff_slot _ _ _ _ _ FFx)).
    reflexivity.
  Qed.

  Lemma mask_self : ltac2:(tb__ "0|0|
S33S8S3bS3eS3cS1cVam;A1S1bVam;A1A2S1dVi;A1A2Z0A2S11A3").
  Proof using FFx.
    apply Z.eqb_eq. apply Z.bits_inj'. intros j Hj.
    rewrite Z.land_spec, Z.lor_spec, Z.bits_0, testbit_bit by exact (proj1 (ff_i _ _ _ _ _ FFx)).
    destruct (Z.eq_dec i j) as [<-|Hne].
    - rewrite (ff_freed_i _ _ _ _ _ FFx), (ff_avail_i _ _ _ _ _ FFx). reflexivity.
    - replace (i =? j) with false by (symmetry; apply Z.eqb_neq; lia). apply Bool.andb_false_r.
  Qed.

  Lemma quick_false : ltac2:(tb__ "0|1|
S33S8SeScS3bS1cVam;A1M0Z0A2A1ScS3bS3dS3cG0S1bVam;A1A2S1dVi;A1A2S23S21Vam;A1A1A2A1A2S6A3").
  Proof using Hslow.
    destruct Hslow as [H | H]; rewrite H; [rewrite Z.eqb_refl; reflexivity|]. rewrite Z.eqb_refl. apply Bool.andb_false_r.
  Qed.

  Lemma free_slow_prefix : ltac2:(tb__ "0|4|
SaS1S18S0A2A1S1S3S12A2M0S35G0S22S7S1S4S0A2M1A1M2S3S1fS1aVg;Vi;A3G2G2S28S3A1M3Lmi;R1G1G1G3Lp0;R1S4S0S22S8S3S29S20R2R1A2A1S8S32R3S14S19S17S24R1A1S9S0A1S6A4Lrg;A2L_;A4Llen;Lr0;X1x1Lp0;S30S3SbA2X7x2Lmi;Vs1;A5R2R1A4S35G0S1eS5S13Vp;A2Vs;A2R3R2A4F_;Fr;Ftr;").
  Proof using FFx Hslow.
    intros tr r HY. unfold p, free.
    apply (yields_bind0 _ _ s tr (g, i) s); [pose proof find_frame_eq as E; unfold p in E; rewrite E; reflexivity|]. cbn [fst snd].
    apply (yields_bind0 _ _ s tr am s); [apply yields_getm; exact (ff_MT _ _ _ _ _ FFx)|].
    apply (yields_bind0 _ _ s tr tt s1); [unfold s1; rewrite (release_slot_eq s g am i fr FFx); reflexivity|].
    apply (yields_bind0 _ _ s1 tr tt s1); [unfold massert; rewrite mask_self; reflexivity|].
    rewrite quick_false. exact HY.
  Qed.

  Theorem free_slow_yields_none : ltac2:(tb__ "0|2|
SaS1S18S0A2A1S12S35S1S7S1S4S0A2M0A1M1S12A2S1fS1aVg;Vi;Vs1;A4R2S2G1S12SdG0A1R1A4A4S35S1S3S12A2S1eS5S13Vp;A2Vs;A2R3S2S3S12SbR2A4A4F_;Fs2;Fktr;").
  Proof using FFx Hslow.
    intros ktr s2 HY. apply free_slow_prefix. apply (yields_bind1 _ _ s1 ktr None s2); [exact HY|]. reflexivity.
  Qed.

  Theorem free_slow_yields_some : ltac2:(tb__ "0|5|
SaS1S18S0A2M0A1S4S0S12S0S35S1S7S1S4S0A2M1A1M2S12A2S1fS1aVg;Vi;Vs1;A4R5S2G2S12S5G1S2S4S0R4R3A4A2R2A4A4S35S1S3S12A2S1eS5S13Vp;A2Vs;A2SfG0R6S10G0S2S18S0S20R5R4A2R2A4S9G0A1A3A3S2S3S12SbS31S2fS14S25R3A1M3R5S19S17S24S3fS14R5G3S19S17Z0S9S0A1M4S6A4A4A1G4S6A4A4R3A2A4A4F_;Fz;Fs2;Flen;Fr;Fktr;").
  Proof using FFx Hslow.
    intros ktr r len s2 z HY. apply free_slow_prefix. apply (yields_bind _ _ s1 ktr _ (Some (r, len)) s2); [exact HY|].
    apply (yields_bind _ _ s2 [(KMunmap r len, z)] [] (negb (z =? 0)) s2); [cbn; auto|]. reflexivity.
  Qed.

  Lemma region_of_nth : ltac2:(tb__ "0|0|
S12S4S14S33S7S14A1S38R3R2A2S5S14R1A2A3S33S14S3fS14R3S25R4A1S19S17Z0S9S0A1S6A4A4R2A3F_;Frg;Fr;Fsx;").
  Proof using . intros sx r rg H. unfold region_of in H. exact (nth_error_nth _ _ _ H). Qed.
End Y.
