(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "bind"; "kreq"; "KMmapRW"; "malloc"; "region"; "RkMap"; "alloc_meta"; "st_mmap_counter"; "KMunmap"; "ask"; "mkRegion"; "page_round"; "ret"; "slotst"; "FUser"; "M"; "SP"; "enframe"; "get"; "itree"; "lupd"; "mkAMeta"; "new_region"; "put"; "rg_len"; "set_mmap_counter"; "set_regions"; "setm"; "slot_zero"; "st_regions"; "step_seq"; "upd_region"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "unit"; "option"; "bool"; "cons"; "nil"; "Some"; "None"; "nat"; "false"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "md_needed"; "md_r"; "md_s2"; "md_s1"; "md_len"; "md_p"; "md_rg"; "md_s6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "region_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "nr_id"; "nr_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "seq_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun.Run"; "md_kill"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "land"; "pow"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfGroup MallocWfSlot
  TryAvailPost FreeNtPost MallocFastPost AllocGroupPost MallocDirectPost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Run.
Variables (s : astate) (n : Z).
Hypothesis Hn : direct_case n.

Lemma malloc_direct_unfold : ltac2:(tb__ "0|8|
S30S15S0S24S26S1A1M0S0A2A2S5Vn;Vs;A2S2S27G0SbS4S31Vn;A1M1A1A1S27S27S11G0A1M2L_;S2fR1A1SeG0S2bS1A1M3A2M4S2S2cG0S18S7SdG1A1M5A2S2cS2S25G0S20S25S2G0G0S8G0G0G2Log;R1S1S2S25G0S1dR1S17G3G3S12R4Z0M6A2G6G6G6Z3fS40G5Z1000A2G6S28SfS1eS29SfA1A3AaA2S25S2S0G0S14S0S41S3fS9R1A1Z1M7A2S43S42Z2Z20A2G7A2A2S22S2S25G0S19S1bR1R2A2A1S25S2S1G0S13R5G6Vn;R2S10A5S1SeG0S2aS1R1A2A2Lp;A4L_;A4Tctr;Ls0;A4L_;A4Lg;S2S27G0SbSaR3G1A2A1S27S2S25G0S21R4S6ScS7S1aR1A1S29S22A1S2dA4Lrg;A2S25G4L_;A4L_;A4X26x2Log;A4L_;A4Lr;A4X27x2Lok;Vs;A5A3").
Proof using Hn.
  destruct (direct_case_b n Hn) as [H1 H2]. unfold malloc. rewrite H1, H2. reflexivity.
Qed.

Theorem malloc_direct_refused : ltac2:(tb__ "0|2|
S39S24S26S1A1M0S0A2S5Vn;Vs;A2S28S24S3S22A2M1S23S3S22S4S31Vn;A1A1Z0A4S29G1A1A3S23G0S0S2bS1A1Vs;A4A4").
Proof using Hn.
  rewrite malloc_direct_unfold. eapply yields_bind_one; [apply yields_ask1; exact I|]. cbn [Z.eqb negb]. apply yields_ret.
Qed.

Lemma s1_eq : ltac2:(tb__ "0|0|
S30S0S3cSdS31Vn;A1A1Vs;A2S34Vs;Vn;A2A3").
Proof using . reflexivity. Qed.
Lemma s2_eq : ltac2:(tb__ "0|0|
S30S0S3dS34Vs;Vn;A2A1S33Vs;Vn;A2A3").
Proof using . unfold seq_post, md_s2. unfold md_s1 at 1. cbn [st_seq set_regions]. reflexivity. Qed.
Lemma r_eq : ltac2:(tb__ "0|0|
S30S2cS3bVs;A1S32Vs;A1A3").
Proof using . reflexivity. Qed.

Variables (z : Z) (ktr : list (kreq * Z)) (s3 : astate).
Hypothesis Hz : z <> 0.

Definition md_kill (t : astate) : astate := ltac2:(tb__ "0|0|
S1cS16S6S1fVt;A1S32Vs;A1ScS7S35Vn;A1S29S22A1S2dA4A4Vt;A2").

Theorem malloc_direct_am_null (zu : Z) : ltac2:(tb__ "0|6|
S39S24S26S1A1M0S0A2M1S8S33Vs;Vn;A2A1Vktr;S23G0S0S2bS1A1M2Vs3;A4A4S30S26S6A1S3aVs3;S32Vs;A1M3A2S2aS6S37Vn;A1A2A3S39G1S5Vn;Vs;A2S28S24S3S22A2M4S23S3S22S4S31Vn;A1M5A1Vz;A4S2eG4Vktr;S28G4S23S3S22SaG3G5A2Vzu;A4S29G4A1A3A3A3S23G0S0G2S3eVs3;A1A4A4F_;F_;").
Proof using Hn Hz.
  intros Ham Hrg. rewrite malloc_direct_unfold.
  change ((KMmapRW (md_needed n), z) :: ktr ++ [(KMunmap (md_r s) (md_needed n), zu)])
    with ([(KMmapRW (md_needed n), z)] ++ (ktr ++ [(KMunmap (md_r s) (md_needed n), zu)])).
  eapply yields_bind; [apply yields_ask1; exact I|].
  replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). cbn [negb].
  eapply yields_bind0; [apply yields_of_eq; apply new_region_eq|]. rewrite s1_eq, r_eq.
  eapply yields_bind0; [apply yields_of_eq; apply step_seq_eq|]. rewrite s2_eq.
  eapply yields_bind; [exact Ham|]. cbn beta iota.
  eapply yields_bind_one; [apply yields_ask1; exact I|].
  eapply yields_bind0; [|apply yields_ret].
  apply yields_of_eq. unfold upd_region, modify, md_kill. do 2 f_equal.
  unfold region_of in Hrg. rewrite (nth_error_nth _ _ _ Hrg). reflexivity.
Qed.

Variable g : sptr.
Hypothesis Ham : ltac2:(tb__ "0|1|
S39S24S26S1A1M0S0A2S8S33Vs;Vn;A2A1Vktr;S23G0S0S2aS1Vg;A2Vs3;A4A4").
Hypothesis Hctr3 : ltac2:(tb__ "0|0|
S30S22S9Vs3;A1S9Vs;A1A3").

Theorem malloc_direct_am_ok : ltac2:(tb__ "0|1|
S39S24S26S1A1M0S0A2S5Vn;Vs;A2S28S24S3S22A2S23S3S22S4S31Vn;A1A1Vz;A4Vktr;A3S23G0S0S2aS1S36Vs;Vn;A2A2S38Vs;Vn;Vs3;Vg;A4A4A4").
Proof using Ham Hctr3 Hn Hz.
  rewrite malloc_direct_unfold.
  change ((KMmapRW (md_needed n), z) :: ktr) with ([(KMmapRW (md_needed n), z)] ++ ktr).
  eapply yields_bind; [apply yields_ask1; exact I|].
  replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). cbn [negb].
  eapply yields_bind0; [apply yields_of_eq; apply new_region_eq|]. rewrite s1_eq, r_eq.
  eapply yields_bind0; [apply yields_of_eq; apply step_seq_eq|]. rewrite s2_eq.
  rewrite <- (app_nil_r ktr). eapply yields_bind; [exact Ham|]. cbn beta iota.
  change (mkAMeta None None (SP (md_r s) 0) 0 0 0 63 (page_round (md_needed n) / 4096) 0 [slot_zero]) with (md_am4 s n).
  eapply yields_bind0; [apply yields_setm|]. change (upd_meta g (MUsed (md_am4 s n)) s3) with (md_s4 s n s3 g).
  eapply yields_bind0; [apply yields_of_eq; apply get_eq|].
  assert (Hc : Z.land (st_mmap_counter (md_s4 s n s3 g) + 1) (2 ^ 32 - 1) = md_ctr1 s).
  { unfold md_ctr1. unfold md_s4, upd_meta. cbn [st_mmap_counter set_metas]. rewrite Hctr3. reflexivity. }
  cbn zeta. rewrite Hc.
  eapply yields_bind0; [apply yields_of_eq; apply put_eq|]. change (set_mmap_counter (md_ctr1 s) (md_s4 s n s3 g)) with (md_s5 s n s3 g).
  eapply yields_bind0; [exact (yields_enframe s n Hn s3 g)|].
  apply yields_ret.
Qed.
End Run.
