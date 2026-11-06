(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "eqb"; "mul"; "@Corelib.Init.Datatypes"; "prod"; "list"; "app"; "bool"; "nil"; "pair"; "fst"; "true"; "nat"; "cons"; "snd"; "Some"; "option"; "None"; "length"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "mcell"; "loc_addr"; "LCtx"; "footprint"; "image"; "CTX_seq"; "CTX_unmap_seq"; "mc_loc"; "user_blocks"; "LMem"; "ly_reg"; "sval_num"; "crange"; "ctx_cells"; "ly_ctx"; "region_of"; "Inv"; "MCell"; "VZ"; "alloc_owned"; "bounded"; "mc_val"; "mc_w"; "U0"; "CTX_mmap_counter"; "layout_ok"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "PGSZ"; "st_regions"; "st_areas"; "RkMap"; "st_brk"; "st_metas"; "SP"; "mkRegion"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "brkst"; "mslot"; "prid"; "rg_len"; "rg_live"; "rg_kind"; "rkind"; "set_regions"; "st_mmap_counter"; "st_seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.MapGrow"; "len"; "s2"; "L'"; "wrapb"; "eN"; "r"; "vm1"; "C_useq"; "chg"; "C_seq"; "new_seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.Generic"; "gL'"; "gr"; "gvm'"; "geN"; "grg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow"; "s2"; "L'"; "len"; "vm1"; "aptr_ok"; "eN"; "wrapb"; "C_seq"; "C_useq"; "chg"; "mg_pre"; "r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_reserved"; "vm_maps"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "blocks"; "topL"; "wz"; "mc_ctx"; "vm_ok"; "img_reserved"; "ledger_ok"; "mc_img_hi"; "mc_img_lo"; "addr_of"; "maps_wf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow"; "Lext"; "vm_okX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage"; "map_fp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "md_len"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "layout_extends"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI MallocLaws
  MallocLemmasBase MallocWfInv MallocWfMeta MallocWfRepr FpLaws WalkArith
  Zones2 ImageDelta AllocMetaImage AllocMetaGrow MallocDirectPost MapsWf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma loc_eq_dec : ltac2:(tb__ "0|1|
S1fS1fS8aS1S1fR2R1A3M0S3G0A1A2Fl2;Fl1;").
Proof. intros l1 l2. destruct l1 as [o1|[r1 p1]], l2 as [o2|[r2 p2]]; try (right; discriminate).
  - destruct (Z.eq_dec o1 o2) as [->|NE]; [left; reflexivity | right; intros E; injection E; auto].
  - destruct (Nat.eq_dec r1 r2) as [->|NE]; [|right; intros E; injection E; auto].
    destruct (Z.eq_dec p1 p2) as [->|NE2]; [left; reflexivity | right; intros E; injection E; auto].
Qed.

Definition aptr_ok (s : astate) : Prop := ltac2:(tb__ "0|0|
S4S2S1S10S3bA1S3fVs;A1S13S3bA1A3S1S0S45Vs;A1Z0A3A2S6eS49S46Vs;A1A1S1dS3cS3eVs;A1A2A2A2").

Lemma map_fp_app_map s rg : ltac2:(tb__ "0|2|
S1S4dS4cVrg;A1S40A3S1S12S4bVrg;A1S16A3S1S10SfS1fS0A2M0A1S87S4eS11S3cS3eVs;A1M1S18S3cVrg;S13S3cA1A3A3Vs;A2A1S11G0S87Vs;A1S18G0S14S1fS0S29S43S1dS3cG1A2Z0A2A1S4aVrg;A1A4S13G0A1A3A3A3F_;F_;").
Proof.
  intros Hk Hl. unfold map_fp. cbn [st_regions set_regions]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, flat_map_app.
  cbn [flat_map Nat.add]. rewrite app_nil_r. rewrite (region_of_app_new s rg), Hk, Hl. f_equal.
  apply flat_map_seq_ext. intros k Hkk. rewrite (region_of_app_old s [rg] k Hkk). reflexivity.
Qed.

Section Generic.
  Variables (C : mconsts) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s s' : astate) (L : layout) (vm : VmMaps) (a len : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S30VX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S1S0S2eVL;A1S7bVC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
S7cVL;Vs;Vvm;A3").
  Hypothesis HVX : vm_okX L s.
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis APTR : aptr_ok s.
  Hypothesis Ha_al : a mod PGSZ = 0.
  Hypothesis Ha_pos : 0 < a.
  Hypothesis Hlen : ltac2:(tb__ "0|0|
S2S7S3dVlen;A2S1S0ScVlen;S3dA2Z0A3A2").
  Hypothesis Ha_ceil : ltac2:(tb__ "0|0|
S7S8Va;Vlen;A2S79VL;A1A2").
  Hypothesis Hfree : ltac2:(tb__ "0|4|
SfS83Q40M0A1M1G1A2M2S3aG2R1S11G2S6fVvm;A1S70Vvm;A1A3A3S0S2S7S84G0S15G1G1R3A3A2M3R1A2S9R1S8G3S84G0S19G1G1R3A3A2A2A2A2S3S2S7Va;R2A2S9R2S8Va;Vlen;A2A2A2A1F_;Fx;F_;Fe;").

  Hypothesis Hregs' : ltac2:(tb__ "0|0|
S1S10S3cA1S3eVs';A1S11S3cS3eVs;A1S18S3cS44S40Vlen;S13S0A1S16A4S13S3cA1A3A3A3").
  Hypothesis Hareas' : ltac2:(tb__ "0|0|
S1S10S3bA1S3fVs';A1S3fVs;A1A3").
  Hypothesis Hmetas' : ltac2:(tb__ "0|0|
S1S10SfS3bS48A2A1S42Vs';A1S42Vs;A1A3").
  Hypothesis Hbrk' : ltac2:(tb__ "0|0|
S1S47S41Vs';A1S41Vs;A1A3").

  Definition gr : nat := length (st_regions s).
  Definition gL' : layout := ltac2:(tb__ "0|0|
S85VL;S5dVa;A3").
  Definition grg : region := ltac2:(tb__ "0|0|
S44S40Vlen;S13S0A1S16A4").
  Definition gvm' : VmMaps := ltac2:(tb__ "0|1|
S71S6fVvm;A1S18SfS83Q40A1M0G0A2S14G0G0S7aVa;A1S7aVlen;A1A4S70Vvm;A1A3S76Vvm;A1S77Vvm;A1S72Vvm;A1S74Vvm;A1S75Vvm;A1S73Vvm;A1A8").
  Definition geN : loc * Z := ltac2:(tb__ "0|0|
S14S1fS0S29S43S5dZ0A2A1Vlen;A4").

  Lemma ga_facts : ltac2:(tb__ "0|3|
S2S7S3dVa;A2S2S7S8Va;Vlen;A2S79VL;A1M0A2S2S7G0Z7fffff800000A2S2S2S7Z0M1Va;A2S9Va;SbZ2Z40A2M2A2A2S2S7G1Vlen;A2S9Vlen;G2A2A2A2A2A2A2").
  Proof using Ha_al Ha_ceil Ha_pos Hlen.
    pose proof Hlen as [L1 L2]. top_ranges. unfold PGSZ in *.
    split; [Z.to_euclidean_division_equations; lia|]. lia.
  Qed.
  Lemma gua : ltac2:(tb__ "0|0|
S1S0S84Q40S7aVa;A1A2Va;A3"). Proof using Ha_al Ha_ceil Ha_pos Hlen. pose proof ga_facts. unfold wz. apply u64. lia. Qed.
  Lemma gun : ltac2:(tb__ "0|0|
S1S0S84Q40S7aVlen;A1A2Vlen;A3"). Proof using Ha_al Ha_ceil Ha_pos Hlen. pose proof ga_facts. unfold wz. apply u64. lia. Qed.

  Lemma g_region_of k : ltac2:(tb__ "0|1|
S1S1bS3cA1M0S2fVs';Vk;A2S12G0L_;S89Vk;S5dA2S1aS3cS60A2S2fVs;Vk;A2X12x2A3").
  Proof using Ha_al Ha_pos Hlen Hregs'.
    unfold region_of. rewrite Hregs'. unfold gr, grg.
    destruct (Nat.eqb k (length (st_regions s))) eqn:E.
    - apply Nat.eqb_eq in E. subst k. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hlt|Hge].
      + rewrite nth_error_app1 by exact Hlt. reflexivity.
      + rewrite nth_error_app2 by lia. replace (nth_error (st_regions s) k) with (@None region) by (symmetry; apply nth_error_None; lia).
        destruct (k - length (st_regions s))%nat as [|k'] eqn:Ek; [lia|]. cbn. destruct k'; reflexivity.
  Qed.
  Lemma g_old_lt k rg : ltac2:(tb__ "0|0|
S1S1bS3cA1S2fVs;Vk;A2S1aS3cVrg;A2A3S2S6eVk;S5dA2S2S1S12S89Vk;S5dA2S1eA3S1S0S2aS5cVk;A2S2aVL;Vk;A2A3A2A2F_;").
  Proof using Ha_al Ha_pos Hlen.
    intros Hk. pose proof (region_of_lt _ _ _ Hk) as Hlt. unfold gr. split; [exact Hlt|]. split; [apply Nat.eqb_neq; lia|].
    unfold gL'. apply Lext_old. unfold gr. lia.
  Qed.

  Lemma g_fp : ltac2:(tb__ "0|1|
S1S10SfS1fS0A2M0A1S23Vs';A1S11G0S23Vs;A1S18G0S5fS13G0A1A3A3A3").
  Proof using Hareas' Hregs'.
    rewrite !footprint_eq, Hareas'. rewrite (map_fp_regions_only (set_regions (st_regions s ++ [grg]) s) s') by (rewrite Hregs'; reflexivity).
    rewrite (map_fp_app_map s grg eq_refl eq_refl). unfold geN, gr, grg. cbn [rg_len]. rewrite app_comm_cons, app_assoc. reflexivity.
  Qed.
  Lemma g_In_fp e : ltac2:(tb__ "0|1|
S5S3aSfS1fS0A2M0Ve;S23Vs';A1A3S4S3aG0Ve;S23Vs;A1A3S1G0Ve;S5fA3A2A2").
  Proof using Hareas' Hlen Hregs'. rewrite g_fp, in_app_iff. cbn [In]. split; intros [H|H]; try tauto; [destruct H as [H|[]]; right; symmetry; exact H | right; left; symmetry; exact H]. Qed.
  Lemma g_ub : ltac2:(tb__ "0|0|
S1S10SfS3bS0A2A1S28Vs';A1S28Vs;A1A3").
  Proof using Hmetas'. unfold user_blocks, used_metas. rewrite Hmetas'. reflexivity. Qed.
  Lemma g_footers : ltac2:(tb__ "0|0|
S1S10S20A1S6dVs';A1S6dVs;A1A3").
  Proof using Hmetas'. unfold footer_cells, used_metas. rewrite Hmetas'. reflexivity. Qed.

  Lemma g_vs_image x : ltac2:(tb__ "0|0|
S2S7S80VC;A1Vx;A2S9Vx;S7fVC;A1A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;Vlen;A2A2A2A1F_;").
  Proof using HIR Hfree.
    intros Hx Hin. destruct (HIR x Hx) as (e & He & Hex).
    exact (Hfree e ltac:(apply in_app_iff; left; exact He) x Hex Hin).
  Qed.
  Lemma g_vs_maps e x : ltac2:(tb__ "0|3|
S3aSfS83Q40M0A1M1G1A2Ve;S70Vvm;A1A3S2S7S84G0S15G1G1Ve;A3A2M2Vx;A2S9Vx;S8G2S84G0S19G1G1Ve;A3A2A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;Vlen;A2A2A2A1F_;F_;").
  Proof using Hfree. intros He Hx Hin. exact (Hfree e ltac:(apply in_app_iff; right; exact He) x Hx Hin). Qed.
  Lemma g_vs_footprint e x : ltac2:(tb__ "0|1|
S3aSfS1fS0A2Ve;S23Vs;A1A3S2S7S21VL;S15S1fS0Ve;A3A2M0Vx;A2S9Vx;S8G0S19S1fS0Ve;A3A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;Vlen;A2A2A2A1F_;F_;").
  Proof using HIR HSI HV Ha_al Ha_pos Hctx Hfree Hlen.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] k].
    - pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_). cbn [fst snd loc_addr] in Hx.
      unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. apply g_vs_image. rewrite Hctx in Hx. lia.
      + exfalso. apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (kk & _ & He). destruct (region_of s kk) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - destruct (V5 p k He) as (e' & He' & R1 & R2). cbn [fst snd loc_addr] in Hx. unfold addr_of in R1, R2. cbn [loc_addr] in R1, R2.
      apply (g_vs_maps e' x He'). destruct p; cbn in *. lia.
  Qed.
  Lemma g_fp_size e : ltac2:(tb__ "0|0|
S3aSfS1fS0A2Ve;S23Vs;A1A3S9Z0S19S1fS0Ve;A3A2F_;").
  Proof using HVX a len.
    intros He. pose proof HVX as (_ & _ & SZ & _). unfold footprint in He. destruct He as [<-|He]; [cbn; unfold CTX_SIZE; lia|].
    apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & <- & _); cbn; unfold PGSZ; lia|].
    apply in_flat_map in He as (k & _ & He). destruct (region_of s k) as [rg|] eqn:Ek; [|destruct He]. destruct (rg_kind rg); try destruct He.
    destruct (rg_live rg) eqn:El; [|destruct He]. destruct He as [<-|[]]. cbn. pose proof (SZ k rg Ek El). unfold PGSZ in *. lia.
  Qed.
  Lemma g_vs_owned x : ltac2:(tb__ "0|0|
S33VL;Vs;Vx;A3S2S3S2S7Va;Vx;A2S9Vx;S8Va;Vlen;A2A2A2A1S2S9Z0Vx;A2S9Vx;SbZ2Z3fA2A2A2A2F_;").
  Proof using HIR HL HSI HV Ha_al Ha_pos Hctx Hfree Hlen.
    intros [(e & He & Hx) _]. pose proof HL as (_ & _ & _ & HR). destruct (HR e He) as [R1 R2]. unfold crange in R1, R2. cbn [fst snd] in R1, R2.
    split; [exact (g_vs_footprint e x He Hx) | lia].
  Qed.
  Lemma g_vs_block b k x : ltac2:(tb__ "0|0|
S3aSfS0S0A2S14S0S0Vb;Vk;A4S78VL;Vs;A2A3S2S7Vb;Vx;A2S9Vx;S8Vb;Vk;A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;Vlen;A2A2A2A1F_;F_;").
  Proof using HI HIR HSI HV HX Ha_al Ha_pos Hctx Hfree Hlen.
    intros Hin Hx. destruct (block_where X R U s L HI HX a Ha_pos b k x Hin Hx) as (e & p & He & _ & Rx).
    exact (g_vs_footprint e x He Rx).
  Qed.

  Lemma gL'_ext : ltac2:(tb__ "0|0|
S8bVL;S5cS5dA3"). Proof using . apply Lext_extends. Qed.
  Lemma gL'_ctx : ltac2:(tb__ "0|0|
S1S0S2eS5cA1S2eVL;A1A3"). Proof using . reflexivity. Qed.
  Lemma gL'_reg_new : ltac2:(tb__ "0|0|
S1S0S2aS5cS5dA2Va;A3"). Proof using . apply Lext_reg. Qed.
  Lemma gL'_top : ltac2:(tb__ "0|0|
S1S0S79S5cA1S79VL;A1A3"). Proof using . reflexivity. Qed.
  Lemma gL'_fp e : ltac2:(tb__ "0|1|
S3aSfS1fS0A2Ve;S23Vs;A1A3S1S0S21S5cS15S1fS0Ve;A3M0A2S21VL;G0A2A3F_;").
  Proof using HI. intros He. exact (loc_addr_ext L gL' gr _ gL'_ext (footprint_below X R U s HI e He)). Qed.
  Lemma gL'_crange e : ltac2:(tb__ "0|0|
S3aSfS1fS0A2Ve;S23Vs;A1A3S1SfS0S0A2S2cS5cVe;A2S2cVL;Ve;A2A3F_;").
  Proof using HI. intros He. unfold crange. rewrite (gL'_fp e He). reflexivity. Qed.
  Lemma gL'_ub b : ltac2:(tb__ "0|1|
S3aSfS3bS0A2Vb;S28Vs;A1A3S1S0S21S5cS29S15S3bS0Vb;A3A1M0A2S21VL;G0A2A3F_;").
  Proof using HI HX. intros Hb. apply (loc_addr_ext L gL' gr _ gL'_ext). cbn. exact (user_block_below X R U s HI HX b Hb). Qed.
  Lemma gL'_eN : ltac2:(tb__ "0|0|
S1SfS0S0A2S2cS5cS5fA2S14S0S0Va;Vlen;A4A3").
  Proof using . unfold crange, geN. cbn [fst snd loc_addr]. rewrite gL'_reg_new. f_equal. lia. Qed.
  Lemma gL'_blocks : ltac2:(tb__ "0|0|
S1S10SfS0S0A2A1S78S5cVs';A2S78VL;Vs;A2A3").
  Proof using HI HX Hmetas'. unfold blocks. rewrite g_ub. apply map_ext_in. intros b Hb. unfold addr_of. rewrite (gL'_ub b Hb). reflexivity. Qed.
  Lemma gL'_addr_of q : ltac2:(tb__ "0|0|
S6eS49Vq;A1S5dA2S1S0S81S5cVq;A2S81VL;Vq;A2A3F_;").
  Proof using . intros Hq. unfold addr_of. apply (loc_addr_ext L gL' gr _ gL'_ext). exact Hq. Qed.

  Theorem g_layout_ok : layout_ok gL' s'.
  Proof using HI HIR HL HSI HV HVX Ha_al Ha_ceil Ha_pos Hareas' Hctx Hfree Hlen Hregs'.
    pose proof HL as (A & B & Cc & D). pose proof ga_facts as (A1 & A2 & A3 & _). pose proof Hlen as [L1 _].
    split; [rewrite gL'_ctx; exact A|]. split.
    { intros k rg Hk Hl. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E.
      - apply Nat.eqb_eq in E. subst k. rewrite gL'_reg_new. exact Ha_al.
      - apply Nat.eqb_neq in E. unfold gL'. rewrite Lext_old by exact E. exact (B k rg Hk Hl). }
    assert (DISJ : forall e, In e (footprint s) -> ranges_disjoint (crange gL' e) (crange gL' geN) /\ ranges_disjoint (crange gL' geN) (crange gL' e)).
    { intros e He. rewrite (gL'_crange e He), gL'_eN. unfold ranges_disjoint, crange. cbn [fst snd].
      pose proof (D e He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd] in P1, P2. pose proof (g_fp_size e He) as SZ.
      destruct (Z_le_dec (loc_addr L (fst e) + snd e) a); [lia|].
      destruct (Z_le_dec (a + len) (loc_addr L (fst e))); [lia|]. exfalso.
      destruct (Z_le_dec (loc_addr L (fst e)) a).
      - apply (g_vs_footprint e a He); unfold PGSZ in *; lia.
      - apply (g_vs_footprint e (loc_addr L (fst e)) He); unfold PGSZ in *; lia. }
    rewrite g_fp, map_app. cbn [map]. split.
    - apply pairwise_insert with (v := []).
      + rewrite app_nil_r. rewrite (map_ext_in (crange gL') (crange L) (footprint s) gL'_crange). exact Cc.
      + intros y Hy. rewrite app_nil_r in Hy. apply in_map_iff in Hy as (e & <- & He). split; [apply (proj2 (DISJ e He)) | apply (proj1 (DISJ e He))].
    - intros rg Hrg. apply in_app_iff in Hrg as [Hrg|[<-|[]]].
      + rewrite (gL'_crange rg Hrg). exact (D rg Hrg).
      + rewrite gL'_eN. cbn [fst snd]. unfold PGSZ in *. lia.
  Qed.

  Hypothesis HMW : maps_wf vm.

  Lemma apart_of_pointwise lo1 n1 lo2 n2 : ltac2:(tb__ "0|3|
S9Z0M0Vn1;A2S9G0Vn2;A2S0S2S7Vlo2;R1A2S9R1S8Vlo2;Vn2;A2M1A2A2S3S2S7Vlo1;R2A2S9R2S8Vlo1;Vn1;A2M2A2A2A1F_;Fx;S4S7G2Vlo2;A2S7G1Vlo1;A2A2F_;F_;F_;").
  Proof using a len.
    intros H1 H2 H. destruct (Z_le_dec (lo1 + n1) lo2); [left; lia|]. destruct (Z_le_dec (lo2 + n2) lo1); [right; lia|]. exfalso.
    destruct (Z_le_dec lo1 lo2); [apply (H lo2); lia | apply (H lo1); lia].
  Qed.

  Lemma g_vs_region k rg : ltac2:(tb__ "0|3|
S1S1bS3cA1S2fVs;Vk;A2S1aS3cVrg;A2A3S1S12S4bVrg;A1S16A3S3aSfS83Q40A1M0G0A2S14G0G0S7aS2aVL;Vk;A2M1A1S7aS4aVrg;A1M2A1A4S70Vvm;A1A3S4S7S8Va;Vlen;A2G1A2S7S8G1G2A2Va;A2A2F_;F_;F_;").
  Proof using HV Ha_al Ha_ceil Ha_pos Hfree Hlen.
    intros Hk Hl Hin. pose proof HV as (_ & _ & _ & _ & _ & _ & W7 & W8 & _). pose proof ga_facts as (A1 & A2 & A3 & A4 & A5). pose proof Hlen as [LL1 _].
    pose proof (W7 k rg Hk Hl) as P7. pose proof (W8 k rg Hk Hl) as [P8 P9]. unfold PGSZ in *.
    apply apart_of_pointwise; [lia | lia |].
    intros x Hx. apply (g_vs_maps _ x Hin). cbn [fst snd]. unfold wz. rewrite !u64 by lia. exact Hx.
  Qed.
  Theorem g_vm_ok : ltac2:(tb__ "0|0|
S7cS5cVs';S5eA3").
  Proof using HI HMW HV Ha_al Ha_ceil Ha_pos Hareas' Hbrk' Hfree Hlen Hregs'.
    pose proof HV as (V1 & V2 & V3 & V5 & W5 & W6 & W7 & W8 & W9 & W10 & W11). pose proof ga_facts as (A1 & A2 & A3 & A4 & A5). pose proof Hlen as [LL1 _].
    unfold vm_ok. rewrite Hbrk'. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|   rewrite gL'_top; exact W11]]]]]]]]]].
    - intros k rg Hk Hl Hkd. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk as <-. rewrite gL'_reg_new. cbn [gvm' vm_maps grg rg_len]. left. reflexivity.
      + destruct (g_old_lt k rg Hk) as (_ & _ & ->). cbn [gvm' vm_maps]. right. exact (V1 k rg Hk Hl Hkd).
    - intros k rg Hk Hkd. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E; [injection Hk as <-; discriminate Hkd|].
      destruct (g_old_lt k rg Hk) as (_ & _ & ->). destruct (V2 k rg Hk Hkd) as (W1 & W2 & W3). cbn [gvm' vm_maps vm_noaccess].
      split; [right; exact W1|]. split; [|exact W3]. intros kk Hk1 Hk2 Hk3. exact (W2 kk Hk1 Hk2 Hk3).
    - pose proof (inv_areas HI) as (_&_&_&_&_&_& A7 &_).
      destruct (st_brk s) as [| |rr pages] eqn:Eb; cbn [gvm' vm_brk vm_start_brk vm_maps]; [| exact I |].
      + unfold gL'. cbn [Lext ly_brk0]. exact V3.
      + destruct V3 as (B1 & B2 & B3 & B4). destruct A7 as (_ & rg & Hrg & _).
        destruct (g_old_lt rr rg Hrg) as (_ & _ & ER). rewrite ER. unfold gL'. cbn [Lext ly_brk0].
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. intros kk Hkk. apply range_in_maps_cons. exact (B4 kk Hkk).
    - intros p k Hin. apply g_In_fp in Hin as [Hin|E].
      + unfold addr_of. pose proof (gL'_fp (LMem p, k) Hin) as EF. cbn [fst] in EF. rewrite EF. apply range_in_maps_cons. exact (V5 p k Hin).
      + unfold geN in E. injection E as -> ->. apply range_in_maps_head; cbn [fst snd]; rewrite ?gua, ?gun; unfold addr_of; cbn [loc_addr]; rewrite gL'_reg_new; lia.
    -   intros k rg off Hk Hkd Hoff. rewrite g_region_of in Hk. destruct (Nat.eqb k gr); [injection Hk as <-; discriminate Hkd | exact (W5 k rg off Hk Hkd Hoff)].
    -   intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite g_region_of in H1, H2.
      destruct (Nat.eqb r1 gr) eqn:E1; [injection H1 as <-; discriminate K1|]. destruct (Nat.eqb r2 gr) eqn:E2; [injection H2 as <-; discriminate K2|].
      destruct (g_old_lt r1 q1 H1) as (_ & _ & ->). destruct (g_old_lt r2 q2 H2) as (_ & _ & ->). exact (W6 r1 r2 q1 q2 Hne H1 H2 K1 K2).
    -   intros k rg Hk Hl. rewrite g_region_of in Hk. destruct (Nat.eqb k gr); [injection Hk as <-; cbn [grg rg_len]; lia | exact (W7 k rg Hk Hl)].
    -   intros k rg Hk Hl. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk as <-. cbn [grg rg_len]. rewrite gL'_reg_new, gL'_top. lia.
      + destruct (g_old_lt k rg Hk) as (_ & _ & ->). rewrite gL'_top. exact (W8 k rg Hk Hl).
    -   intros k rg q m Hk Hkd Hl Hin Hne. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E; [injection Hk as <-; discriminate Hkd|].
      destruct (g_old_lt k rg Hk) as (Hlt & _ & ->). apply g_In_fp in Hin as [Hin|Eq].
      + pose proof (gL'_fp (LMem q, m) Hin) as EF. cbn [fst] in EF. rewrite EF. exact (W9 k rg q m Hk Hkd Hl Hin Hne).
      + unfold geN in Eq. injection Eq as -> ->. cbn [loc_addr]. rewrite gL'_reg_new, Z.add_0_r.
        exact (g_vs_region k rg Hk Hl (proj1 (V2 k rg Hk Hkd))).
    -   intros rb p k rgk Hb Hk Hkd Hl. rewrite g_region_of in Hk.
      pose proof (inv_areas HI) as (_&_&_&_&_&_& A7 &_). rewrite Hb in A7. destruct A7 as (_ & rgb & Hrgb & _ & _ & Hp).
      destruct (g_old_lt rb rgb Hrgb) as (_ & _ & ER). rewrite ER.
      destruct (Nat.eqb k gr) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk as <-. rewrite gL'_reg_new. cbn [grg rg_len].
        rewrite Hb in V3. destruct V3 as (B1 & B2 & B3 & B4).
        apply (pages_apart (vm_maps vm) a len (ly_reg L rb) p); [| | unfold PGSZ in LL1; lia | exact Hp].
        * intros e He. pose proof (mwf_In_pos _ e HMW He) as P. pose proof (urange (fst e)).
          apply apart_of_pointwise; [unfold PGSZ in *; lia | exact P |]. intros x Hx. exact (g_vs_maps e x He Hx).
        * intros kk Hkk. rewrite B1. exact (B4 kk Hkk).
      + destruct (g_old_lt k rgk Hk) as (_ & _ & ->). exact (W10 rb p k rgk Hb Hk Hkd Hl).
  Qed.

  Theorem g_maps_wf : maps_wf gvm'.
  Proof using HMW Ha_al Ha_ceil Ha_pos Hfree Hlen.
    pose proof ga_facts as (A1 & A2 & A3 & A4 & A5). pose proof Hlen as [LL1 _]. unfold maps_wf, gvm'. cbn [vm_maps].
    apply mwf_cons; [exact HMW | cbn [snd]; rewrite gun; unfold PGSZ in LL1; lia |].
    intros e' He'. unfold wdisj. cbn [fst snd]. rewrite gua, gun.
    pose proof (mwf_In_pos _ e' HMW He') as P. pose proof (urange (fst e')).
    apply apart_of_pointwise; [unfold PGSZ in *; lia | exact P |]. intros x Hx. exact (g_vs_maps e' x He' Hx).
  Qed.

  Theorem g_vm_okX : vm_okX gL' s'.
  Proof using HVX Ha_al Ha_ceil Ha_pos Hlen Hregs'.
    pose proof HVX as (X1 & X2 & X3 & X4). pose proof ga_facts as (A1 & A2 & A3 & A4 & A5). pose proof Hlen as [LL1 _].
    split; [|split; [|split]].
    - intros k rg off Hk Hkd Hoff. rewrite g_region_of in Hk. destruct (Nat.eqb k gr); [injection Hk as <-; discriminate Hkd | exact (X1 k rg off Hk Hkd Hoff)].
    - intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite g_region_of in H1, H2.
      destruct (Nat.eqb r1 gr) eqn:E1; [injection H1 as <-; discriminate K1|]. destruct (Nat.eqb r2 gr) eqn:E2; [injection H2 as <-; discriminate K2|].
      destruct (g_old_lt r1 q1 H1) as (_ & _ & ->). destruct (g_old_lt r2 q2 H2) as (_ & _ & ->). exact (X2 r1 r2 q1 q2 Hne H1 H2 K1 K2).
    - intros k rg Hk Hl. rewrite g_region_of in Hk. destruct (Nat.eqb k gr); [injection Hk as <-; cbn [grg rg_len]; lia | exact (X3 k rg Hk Hl)].
    - intros k rg Hk Hl. rewrite g_region_of in Hk. destruct (Nat.eqb k gr) eqn:E.
      + apply Nat.eqb_eq in E. subst k. injection Hk as <-. cbn [grg rg_len]. rewrite gL'_reg_new, gL'_top. lia.
      + destruct (g_old_lt k rg Hk) as (_ & _ & ->). rewrite gL'_top. exact (X4 k rg Hk Hl).
  Qed.

  Theorem g_ledger : ltac2:(tb__ "0|1|
S2S7eVC;S5eA2S2S7dVC;S5eA2S1S10SfS83Q40A1M0G0A2A1S6fS5eA1S6fVvm;A1A3A2A2").
  Proof using HIR HLG HSI HV Ha_al Ha_ceil Ha_pos Hfree Hlen.
    pose proof ga_facts as (A1 & A2 & A3 & A4 & A5). pose proof Hlen as [LL1 _].
    split; [|split; [exact HIR | reflexivity]].
    intros e [<-|He]; [|exact (HLG e He)]. cbn [fst snd]. rewrite gua, gun. split; [exact A1|].
    split; [change (alloc_top gvm') with (alloc_top vm); rewrite <- (vm_ok_top L s vm HV); exact A2|].
    pose proof HSI as (_&_&_&_&_&_&_&_&_& [CX1 CX2] &_& IMG1 & IMG2).
    destruct (Z_le_dec (a + len) (mc_img_lo C)); [left; lia|]. destruct (Z_le_dec (mc_img_hi C) a); [right; lia|]. exfalso.
    destruct (Z_le_dec a (mc_img_lo C)).
    - apply (g_vs_image (mc_img_lo C)); unfold CTX_SIZE, PGSZ in *; lia.
    - apply (g_vs_image a); unfold PGSZ in *; lia.
  Qed.

  Lemma g_aptr : ltac2:(tb__ "0|0|
S1S0S45Vs';A1S45Vs;A1A3S1S3bS46Vs';A1S46Vs;A1A3S65Vs';A1F_;F_;").
  Proof using APTR Hareas' Hregs' a.
    intros E1 E2. unfold aptr_ok. rewrite Hareas', Hregs', E1, E2, length_app. cbn [length]. destruct APTR as [H|H]; [left; exact H | right; lia].
  Qed.

  Local Ltac ctx_offs := unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
    CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk,
    CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
  Lemma g_cell_stable c : ltac2:(tb__ "0|2|
S3aS20Vc;S11S20S24Vs;A1S6dVs;A1A3A3S2S1S0S21S5cS27Vc;A1M0A2S21VL;G0A2A3S1S0S2bS5cS35Vc;A1M1A2S2bVL;G1A2A3A2F_;").
  Proof using APTR HI HX Ha_pos len.
    intros Hin. destruct APTR as [[E1 E2]|LT].
    - apply (cell_stable X R U s HI HX L gL' c gL'_ext Hin). intros _ _. exact E1.
    - destruct (loc_eq_dec (mc_loc c) (LCtx CTX_avail_meta_areas)) as [E|NE].
      + split; [rewrite E; cbn [loc_addr]; reflexivity|].
        assert (HV' : val_below gr (mc_val c)).
        { apply in_app_iff in Hin as [Hin|Hin].
          - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin].
            + unfold ctx_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
              * cbn [In] in Hin.
                destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc] in E;
                  try (injection E as E'; ctx_offs; lia).
                cbn [mc_val]. destruct (match st_areas s with [] => true | _ => false end && (st_avail_meta_area_count s =? 0))%bool; [exact I|]. exact LT.
              * exfalso. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]]; apply in_map_iff in Hin as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc] in E; injection E; ctx_offs; lia.
            + exfalso. destruct (old_noctx_loc X R U s HI HX c (or_introl Hin)) as [_ (p & Hp)]. rewrite Hp in E. discriminate E.
          - exfalso. destruct (old_noctx_loc X R U s HI HX c (or_intror Hin)) as [_ (p & Hp)]. rewrite Hp in E. discriminate E. }
        exact (sval_num_ext L gL' gr _ gL'_ext HV').
      + apply (cell_stable X R U s HI HX L gL' c gL'_ext Hin). intros E0. exfalso. exact (NE E0).
  Qed.
End Generic.

Section MapGrow.
  Variables (C : mconsts) (s : astate) (n : Z) (L : layout) (vm : VmMaps) (a : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S30S13S3bA1S1cSfS3bS0A2A1S37Vs;A4").
  Hypothesis Hn : direct_case n.
  Hypothesis HL : layout_ok L s.
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S1S0S2eVL;A1S7bVC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
S7cVL;Vs;Vvm;A3").
  Hypothesis HVX : vm_okX L s.
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis HMW : maps_wf vm.
  Hypothesis APTR : aptr_ok s.
  Hypothesis Ha_al : a mod PGSZ = 0.
  Hypothesis Ha_pos : 0 < a.
  Hypothesis Ha_ceil : ltac2:(tb__ "0|0|
S7S8Va;S88Vn;A1A2S79VL;A1A2").
  Hypothesis Hfree : ltac2:(tb__ "0|4|
SfS83Q40M0A1M1G1A2M2S3aG2R1S11G2S6fVvm;A1S70Vvm;A1A3A3S0S2S7S84G0S15G1G1R3A3A2M3R1A2S9R1S8G3S84G0S19G1G1R3A3A2A2A2A2S3S2S7Va;R2A2S9R2S8Va;S88Vn;A1A2A2A2A1F_;Fx;F_;Fe;").

  Definition r : nat := length (st_regions s).
  Definition len : Z := md_len n.
  Definition L' : layout := ltac2:(tb__ "0|0|
S85VL;S56Va;A3").
  Definition s2 : astate := md_s2 s n.
  Definition rgN : region := md_rg n.
  Definition vm1 : VmMaps := ltac2:(tb__ "0|1|
S71S6fVvm;A1S18SfS83Q40A1M0G0A2S14G0G0S7aVa;A1S7aS51A1A4S70Vvm;A1A3S76Vvm;A1S77Vvm;A1S72Vvm;A1S74Vvm;A1S75Vvm;A1S73Vvm;A1A8").
  Definition eN : loc * Z := ltac2:(tb__ "0|0|
S14S1fS0S29S43S56Z0A2A1S51A4").

  Lemma HX0 : xraw [] s. Proof using . intros q []. Qed.
  Lemma len_facts : ltac2:(tb__ "0|0|
S2S7SeZ20S3dA2S51A2S2S1S0ScS51S3dA2Z0A3S7S51SbZ2Z3fA2A2A2A2").
  Proof using Ha_pos Hn. pose proof (md_len_facts n Hn) as (L1 & L2 & L3 & L4 & L5). unfold len. unfold PGSZ in *. lia. Qed.
  Lemma Hlen' : ltac2:(tb__ "0|0|
S2S7S3dS51A2S1S0ScS51S3dA2Z0A3A2"). Proof using Ha_pos Hn. pose proof len_facts. unfold PGSZ in *. lia. Qed.
  Lemma s2_regions : ltac2:(tb__ "0|0|
S1S10S3cA1S3eS52A1S11S3cS3eVs;A1S18S3cS44S40S51S13S0A1S16A4S13S3cA1A3A3A3"). Proof using HI. exact (proj1 (proj2 (proj2 (s2_shape s n HI)))). Qed.
  Lemma s2_areas : ltac2:(tb__ "0|0|
S1S10S3bA1S3fS52A1S3fVs;A1A3"). Proof using HI. exact (proj1 (proj2 (s2_shape s n HI))). Qed.
  Lemma s2_metas : ltac2:(tb__ "0|0|
S1S10SfS3bS48A2A1S42S52A1S42Vs;A1A3"). Proof using HI. exact (proj1 (s2_shape s n HI)). Qed.
  Lemma s2_brk : ltac2:(tb__ "0|0|
S1S47S41S52A1S41Vs;A1A3"). Proof using HI. pose proof (s2_shape s n HI) as (_&_&_&_&_&_&_&_&_&_&B&_). exact B. Qed.

  Local Ltac inst lem := pose proof s2_regions; pose proof s2_areas; pose proof s2_metas; pose proof s2_brk; pose proof Hlen'; pose proof HX0;
                         eapply lem; eassumption.

  Lemma a_facts : ltac2:(tb__ "0|3|
S2S7S3dVa;A2S2S7S8Va;S51A2S79VL;A1M0A2S2S7G0Z7fffff800000A2S2S2S7Z0M1Va;A2S9Va;SbZ2Z40A2M2A2A2S2S7G1S51A2S9S51G2A2A2A2A2A2A2").
  Proof using HI Ha_al Ha_ceil Ha_pos Hn. inst ga_facts. Qed.
  Lemma fp_s2 : ltac2:(tb__ "0|1|
S1S10SfS1fS0A2M0A1S23S52A1S11G0S23Vs;A1S18G0S55S13G0A1A3A3A3"). Proof using HI Ha_pos Hn. inst g_fp. Qed.
  Lemma In_fp_s2 e : ltac2:(tb__ "0|1|
S5S3aSfS1fS0A2M0Ve;S23S52A1A3S4S3aG0Ve;S23Vs;A1A3S1G0Ve;S55A3A2A2"). Proof using HI Ha_pos Hn. inst g_In_fp. Qed.
  Lemma ub_s2 : ltac2:(tb__ "0|0|
S1S10SfS3bS0A2A1S28S52A1S28Vs;A1A3"). Proof using HI Ha_pos Hn. inst g_ub. Qed.
  Lemma footers_s2 : ltac2:(tb__ "0|0|
S1S10S20A1S6dS52A1S6dVs;A1A3"). Proof using HI Ha_pos Hn. inst g_footers. Qed.
  Lemma grant_vs_image x : ltac2:(tb__ "0|0|
S2S7S80VC;A1Vx;A2S9Vx;S7fVC;A1A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;S51A2A2A2A1F_;"). Proof using HI HIR Ha_pos Hfree Hn. inst g_vs_image. Qed.
  Lemma grant_vs_footprint e x : ltac2:(tb__ "0|1|
S3aSfS1fS0A2Ve;S23Vs;A1A3S2S7S21VL;S15S1fS0Ve;A3A2M0Vx;A2S9Vx;S8G0S19S1fS0Ve;A3A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;S51A2A2A2A1F_;F_;"). Proof using HI HIR HSI HV Ha_al Ha_pos Hctx Hfree Hn. inst g_vs_footprint. Qed.
  Lemma grant_vs_owned x : ltac2:(tb__ "0|0|
S33VL;Vs;Vx;A3S2S3S2S7Va;Vx;A2S9Vx;S8Va;S51A2A2A2A1S2S9Z0Vx;A2S9Vx;SbZ2Z3fA2A2A2A2F_;"). Proof using HI HIR HL HSI HV Ha_al Ha_pos Hctx Hfree Hn. inst g_vs_owned. Qed.
  Lemma grant_vs_block b k x : ltac2:(tb__ "0|0|
S3aSfS0S0A2S14S0S0Vb;Vk;A4S78VL;Vs;A2A3S2S7Vb;Vx;A2S9Vx;S8Vb;Vk;A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;S51A2A2A2A1F_;F_;"). Proof using HI HIR HSI HV Ha_al Ha_pos Hctx Hfree Hn. inst g_vs_block. Qed.
  Lemma L'_reg_new : ltac2:(tb__ "0|0|
S1S0S2aS53S56A2Va;A3"). Proof using . apply Lext_reg. Qed.
  Lemma L'_top : ltac2:(tb__ "0|0|
S1S0S79S53A1S79VL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_fp e : ltac2:(tb__ "0|1|
S3aSfS1fS0A2Ve;S23Vs;A1A3S1S0S21S53S15S1fS0Ve;A3M0A2S21VL;G0A2A3F_;"). Proof using HI Ha_pos Hn. inst gL'_fp. Qed.
  Lemma L'_ub b : ltac2:(tb__ "0|1|
S3aSfS3bS0A2Vb;S28Vs;A1A3S1S0S21S53S29S15S3bS0Vb;A3A1M0A2S21VL;G0A2A3F_;"). Proof using HI Ha_pos Hn. inst gL'_ub. Qed.
  Lemma L'_eN : ltac2:(tb__ "0|0|
S1SfS0S0A2S2cS53S55A2S14S0S0Va;S51A4A3"). Proof using HI Ha_pos Hn. inst gL'_eN. Qed.
  Lemma L'_blocks : ltac2:(tb__ "0|0|
S1S10SfS0S0A2A1S78S53S52A2S78VL;Vs;A2A3"). Proof using HI Ha_pos Hn. inst gL'_blocks. Qed.
  Theorem layout_ok_s2 : layout_ok L' s2. Proof using HI HIR HL HSI HV HVX Ha_al Ha_ceil Ha_pos Hctx Hfree Hn. inst g_layout_ok. Qed.
  Theorem vm_ok_s2 : vm_ok L' s2 vm1. Proof using HI HMW HV Ha_al Ha_ceil Ha_pos Hfree Hn. inst g_vm_ok. Qed.
  Theorem vm_okX_s2 : vm_okX L' s2. Proof using HI HVX Ha_al Ha_ceil Ha_pos Hn. inst g_vm_okX. Qed.
  Theorem maps_wf_s2 : maps_wf vm1. Proof using HI HMW Ha_al Ha_ceil Ha_pos Hfree Hn. inst g_maps_wf. Qed.
  Theorem ledger_s2 : ltac2:(tb__ "0|1|
S2S7eVC;S57A2S2S7dVC;S57A2S1S10SfS83Q40A1M0G0A2A1S6fS57A1S6fVvm;A1A3A2A2"). Proof using HI HIR HLG HSI HV Ha_al Ha_ceil Ha_pos Hfree Hn. inst g_ledger. Qed.
  Lemma aptr_s2 : aptr_ok s2.
  Proof using APTR HI Ha_pos Hn.
    pose proof (s2_shape s n HI) as (_ & Far & Frg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fac & _ & _ & _ & Fap).
    inst g_aptr.
  Qed.
  Lemma bounded_s2 : ltac2:(tb__ "0|0|
S34Vs;A1S34S52A1F_;").
  Proof using HI a.
    intros (B1 & B2 & B3 & B4). pose proof (s2_shape s n HI) as (Fm & Far & Frg & _ & _ & _ & Fus & _ & _ & _ & _ & _ & _ & _ & Fac & Fsh & _ & _ & Fap).
    unfold bounded, usage_of in *. unfold s2. rewrite Far, Fsh, Fus, Fac, Fap, Frg, length_app. cbn [length].
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. destruct B4 as [H|H]; [left; exact H | right; lia].
  Qed.
  Lemma cell_stable_s c : ltac2:(tb__ "0|2|
S3aS20Vc;S11S20S24Vs;A1S6dVs;A1A3A3S2S1S0S21S53S27Vc;A1M0A2S21VL;G0A2A3S1S0S2bS53S35Vc;A1M1A2S2bVL;G1A2A3A2F_;").
  Proof using APTR HI Ha_pos Hn. inst g_cell_stable. Qed.

  Definition new_seq : Z := ltac2:(tb__ "0|2|
S12S0L_;SdS50Vs;A1M0ZffA2Z1M1S8G0G1A2X12x2").
  Definition wrapb : bool := st_seq s =? 255.
  Definition C_seq : mcell := ltac2:(tb__ "0|0|
S31S22S25A1U1S32S5bA1A3").
  Definition C_useq (k : nat) : mcell := ltac2:(tb__ "0|0|
S31S22S8S26SaVk;A1A2A1U1S32Z0A1A3").
  Definition chg (c : mcell) : Prop := ltac2:(tb__ "0|0|
S4S1S20Vc;S5aA3S2S1S12S54S16A3S6S17S17S2S6eR1U20A2S1S20Vc;S58R1A1A3A2Lk;A2A2A2").

  Local Ltac ctx_offs := unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
    CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk,
    CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.

  Lemma ctx_cells_s2 c : ltac2:(tb__ "0|1|
S3aS20Vc;S2dS52A1A3S4S59Vc;A1S2S3aS20Vc;S2dVs;A1A3S2S1S12S54S16A3S17S6eR1U20A2S3S1S1fS27Vc;A1M0S22S8S26SaR2A1A2A1A3A1F_;Fk;F_;S3S1S1fG0S22S25A1A3A1A2A2A2F_;").
  Proof using HI Ha_pos.
    pose proof (s2_shape s n HI) as (Fm & Far & Frg & Fctr & Fini & Fact & Fus & Fsq & Fusq & Fbn & Fbrk & Fhd & Fav & Favc & Fac & Fsh & Fah & Fat & Fap).
    intros Hin. unfold ctx_cells in Hin. unfold s2 in Hin.
    rewrite ?Fm, ?Far, ?Fctr, ?Fini, ?Fact, ?Fus, ?Fsq, ?Fusq, ?Fbn, ?Fbrk, ?Fhd, ?Fav, ?Favc, ?Fac, ?Fsh, ?Fah, ?Fat, ?Fap in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        try (left; left; reflexivity);
        (right; split; [unfold ctx_cells; apply in_app_iff; left; cbn [In]; tauto
                      | split; [intros _ k Hk E | intros E]; cbn [mc_loc] in E; injection E; ctx_offs; lia]).
    - assert (CASES : forall l1 l2 l3 l4 : list mcell, In c (l1 ++ l2 ++ l3 ++ l4) -> In c l1 \/ In c l2 \/ In c l3 \/ In c l4).
      { intros l1 l2 l3 l4 H. rewrite !in_app_iff in H. tauto. }
      apply CASES in Hin as [Hin|[Hin|[Hin|Hin]]]; apply in_map_iff in Hin as (k & <- & Hk); apply in_seq in Hk.
      + right. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
        split; [intros _ kk Hkk E | intros E]; cbn [mc_loc] in E; injection E; ctx_offs; lia.
      + right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
        split; [intros _ kk Hkk E | intros E]; cbn [mc_loc] in E; injection E; ctx_offs; lia.
      + unfold chg, wrapb, C_useq. destruct (st_seq s =? 255) eqn:Ew.
        * left. right. split; [reflexivity|]. exists k. split; [lia|]. rewrite nth_repeat. reflexivity.
        * right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
          split; [intros E0; discriminate E0 | intros E; cbn [mc_loc] in E; injection E; ctx_offs; lia].
      + right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
        split; [intros _ kk Hkk E | intros E]; cbn [mc_loc] in E; injection E; ctx_offs; lia.
  Qed.

  Lemma image_s2 c : ltac2:(tb__ "0|1|
S3aS20Vc;S11S20S24S52A1S6dS52A1A3A3S4S59Vc;A1S2S3aS20Vc;S11S20S24Vs;A1S6dVs;A1A3A3S2S1S12S54S16A3S17S6eR1U20A2S3S1S1fS27Vc;A1M0S22S8S26SaR2A1A2A1A3A1F_;Fk;F_;S3S1S1fG0S22S25A1A3A1A2A2A2F_;").
  Proof using HI Ha_pos Hn.
    intros Hin. rewrite footers_s2 in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin]; [destruct (ctx_cells_s2 c Hin) as [X|(Y1 & Y2 & Y3)]; [left; exact X | right; split; [apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Y1 | auto]]|].
      right. unfold used_metas in Hin. rewrite s2_areas, s2_metas in Hin.
      assert (OLD : In c (areas_cells s (st_areas s) ++ flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s))).
      { unfold used_metas. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left|right; exact Hin].
        rewrite (areas_cells_metas s s2 (st_areas s) (eq_sym s2_metas)). exact Hin. }
      destruct (old_noctx_loc [] None U0 s HI HX0 c (or_introl OLD)) as [_ (p & Hp)].
      split; [apply in_app_iff; left; unfold image; apply in_app_iff; right; exact OLD|]. rewrite Hp. split; [intros _ k _ E; discriminate E | intros E; discriminate E].
    - right. destruct (old_noctx_loc [] None U0 s HI HX0 c (or_intror Hin)) as [_ (p & Hp)].
      split; [apply in_app_iff; right; exact Hin|]. rewrite Hp. split; [intros _ k _ E; discriminate E | intros E; discriminate E].
  Qed.

  Lemma C_seq_In : In C_seq (image s2).
  Proof using HI.
    pose proof (s2_shape s n HI) as (_ & _ & _ & _ & _ & _ & _ & Fsq & _).
    unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. unfold C_seq, new_seq. unfold s2 in Fsq |- *. rewrite <- Fsq. cbn [In]. tauto.
  Qed.
  Lemma C_useq_In k : ltac2:(tb__ "0|0|
S1S12S54S16A3S6eVk;U20A2S3aS20S58Vk;A1S24S52A1A3F_;F_;").
  Proof using HI a.
    intros Hw Hk. pose proof (s2_shape s n HI) as (_ & _ & _ & _ & _ & _ & _ & _ & Fusq & _).
    unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists k. split; [|apply in_seq; lia]. unfold C_useq. unfold s2 in Fusq |- *. rewrite Fusq. unfold wrapb in Hw. rewrite Hw. rewrite nth_repeat. reflexivity.
  Qed.

  Lemma seq_addr : ltac2:(tb__ "0|2|
S2S1S0S21S53S22S25A1A2S8S7bVC;A1M0S25A2A3S17S1S0S21S53S22S8S26SaR1A1M1A2A1A2S8S8G0S26A2G1A2A3Fk;A2").
  Proof using Hctx. cbn [loc_addr L' Lext ly_ctx]. rewrite Hctx. split; [reflexivity | intros k; lia]. Qed.
End MapGrow.

Local Ltac ctx_offs2 := unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
    CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk,
    CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces, CTX_SIZE in *.

Lemma ctx_cells_at_ctr st c o : ltac2:(tb__ "0|0|
S3aS20Vc;S2dVst;A1A3S1S1fS27Vc;A1S22Vo;A1A3S9Vo;Z10A2S9ZcS8Vo;SaS36Vc;A1A1A2A2S1S20Vc;S31S22S38A1U4S32S4fVst;A1A1A3A3F_;F_;F_;F_;").
Proof.
  intros Hin Ho O1 O2. unfold ctx_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; try lia; reflexivity.
  - exfalso. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]]; apply in_map_iff in Hin as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; lia.
Qed.
Lemma ctx_cells_at_seq st c o : ltac2:(tb__ "0|1|
S3aS20Vc;S2dVst;A1A3S1S1fS27Vc;A1M0S22Vo;A1A3S9Vo;Z391A2S9Z390S8Vo;SaS36Vc;A1A1A2A2S1S1fG0S22S25A1A3F_;F_;F_;F_;").
Proof.
  intros Hin Ho O1 O2. rewrite Ho. unfold ctx_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; try lia; reflexivity.
  - exfalso. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]]; apply in_map_iff in Hin as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; lia.
Qed.
Lemma ctx_cells_at_useq st c o : ltac2:(tb__ "0|1|
S3aS20Vc;S2dVst;A1A3S1S1fS27Vc;A1M0S22Vo;A1A3S9Vo;Z370A2S9Z350S8Vo;SaS36Vc;A1A1A2A2S6S17S17S2S6eR1U20A2S1S1fG0S22S8S26SaR1A1A2A1A3A2Lk;A2F_;F_;F_;F_;").
Proof.
  intros Hin Ho O1 O2. rewrite Ho. unfold ctx_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exfalso. cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; lia.
  - rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]]; apply in_map_iff in Hin as (k & <- & Hk); apply in_seq in Hk; cbn [mc_loc mc_w] in Ho, O2; injection Ho as <-; ctx_offs2; try lia.
    exists k. split; [lia | reflexivity].
Qed.

Record mg_pre (C : mconsts) (s : astate) (n : Z) (L : layout) (vm : VmMaps) (a : Z) : Prop := MG {
  mg_I : Inv [] None U0 s;
  mg_n : direct_case n;
  mg_L : layout_ok L s;
  mg_ctx : ly_ctx L = mc_ctx C;
  mg_SI : statics_in_image C;
  mg_V : vm_ok L s vm;
  mg_VX : vm_okX L s;
  mg_LG : ledger_ok C vm;
  mg_IR : img_reserved C vm;
  mg_MW : maps_wf vm;
  mg_aptr : aptr_ok s;
  mg_bounded : bounded s;
  mg_al : a mod PGSZ = 0;
  mg_pos : 0 < a;
  mg_ceil : a + md_len n <= topL L;
  mg_free : forall e, In e (vm_reserved vm ++ vm_maps vm) ->
    forall x, bv_unsigned (fst e) <= x < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (a <= x < a + md_len n) }.

Section Bundled.
  Variables (C : mconsts) (s : astate) (n : Z) (L : layout) (vm : VmMaps) (a : Z).
  Hypothesis HP : ltac2:(tb__ "0|0|
S6bVC;Vs;Vn;VL;Vvm;Va;A6").
  Local Ltac go lem := destruct HP; eapply lem; eassumption.

  Lemma mgI2 : ltac2:(tb__ "0|0|
S30S13S3bA1S1cSfS3bS0A2A1S37S61Vs;Vn;A2A4"). Proof using HP. destruct HP; apply Inv_s2; assumption. Qed.
  Lemma mgX2 : ltac2:(tb__ "0|0|
S8cS13S3bA1S61Vs;Vn;A2A2"). Proof using . intros q []. Qed.
  Lemma mgB2 : ltac2:(tb__ "0|0|
S34S61Vs;Vn;A2A1"). Proof using HP. go bounded_s2. Qed.
  Lemma mgA2 : ltac2:(tb__ "0|0|
S65S61Vs;Vn;A2A1"). Proof using HP. go aptr_s2. Qed.
  Lemma mgLay : ltac2:(tb__ "0|0|
S39S62Vs;VL;Va;A3S61Vs;Vn;A2A2"). Proof using HP. go layout_ok_s2. Qed.
  Lemma mgVm : ltac2:(tb__ "0|0|
S7cS62Vs;VL;Va;A3S61Vs;Vn;A2S64Vn;Vvm;Va;A3A3"). Proof using HP. go vm_ok_s2. Qed.
  Lemma mgVmX : ltac2:(tb__ "0|0|
S86S62Vs;VL;Va;A3S61Vs;Vn;A2A2"). Proof using HP. go vm_okX_s2. Qed.
  Lemma mgLedger : ltac2:(tb__ "0|2|
S2S7eVC;S64Vn;Vvm;Va;A3M0A2S2S7dVC;G0A2S1S10SfS83Q40A1M1G1A2A1S6fG0A1S6fVvm;A1A3A2A2"). Proof using HP. go ledger_s2. Qed.
  Lemma mgMW : ltac2:(tb__ "0|0|
S82S64Vn;Vvm;Va;A3A1"). Proof using HP. go maps_wf_s2. Qed.
  Lemma mgFp e : ltac2:(tb__ "0|1|
S5S3aSfS1fS0A2M0Ve;S23S61Vs;Vn;A2A1A3S4S3aG0Ve;S23Vs;A1A3S1G0Ve;S66Vs;Vn;A2A3A2A2"). Proof using HP. go In_fp_s2. Qed.
  Lemma mgLfp e : ltac2:(tb__ "0|1|
S3aSfS1fS0A2Ve;S23Vs;A1A3S1S0S21S62Vs;VL;Va;A3S15S1fS0Ve;A3M0A2S21VL;G0A2A3F_;"). Proof using HP. go L'_fp. Qed.
  Lemma mgLub b : ltac2:(tb__ "0|1|
S3aSfS3bS0A2Vb;S28Vs;A1A3S1S0S21S62Vs;VL;Va;A3S29S15S3bS0Vb;A3A1M0A2S21VL;G0A2A3F_;"). Proof using HP. go L'_ub. Qed.
  Lemma mgUb : ltac2:(tb__ "0|0|
S1S10SfS3bS0A2A1S28S61Vs;Vn;A2A1S28Vs;A1A3"). Proof using HP. go ub_s2. Qed.
  Lemma mgFooters : ltac2:(tb__ "0|0|
S1S10S20A1S6dS61Vs;Vn;A2A1S6dVs;A1A3"). Proof using HP. go footers_s2. Qed.
  Lemma mgBlocks : ltac2:(tb__ "0|0|
S1S10SfS0S0A2A1S78S62Vs;VL;Va;A3S61Vs;Vn;A2A2S78VL;Vs;A2A3"). Proof using HP. go L'_blocks. Qed.
  Lemma mgImage c : ltac2:(tb__ "0|2|
S3aS20Vc;S11S20S24S61Vs;Vn;A2M0A1S6dG0A1A3A3S4S6aVs;Vc;A2S2S3aS20Vc;S11S20S24Vs;A1S6dVs;A1A3A3S2S1S12S67Vs;A1S16A3S17S6eR1U20A2S3S1S1fS27Vc;A1M1S22S8S26SaR2A1A2A1A3A1F_;Fk;F_;S3S1S1fG1S22S25A1A3A1A2A2A2F_;").
  Proof using HP. go image_s2. Qed.
  Lemma mgStable c : ltac2:(tb__ "0|3|
S3aS20Vc;S11S20S24Vs;A1S6dVs;A1A3A3S2S1S0S21S62Vs;VL;Va;A3M0S27Vc;A1M1A2S21VL;G1A2A3S1S0S2bG0S35Vc;A1M2A2S2bVL;G2A2A3A2F_;").
  Proof using HP. go cell_stable_s. Qed.
  Lemma mgSeqIn : ltac2:(tb__ "0|0|
S3aS20S68Vs;A1S24S61Vs;Vn;A2A1A3"). Proof using HP. go C_seq_In. Qed.
  Lemma mgUseqIn k : ltac2:(tb__ "0|0|
S1S12S67Vs;A1S16A3S6eVk;U20A2S3aS20S69Vk;A1S24S61Vs;Vn;A2A1A3F_;F_;"). Proof using HP. destruct HP; eapply (C_useq_In s n a); eassumption. Qed.
  Lemma mgOwned x : ltac2:(tb__ "0|0|
S33VL;Vs;Vx;A3S2S3S2S7Va;Vx;A2S9Vx;S8Va;S63Vn;A1A2A2A2A1S2S9Z0Vx;A2S9Vx;SbZ2Z3fA2A2A2A2F_;"). Proof using HP. go grant_vs_owned. Qed.
  Lemma mgBlock b k x : ltac2:(tb__ "0|0|
S3aSfS0S0A2S14S0S0Vb;Vk;A4S78VL;Vs;A2A3S2S7Vb;Vx;A2S9Vx;S8Vb;Vk;A2A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;S63Vn;A1A2A2A2A1F_;F_;"). Proof using HP. go grant_vs_block. Qed.
  Lemma mgImg x : ltac2:(tb__ "0|0|
S2S7S80VC;A1Vx;A2S9Vx;S7fVC;A1A2A2S3S2S7Va;Vx;A2S9Vx;S8Va;S63Vn;A1A2A2A2A1F_;"). Proof using HP. go grant_vs_image. Qed.
  Lemma mgSeqAddr : ltac2:(tb__ "0|3|
S2S1S0S21S62Vs;VL;Va;A3M0S22S25A1A2S8S7bVC;A1M1S25A2A3S17S1S0S21G0S22S8S26SaR1A1M2A2A1A2S8S8G1S26A2G2A2A3Fk;A2").
  Proof using HP. go seq_addr. Qed.
  Lemma mgA : ltac2:(tb__ "0|4|
S2S7S3dVa;A2S2S7S8Va;S63Vn;A1M0A2S79VL;A1M1A2S2S7G1Z7fffff800000A2S2S2S7Z0M2Va;A2S9Va;SbZ2Z40A2M3A2A2S2S7G2G0A2S9G0G3A2A2A2A2A2A2"). Proof using HP. go a_facts. Qed.
  Lemma mgLeN : ltac2:(tb__ "0|0|
S1SfS0S0A2S2cS62Vs;VL;Va;A3S66Vs;Vn;A2A2S14S0S0Va;S63Vn;A1A4A3"). Proof using . unfold crange, eN. cbn [fst snd loc_addr]. rewrite (L'_reg_new s L a). f_equal. lia. Qed.
  Lemma mgLnew : ltac2:(tb__ "0|0|
S1S0S2aS62Vs;VL;Va;A3S6cVs;A1A2Va;A3"). Proof using . apply L'_reg_new. Qed.
  Lemma mgLctx : ltac2:(tb__ "0|0|
S1S0S2eS62Vs;VL;Va;A3A1S7bVC;A1A3"). Proof using HP. destruct HP. cbn. assumption. Qed.
End Bundled.
