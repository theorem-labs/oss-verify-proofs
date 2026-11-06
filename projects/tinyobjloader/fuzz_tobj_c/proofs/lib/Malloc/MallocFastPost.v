(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "eqb"; "pow"; "to_nat"; "mul"; "leb"; "even"; "div"; "land"; "ltb"; "of_nat"; "testbit"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "mslot"; "padd"; "am_avail"; "bind"; "frame"; "ameta"; "IB"; "MUsed"; "nth_slot"; "kreq"; "UNIT"; "ret"; "st_active"; "usage_of"; "FUser"; "MMAP_THRESHOLD"; "region"; "size_to_class"; "ss_fr"; "M"; "am_freed"; "am_last"; "am_mem"; "fkind"; "fr_kind"; "malloc"; "slot_start"; "slotst"; "ss_hdr"; "AREA_HDR"; "PGSZ"; "am_set_avail"; "bit"; "class_size"; "get"; "getm"; "mkSlot"; "mlookup"; "prid"; "setm"; "st_metas"; "FModel"; "HActive"; "KJunk"; "METAS_PER_AREA"; "META_SIZE"; "NEST_FUEL"; "RkMap"; "SP"; "alloc_slot"; "am_next"; "am_prev"; "am_sc"; "am_slots"; "ctz32"; "enframe"; "fail"; "get_head"; "lowbit"; "mkFrame"; "osptr_eqb"; "rg_kind"; "rkind"; "size_overflows"; "st_areas"; "st_mmap_counter"; "upd_slot"; "@Corelib.Init.Datatypes"; "option"; "bool"; "prod"; "Some"; "pair"; "true"; "nil"; "None"; "app"; "cons"; "andb"; "fst"; "list"; "snd"; "unit"; "false"; "length"; "nat"; "negb"; "tt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "yields"; "MCell"; "VZ"; "cell_range"; "image"; "MT"; "loc"; "mc_w"; "cell_holds"; "loc_addr"; "mc_loc"; "mc_val"; "usedX"; "META_avail"; "VLo5"; "alloc_owned"; "footprint"; "optr"; "ranges_disjoint"; "sval"; "user_blocks"; "META_bits"; "META_freed"; "META_mem"; "META_next"; "META_prev"; "VP"; "crange"; "fold_off"; "group_extent"; "hdr_byte3"; "hdr_off16"; "le_byte"; "meta_bits"; "range_incl"; "region_of"; "sval_num"; "used_metas"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.Gap"; "f_idx"; "f_s'"; "f_am2"; "f_bv1"; "f_st"; "f_e"; "f_zg"; "f_fr"; "f_newcells"; "f_off"; "in_zone"; "f_avoids"; "f_bv0"; "f_footcells"; "f_frcells"; "f_hdrcells"; "f_rv1"; "f_zm"; "in_av"; "f_Cavail"; "f_rv0"; "f_p"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.Post"; "mf_idx"; "mf_off"; "mf_slack"; "mf_stride"; "mf_ctr"; "mf_am1"; "mf_am2"; "mf_first"; "mf_frame"; "mf_hdr"; "mf_off0"; "mf_reserved"; "mf_rsv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "mf_ptr"; "loop_case"; "mf_first"; "mf_hdr"; "mf_stride"; "mf_post"; "mf_trace"; "coarse_case"; "fast_case"; "malloc_loop"; "mf_am2"; "mf_frame"; "mf_idx"; "mf_off"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "frame_footer_cells"; "slot_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "wz"; "mc_img_hi"; "mc_img_lo"; "statics_ok"; "topL"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv"; "mkMA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones"; "zone_range"; "own_hdr"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocWfSlot MallocWfMalloc MallocWfArith MallocLayout MallocFooter MallocFooterLemmas NestTier MallocIface MallocLaws MallocCallocLemmas FreeQuickModel Zones ImageUpd FpLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition malloc_class (s : astate) (n : Z) : Z := ltac2:(tb__ "0|6|
S29Vn;A1S0SaeS5bS16A1M0ScR1A1S24Vs;A1M1S62S16A1M2A4G0S5cS0L_;M3S65S65S65S65S65S54R1G2A2SeZ4R2A2A2S12R2Z20A2A2S6dSaR2Z6A2A1A2SfR2A1A2SaS25Vs;R2A2Z0M4A2A2S25Vs;S7R2Z1M5A2A2S0G0S5cLx;SaeG0ScS7R3G5A2A1G1G2A4S16S5bS18A1S5cLx;S3dS40Vs;A1R1A2S18S18S5cLm;R1G0G0S60Lnext;Lprev;S60S1dS65SaS1aR1A1G4A2SaS2cR1A1G4A2A2Lam;X18x3Lm;S60X5bx2Lh;S60X5bx2S5cS5cS0Lhead_full;R1S7R2Z3A2R2X5cx2S0G3SeR1ZcA2S7R5G5A2R5X5cx2Tu;Thead_full;Tu;R2X5cx2Tg0;Tsc0;").

Definition malloc_loop (n : Z) : M (option sptr) := ltac2:(tb__ "0|a|
S1bS17S5bS16A1M0S3aS17SbcR1Vn;A2S0SaeG0ScR1A1S24R2A1S62S16A1M1A4G0S1bS5bS5dS16S0A2M2A1M3G0G0S2bG3A1M4Lg;R1S16S1bS1dG3S3bR1A1S1dS5cG4L_;M5SaS1aR1A1M6Z0M7A2S23G3S62G2A1A2M8S52G6A1S0S1bS69G3S3fR3S37S9S1aR2A1R1A2R2A2A2S69S23G3S5eG2S5fS16S0R4S4eR2A1A4A2A2L_;A4Tfirst;X5cx2Lam;A4Lgm;G8X5bx2G3S1bG3G0G3G4Lr;R1G2S23G3S5eG2R1A2A2Lgi;S1bS0G3S49S46R3Vn;A3S0G5S12R1G7A2G8S1bG0G3S51S42R4A1A1G0G0G4Lhd;R1S16S23G3S5eG2S5fS16S0R1R3A4A2A2Lgm;S50G3S41Z9A1A2X5bx2Lhd;A4X5cx2Lidx;A4X5bx2G3G3S2bG0A1M9Lgi;R1G2G2G9Lp;R1S16S0S1bS17G0S3aS17S1bS16G0S4fR3R2Vn;S59R1A1S26A5S16S23G0S5eS16R1A2A2Lp;A4Ls;A4Lidx;Lgm;X5dx1Lp;S23G0G1A2X5bx2Lgi;A4Lr;A4Tg;Tsc;Ls;A4").

Lemma malloc_loop_eq : ltac2:(tb__ "0|0|
S0S2S5cS57R1A1S6aA3S2S5cSeS27R2A2S6aA3S2S2bS5bS16A1A1S31R3A1Sc6R3A1A3F_;F_;Fn;").
Proof. intros n H1 H2. unfold malloc. rewrite H1, H2. reflexivity. Qed.

Definition loop_case (s : astate) (n : Z) (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|2|
S1S1S6Z0M0Vn;A2S8Vn;S27A2A2S1S2S5bS16A1M1SaeG1ScSbcVs;Vn;A2A1S24Vs;A1S62S16A1A4S5eS16Vg;A2A3S1S2S5bS18A1S76Vs;Vg;A2S5eS18S1fVam;A1A2A3S3S2S0S1aVam;A1G0A3A1A2A2A2").

Definition fast_case (s : astate) (n : Z) (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|2|
S1S1S6Z0M0Vn;A2S8Vn;S27A2A2S1S2S5bS16A1M1SaeG1ScS29Vn;A1A1S24Vs;A1S62S16A1A4S5eS16Vg;A2A3S1S2S5bS18A1S76Vs;Vg;A2S5eS18S1fVam;A1A2A3S3S2S0S1aVam;A1G0A3A1A2A2A2").

Definition coarse_case (s : astate) (n : Z) (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|5|
S1S1S6Z0M0Vn;A2S8Vn;S27A2A2S1S29Vn;A1S0S1S2S5bS16A1M1SaeG1ScR1A1S24Vs;A1M2S62S16A1M3A4G3A3S1S1S6Z4R1A2S8R1Z20A2A2S1S3S2S0R1Z6A3A1S1S2S5cSfR1A1S60A3S1S2S0S25Vs;R1A2G0A3S1S6S25Vs;S7R1Z1A2M4A2ZcA2S2G1SaeG1ScG4A1G2G3A4S5eS16Vg;A2A3A2A2A2A2A2A2Tsc0;S1S2S5bS18A1S76Vs;Vg;A2S5eS18S1fVam;A1A2A3S3S2S0S1aVam;A1G0A3A1A2A2A2").

Lemma malloc_class_cases : ltac2:(tb__ "0|d|
S17S0S29R1A1S0S5S1S2S0SbcR3R2A2M0R1A3S5S3S2S5bS16A1M1SaeG1ScR1A1S24R3A1M2S62S16A1M3A4G3A3M4A1S5S3S1S6Z4R1A2S8R1Z20A2A2M5A1S5S2S0R1Z6A3M6S5S2S5cSfR1A1M7S6aA3S5S3S2S0S25R3R1A2Z0M8A3M9A1S8ZcMaS7S25R3S7R1Z1A2MbA2S5cS0L_;G1S5cLx;SaeG1ScGbA1G2G3A4S16S5bS18A1S5cLx;S3dS40R4A1R1A2S18S18S5cLm;R1G1G1S60Lnext;Lprev;S60S1dS65SaS1aR1A1G8A2SaS2cR1A1G8A2A2Lam;X18x3Lm;S60X5bx2Lh;S60X5bx2Z3G8X5cx2A2McA2A2A2A2A2A2A2S1S2S0G0GbA3S1G4S1G5S1S3G6A1S1S2S5cG7S60A3S1G9S6GcGaA2A2A2A2A2A2A2A2Tsc0;Fn;Fs;").
Proof.
  intros s n sc0. unfold malloc_class. fold sc0. cbn zeta.
  destruct (nth (Z.to_nat sc0) (st_active s) None) as [g0|] eqn:Eg0; cbn [osptr_eqb andb].
  { left. split; [reflexivity|]. left. discriminate. }
  destruct (4 <=? sc0) eqn:E4; cbn [andb]; [apply Z.leb_le in E4|apply Z.leb_gt in E4; left; split; [reflexivity|]; right; left; lia].
  destruct (sc0 <? 32) eqn:E32; cbn [andb]; [apply Z.ltb_lt in E32|apply Z.ltb_ge in E32; left; split; [reflexivity|]; right; left; lia].
  destruct (sc0 =? 6) eqn:E6; cbn [negb andb]; [apply Z.eqb_eq in E6; left; split; [reflexivity|]; right; right; left; lia|apply Z.eqb_neq in E6].
  destruct (Z.even sc0) eqn:Ee; cbn [andb]; [|left; split; [reflexivity|]; right; right; right; left; reflexivity].
  destruct (usage_of s sc0 =? 0) eqn:Eu; [apply Z.eqb_eq in Eu|apply Z.eqb_neq in Eu; left; split; [reflexivity|]; do 4 right; left; exact Eu].
  set (hf := match nth (Z.to_nat (sc0 + 1)) (st_active s) None with | None => true | Some h => _ end).
  destruct hf.
  - destruct (usage_of s (sc0 + 1) + 3 <=? 12) eqn:E12; [apply Z.leb_le in E12; right | apply Z.leb_gt in E12; left; split; [reflexivity|]; do 5 right; lia].
    repeat split; auto.
  - rewrite Z.add_0_r. destruct (usage_of s (sc0 + 1) <=? 12) eqn:E12; [apply Z.leb_le in E12; right | apply Z.leb_gt in E12; left; split; [reflexivity|]; do 5 right; lia].
    repeat split; auto.
Qed.

Lemma malloc_class_range : ltac2:(tb__ "0|2|
S17S0S1S6Z0M0R1A2S8R1S27A2A2S1S1S6G0SbcR3R2A2M1A2S8G1Z30A2A2S6S7R2S1eA2S39G1A1A2A2F_;Fn;Fs;").
Proof.
  intros s n Hn. pose proof (size_to_class_range n Hn) as [R1 R2].
  destruct (malloc_class_cases s n) as [[-> _]|(E & _ & R & _)]; [auto|]. rewrite E.
  split; [lia|]. pose proof (class_size_mono (size_to_class n) (size_to_class n + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fast_loop_case : ltac2:(tb__ "0|0|
S17S0S16S1dSc5R4R3R2R1A4SbeR5R4R3R2A4F_;Fam;Fg;Fn;Fs;").
Proof.
  intros s n g am (Hn & Hact & HMT & Hav). split; [exact Hn|]. split; [|auto].
  destruct (malloc_class_cases s n) as [[-> _]|(_ & E & _)]; [exact Hact|]. rewrite E in Hact. discriminate.
Qed.

Lemma coarse_loop_case : ltac2:(tb__ "0|0|
S17S0S16S1dSc4R4R3R2R1A4SbeR5R4R3R2A4F_;Fam;Fg;Fn;Fs;").
Proof.
  intros s n g am (Hn & HX & HMT & Hav). cbn zeta in HX. destruct HX as (Hg0 & Hr & H6 & Hev & Hu0 & Hu1 & Hact).
  split; [exact Hn|]. split; [|auto].
  destruct (malloc_class_cases s n) as [[E C]|(E & _)]; rewrite E; [|exact Hact].
  exfalso. rewrite Hact in C. unfold MT in HMT. rewrite HMT in C.
  replace (am_avail am =? 0) with false in C by (symmetry; apply Z.eqb_neq; exact Hav). cbn [andb] in C.
  destruct C as [C|[C|[C|[C|[C|C]]]]]; try tauto; try lia. rewrite Hev in C. discriminate.
Qed.

Section Post.
  Variables (s : astate) (n : Z) (g : sptr) (am : ameta).

  Definition mf_first : Z := lowbit (am_avail am).
  Definition mf_idx : Z := ctz32 mf_first.
  Definition mf_stride : Z := stride_of am.
  Definition mf_slack : Z := ltac2:(tb__ "0|0|
S10S9S9Sb2S1eA2Vn;A2S22A2").
  Definition mf_ctr : Z := st_mmap_counter s.

  Definition mf_off0 (z : Z) : Z := ltac2:(tb__ "0|3|
S5cS0L_;M0SaSb1Z0M1A2G1S5bS5dS0S0A2M2A1S0Lx;S34S20Vam;SafA2A1G2G2S0Lp;R1S0S0S11G0SaR2G1A2Sb3S7R1Z1A2X5cx2ZffA2Lh16;Lh3;X5dx1Lp;S15Vz;Z100A2X5bx2X5cx2").
  Definition mf_off (z : Z) : Z := ltac2:(tb__ "0|0|
S8dSb1Sb9Vz;A1A2").
  Definition mf_reserved (z : Z) : Z := ltac2:(tb__ "0|0|
S9S9S9Sb2S1eA2SdS22Sb0Vz;A1A2A2Vn;A2").
  Definition mf_rsv (z : Z) : Z := ltac2:(tb__ "0|2|
S5cS0L_;SeZ5M0SbaVz;A1M1A2G0G1X5cx2").
  Definition mf_hdr (z : Z) : Z * Z := ltac2:(tb__ "0|1|
S5cS5dS0S0A2L_;SaSb0Vz;A1M0Z0A2S5fS0S0S7SafSdSbbVz;A1Z20A2A2S10SdSb2SafA2S22A2A4S5fS0S0Ze0G0A4X5cx2").
  Definition mf_frame (z : Z) : frame := ltac2:(tb__ "0|0|
S53Sb0Vz;A1Vn;S26A3").
  Definition mf_am1 : ameta := ltac2:(tb__ "0|0|
S37S9S1aVam;A1Sb6A2Vam;A2").
  Definition mf_am2 (z : Z) : ameta := ltac2:(tb__ "0|0|
S5aSb4SafS3cS5eS5dS0S0A2Sb8Vz;A1A2S5eS1cSb7Vz;A1A2A2A3").
  Definition mf_post (z : Z) : astate := ltac2:(tb__ "0|0|
Sd6Vg;S1fSb5Vz;A1A1Vs;A3").
  Definition mf_ptr (z : Z) : sptr := ltac2:(tb__ "0|0|
S19S32Vam;SafA2SdS22Sb0Vz;A1A2A2").

  Definition mf_trace (z : Z) : list (kreq * Z) := ltac2:(tb__ "0|4|
S5cS67S5dS21S0A2M0A1M1L_;SaSb1Z0A2S61G0A1M2S5bS5dS0S0A2M3A1G1Lx;S34S20Vam;SafA2A1G3G2Lp;S64G0S5fS21S0S43S11Sb3ZffA2A1Vz;A4G2A3X5bx2X5cx2").
End Post.

Lemma yields_bind {A B} (m : M A) (k : A -> M B) s tr1 tr2 a s1 b : ltac2:(tb__ "0|1|
S71S5dVA;S17A2Vm;Vs;A1Vtr1;S5fVA;S17Va;Vs1;A4A4S71S5dVB;S17A2M0Vk;Va;Vs1;A2Vtr2;Vb;A4S71G0S1bVA;VB;Vm;Vk;Vs;A5S63S5dS21S0A2Vtr1;Vtr2;A3Vb;A4F_;F_;").
Proof. intros H1 H2. unfold bind. exact (yields_ibind _ _ tr1 tr2 (a, s1) b H1 H2). Qed.

Lemma yields_bind0 {A B} (m : M A) (k : A -> M B) s tr a s1 b : ltac2:(tb__ "0|1|
S71S5dVA;S17A2Vm;Vs;A1S61S5dS21S0A2A1S5fVA;S17Va;Vs1;A4A4S71S5dVB;S17A2M0Vk;Va;Vs1;A2Vtr;Vb;A4S71G0S1bVA;VB;Vm;Vk;Vs;A5Vtr;Vb;A4F_;F_;").
Proof. intros H1 H2. exact (yields_bind m k s [] tr a s1 b H1 H2). Qed.

Lemma yields_bind1 {A B} (m : M A) (k : A -> M B) s tr a s1 b : ltac2:(tb__ "0|1|
S71S5dVA;S17A2Vm;Vs;A1Vtr;S5fVA;S17Va;Vs1;A4A4S71S5dVB;S17A2M0Vk;Va;Vs1;A2S61S5dS21S0A2A1Vb;A4S71G0S1bVA;VB;Vm;Vk;Vs;A5Vtr;Vb;A4F_;F_;").
Proof. intros H1 H2. rewrite <- (app_nil_r tr). exact (yields_bind m k s tr [] a s1 b H1 H2). Qed.

Lemma yields_ret {A} (a : A) s : ltac2:(tb__ "0|0|
S71S5dVA;S17A2S23VA;Va;Vs;A3S61S5dS21S0A2A1S5fVA;S17Va;Vs;A4A4").
Proof. reflexivity. Qed.

Lemma yields_getm s q am : ltac2:(tb__ "0|0|
S2S5bS18A1S76Vs;Vq;A2S5eS18S1fVam;A1A2A3S71S5dS1dS17A2S3bVq;Vs;A2S61S5dS21S0A2A1S5fS1dS17Vam;Vs;A4A4F_;").
Proof. intros H. unfold getm. apply (yields_bind0 _ _ s [] s s). { reflexivity. } unfold MT in H. rewrite H. reflexivity. Qed.

Lemma yields_setm s q am : ltac2:(tb__ "0|0|
S71S5dS69S17A2S3fVq;Vam;Vs;A3S61S5dS21S0A2A1S5fS69S17S6eSd6Vq;S1fVam;A1Vs;A3A4A4").
Proof. reflexivity. Qed.

Section Yields.
  Variables (s : astate) (n : Z) (g : sptr) (am : ameta).
  Hypothesis HW : WF s.
  Hypothesis HC : ltac2:(tb__ "0|0|
SbeVs;Vn;Vg;Vam;A4").

  Lemma mfy_u : ltac2:(tb__ "0|0|
S7dS61S16A1Vs;Vg;Vam;A4").
  Proof using HC. apply usedX_intro; [reflexivity | exact (proj1 (proj2 (proj2 HC)))]. Qed.

  Lemma mfy_sc : ltac2:(tb__ "0|2|
S1S2S0S4cVam;A1M0SbcVs;Vn;A2A3S1S1S6Z0G0A2S8G0Z30A2A2S1S6S7Vn;S1eA2S39G0A1M1A2S6G1Sc1Vam;A1A2A2A2A2").
  Proof using HC HW.
    destruct HC as (Hn & Hact & HMT & Hav).
    pose proof (malloc_class_range s n Hn) as [R1 R2].
    destruct (head_used [] None U0 s (malloc_class s n) g HW R1 Hact) as (am' & Hu' & Hsc).
    pose proof (usedX_fun _ _ _ _ _ Hu' mfy_u) as ->.
    rewrite Hsc. split; [reflexivity|]. split; [exact R1|]. split; [exact R2|].
    destruct (lowbit_spec (am_avail am) ltac:(pose proof (inv_groups HW g am mfy_u) as ((_ & _ & _ & Gav & _) & _); lia)) as (k & Hk & _ & Hb & _).
    rewrite <- Hsc. apply (avail_bit_not_undersized [] None U0 s g am k HW mfy_u ltac:(lia) Hk).
    rewrite Z.lor_spec, Hb. reflexivity.
  Qed.

  Lemma mfy_first : ltac2:(tb__ "0|0|
S4S0S0S1S1S6Z0R1A2S6R1S2dVam;A1A2A2S1S2S0SbfVam;A1S38R1A1A3S1S2S0Sc9Vam;A1R1A3S2S5cS14S1aVam;A1R1A2S60A3A2A2A2Lk;A2").
  Proof using HC HW.
    pose proof (inv_groups HW g am mfy_u) as ((Glast & _ & _ & Gav & _ & _ & Gabove & _) & _).
    destruct HC as (_ & _ & _ & Hav).
    destruct (lowbit_spec (am_avail am) ltac:(lia)) as (k & Hk & Hl & Hb & _).
    exists k. unfold mf_idx, mf_first. rewrite Hl, ctz32_bit by exact Hk.
    split; [|auto]. split; [exact Hk|].
    destruct (Z_le_dec k (am_last am)); [assumption|]. exfalso.
    destruct (Gabove k ltac:(lia)) as [X _]. rewrite X in Hb. discriminate.
  Qed.

  Theorem malloc_fast_yields : ltac2:(tb__ "0|1|
S0S1S6Z0R1A2S8R1Z100A2A2S71S5dS5bS16A1M0S17A2S31Vn;Vs;A2Sc3Vs;Vn;Vam;R2A4S5fG0S17S5eS16SbdVs;Vn;Vam;R2A4A2Sc2Vs;Vn;Vg;Vam;R2A5A4A4F_;Fz;").
  Proof using HC HW.
    intros z Hz. destruct HC as (Hn & Hact & HMT & Hav).
    destruct mfy_first as (k & Hk & Efirst & Eidx & Hbit).
    pose proof (inv_groups HW g am mfy_u) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    pose proof G as ((Glast & _ & Glen & _) & _).
    rewrite malloc_loop_eq.
    2:{ unfold size_overflows. apply Z.leb_gt. unfold MMAP_THRESHOLD in Hn. lia. }
    2:{ apply Z.leb_gt. lia. }
    unfold malloc_loop.
    eapply yields_bind0; [apply yields_ret|].
    cbn zeta. rewrite Hact.

    eapply yields_bind0.
    { eapply yields_bind0; [apply (yields_getm _ _ _ HMT)|].
      replace (am_avail am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hav).
      eapply yields_bind0; [apply yields_setm|]. apply yields_ret. }
    cbn beta iota.
    eapply yields_bind0; [apply yields_ret|]. cbn beta iota.
    eapply yields_bind0; [apply yields_ret|].
    eapply yields_bind1; [|apply yields_ret].

    unfold enframe.
    eapply yields_bind0; [apply yields_getm; rewrite MT_upd_same; reflexivity|].
    fold (mf_first am). fold (mf_idx am).
    change (am_last (am_set_avail (am_avail am - mf_first am) am)) with (am_last am).
    change (stride_of (am_set_avail (am_avail am - mf_first am) am)) with (mf_stride am).
    change (nth_slot (am_set_avail (am_avail am - mf_first am) am) (mf_idx am)) with (nth_slot am (mf_idx am)).
    change (st_mmap_counter (upd_meta g (MUsed (am_set_avail (am_avail am - mf_first am) am)) s)) with (mf_ctr s).
    unfold mcheck. replace ((0 <=? mf_idx am) && (mf_idx am <=? am_last am))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    eapply yields_bind0; [apply yields_ret|].
    fold (mf_slack n am).

    eapply (yields_bind1 _ _ _ (mf_trace s n am z) (mf_off0 s n am z)).
    { unfold mf_trace, mf_off0. destruct (mf_slack n am =? 0); [apply yields_ret|].
      destruct (ss_hdr (nth_slot am (mf_idx am))) as [[h3 h16]|]; [apply yields_ret|].
      cbn. split; [reflexivity|]. split; [exact Hz|]. reflexivity. }
        match goal with |- yields ((massert (?o <=? _) _ ;; _) _) _ _ => change o with (fold_off (mf_slack n am) (mf_off0 s n am z)) end.
    fold (mf_off s n am z).
    assert (Hslack : 0 <= mf_slack n am).
    { pose proof mfy_sc as (_ & _ & F1 & F2). unfold mf_slack. apply Z.div_pos; [|unfold UNIT; lia]. unfold IB in *. lia. }
    assert (Hoff0 : 0 <= mf_off0 s n am z < 256).
    { unfold mf_off0. destruct (mf_slack n am =? 0); [lia|]. destruct (ss_hdr (nth_slot am (mf_idx am))) as [[h3 h16]|].
      - pose proof (land255_range (if h3 =? 0 then mf_ctr s else h16 + 1)). lia.
      - pose proof (mod256_range z). lia. }
    pose proof (fold_off_ok (mf_slack n am) (mf_off0 s n am z) Hslack Hoff0) as Hoff. fold (mf_off s n am z) in Hoff.
    unfold massert. replace (mf_off s n am z <=? mf_slack n am) with true by (symmetry; apply Z.leb_le; lia).
    eapply yields_bind0; [apply yields_ret|].
    eapply yields_bind0; [apply yields_setm|].
    rewrite upd_meta_twice.
    unfold mf_ptr, mf_post, mf_am2, mf_am1, mf_hdr, mf_frame, mf_rsv, mf_reserved.
    change (slot_start (am_set_avail (am_avail am - mf_first am) am) (mf_idx am)) with (slot_start am (mf_idx am)).
    apply yields_ret.
  Qed.
End Yields.

Section Gap.
  Variables (C : mconsts) (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (z : Z).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm : VmMaps).
  Hypothesis HMI : ltac2:(tb__ "0|0|
Sd9VC;SdaVs;VL;A2Vrd0;Vwok0;Vvm;A5").
  Hypothesis HC : ltac2:(tb__ "0|0|
SbeVs;Vn;Vg;Vam;A4").
  Hypothesis Hz : 0 <= z < 256.
  Hypothesis HS : statics_in_image C.

  Definition f_idx : Z := mf_idx am.
  Definition f_off : Z := ltac2:(tb__ "0|0|
ScaVs;Vn;Vam;Vz;A4").
  Definition f_fr : frame := ltac2:(tb__ "0|0|
Sc8Vs;Vn;Vam;Vz;A4").
  Definition f_am2 : ameta := ltac2:(tb__ "0|0|
Sc7Vs;Vn;Vam;Vz;A4").
  Definition f_s' : astate := ltac2:(tb__ "0|0|
Sc2Vs;Vn;Vg;Vam;Vz;A5").
  Definition f_st : Z := ltac2:(tb__ "0|0|
ScfVL;S32Vam;S98A2A2").
  Definition f_p : Z := ltac2:(tb__ "0|0|
ScfVL;SbdVs;Vn;Vam;Vz;A4A2").
  Definition f_e : Z := ltac2:(tb__ "0|0|
ScfVL;SceVam;S98A2A2").
  Definition f_zg : Z := addr_of L g.
  Definition f_zm : Z := ltac2:(tb__ "0|0|
ScfVL;S2eVam;A1A2").

  Definition f_bv0 : byteview := byteview_of rd0 wok0.
  Definition f_bv1 : byteview := byteview_of rd1 wok1.
  Definition f_rv0 : byteview := byteview_of rd0 (fun _ => true).
  Definition f_rv1 : byteview := byteview_of rd1 (fun _ => true).

  Definition f_Cavail : mcell := ltac2:(tb__ "0|0|
S72S70S19Vg;S7eA2A1U4S73S9S1aVam;A1SbfVam;A1A2A1A3").
  Definition f_hdrcells : list mcell := ltac2:(tb__ "0|1|
S5dS0S0A2S67S6fA1Lp;Sc0Vs;Vn;Vam;Vz;A4S0S0S64S6fS72S70S19S32Vam;S98A2M0N3A2A1U1S73R2A1A3S64S6fS72S70S19G0N2A2A1U2S73R1A1A3S61S6fA1A3A3Lh16;Lh3;X5dx1").
  Definition f_frcells : list mcell := ltac2:(tb__ "0|4|
S5cS67S6fA1L_;SaSa1Z0M0A2S61S6fA1M1S64S6fS72S70S19SbdVs;Vn;Vam;Vz;A4M2N4A2A1U1M3S73G0A1A3S64S6fS72S70S19G2N3A2A1G3S73S8fVam;S98S9fA3A1A3S64S6fS72S70S19G2N2A2A1U2S73S90Vam;S98S9fA3A1A3G1A3A3A3X5cx2").
  Definition f_footcells : list mcell := ltac2:(tb__ "0|0|
ScdVam;S98S9fA3").
  Definition f_newcells : list mcell := ltac2:(tb__ "0|0|
S64S6fSabS63S6fSa7S63S6fSa6Sa5A3A3A3").

  Definition in_zone (x : Z) : Prop := ltac2:(tb__ "0|0|
S1S6S9S9cZ3A2Vx;A2S8Vx;S9dA2A2").
  Definition in_av (x : Z) : Prop := ltac2:(tb__ "0|0|
S1S6S7S9eZ18A2Vx;A2S8Vx;S7S9eZ1cA2A2A2").

  Hypothesis V1 : ltac2:(tb__ "0|1|
S0S1S6Z0R1A2S8R1SbZ2Z40A2A2A2S3Sa2R2A1A1S3SaaR3A1A1S1S2S5bSd7Q8A1A1Vrd1;Sd0R4A1M0A1Vrd0;G0A1A3S2S5cVwok1;G0A1Vwok0;G0A1A3A2F_;F_;F_;Fx;").
  Hypothesis V2 : ltac2:(tb__ "0|1|
S0Sa2R1A1S1S2S5cVwok1;Sd0R2A1A1S60A3S4Sd7Q8A1M0G0S2S5bG0A1Vrd1;Sd0R3A1A1S5eG0R1A2A3Lb;A2A2F_;Fx;").
  Hypothesis V3 : ltac2:(tb__ "0|3|
S6fS97S6fR1Sa0A3S6cSd5R1S78R3A1A2S1S2S5cVwok1;Sd0S7S7aVL;S7bR4A1A2S13R2A1A2A1M0A1S60A3S2S5bSd7Q8M1A1M2A1Vrd1;G0A1S5eG2Sd8G1S91S95VL;S7cR4A1A2S78R4A1R2A3A2A2A3A2F_;Fj;F_;Fc;").

  Lemma F_W : WF s. Proof using HMI. exact (proj1 HMI). Qed.
  Lemma F_u : ltac2:(tb__ "0|0|
S7dS61S16A1Vs;Vg;Vam;A4"). Proof using HC. exact (mfy_u s n g am HC). Qed.
  Lemma F_um : ltac2:(tb__ "0|0|
S97S5dS16S1dA2S5fS16S1dVg;Vam;A4S96Vs;A1A3"). Proof using HC HMI. apply (used_metas_usedX s g am F_W). apply F_u. Qed.
  Lemma F_MT : ltac2:(tb__ "0|0|
S2S5bS18A1S76Vs;Vg;A2S5eS18S1fVam;A1A2A3"). Proof using HC. exact (proj1 (proj2 (proj2 HC))). Qed.
  Lemma F_ND : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys F_W)). Qed.
  Lemma F_repr : ltac2:(tb__ "0|0|
SccVL;Vs;Sa4A3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 HMI)))). Qed.
  Lemma F_L : layout_ok L s. Proof using HMI. exact (proj1 (proj1 F_repr)). Qed.
  Lemma F_idx : ltac2:(tb__ "0|0|
S1S1S6Z0S98A2S6S98S2dVam;A1A2A2S1S2S5cS14S1aVam;A1S98A2S60A3S2S0SbfVam;A1S38S98A1A3A2A2").
  Proof using HC HMI. destruct (mfy_first s n g am F_W HC) as (k & Hk & E1 & E2 & Hb). unfold f_idx. rewrite E2. auto. Qed.
  Lemma F_sl : ltac2:(tb__ "0|0|
S2S5bS1cA1S2aS20Vam;S98A2A1S62S1cA1A3").
  Proof using HC HMI.
    pose proof (inv_groups F_W g am F_u) as (_ & _ & Gsl & _). destruct F_idx as (Hi & Hb & _).
    pose proof (Gsl f_idx Hi) as (_ & _ & S3). destruct (ss_fr (nth_slot am f_idx)) as [fr|]; [|reflexivity].
    destruct S3 as (Hal & _). unfold allocated in Hal. rewrite Z.lor_spec, Hb in Hal. discriminate.
  Qed.
  Lemma F_len : ltac2:(tb__ "0|0|
Sd5ScS98A1S6bS33S4dVam;A1A2A2").
  Proof using HC HMI Hz. pose proof (inv_groups F_W g am F_u) as ((_ & _ & L0 & _) & _). rewrite L0. destruct F_idx as (Hi & _). lia. Qed.
  Lemma F_s' : ltac2:(tb__ "0|0|
S2S17S99Sd6Vg;S1fS9aA1Vs;A3A3"). Proof using . reflexivity. Qed.
  Lemma F_y : ltac2:(tb__ "0|1|
S71S5dS5bS16A1M0S17A2S31Vn;Vs;A2Sc3Vs;Vn;Vam;Vz;A4S5fG0S17S5eS16SbdVs;Vn;Vam;Vz;A4A2S99A4A4").
  Proof using HC HMI Hz. exact (malloc_fast_yields s n g am F_W HC z Hz). Qed.
  Lemma F_W' : WF f_s'.
  Proof using HC HMI Hz. exact (malloc_wf s n _ _ _ F_W (proj1 (proj1 HC)) F_y). Qed.
  Lemma F_L' : layout_ok L f_s'. Proof using HMI. exact F_L. Qed.
  Lemma F_MT' : ltac2:(tb__ "0|0|
S2S5bS18A1S76S99Vg;A2S5eS18S1fS9aA1A2A3"). Proof using . rewrite F_s', MT_upd_same. reflexivity. Qed.
  Lemma F_u' : ltac2:(tb__ "0|0|
S7dS61S16A1S99Vg;S9aA4"). Proof using . apply usedX_intro; [reflexivity | exact F_MT']. Qed.
  Lemma F_am2_slot j : ltac2:(tb__ "0|0|
S6Z0Vj;A2S2S33S20S9aVj;A2S5cS33L_;SaVj;S98A2S3cS5eS5dS0S0A2Sc0Vs;Vn;Vam;Vz;A4A2S5eS1cS9fA2A2S20Vam;Vj;A2X5cx2A3F_;").
  Proof using HC HMI Hz.
    intros Hj. unfold f_am2, mf_am2. rewrite nth_slot_upd_slot; [| pose proof F_idx; unfold f_idx in *; lia | exact Hj |].
    - unfold f_idx, f_fr. destruct (j =? mf_idx am); reflexivity.
    - unfold mf_am1. cbn [am_slots am_set_avail]. exact F_len.
  Qed.
  Lemma F_sl' : ltac2:(tb__ "0|0|
S2S5bS1cA1S2aS20S9aS98A2A1S5eS1cS9fA2A3").
  Proof using HC HMI Hz. rewrite F_am2_slot by (pose proof F_idx; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma F_hdr' : ltac2:(tb__ "0|1|
S2S5bS5dS0S0A2M0A1S34S20S9aS98A2A1S5eG0Sc0Vs;Vn;Vam;Vz;A4A2A3").
  Proof using HC HMI Hz. rewrite F_am2_slot by (pose proof F_idx; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma F_kind : ltac2:(tb__ "0|0|
S2S2fS30S9fA1S26A3"). Proof using . reflexivity. Qed.
  Lemma F_off : ltac2:(tb__ "0|1|
S1S1S6Z0M0Sa1A2S6Sa1ZffA2A2S1S6S7SdS22Sa1A2Vn;A2S9Sc1Vam;A1S1eA2A2S6G0Vn;A2A2A2").
  Proof using HC HMI Hz.
    pose proof (mfy_sc s n g am F_W HC) as (_ & _ & Fit & Und). destruct HC as (Hn & _).
    assert (Hslack : 0 <= mf_slack n am) by (unfold mf_slack; apply Z.div_pos; [unfold IB in *; lia|unfold UNIT; lia]).
    assert (Hoff0 : 0 <= mf_off0 s n am z < 256).
    { unfold mf_off0. destruct (mf_slack n am =? 0); [lia|]. destruct (ss_hdr (nth_slot am (mf_idx am))) as [[h3 h16]|].
      - pose proof (land255_range (if h3 =? 0 then mf_ctr s else h16 + 1)). lia.
      - pose proof (mod256_range z). lia. }
    pose proof (fold_off_ok (mf_slack n am) (mf_off0 s n am z) Hslack Hoff0) as Hoff.
    pose proof (fold_off_le (mf_slack n am) (mf_off0 s n am z) ltac:(lia) Hslack) as Hoffle.
    unfold f_off, mf_off. split; [lia|]. split; [|lia].
    assert (UNIT * mf_slack n am <= mf_stride am - IB - n).
    { unfold mf_slack, UNIT. pose proof (Z.mul_div_le (mf_stride am - IB - n) 16 ltac:(lia)). lia. }
    unfold UNIT in *. nia.
  Qed.

  Lemma F_geom : ltac2:(tb__ "0|5|
S1S6Z10Sc1Vam;A1M0A2S1S2S0S9cS7S7Sa9S22A2SdG0S98A2M1A2A3S1S2S0SadS7S9cSdS22Sa1A2A2A3S1S2S0S9dS9S7S9cG0A2S1eA2A3S1S2S5dS0S0A2SdbVL;Vam;S98A3S5fS0S0S9S9cZ3M2A2S7S9G0S1eA2G2A2A4A3S1S8Z0M3Sa9A2S1S8S7S9dS1eA2SbZ2Z3fA2A2S1S1S6G3G1A2S6S7G1G0A2SdG0S7S2dVam;A1Z1A2A2A2A2S4S5dS77S0A2M4G4S1S97G4R1S81Vs;A1A3S1S93S5fS0S0Sa9S7S8eVam;A1S1eA2A4S8cVL;R1A2A2S2S77S66S77S0R1A3S70S48S3eS2eVam;A1A1G3A2A1A3A2A2Lrg;A2A2A2A2A2A2A2A2A2").
  Proof using HC HMI Hz.
    pose proof (inv_groups F_W g am F_u) as G0. pose proof (stride_pos _ _ _ _ _ G0) as Sp.
    destruct (used_group_region [] None U0 s g am F_W F_u) as (rg & Hr & Hk & Hl & Ho0 & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
    pose proof F_L as (_ & _ & _ & POS). destruct (POS _ InR) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    pose proof F_idx as (Hi & _).
    assert (E1 : f_st = f_zm + UNIT + mf_stride am * f_idx).
    { unfold f_st, f_zm, addr_of, loc_addr, slot_start, mf_stride. destruct (am_mem am); cbn [padd]. lia. }
    assert (E2 : f_p = f_st + UNIT * f_off).
    { unfold f_p, f_st, mf_ptr, f_off, f_idx, addr_of, loc_addr. destruct (slot_start am (mf_idx am)); cbn [padd]. lia. }
    assert (E3 : f_e = f_st + mf_stride am - IB).
    { unfold f_e, f_st, addr_of, loc_addr, slot_end, mf_stride. destruct (slot_start am f_idx); cbn [padd]. lia. }
    assert (Hsi : 0 <= mf_stride am * f_idx /\ mf_stride am * f_idx + mf_stride am <= mf_stride am * (am_last am + 1)) by (unfold mf_stride in *; split; nia).
    assert (Ezm : f_zm = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold f_zm, addr_of, loc_addr; destruct (am_mem am); reflexivity).
    split; [exact Sp|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [unfold zone_range; rewrite E1; unfold f_zm, addr_of, mf_stride; reflexivity|].
    split; [lia|]. split; [unfold group_extent, mf_stride in *; lia|]. split; [exact Hsi|].
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [exact InR|]. split; [|reflexivity].
    unfold range_incl, crange, loc_addr. cbn [fst snd]. lia.
  Qed.

  Lemma F_area : ltac2:(tb__ "0|3|
S4S16S16S4S0S0S1S97S16R2S58Vs;A1A3S1S1S6Z0M0R1A2S8R1S44A2A2S1S2S16Vg;S19R2S7S35SdS45R1A2M1A2A2A3S1S97S5dS77S0A2S5fS77S0S70R2A1S36A4S81Vs;A1A3S1S8G0ScfVL;R2A2M2A2S1S8S7G2S36A2SbZ2Z3fA2A2S1S2S0S9eS7S7G2S35A2G1A2A3S4S28S28S1S2S5bS28A1S94Vs;S3eR3A1A2S5eS28R1A2A3S3S2S56S55R1A1S47A3A1A2Lrga;A2A2A2A2A2A2A2A2Lk;A2La;A2").
  Proof using HC HMI Hz.
    pose proof (usedX_MT _ _ _ _ F_u) as [Mg _].
    destruct (meta_in_area s g (MUsed am) F_W ltac:(unfold MT in Mg; apply In_of_mlookup; exact Mg)) as (a & k & Ha & Hk & Eg).
    exists a, k. split; [exact Ha|]. split; [exact Hk|]. split; [exact Eg|].
    assert (InA : In (LMem a, PGSZ) (footprint s)).
    { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. }
    split; [exact InA|].
    pose proof F_L as (_ & _ & _ & POS). destruct (POS _ InA) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    unfold f_zg, addr_of. split; [destruct a; cbn in *; lia|]. split; [destruct a; cbn in *; lia|].
    split; [rewrite Eg; unfold loc_addr; destruct a; cbn [padd]; lia|].
    pose proof (inv_areas F_W) as (_ & A2 & _). destruct (A2 _ Ha) as (r & o & rga & Ea & _ & _ & Hra & _ & _ & Hkind).
    exists rga. subst a. cbn [prid]. split; [exact Hra|]. destruct (rg_kind rga); [discriminate|discriminate|destruct Hkind].
  Qed.

  Lemma FBV1 : ltac2:(tb__ "0|1|
S0S1S6Z0R1A2S8R1SbZ2Z40A2A2A2S3Sa2R2A1A1S3SaaR3A1A1S1S2S5bS0A1M0S9bR4A1Sa4R4A1A3S2G0Sa8R4A1SacR4A1A3A2F_;F_;F_;Fx;").
  Proof using V1.
    intros x Hx Hb Hw. destruct (V1 x Hx Hb Hw) as [E1 E2].
    unfold f_bv1, f_bv0, f_rv1, f_rv0, byteview_of. unfold wz in E1, E2. rewrite E1, E2. split; reflexivity.
  Qed.

  Lemma FBV2 : ltac2:(tb__ "0|0|
S0S1S6Z0R1A2S8R1SbZ2Z40A2A2A2Sa2R2A1S3S2S5bS0A1S9bR3A1S62S0A1A3A1F_;F_;Fx;").
  Proof using Hz V2.
    intros x Hx Hb. destruct (V2 x Hb) as [E1 [b E2]]. unfold f_bv1, byteview_of. unfold wz in E1, E2.
    replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite E1, E2. discriminate.
  Qed.

  Lemma FBV3 : ltac2:(tb__ "0|0|
S6fS97S6fR1Sa0A3S6Z0S7aVL;S7bR2A1A2A2S6S7S7aVL;S7bR3A1A2S13S78R3A1A1A2SbZ2Z40A2A2S0S3S2S84S7cR5A1S7fR1A1A3A1Fv;S79VL;S9bR5A3F_;F_;F_;F_;Fc;").
  Proof using Hz V3.
    intros c Hc Hlo Hhi Hnv. unfold cell_holds.
    destruct (mc_val c) as [v|q|v|] eqn:Ev; [| | exfalso; exact (Hnv v eq_refl) |];
      intros j Hj; destruct (V3 c Hc j Hj) as [E1 E2]; rewrite Ev in E2; unfold f_bv1, byteview_of; unfold wz in E1, E2;
      (replace ((0 <=? loc_addr L (mc_loc c) + Z.of_nat j) && (loc_addr L (mc_loc c) + Z.of_nat j <? 2 ^ 64))%bool with true
         by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia));
      cbn [andb]; rewrite E1, E2; f_equal; apply Z_to_bv_small; change (bv_modulus 8) with 256; unfold le_byte; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma own_hdr_new : ltac2:(tb__ "0|0|
S2S67S6fA1SdcS9aS98A2S63S6fSa7Sa6A3A3").
  Proof using HC HMI Hz.
    unfold own_hdr. rewrite F_hdr', F_sl'. unfold f_hdrcells, f_frcells, f_off, f_fr, mf_frame. cbn [fr_off].
    destruct (mf_hdr s n am z) as [h3 h16]. reflexivity.
  Qed.

  Lemma image'_cases c : ltac2:(tb__ "0|0|
S97S6fVc;S75S99A1A3S5S97S6fVc;Sa0A3S97S6fVc;S75Vs;A1A3A2F_;").
  Proof using HC HMI Hz.
    intros Hin. rewrite F_s' in Hin.
    destruct (upd_image_In s g am f_am2 F_ND F_MT c Hin) as [Hold | [Hm | Hgr]]; [right; exact Hold| |].
    - unfold meta_slot_cells in Hm. cbn in Hm.
      assert (OLD : forall c', In c' (meta_slot_cells g (Some (MUsed am))) -> In c' (image s)).
      { intros c' Hc'. exact (meta_cells_in_image s g am c' F_W F_u Hc'). }
      unfold meta_slot_cells in OLD.
      destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      1,2,3,5,6: right; apply OLD; cbn; tauto.
      left. left. reflexivity.
    - unfold group_cells in Hgr. apply in_app_iff in Hgr as [Hh|Hsl].
      + right. apply (In_image_group s g am c F_um). unfold group_cells. apply in_app_iff. left. exact Hh.
      + apply in_flat_map in Hsl as [j [Hj Hc]]. apply In_zseq in Hj. change (am_last f_am2) with (am_last am) in Hj.
        unfold slot_cells in Hc. rewrite (F_am2_slot j) in Hc by lia.
        change (slot_start f_am2 j) with (slot_start am j) in Hc.
        destruct (j =? f_idx) eqn:Eji.
        * apply Z.eqb_eq in Eji. subst j. cbn [ss_hdr ss_fr] in Hc.
          apply in_app_iff in Hc as [Hc|Hc].
          -- right. destruct Hc as [<-|[]]. exact (proj1 (slot_start_cells s g am f_idx F_W F_um (proj1 F_idx))).
          -- assert (K : In c (own_hdr f_am2 f_idx)).
             { unfold own_hdr. rewrite F_hdr', F_sl'. exact Hc. }
             rewrite own_hdr_new in K. left. right. apply in_app_iff in K. apply in_app_iff.
             destruct K as [K|K]; [left; exact K | right; apply in_app_iff; left; exact K].
        * right. apply (In_image_group s g am c F_um). apply (In_group_slot g am j); [lia|]. exact Hc.
  Qed.

  Lemma Cavail_range : ltac2:(tb__ "0|0|
S2S5dS0S0A2S74VL;SabA2S5fS0S0S7S9eZ18A2Z4A4A3").
  Proof using HC Hz. unfold cell_range, f_Cavail, f_zg, addr_of, loc_addr, META_avail. destruct g; cbn [mc_loc mc_w padd]. f_equal; lia. Qed.

  Lemma Cavail_in : In f_Cavail (image f_s').
  Proof using HC HMI Hz.
    rewrite F_s'. apply (upd_image_meta s g f_am2). { rewrite <- F_s'. exact F_W'. }
    unfold meta_slot_cells. cbn. do 3 right. left. reflexivity.
  Qed.

  Lemma newcells_ranges c : ltac2:(tb__ "0|2|
S97S6fVc;S63S6fSa7S63S6fSa6Sa5A3A3A3S1S6S9S9cZ3A2S66S0S0S74VL;Vc;A2M0A3M1A2S1S6S7G1S68S0S0G0A3A2S9dA2S1Sd5U0S78Vc;A1A2S0S3S2S84S7cVc;A1S7fR1A1A3A1Fv;A2A2A2F_;").
  Proof using HC HMI Hz.
    intros Hc. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & _). pose proof F_off as (Ho & Hfit & Hn).
    assert (Est : forall d, cell_range L (MCell (LMem (padd (slot_start am f_idx) d)) 1 (VZ 0)) = (f_st + d, 1)
                  /\ forall w v, cell_range L (MCell (LMem (padd (slot_start am f_idx) d)) w v) = (f_st + d, Z.of_nat w)).
    { intros d. unfold cell_range, f_st, addr_of, loc_addr. destruct (slot_start am f_idx); cbn [mc_loc mc_w padd]. split; [f_equal; lia|]. intros; f_equal; lia. }
    assert (Ep : forall w v d, cell_range L (MCell (LMem (padd (mf_ptr s n am z) d)) w v) = (f_p + d, Z.of_nat w)).
    { intros w v d. unfold cell_range, f_p, addr_of, loc_addr. destruct (mf_ptr s n am z); cbn [mc_loc mc_w padd]. f_equal; lia. }
    assert (Ee : forall w v d, cell_range L (MCell (LMem (padd (slot_end am f_idx) d)) w v) = (f_e + d, Z.of_nat w)).
    { intros w v d. unfold cell_range, f_e, addr_of, loc_addr. destruct (slot_end am f_idx); cbn [mc_loc mc_w padd]. f_equal; lia. }
    unfold f_hdrcells, f_frcells, f_footcells, frame_footer_cells in Hc. rewrite F_kind in Hc.
    change (frame_ptr am f_idx f_fr) with (mf_ptr s n am z) in Hc.
    change (fr_n f_fr) with n in Hc.
    assert (Hrsv : reserved_of am f_fr = mf_stride am - IB - UNIT * f_off - n) by reflexivity.
    unfold IB, UNIT in *.
    destruct (mf_hdr s n am z) as [h3 h16].
    apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
    - destruct Hc as [<-|[<-|[]]]; (rewrite (proj2 (Est _)); cbn [mc_w mc_val fst snd Z.of_nat]; split; [lia|]; split; [lia|]; split; [cbn; lia | intros; discriminate]).
    - destruct (f_off =? 0) eqn:E0; [destruct Hc|]. apply Z.eqb_neq in E0.
      destruct Hc as [<-|[<-|[<-|[]]]]; (rewrite Ep; cbn [mc_w mc_val fst snd Z.of_nat]; split; [lia|]; split; [lia|]; split; [cbn; lia | intros; discriminate]).
    - apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
      + destruct (0 <? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.ltb_lt in Er. destruct Hc as [<-|[]].
        rewrite Ep. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
      + destruct (5 <=? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.leb_le in Er. destruct Hc as [<-|[]].
        rewrite Ee. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
      + destruct (5 <? reserved_of am f_fr) eqn:Er; [|destruct Hc]. apply Z.ltb_lt in Er. destruct Hc as [<-|[]].
        rewrite Ee. cbn [mc_w mc_val fst snd Z.of_nat]. split; [lia|]. split; [lia|]. split; [cbn; lia | intros; discriminate].
  Qed.

  Lemma newcells_hold c : ltac2:(tb__ "0|0|
S97S6fVc;Sa0A3S79VL;S9bVc;A3F_;").
  Proof using HC HMI Hz V3.
    intros Hc. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & _).
    destruct F_area as (a & k & Ha & Hk & Eg & InA & Pa & Pa2 & Ezg & _).
    destruct Hc as [<- | Hc].
    - apply FBV3; [left; reflexivity | | | intros; discriminate];
        pose proof (f_equal fst Cavail_range) as R; unfold cell_range in R; cbn [fst mc_loc] in R; rewrite R; cbn [mc_w f_Cavail];
        unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia.
    - destruct (newcells_ranges c Hc) as (R1 & R2 & Rw & Rv). unfold cell_range in R1, R2. cbn [fst snd] in R1, R2.
      apply FBV3; [right; exact Hc | | | exact Rv]; unfold UNIT, IB in *; lia.
  Qed.

  Definition f_avoids (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S1S83Vr;SdbVL;Vam;S98A3A2S83Vr;S5fS0S0S7S9eZ18A2Z4A4A2A2").

  Lemma avoids_bytes lo w : ltac2:(tb__ "0|2|
Sa3S5fS0S0Vlo;Vw;A4A1S8Z0Vlo;A2S8S7Vlo;Vw;A2M0SbZ2Z3fA2A2S0S1S6Vlo;R1A2S8R1G0A2A2S1S2S5bS0A1M1S9bR2A1Sa4R2A1A3S2G1Sa8R2A1SacR2A1A3A2F_;Fx;F_;F_;F_;").
  Proof using HC HMI Hz V1.
    intros [D1 D2] Hlo Hhi x Hx. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & _). rewrite EZ in D1.
    unfold ranges_disjoint in D1, D2. cbn [fst snd] in D1, D2.
    apply FBV1; [lia | unfold in_zone; unfold IB in *; lia | unfold in_av; lia].
  Qed.

  Lemma cell_transfer c : ltac2:(tb__ "0|2|
S79VL;Sa4Vc;A3Sa3S74VL;Vc;A2M0A1Sd5U0S78Vc;A1A2S8Z0S66S0S0G0A3M1A2S8S7G1S68S0S0G0A3A2SbZ2Z3fA2A2S79VL;S9bVc;A3F_;F_;F_;F_;F_;").
  Proof using HC HMI Hz V1.
    intros Hc Hav Hw Hlo Hhi. unfold cell_range in *. cbn [fst snd] in Hlo, Hhi.
    pose proof (avoids_bytes _ _ Hav Hlo Hhi) as B.
    unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
      rewrite (proj1 (B (loc_addr L (mc_loc c)) ltac:(lia))). exact Hb.
    - intros j Hj. rewrite (proj1 (B (loc_addr L (mc_loc c) + Z.of_nat j) ltac:(lia))). exact (Hc j Hj).
  Qed.

  Lemma image_cell_span c : ltac2:(tb__ "0|2|
S97S6fVc;S75Vs;A1A3S1S8Z0S66S0S0S74VL;Vc;A2M0A3M1A2S8S7G1S68S0S0G0A3A2SbZ2Z3fA2A2A2F_;").
  Proof using HMI Hz.
    intros Hin. destruct (image_in_footprint s L c F_W F_L Hin) as (rg & Hrg & [I1 I2]).
    pose proof F_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Lemma footer_cell_span c : ltac2:(tb__ "0|2|
S97S6fVc;ScbVs;A1A3S1S8Z0S66S0S0S74VL;Vc;A2M0A3M1A2S8S7G1S68S0S0G0A3A2SbZ2Z3fA2A2A2F_;").
  Proof using HMI Hz.
    intros Hin. destruct (footer_in_footprint s L c F_W F_L Hin) as (rg & Hrg & [I1 I2]).
    pose proof F_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    assert (0 <= snd (cell_range L c)) by (unfold cell_range; cbn; lia). lia.
  Qed.

  Lemma Hng_s : ltac2:(tb__ "0|0|
S1cS2S5bS1cA1S2aS20Vam;S98A2A1S5eS1cR1A2A3S2S2fS30R2A1S26A3F_;Ff;").
  Proof using HC HMI. intros f Hf. rewrite F_sl in Hf. discriminate. Qed.
  Lemma Hng_s' : ltac2:(tb__ "0|0|
S1cS2S5bS1cA1S2aS20S9aS98A2A1S5eS1cR1A2A3S2S2fS30R2A1S26A3F_;Ff;").
  Proof using HC HMI Hz. intros f Hf. rewrite F_sl' in Hf. injection Hf as <-. reflexivity. Qed.

  Lemma old_cell_avoids c : ltac2:(tb__ "0|0|
S97S6fVc;S75Vs;A1A3S97S6fVc;S75S99A1A3S3S97S6fVc;Sa0A3A1Sa3S74VL;Vc;A2A1F_;F_;F_;").
  Proof using HC HMI Hz.
    intros Hin Hin' Hnew. split.
    - destruct (zone_image_addr f_s' L g f_am2 f_idx F_W' F_L' F_u' (proj1 F_idx) Hng_s' c Hin') as [Hown | D].
      + exfalso. apply Hnew. rewrite own_hdr_new in Hown. right. apply in_app_iff in Hown. apply in_app_iff.
        destruct Hown as [K|K]; [left; exact K | right; apply in_app_iff; left; exact K].
      + exact D.
    - destruct (pairwise_In_cases ranges_disjoint (cell_range L) (image f_s') c f_Cavail (image_cells_disjoint f_s' L F_W' F_L') Hin' Cavail_in) as [E|[D|D]].
      + exfalso. apply Hnew. left. symmetry. exact E.
      + rewrite Cavail_range in D. exact D.
      + rewrite Cavail_range in D. apply ranges_disjoint_sym. exact D.
  Qed.

  Lemma footer'_cases c : ltac2:(tb__ "0|0|
S97S6fVc;ScbS99A1A3S5S97S6fVc;Sa5A3S97S6fVc;ScbVs;A1A3A2F_;").
  Proof using HC HMI Hz.
    intros Hin. rewrite F_s' in Hin.
    destruct (upd_footer_In s g am f_am2 F_ND F_MT c Hin) as [H|H]; [right; exact H|].
    unfold group_footer_cells in H. destruct H as [<-|H].
    - right. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact F_um|]. left. reflexivity.
    - apply in_flat_map in H as [j [Hj H]]. apply In_zseq in Hj. change (am_last f_am2) with (am_last am) in Hj.
      rewrite (F_am2_slot j) in H by lia.
      destruct (j =? f_idx) eqn:Eji.
      + apply Z.eqb_eq in Eji. subst j. cbn [ss_fr] in H. left. exact H.
      + right. unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact F_um|]. cbn [snd].
        unfold group_footer_cells. right. apply in_flat_map. exists j. split; [apply In_zseq; lia|].
        destruct (ss_fr (nth_slot am j)) as [f|]; [|destruct H]. exact H.
  Qed.

  Lemma footer_avoids c : ltac2:(tb__ "0|0|
S97S6fVc;ScbVs;A1A3Sa3S74VL;Vc;A2A1F_;").
  Proof using HC HMI Hz.
    intros Hin. split.
    - destruct (zone_footer_addr s L g am f_idx F_W F_L F_u (proj1 F_idx) Hng_s c Hin) as [(f & Hf & _) | D]; [|exact D].
      rewrite F_sl in Hf. discriminate.
    - destruct F_area as (a & k & Ha & Hk & Eg & InA & Pa & Pa2 & Ezg & (rga & Hra & Hka)).
      destruct (In_footer_cells_inv s c Hin) as (g' & am' & Hg' & Hc).
      apply (used_metas_usedX s g' am' F_W) in Hg'.
      destruct (used_group_region [] None U0 s g' am' F_W Hg') as (rg' & Hr' & Hk' & Hl' & Ho' & Hext' & _).
      destruct (In_group_footer_cells [] None U0 s g' am' c F_W Hg' Hc) as (d & E & Hd & Hw & _).
      pose proof F_L as (_ & _ & PW & _).
      assert (Hne : (LMem (SP (prid (am_mem am')) 0), rg_len rg') <> (LMem a, PGSZ)).
      { intros X. injection X as Ea _. rewrite <- Ea in Hra. cbn [prid] in Hra. rewrite Hr' in Hra. injection Hra as <-. exact (Hka Hk'). }
      destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (footprint_region_In s _ _ Hr' Hk' Hl') InA Hne) as [D|D];
        unfold crange, loc_addr, ranges_disjoint in D; cbn [fst snd] in D;
        unfold cell_range, ranges_disjoint; rewrite E; cbn [fst snd]; unfold loc_addr; destruct (am_mem am') as [r o]; cbn [padd prid poff] in *;
        unfold addr_of, loc_addr in Ezg; destruct a as [ra oa]; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia.
  Qed.

  Theorem reprP_post : ltac2:(tb__ "0|0|
SccVL;S99S9bA3").
  Proof using HC HMI Hz V1 V2 V3.
    pose proof F_repr as [[HL0 [HI HR]] HF].
    split; [split; [exact F_L'|split]|].
    - apply Forall_forall. intros c Hin'.
      destruct (in_dec mcell_eq_dec c f_newcells) as [Hnew|Hnew]; [exact (newcells_hold c Hnew)|].
      destruct (image'_cases c Hin') as [Hnew'|Hold]; [exfalso; exact (Hnew Hnew')|].
      pose proof (image_cell_span c Hold) as [P1 P2].
      apply (cell_transfer c); [| apply (old_cell_avoids c Hold Hin' Hnew) | exact (image_cell_w s c Hold) | exact P1 | exact P2].
      exact (proj1 (Forall_forall _ _) HI c Hold).
    -
      intros x [(rg & Hrg & Hx) Hnu].
      rewrite F_s' in Hrg. change (footprint (upd_meta g (MUsed f_am2) s)) with (footprint s) in Hrg.
      destruct (malloc_blocks s n _ _ _ F_W (proj1 (proj1 HC)) F_y) as (l1 & l2 & EB1 & EB2 & _).
      assert (M0 : f_bv0 x <> None).
      { apply HR. split; [exists rg; split; [exact Hrg | exact Hx]|].
        intros (b & Hb & Hxb). apply Hnu. exists b. split; [|exact Hxb].
        change (user_blocks f_s') with (user_blocks f_s') . rewrite EB1. rewrite EB2 in Hb.
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
      pose proof F_L as (_ & _ & _ & POS). destruct (POS rg Hrg) as [Q1 Q2]. unfold crange in Q1, Q2. cbn [fst snd] in Q1, Q2.
      destruct (Z_le_dec (f_st - 3) x) as [A|A]; [destruct (Z_lt_dec x f_e) as [B|B]|].
      + apply FBV2; [lia | unfold in_zone; lia].
      + destruct (Z_le_dec (f_zg + 24) x) as [A2|A2]; [destruct (Z_lt_dec x (f_zg + 28)) as [B2|B2]|].
        * pose proof (newcells_hold f_Cavail (or_introl eq_refl)) as CH. unfold cell_holds, f_Cavail in CH. cbn [mc_val mc_loc mc_w] in CH.
          pose proof (f_equal fst Cavail_range) as R. unfold cell_range, f_Cavail in R. cbn [fst mc_loc] in R. rewrite R in CH.
          specialize (CH (Z.to_nat (x - (f_zg + 24))) ltac:(lia)). rewrite Z2Nat.id in CH by lia.
          replace (f_zg + 24 + (x - (f_zg + 24))) with x in CH by lia. rewrite CH. discriminate.
        * rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia) ltac:(unfold in_av; lia))). exact M0.
        * rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia) ltac:(unfold in_av; lia))). exact M0.
      + destruct (Z_le_dec (f_zg + 24) x) as [A2|A2]; [destruct (Z_lt_dec x (f_zg + 28)) as [B2|B2]|].
        * pose proof (newcells_hold f_Cavail (or_introl eq_refl)) as CH. unfold cell_holds, f_Cavail in CH. cbn [mc_val mc_loc mc_w] in CH.
          pose proof (f_equal fst Cavail_range) as R. unfold cell_range, f_Cavail in R. cbn [fst mc_loc] in R. rewrite R in CH.
          specialize (CH (Z.to_nat (x - (f_zg + 24))) ltac:(lia)). rewrite Z2Nat.id in CH by lia.
          replace (f_zg + 24 + (x - (f_zg + 24))) with x in CH by lia. rewrite CH. discriminate.
        * rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia) ltac:(unfold in_av; lia))). exact M0.
        * rewrite (proj1 (FBV1 x ltac:(lia) ltac:(unfold in_zone; lia) ltac:(unfold in_av; lia))). exact M0.
    - apply Forall_forall. intros c Hin'.
      destruct (footer'_cases c Hin') as [Hnew | Hold].
      + apply newcells_hold. right. apply in_app_iff. right. apply in_app_iff. right. exact Hnew.
      + pose proof (footer_cell_span c Hold) as [P1 P2].
        apply (cell_transfer c); [| apply (footer_avoids c Hold) | exact (footer_cells_w s c Hold) | exact P1 | exact P2].
        exact (proj1 (Forall_forall _ _) HF c Hold).
  Qed.

  Lemma W_place : ltac2:(tb__ "0|7|
S4S0S0S4S0S0S4S0S0S1S6S7R3ZdA2S9S9cZ3A2M0A2S1S6S7S9dZ4A2S7R3R2A2M1A2S1S5S6G1Sd2VC;A1M2A2S6Sd1VC;A1M3R3A2A2S1S6R1S9eA2S1S6S7S9eZ28A2S7R1Z1000M4A2M5A2S1S5S6G5G2A2S6G3R1A2A2S1S6G4R3A2S1S6G4R1A2S1S6G1Sd4VL;A1M6A2S1S6G5G6A2S1S8G6SbZ2Z3fA2A2S6G0S9dA2A2A2A2A2A2A2A2A2A2A2A2LA;A2Llen;A2LR;A2").
  Proof using HC HMI Hz.
    pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & (rg & Hrg & [RI1 RI2] & Erg)).
    destruct F_area as (a & k & Ha & Hk & Eg & InA & Pa & Pa2 & Ezg & _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HMI))))) as HV. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))))) as HLG.
    cbn [ma_s ma_L] in HV, HLG.
    destruct rg as [lc len]. cbn [fst] in Erg. subst lc.
    unfold crange, loc_addr in RI1, RI2. cbn [fst snd] in RI1, RI2.
    pose proof (extent_pos _ _ _ _ _ (inv_groups F_W g am F_u)) as EP.
    assert (Hlen : 0 <= len) by (unfold IB in RI2; lia).
    pose proof (fp_mem_range C L s vm _ _ HV HLG Hrg Hlen) as (M1 & M2 & M3).
    pose proof (fp_mem_range C L s vm _ _ HV HLG InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
    unfold addr_of, loc_addr in M1, M2, M3. unfold addr_of in A1, A2, A3.
    unfold addr_of in Ezg, Pa.
    exists (ly_reg L (prid (am_mem am)) + 0), len, (loc_addr L (LMem a)).
    assert (X3 : f_e <= f_zm + group_extent am) by (unfold group_extent, mf_stride, UNIT, IB in *; lia).
    clear Hsi2 EZ.
    unfold UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *.
    top_ranges.
    repeat split; lia.
  Qed.

  Lemma written_not_static x lo n0 : ltac2:(tb__ "0|1|
S1S6Sd2VC;A1Vlo;A2S6S7Vlo;Vn0;A2M0Sd1VC;A1A2A2S1S6Vlo;Vx;A2S8Vx;G0A2A2S1S1S6Z0Vx;A2S8Vx;SbZ2Z40A2A2A2S1S3Sa2Vx;A1A1S3SaaVx;A1A1A2A2F_;F_;").
  Proof using HC HMI HS Hz.
    intros Hlo Hx. pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg & Hceil).
    destruct W_place as (R & len & A & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    unfold in_zone, in_av. unfold PGSZ, UNIT in Hpg, Hceil.
    split; [lia|]. split; lia.
  Qed.

  Lemma statics_post : ltac2:(tb__ "0|0|
Sd3VC;Sa8S9bA3").
  Proof using HC HMI HS Hz V1.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))) as ST. cbn [ma_s ma_L] in ST. fold f_rv0 f_bv0 in ST.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (Ilibc & Irep & Isc & Ismall & Imed & Ictz & Igot & Iguard & Ilock & Ictx & Ierr & Hpg & Hceil).
    assert (RV : forall lo n0, mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> forall x, lo <= x < lo + n0 -> f_rv1 x = f_rv0 x /\ f_bv1 x = f_bv0 x).
    { intros lo n0 Hlo x Hx. destruct (written_not_static x lo n0 Hlo Hx) as (X1 & X2 & X3).
      destruct (FBV1 x X1 X2 X3) as [B R]. auto. }
    assert (HR : forall a0 w v lo n0, holds f_rv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds f_rv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj1 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    assert (HB : forall a0 w v lo n0, holds f_bv0 a0 w v -> mc_img_lo C <= lo /\ lo + n0 <= mc_img_hi C -> lo <= a0 -> a0 + Z.of_nat w <= lo + n0 -> holds f_bv1 a0 w v).
    { intros a0 w v lo n0 Hh Hlo Ha Hw j Hj. rewrite (proj2 (RV lo n0 Hlo (a0 + Z.of_nat j) ltac:(lia))). exact (Hh j Hj). }
    destruct ST as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & (gd & T9 & T10)).
    unfold statics_ok, mc_need_locks, mc_page_size in *.
    split; [apply (HR _ _ _ _ _ T1 Ilibc); cbn; lia|].
    split; [apply (HR _ _ _ _ _ T2 Ilibc); cbn; lia|].
    split; [apply (HR _ _ _ _ _ T3 Irep); cbn; lia|].
    split; [apply (HB _ _ _ _ _ T4 Ilock); cbn; lia|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Isc (mc_size_classes C + Z.of_nat j) ltac:(lia))); exact (T5 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Ismall (mc_small_cnt_tab C + Z.of_nat j) ltac:(lia))); exact (T6 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Imed (mc_med_cnt_tab C + Z.of_nat j) ltac:(lia))); exact (T7 j Hj)|].
    split; [intros j Hj; rewrite (proj1 (RV _ _ Ictz (mc_ctz_tab C + Z.of_nat j) ltac:(lia))); exact (T8 j Hj)|].
    exists gd. split.
    - apply (HR _ _ _ _ _ T9 Igot); cbn; lia.
    - apply (HR _ _ _ _ _ T10 Iguard); cbn; lia.
  Qed.

  Theorem minv_post : ltac2:(tb__ "0|0|
Sd9VC;SdaS99VL;A2Vrd1;Vwok1;Vvm;A5").
  Proof using HC HMI HS Hz V1 V2 V3.
    pose proof HMI as (_ & HB & HC0 & _ & HV & _ & HA & HLG & HIMG & HMW & HRCH). cbn [ma_s ma_L] in HB, HC0, HV, HA, HLG, HRCH.
    split; [exact F_W'|]. split; [rewrite F_s'; exact HB|]. split; [exact HC0|].
    split; [exact reprP_post|]. split; [rewrite F_s'; exact HV|]. split; [exact statics_post|].
    split; [|split; [exact HLG|]; split; [exact HIMG|]; split; [exact HMW|];
              rewrite F_s'; apply (reach_ok_upd s g am f_am2 F_MT); [reflexivity | cbn; lia | exact HRCH]].
    cbn [ma_s]. rewrite F_s'. change (st_init_done (upd_meta g (MUsed f_am2) s)) with (st_init_done s).
    intros Hf. exfalso.

    destruct (inv_ctx F_W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit & _).
    destruct (Hinit Hf) as (Hm & _). pose proof F_MT as M. unfold MT in M. rewrite Hm in M. cbn in M. discriminate.
  Qed.

  Lemma cell_owned c x : ltac2:(tb__ "0|2|
S5S97S6fVc;S75Vs;A1A3S97S6fVc;ScbVs;A1A3A2S1S6S66S0S0S74VL;Vc;A2M0A3M1Vx;A2S8Vx;S7G1S68S0S0G0A3A2A2A2S80VL;Vs;Vx;A3F_;F_;").
  Proof using HMI Hz.
    intros Hc Hx. split.
    - destruct Hc as [Hc|Hc].
      + destruct (image_in_footprint s L c F_W F_L Hc) as (rg & Hrg & [I1 I2]). exists rg. split; [exact Hrg|]. unfold crange in I1, I2. cbn [fst snd] in I1, I2. lia.
      + destruct (footer_in_footprint s L c F_W F_L Hc) as (rg & Hrg & [I1 I2]). exists rg. split; [exact Hrg|]. unfold crange in I1, I2. cbn [fst snd] in I1, I2. lia.
    - intros (b & Hb & Hxb).
      assert (D : ranges_disjoint (cell_range L c) (block_range L b)).
      { destruct Hc as [Hc|Hc]; [exact (image_outside_user_blocks s L c b F_W F_L Hc Hb) | exact (footer_outside_user_blocks s L c b F_W F_L Hc Hb)]. }
      unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. lia.
  Qed.

  Theorem slot_owned x : ltac2:(tb__ "0|0|
S1S6S9S9cZ4A2Vx;A2S8Vx;S9dA2A2S80VL;Vs;Vx;A3F_;").
  Proof using HC HMI Hz.
    intros Hx. pose proof F_geom as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & [Hsi1 Hsi2] & (rg & Hrg & [RI1 RI2] & Erg)).
    destruct (Z.eq_dec x (f_st - 4)) as [->|Hne].
    -
      pose proof (proj1 (slot_start_cells s g am f_idx F_W F_um (proj1 F_idx))) as C1.
      apply (cell_owned _ _ (or_introl C1)). unfold cell_range, f_st, addr_of, loc_addr. cbn [mc_loc mc_w fst snd].
      destruct (slot_start am f_idx); cbn [padd]. lia.
    - split.
      + exists rg. split; [exact Hrg|]. unfold crange in RI1, RI2. cbn [fst snd] in RI1, RI2.
        unfold group_extent, mf_stride, UNIT, IB in *. lia.
      + intros ([q m] & Hb & Hxb). cbn [fst snd] in Hxb.
        destruct (zone_block_addr s L g am f_idx F_W F_L F_u (proj1 F_idx) Hng_s q m Hb) as [(f & Hf & _) | D].
        * rewrite F_sl in Hf. discriminate.
        * rewrite EZ in D. unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. unfold UNIT, IB in *. lia.
  Qed.

  Lemma meta_cells_old : ltac2:(tb__ "0|3|
S1S97S6fS72S70S19Vg;S88A2A1U8M0S8bS2eVam;A1A1A3S75Vs;A1M1A3S1S97S6fS72S70S19Vg;S7eA2A1U4M2S73S1aVam;A1A1A3G1A3S1S97S6fS72S70S19Vg;S87A2A1G2S73S2cVam;A1A1A3G1A3S1S97S6fS72S70S19Vg;S86A2A1G0S73S92Vam;A1A1A3G1A3S1S97S6fS72S70S19Vg;S8aA2A1G0S82S4bVam;A1A1A3G1A3S97S6fS72S70S19Vg;S89A2A1G0S82S4aVam;A1A1A3G1A3A2A2A2A2A2").
  Proof using HC HMI Hz.
    assert (K : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> In c (image s)).
    { intros c Hc. exact (meta_cells_in_image s g am c F_W F_u Hc). }
    unfold meta_slot_cells in K. repeat split; apply K; cbn; tauto.
  Qed.

  Theorem blocks_post : ltac2:(tb__ "0|2|
S4S67S5dS16S0A2M0A1M1G1S4G1G1S1S2G1S85S99A1S63G0R2S64G0S5fS16S0SbdVs;Vn;Vam;Vz;A4Vn;A4R1A3A3A3S2G1S85Vs;A1S63G0R2R1A3A3A2Ll2;A2Ll1;A2").
  Proof using HC HMI Hz.
    destruct (malloc_blocks s n _ _ _ F_W (proj1 (proj1 HC)) F_y) as (l1 & l2 & E1 & E2 & _). exists l1, l2. auto.
  Qed.
End Gap.
