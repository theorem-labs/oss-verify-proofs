(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "mul"; "land"; "sub"; "div"; "eqb"; "ltb"; "of_nat"; "of_N"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "sx32"; "zalu"; "zle"; "zsublist"; "zsupported"; "toS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView.BV.Blk"; "rho1"; "zA"; "pS"; "zG"; "zMem"; "h16"; "zP"; "G0"; "bits"; "h3"; "n"; "p"; "sec"; "st"; "sti"; "sz"; "xv"; "vals"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "eval"; "rw"; "sv"; "sprop"; "valuation"; "SLit"; "SAlu"; "rl"; "rm"; "SExt"; "holds"; "ranges_disjoint"; "SAluW"; "SLBytes"; "SMd"; "enc_bytes"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "cons"; "pair"; "true"; "nat"; "option"; "Some"; "fst"; "length"; "nil"; "false"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "MCell"; "alloc_owned"; "VZ"; "loc_addr"; "image"; "CTX_SIZE"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "VP"; "VSec"; "frame_ptr"; "frames"; "mc_loc"; "mc_w"; "region_of"; "CTX_secret"; "LCtx"; "byteview"; "cell_holds"; "get_meta_asserts"; "group_extent"; "hdr_byte3"; "hdr_off16"; "ly_ctx"; "ly_reg"; "user_blocks"; "view_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "padd"; "PGSZ"; "am_sc"; "am_maplen"; "region"; "am_avail"; "am_freed"; "ameta"; "frame"; "am_mem"; "UNIT"; "am_last"; "rg_len"; "size_classes"; "znth"; "prid"; "rg_live"; "AREA_HDR"; "FUser"; "IB"; "METAS_PER_AREA"; "META_SIZE"; "RkMap"; "SP"; "astate"; "fkind"; "fr_kind"; "fr_n"; "fr_off"; "poff"; "rg_kind"; "rkind"; "st_areas"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "mc_ctx"; "size_classes_bytes"; "mc_img_hi"; "mc_img_lo"; "mc_replaced"; "addr_of"; "C_P"; "C_U"; "byteview_of"; "owned"; "vm_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "d_range"; "carvable"; "bv_val"; "bv_mem"; "L_SIZECLASSES"; "bv_facts"; "bv_g"; "set_rws"; "MASK_PAGE"; "block_view_stmt"; "bv_area"; "bv_ctx"; "bv_grp"; "bv_hdr"; "bv_meta"; "GM_A0"; "GM_A1"; "GM_B"; "bv_bit"; "bv_bits"; "bv_facts_common"; "bv_facts_direct"; "bv_facts_map"; "bv_facts_nomap"; "bv_facts_sized"; "bv_idx"; "bv_last"; "bv_maplen"; "bv_ram"; "bv_sc"; "bv_scsize"; "d_pairwise"; "gm_variant"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_ADD"; "aluop"; "M_MUL"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "owned_mapped"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv";
"mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocLaws ClientLaws MallocFooter MallocWfRepr MallocWfMain
  FpLaws FreeQuickModel Contract Glue ReprGlue ZEval ZBits BlockViewIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma size_classes_bytes_range : ltac2:(tb__ "0|0|
S94S0S0S3S8Z0R1A2SaR1Z100A2A2Lb;S99A3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool size_classes_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma zl_table : ltac2:(tb__ "0|2|
S4S47S0A1S95S31Q8M0A1M1S0G1S32G0R1A2Lb;S95S0G1S30G0A1S99A4A4S99A3").
Proof.
  rewrite map_map. rewrite <- (map_id size_classes_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) size_classes_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.
Lemma table_u16 : ltac2:(tb__ "0|1|
S0S3S8Z0R1A2SaR1Z30A2A2S4S0S1aS1bSdZ2M0R2A2G0S99A3A1S81R2S80A2A3F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => zle (zsublist (2 * sc) 2 size_classes_bytes) =? znth sc size_classes) 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.
Lemma znth_size_classes_range : ltac2:(tb__ "0|1|
S0S3S8Z0R1A2SaR1Z30A2A2S3S8Z1S81R2S80A2M0A2S8G0Z1fffA2A2F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => (1 <=? znth sc size_classes) && (znth sc size_classes <=? 8191))%bool 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma m64 : ltac2:(tb__ "0|1|
S0S3S8Z0R1A2SaR1ScZ2Z40A2M0A2A2S4S0SbR2G0A2R2A3F_;Fz;").
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma set_rws_rm : ltac2:(tb__ "0|0|
S38S47S46S1S0A2A1S4S31Q40A1S4cS31Q8A1A1F_;S3cSaaR2R1A2A1S3cR2A1A3Fl;Fr;").
Proof. intros r l. induction l as [|[iz z] t IH]; cbn [set_rws]; [reflexivity|]. rewrite rho_set_rw_rm. exact IH. Qed.
Lemma set_rws_rl : ltac2:(tb__ "0|0|
S38S47S46S1S0A2A1S4S1S47S31Q8A1A1F_;S3bSaaR2R1A2A1S3bR2A1A3Fl;Fr;").
Proof. intros r l. induction l as [|[iz z] t IH]; cbn [set_rws]; [reflexivity|]. rewrite rho_set_rw_rl. exact IH. Qed.
Lemma set_rws_rw_other : ltac2:(tb__ "0|1|
S38S47S46S1S0A2M0A1S1S7S44S1R1S95G0S1S4eS1S0A2R2A4A3A1S4S31Q40A1S35SaaR4R3A2R2A2S35R4R2A2A3F_;Fv;Fl;Fr;").
Proof.
  intros r l v. induction l as [|[iz z] t IH]; cbn [set_rws map fst]; intros Hn; [reflexivity|].
  rewrite rho_set_rw_other by (intros ->; apply Hn; left; reflexivity). apply IH. intros X. apply Hn. right. exact X.
Qed.
Lemma bv_val_rm : ltac2:(tb__ "0|0|
S38S47S0A1S4S31Q40A1S4cS31Q8A1A1F_;S3cSa5R2R1A2A1S3cR2A1A3Fvs;Fr;").
Proof. intros. unfold bv_val. rewrite rho_set_rl_rm. apply set_rws_rm. Qed.
Lemma bv_val_rl_other : ltac2:(tb__ "0|0|
S38S47S0A1S1S7S4S1R1Sa7A3A1S4S47S31Q8A1A1S3bSa5R4R3A2R2A2S3bR4R2A2A3F_;Fl;Fvs;Fr;").
Proof. intros. unfold bv_val. rewrite rho_set_rl_other by assumption. rewrite set_rws_rl. reflexivity. Qed.
Lemma bv_val_rl_1 : ltac2:(tb__ "0|2|
S38S47S0A1S4S47S31Q8M0A1M1A1S3bSa5R2R1A2Sa7A2S95S0G1S30G0A1S99A4A3Fvs;Fr;").
Proof. intros. unfold bv_val. apply rho_set_rl_at. Qed.
Lemma bv_val_rw_other : ltac2:(tb__ "0|0|
S38S47S0A1S1S4S4bS4fS0R2A2U7A3S6ScbR2P82A2ScbP88R2A2A2S4S31Q40A1S35Sa5R5R4A2R3A2S35R5R3A2A3F_;F_;Fv;Fvs;Fr;").
Proof.
  intros r vs v Hlen Hv. unfold bv_val. rewrite rho_set_rl_rw. apply set_rws_rw_other.
  destruct vs as [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|]]]]]]]]; try discriminate Hlen. cbn. unfold bv_vars. cbn. intros X. lia.
Qed.

Lemma rw_bv_val : ltac2:(tb__ "0|3|
S38S0S0S0S0S0S0S0S3S4S31Q40M0A1M1S35Sa5R8S48S0R7S48S0R6S48S0R5S48S0R4S48S0R3S48S0R2S48S0R1S50S0A1A3A3A3A3A3A3A3A2M2P82A2S30G0R7A2A3S3S4G1S35G2P83A2S30G0R6A2A3S3S4G1S35G2P84A2S30G0R5A2A3S3S4G1S35G2P85A2S30G0R4A2A3S3S4G1S35G2P86A2S30G0R3A2A3S3S4G1S35G2P87A2S30G0R2A2A3S4G1S35G2P88A2S30G0R1A2A3A2A2A2A2A2A2Fv6;Fv5;Fv4;Fv3;Fv2;Fv1;Fv0;Fr;").
Proof. intros. repeat split; reflexivity. Qed.

Lemma user_block_frame : ltac2:(tb__ "0|2|
S8bS72S0S44S46S72S0A2S49S72S0R2R1A4S70R3A1A3S5S72S72S5S7aS7aS5S0S0S5S7bS7bS3S44S46S46S46S72S7aA2M0S0A2M1S7bA2S49G1S7bS49G0S0S49S72S7aR4R3A4R2A4R1A4S62R8A1A3S3S4S8cS8dR1A1S85A3S3S4S72R7S61R3R2R1A3A3S4S0R6S8eR1A1A3A2A2A2Lfr;A2Li;A2Lam;A2Lg;A2F_;Fn;Fq;Fs;").
Proof.
  intros s q n Hin. unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]]. cbn [snd] in Hin.
  apply in_flat_map in Hin as [i [Hi Hin]].
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Hsl; [|destruct Hin].
  destruct (fr_kind fr) eqn:Hk; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
  exists g, am, i, fr. split; [|split; [exact Hk | split; reflexivity]].
  unfold frames. apply in_flat_map. exists (g, am). split; [exact Hg|]. apply in_flat_map. exists i. split; [exact Hi|].
  rewrite Hsl. left. reflexivity.
Qed.

Section BV.
Variable segs : list Segment.
Variable C : mconsts.
Hypothesis HSI : statics_in_image C.

Hypothesis Hrc : ltac2:(tb__ "0|2|
S6S8S9S98VC;A1M0S5aA2S9cVC;A1M1A2S8S9G1Z4A2G0A2A2").

Section Blk.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (vm : VmMaps) (m : word -> option byte) (rho : valuation) (pv : positive).
Hypothesis HMI : ltac2:(tb__ "0|0|
Sd0VC;Sd1Vs;VL;A2Sc4Vsegs;Vm;A2Sc5Vsegs;Vm;A2Vvm;A5").
Hypothesis Hfr : ltac2:(tb__ "0|2|
S44S46S46S46S72S7aA2M0S0A2M1S7bA2S49G1S7bS49G0S0S49S72S7aVg;Vam;A4Vi;A4Vfr;A4S62Vs;A1A3").
Hypothesis Hkind : fr_kind fr = FUser.
Definition p : sptr := ltac2:(tb__ "0|0|
S61Vam;Vi;Vfr;A3").
Definition zP : Z := addr_of L p.
Hypothesis Hp : ltac2:(tb__ "0|0|
S4S0S32Q40S35Vrho;Vpv;A2A2S24A3").
Hypothesis Hpv : (pv < 130)%positive.

Let bv0 : ltac2:(tb__ "0|0|
S68") := ltac2:(tb__ "0|0|
Sa0Sc4Vsegs;Vm;A2Sc5Vsegs;Vm;A2A2").
Lemma HW : WF s. Proof using HMI Hrc. pose proof HMI as X. unfold MInv in X. cbn zeta in X. tauto. Qed.
Lemma HC : ltac2:(tb__ "0|0|
S4S0S6eVL;A1S98VC;A1A3"). Proof using HMI Hrc. pose proof HMI as X. unfold MInv in X. cbn zeta in X. tauto. Qed.
Lemma HLok : layout_ok L s. Proof using HMI Hrc. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. tauto. Qed.
Lemma HI : ltac2:(tb__ "0|0|
S94S53S69VL;Vbv0;A2S59Vs;A1A3"). Proof using HMI Hrc. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. unfold bv0. tauto. Qed.
Lemma HO : ltac2:(tb__ "0|0|
ScfVL;Vs;Vbv0;A3"). Proof using HMI Hrc. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. unfold bv0. tauto. Qed.
Lemma HV : ltac2:(tb__ "0|0|
Sa2VL;Vs;Vvm;A3"). Proof using HMI Hrc. pose proof HMI as X. unfold MInv in X. cbn zeta in X. tauto. Qed.
Lemma HLG : ledger_ok C vm. Proof using HMI Hrc. pose proof HMI as X. unfold MInv in X. cbn zeta in X. tauto. Qed.
Lemma FFx : ltac2:(tb__ "0|0|
SceVs;Vg;Vam;Vi;Vfr;A5"). Proof using HMI Hfr Hrc. exact (frame_facts_of s g am i fr HW Hfr). Qed.

Definition zMem : Z := ltac2:(tb__ "0|0|
S9dVL;S7cVam;A1A2").
Definition zG : Z := addr_of L g.
Definition h3 : Z := ltac2:(tb__ "0|0|
S6cVam;Vi;Vfr;A3").
Definition h16 : Z := ltac2:(tb__ "0|0|
S6dVam;Vi;Vfr;A3").
Definition bits : Z := meta_bits am.
Definition sec : Z := ly_sec L.

Variables (a : sptr) (k : Z).
Hypothesis Harea : ltac2:(tb__ "0|2|
S3S44S72Va;S93Vs;A1A3S3S3S8Z0Vk;A2SaVk;S87A2A2S3S4S72Vg;S73Va;S9S84SdS88Vk;A2A2A2A3S3S44S53S55S54Va;A1U8M0S60A3S59Vs;A1M1A3S44S53S55S67S66A1G0S60A3G1A3A2A2A2A2").
Definition zA : Z := addr_of L a.

Lemma GM : ltac2:(tb__ "0|5|
S3S44S53S55S54S73S29N4A2A1U1M0S57Z0A1A3S59Vs;A1M1A3S3S44S53S55S54S73S29N3A2A1G0S57S27A1A3G1A3S3S44S53S55S54S73S29N2A2A1U2S57S23A1A3G1A3S3S44S53S55S54S7cVam;A1M2A1U8M3S5fVg;A1A3G1A3S3S44S53S55S54S73Vg;S5eA2A1G3S5fG2A1A3G1A3S3S44S53S55S54S73Vg;S5bA2A1U4M4S57S78Vam;A1A1A3G1A3S3S44S53S55S54S73Vg;S5dA2A1G4S57S79Vam;A1A1A3G1A3S3S44S53S55S54S73Vg;S5cA2A1G3S57S26A1A3G1A3S3S4S72S73S29SfSdS15S7dA1S23A2S7dA2A2G2A3S3S4S0SeS27Z1fA2Vi;A3S4S45S6aS29G2S71Vs;Vg;Vam;Vi;Vfr;A5A3S4aA3A2A2A2A2A2A2A2A2A2A2").
Proof using HMI Hfr Hrc.
  pose proof (get_meta_ok s g am i fr HW Hfr) as X. cbn zeta in X. fold p in X.
  destruct X as (C4 & C3 & C2 & CG & CM & CA & CF & CB & BASE & _ & IDX & ASR & _).
  repeat (split; [assumption|]). exact ASR.
Qed.

Lemma Hareg : ltac2:(tb__ "0|0|
S5S4bS4bS5S0S0S5S77S77S3S4S72Va;S8aR3R2A2A3S3S4S0SbR2S74A2Z0A3S3S8S74R2A2S3S4S4cS77A1S65Vs;R3A2S4dS77R1A2A3S3S4S45S83R1A1S4aA3S8S9R2S74A2S7fR1A1A2A2A2A2A2A2Lrga;A2Lo;A2Lr;A2").
Proof using HMI Harea Hrc.
  destruct Harea as (Ha & _). destruct (proj1 (proj2 (inv_areas HW)) a Ha) as (r & o & rga & E & Ho & Hpo & Hr & Hl & Hfit & _).
  exists r, o, rga. repeat (split; [assumption|]). exact Hfit.
Qed.
Lemma HzA : ltac2:(tb__ "0|1|
S3S8S74S1fA2S3S8S9S1fS74A2M0S97VL;A1A2S3S4S0SbS1fS74A2Z0A3S6S8G0S9bVC;A1A2S8S9aVC;A1S1fA2A2A2A2A2").
Proof using HMI Harea Hrc pv.
  destruct Harea as (Ha & _).
  assert (HEa : In (LMem a, PGSZ) (footprint s)).
  { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. split; [reflexivity | exact Ha]. }
  pose proof (fp_mem_range C L s vm a PGSZ HV HLG HEa ltac:(unfold PGSZ; lia)) as (G1 & G2 & G3). fold zA in G1, G2, G3. unfold zA, addr_of in *.
  destruct Hareg as (r & o & rga & E & Ho & _ & Hr & Hl & _).
  pose proof (proj1 (proj2 HLok) r rga Hr Hl) as AL. rewrite E in *. unfold loc_addr in *. cbn [prid poff] in *.
  split; [lia|]. split; [lia|]. split; [|lia]. rewrite Z.add_mod, AL, Ho by (unfold PGSZ; lia). reflexivity.
Qed.

Definition G0 : Z := ltac2:(tb__ "0|0|
S6fVL;S82S7cVam;A1A1A2").
Lemma Hgrp : ltac2:(tb__ "0|6|
S5S77S77S3S4S4cS77A1S65Vs;S82S7cVam;A1M0A1A2S4dS77R1A2A3S3S4S92S91R1A1S89A3S3S4S45S83R1A1S4aA3S3S8Z0M1S90G0A1M2A2S3S8S9S9G2S6bVam;A1A2S86A2S7fR1A1M3A2S3SaG1S76Vam;A1M4A2S3S4S0G2G1A3S4S0S7fR2A1SdG4S74A2A3A2F_;S3S8S74S25A2S3S8S9S25G3A2M5S97VL;A1A2S3S4S0SbS25S74A2G1A3S3S6S8G5S9bVC;A1A2S8S9aVC;A1S25A2A2S4S0S22S9S25G2A2A3A2A2A2A2A2A2A2A2A2A2Lrgm;A2").
Proof using HMI Hfr Hpv Hrc.
  destruct (ff_region _ _ _ _ _ FFx) as (rg & Hr & Hk & Hl & Ho & He & Hm).
  exists rg. repeat (split; [assumption|]).
  pose proof (footprint_region_In s _ rg Hr Hk Hl) as HEg.
  assert (LEN : 0 <= rg_len rg). { pose proof (ff_stride_pos _ _ _ _ _ FFx). pose proof (ff_last _ _ _ _ _ FFx). unfold group_extent, UNIT, IB in He. nia. }
  pose proof (fp_mem_range C L s vm _ _ HV HLG HEg LEN) as (G1 & G2 & G3). unfold addr_of, loc_addr in G1, G2, G3. cbn [prid poff] in G1, G2, G3.
  pose proof (proj1 (proj2 HLok) _ rg Hr Hl) as AL. unfold G0, zMem, addr_of, loc_addr. destruct (am_mem am) as [r o]. cbn [prid poff] in *.
  rewrite Z.add_0_r in *. repeat split; lia.
Qed.
Lemma Hctx : ltac2:(tb__ "0|4|
S3S8S74S98VC;A1M0A2S3S8S9G0S5aA2S9aVC;A1M1A2S3S8S9bVC;A1M2G0A2S3S8S9G1S7dA2S97VL;A1A2S3S8G2S9cVC;A1M3A2S8S9G3Z4A2G1A2A2A2A2A2A2").
Proof using HSI pv. pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. pose proof (topL_range L). lia. Qed.

Definition st : Z := stride_of am.
Definition sti : Z := st * i.
Definition n : Z := fr_n fr.

Lemma R_all : ltac2:(tb__ "0|12|
S3S3S8Z0M0Vi;A2S8Vi;S7eVam;A1M1A2A2S3S3S8G0G1A2S8G1Z1fA2A2S3S3S8G0S8fVfr;A1M2A2S8G2ZffA2A2S3S8G0S28A2S3S8S9SdZ10M3G2A2M4S28A2SfS2bZ4A2A2S3S3S8G0S23A2S8S23ZffffA2A2S3S4S0SdG3S23A2M5S9S2cG4A2A3S3S8G3S2bA2S3S8G0S2cA2S3S8G0S76Vam;A1M6A2S3S3S8G0S78Vam;A1M7A2SaG7ScZ2M8Z20M9A2MaA2A2S3S3S8G0S79Vam;A1MbA2SaGbGaA2A2S3S6S3S8G0S75Vam;A1McA2SaGcZ30A2A2S3S4S0GcZ3fA3S3S4S0G1G0A3S8Z1MdG6A2A2A2A2S3S4S0S24S9S9S9S22G3A2MeS2cA2G4A2A3S3S4S0S22SfSfS24G5A2G3A2A3S3S8Z1000MfS22A2S3S8S9GeSdS2bS9G1GdA2A2M10A2S97VL;A1M11A2S3S8G11Z7fffff800000A2S3S8GfS1fA2S3S8S9S1fGfA2G11A2S3S4S0SbS1fGfA2G0A3S3S4S0S21S9S9S1fZ18A2SdZ28Vk;A2A2A3S3S3S8G0Vk;A2SaVk;Z65A2A2S3S3S8G0S27A2S8S27ZbfA2A2S3S4S0S26S9S9S9G1G9A2SdZ40GcA2A2SdGfG6A2A2A3S3SaG6ScG8Z23A2A2S8S9S2cS2bA2G10A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HMI Harea Hfr Hkind Hpv Hrc.
  pose proof FFx as F. destruct F as [Fu FMT Fi Fsl Flast Fn Foff Ffit Fh16 Fav Ffr Favi Ffri Fml Fsp Fs16 Fm16 Fsc Fext Freg Far Finit].
  pose proof GM as (_ & _ & _ & _ & _ & _ & _ & _ & BASE & _ & _).
  pose proof Hgrp as (rgm & _ & _ & _ & Ho & He & Hm & G1 & G2 & _ & _ & EM).
  pose proof HzA as (A1 & A2 & A3 & _). destruct Harea as (_ & Hk & Hg & _).
  assert (EP : zP = zMem + 16 + sti + 16 * fr_off fr).
  { unfold zP, zMem, p, frame_ptr, slot_start, addr_of, loc_addr, sti, st. destruct (am_mem am) as [r o]. cbn [padd]. unfold UNIT. lia. }
  assert (EB : zMem = zP - 16 * h16 - 16).
  { unfold zMem, zP, addr_of. rewrite <- BASE. unfold loc_addr, p, frame_ptr, slot_start. destruct (am_mem am) as [r o]. cbn [padd]. unfold UNIT, h16. lia. }
  assert (EG : zG = zA + 24 + 40 * k).
  { unfold zG, zA, addr_of, loc_addr. rewrite Hg. destruct a as [r o]. cbn [padd]. unfold AREA_HDR, META_SIZE. lia. }
  assert (H3 : 0 <= h3 <= 191).
  { unfold h3, hdr_byte3. rewrite Hkind. unfold rsv_code. destruct (5 <=? _) eqn:E5; [apply Z.leb_le in E5 | apply Z.leb_gt in E5]; unfold UNIT, IB in *; lia. }
  assert (ML : am_maplen am < 2 ^ 35).
  { destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos|]; [|lia]. destruct (Hm Hpos) as [_ Hlen]. top_ranges. unfold PGSZ in *. lia. }
  assert (STI : 0 <= sti /\ sti + st <= st * (am_last am + 1)).
  { unfold sti, st. split; [apply Z.mul_nonneg_nonneg; lia|].
    replace (stride_of am * (am_last am + 1)) with (stride_of am * am_last am + stride_of am) by lia.
    assert (stride_of am * i <= stride_of am * am_last am) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  unfold group_extent, UNIT, IB, PGSZ, METAS_PER_AREA in *. fold st in He. rewrite EM in *.
  top_ranges. unfold n, st, sti, h16, bits, meta_bits in *.
  repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma HzP16 : zP mod 16 = 0.
Proof using HMI Harea Hfr Hkind Hpv Hrc.
  pose proof R_all as R. pose proof Hgrp as (rgm & _ & _ & _ & _ & _ & _ & _ & _ & AL & _ & EM).
  pose proof (ff_mem16 _ _ _ _ _ FFx) as M. pose proof (ff_stride16 _ _ _ _ _ FFx) as S16. fold st in S16.
  assert (E : zP = G0 + poff (am_mem am) + 16 + sti + 16 * fr_off fr) by lia. rewrite E. unfold sti.
  unfold PGSZ in AL. apply Z.mod_divide in M; [|lia]. apply Z.mod_divide in S16; [|lia]. apply Z.mod_divide in AL; [|lia].
  destruct M as [q1 H1]. destruct S16 as [q2 H2]. destruct AL as [q3 H3]. rewrite H1, H2, H3.
  replace (q3 * 4096 + q1 * 16 + 16 + q2 * 16 * i + 16 * fr_off fr) with ((q3 * 256 + q1 + 1 + q2 * i + fr_off fr) * 16) by lia.
  apply Z_mod_mult.
Qed.

Definition vals : list Z := ltac2:(tb__ "0|0|
S48S0S27S48S0S23S48S0S21S48S0S78Vam;A1S48S0S79Vam;A1S48S0S26S48S0SbS2aScZ2Z40A2A2S50S0A1A3A3A3A3A3A3A3").
Definition rho1 : valuation := bv_val rho vals.
Let zr1 := zr_of rho1.
Let zl1 := zl_of rho1.

Lemma u64 : ltac2:(tb__ "0|1|
S0S3S8Z0R1A2SaR1ScZ2Z40A2A2A2S4S0S32Q40M0S30G0R2A2A2R2A3F_;Fz;").
Proof using pv zl1 zr1. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma zr1_pv : zr1 pv = zP.
Proof using Hp Hpv zl1. unfold zr1, zr_of, rho1. rewrite bv_val_rw_other by (try reflexivity; lia). exact Hp. Qed.
Lemma zr1_vals : ltac2:(tb__ "0|0|
S3S4S0Vzr1;P82A1S27A3S3S4S0Vzr1;P83A1S23A3S3S4S0Vzr1;P84A1S21A3S3S4S0Vzr1;P85A1S78Vam;A1A3S3S4S0Vzr1;P86A1S79Vam;A1A3S3S4S0Vzr1;P87A1S26A3S4S0Vzr1;P88A1SbS2aScZ2Z40A2A2A3A2A2A2A2A2A2").
Proof using HMI Harea Hfr Hkind Hpv Hrc zl1.
  pose proof R_all as R. unfold zr1, zr_of, rho1, vals.
  destruct (rw_bv_val rho h3 h16 zG (am_avail am) (am_freed am) bits (sec mod 2 ^ 64)) as (E0 & E1 & E2 & E3 & E4 & E5 & E6).
  rewrite E0, E1, E2, E3, E4, E5, E6, !u64; [repeat split; reflexivity | apply Z.mod_pos_bound; lia | lia..].
Qed.
Lemma zl1_1 : ltac2:(tb__ "0|0|
S4S47S0A1Vzl1;Sa7A1S99A3"). Proof using L am fr g i rho. unfold zl1, zl_of, rho1. rewrite bv_val_rl_1. apply zl_table. Qed.

Definition pS : sv := SVar pv.
Ltac zfact := cbn [zholds zcond].
Lemma ze_var : ltac2:(tb__ "0|0|
S1S4S0S16Vzr1;Vzl1;S33R1A1A3SbVzr1;R1A1ScZ2Z40A2A2A3Fj;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S0S4S0S16Vzr1;Vzl1;S39R1A1A3SbR1ScZ2Z40A2A2A3Fz;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
Sc8S36S36S4S0S16Vzr1;Vzl1;S3aR3R2R1A3A3S19Z40R3S16Vzr1;Vzl1;R2A3S16Vzr1;Vzl1;R1A3A4A3Fy;Fx;Fop;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
Sc8S36S36S4S0S16Vzr1;Vzl1;S40R3R2R1A3A3S18S19Z20M0R3SbS16Vzr1;Vzl1;R2A3ScZ2G0A2M1A2SbS16Vzr1;Vzl1;R1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S36S36S4S0S16Vzr1;Vzl1;S42Sc9R2R1A3A3SbSdS16Vzr1;Vzl1;R2A3S16Vzr1;Vzl1;R1A3A2ScZ2Z40A2A2A3Fy;Fx;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S45S2S36S4S0S16Vzr1;Vzl1;S3dR3R2R1A3A3S45S0Lsg;R3SbS1dS14R2A1M0S16Vzr1;Vzl1;R1A3M1A2ScZ2M2Z40A2A2SbG1ScG2G0A2A2X45x2A3Fx;Fw;Fsg;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S1S36S0S4S0S16Vzr1;Vzl1;S41R3R2R1A3A3SbS1aS1bS16Vzr1;Vzl1;R2A3R1Vzl1;R3A1A3A1ScZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using L am fr g i rho. reflexivity. Qed.
Lemma m64_small : ltac2:(tb__ "0|1|
S0S8Z0R1A2SaR2ScZ2Z40A2M0A2S4S0SbR3G0A2R3A3F_;F_;Fz;").
Proof using pv zl1 zr1. intros. apply Z.mod_small. lia. Qed.
Lemma bits_range : 0 <= bits < 2 ^ 48.
Proof using HMI Harea Hfr Hkind Hpv Hrc zl1 zr1. pose proof R_all as R. lia. Qed.

Lemma ze_p : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S20A3S24A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc. unfold pS. rewrite ze_var, zr1_pv. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze130 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P82A1A3S27A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 zr1_vals). pose proof R_all. apply m64_small; lia. Qed.
Lemma ze131 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P83A1A3S23A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 (proj2 zr1_vals)). pose proof R_all. apply m64_small; lia. Qed.
Lemma ze132 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P84A1A3S21A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 (proj2 (proj2 zr1_vals))). pose proof R_all. apply m64_small; lia. Qed.
Lemma ze133 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P85A1A3S78Vam;A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 (proj2 (proj2 (proj2 zr1_vals)))). pose proof R_all. apply m64_small; lia. Qed.
Lemma ze134 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P86A1A3S79Vam;A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 (proj2 (proj2 (proj2 (proj2 zr1_vals))))). pose proof R_all. apply m64_small; lia. Qed.
Lemma ze135 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P87A1A3S26A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 zr1_vals)))))). pose proof bits_range. apply m64_small; lia. Qed.
Lemma ze136 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S33P88A1A3SbS2aScZ2Z40A2A2A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_var, (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 zr1_vals)))))). pose proof (Z.mod_pos_bound sec (2 ^ 64) ltac:(lia)). apply m64_small; lia. Qed.

Lemma ze_idx : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;SbcA3Vi;A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_idx, bv_idxb. rewrite ze_alu, ze130, ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31.
  pose proof R_all as R. rewrite (m64_small h3) by lia. pose proof GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & IDX & _). exact IDX.
Qed.

Lemma bits_decomp : ltac2:(tb__ "0|6|
S3S4S0SbS26Z20M0A2S7eVam;A1M1A3S3S4S0S10S26Z1000M2A2S76Vam;A1A3S3S4S0S10SbS26G2A2M3Z40M4A2S75Vam;A1M5A3S3S4S0G3S9S9G1G0A2SdG4G5A2A2A3S3S8Z0G5A2SaG5G4A2A2A2A2A2A2").
Proof using HMI Harea Hfr Hkind Hpv Hrc zl1 zr1.
  pose proof R_all as R.
  assert (SC : 0 <= am_sc am < 64) by lia.
  assert (EB : bits = am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) by lia.
  assert (LL : 0 <= am_last am <= 31) by lia. assert (ML : 0 <= am_maplen am) by lia.
  clear R. rewrite EB.
  set (l := am_last am) in *. set (c := am_sc am) in *. set (mm := am_maplen am) in *.
  assert (M4096 : (l + 32 + 64 * c + 4096 * mm) mod 4096 = l + 32 + 64 * c).
  { replace (l + 32 + 64 * c + 4096 * mm) with ((l + 32 + 64 * c) + mm * 4096) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  split. { replace (l + 32 + 64 * c + 4096 * mm) with (l + (1 + 2 * c + 128 * mm) * 32) by lia.
           rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  split. { replace (l + 32 + 64 * c + 4096 * mm) with ((l + 32 + 64 * c) + mm * 4096) by lia.
           rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split. { rewrite M4096. replace (l + 32 + 64 * c) with ((l + 32) + c * 64) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split; [exact M4096 | lia].
Qed.

Lemma ze_last : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;SbdA3S7eVam;A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_last, bv_bits. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite land_31. apply bits_decomp.
Qed.
Lemma ze_maplen : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;SbeA3S76Vam;A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_maplen, bv_bits. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (12 mod 2 ^ 64 mod 64) with 12.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. apply bits_decomp.
Qed.
Lemma ze_sc : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;Sc0A3S75Vam;A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_sc, bv_bits. rewrite ze_alu, ze_alu, ze135, !ze_lit. cbn [zalu].
  change (52 mod 2 ^ 64 mod 64) with 52. change (58 mod 2 ^ 64 mod 64) with 58.
  pose proof bits_range as B. pose proof bits_decomp as (_ & _ & M & _).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small ((bits * 2 ^ 52) mod 2 ^ 64) (2 ^ 64)) by (apply Z.mod_pos_bound; lia).
  rewrite <- M.
  replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  replace (2 ^ 58) with (2 ^ 52 * 2 ^ 6) by reflexivity.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma land3072_mod : ltac2:(tb__ "0|1|
S0S4S0SeR1Zc00M0A2SeSbR1Z1000A2G0A2A3Fb;").
Proof using pv zl1 zr1. intros b. change 4096 with (2 ^ 12). rewrite <- (land_ones_low b 12) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma ze_bits3072 : ltac2:(tb__ "0|1|
S4S0S16Vzr1;Vzl1;S3aSc6Sb6S39Zc00M0A1A3A3SeSbS26Z1000A2G0A2A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_bits. rewrite ze_alu, ze135, ze_lit. pose proof bits_range. cbn [zalu]. rewrite !Z.mod_small by lia. apply land3072_mod.
Qed.
Lemma land3072_lo : ltac2:(tb__ "0|1|
S0S3S8Z0R1A2SaR1Zc00M0A2A2S4S45S11SeR2G0A2G0A2S51A3F_;Fr;").
Proof using pv zl1 zr1.
  intros r Hr.
  pose proof (forall_range_dec (fun r => negb (Z.land r 3072 =? 3072)) 0 3072 ltac:(vm_compute; reflexivity) r ltac:(lia)) as X.
  apply Bool.negb_true_iff in X. exact X.
Qed.
Lemma land3072_hi : ltac2:(tb__ "0|1|
S0S3S8Zc00M0R1A2SaR1Z1000A2A2S4S45S11SeR2G0A2G0A2S4aA3F_;Fr;").
Proof using pv zl1 zr1.
  intros r Hr. exact (forall_range_dec (fun r => Z.land r 3072 =? 3072) 3072 1024 ltac:(vm_compute; reflexivity) r ltac:(lia)).
Qed.

Definition sz : Z := ltac2:(tb__ "0|0|
S81S75Vam;A1S80A2").
Lemma ze_scsize : ltac2:(tb__ "0|1|
S3S8Z0S75Vam;A1M0A2SaG0Z30A2A2S4S0S16Vzr1;Vzl1;Sc1A3S2dA3F_;").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  intros Hsc. unfold bv_scsize. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_alu, ze_sc, ze_lit. cbn [zalu].
  change (1 mod 2 ^ 64 mod 64) with 1. rewrite zl1_1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (Z.mod_small (am_sc am * 2)) by lia. rewrite (Z.mul_comm (am_sc am) 2).
  rewrite table_u16 by lia. fold sz. pose proof (znth_size_classes_range (am_sc am) Hsc) as SZ. fold sz in SZ.
  change (Z.of_N 16) with 16. rewrite (Z.mod_small sz (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma asserts_unpack : ltac2:(tb__ "0|3|
S3S45OL_;S12S75Vam;A1M0Z30A2S3S8SdS2dVi;A2S23A2SaS23SdS2dS9Vi;Z1M1A2A2A2A2S4S0G0Z3fA3X45x2SaZ0S76Vam;A1M2A2S8S23SfS10SdG2Z1000A2Z10A2G1A2A2F_;A2").
Proof using HMI Hfr Hrc pv zl1 zr1.
  pose proof GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & IDX & ASR). unfold get_meta_asserts, view_of in ASR.
  cbn [gm_p4 gm_p3 gm_off16 gm_mem gm_avail gm_freed gm_last gm_sc gm_maplen gm_area_check] in ASR.
  fold h3 h16 in ASR. rewrite IDX in ASR.
  apply andb_prop in ASR as [ASR I9]. apply andb_prop in ASR as [ASR I8].
  split.
  - destruct (am_sc am <? 48); [|apply Z.eqb_eq in I8; exact I8].
    apply andb_prop in I8 as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. fold sz in A, B. lia.
  - intros Hm. destruct (0 <? am_maplen am) eqn:E; [|apply Z.ltb_ge in E; lia]. cbn [implb] in I9. apply Z.leb_le in I9. exact I9.
Qed.

Lemma pow2_i_range : ltac2:(tb__ "0|2|
S3S3S8Z1ScZ2M0Vi;A2M1A2SaG1ScG0Z20A2A2A2S8G1ScG0Z1fA2A2A2").
Proof using HMI Harea Hfr Hkind Hpv Hrc zl1 zr1.
  pose proof R_all as R. split; [split|].
  - apply Z.le_trans with (2 ^ 0); [lia|]. apply Z.pow_le_mono_r; lia.
  - apply Z.pow_lt_mono_r; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.
Lemma ze_bit : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;Sb5A3S18ScZ2Vi;A2A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_bit. rewrite ze_aluw, ze_idx, ze_lit. cbn [zalu]. pose proof R_all as R. pose proof pow2_i_range as P.
  change (1 mod 2 ^ 64 mod 2 ^ 32) with 1. rewrite (Z.mod_small i) by lia. rewrite (Z.mod_small i) by lia.
  rewrite Z.shiftl_1_l. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_sx133 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S3dS4aQ20S33P85A1A3A3S18S78Vam;A1A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_ext, ze133. reflexivity. Qed.
Lemma ze_sx134 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S3dS4aQ20S33P86A1A3A3S18S79Vam;A1A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho. rewrite ze_ext, ze134. reflexivity. Qed.

Lemma ze_mem : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;Sa6S20A1A3S9S22Z10A2A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc.
  unfold bv_mem, bv_off. rewrite ze_alu, ze_p, ze_alu, ze131, ze_lit. cbn [zalu]. change (4 mod 2 ^ 64 mod 64) with 4.
  pose proof R_all as R.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (h16 * 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ze_memm16 : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S3aSc7Sa6S20A1S39N10A1A3A3S22A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc.
  rewrite ze_alu, ze_mem, ze_lit. cbn [zalu]. pose proof R_all as R.
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
  replace (zMem + 16 + (2 ^ 64 - 16)) with (zMem + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_area : ltac2:(tb__ "0|0|
S4S0S16Vzr1;Vzl1;S3aSc6Sa9S39SabA1A3A3S1fA3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  unfold bv_g. rewrite ze_alu, ze132, ze_lit. cbn [zalu]. pose proof R_all as R.
  rewrite (Z.mod_small zG) by lia.
  match goal with |- Z.land zG ?mm = _ => replace mm with (2 ^ 64 - 2 ^ 12) by reflexivity end.
  rewrite (land_high_mask zG 12) by lia. change (2 ^ 12) with 4096.
  replace zG with (24 + 40 * k + zA) by lia.
  assert (HA : zA mod 4096 = 0) by lia.
  rewrite <- Z.add_mod_idemp_r, HA, Z.add_0_r by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ZF_common : ltac2:(tb__ "0|0|
S94S37S17Vzr1;Vzl1;A2Sb7S20A1A3").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  pose proof R_all as R. unfold bv_facts_common, bv_idxb, bv_off, bv_avail, bv_freed.
  constructor. { zfact. rewrite ze130, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze131, ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
  constructor. { zfact. rewrite ze_last, ze_idx. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_alu, ze_sx133, ze_bit, ze_lit. cbn [zalu]. pose proof pow2_i_range.
                 pose proof (sx32_range (am_avail am) ltac:(lia)). pose proof (sx32_range (2 ^ i) ltac:(lia)).
                 rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
                 rewrite land_pow2_testbit, (ff_avail_i _ _ _ _ _ FFx) by lia. reflexivity. }
  constructor. { zfact. rewrite ze_alu, ze_sx134, ze_bit, ze_lit. cbn [zalu]. pose proof pow2_i_range.
                 pose proof (sx32_range (am_freed am) ltac:(lia)). pose proof (sx32_range (2 ^ i) ltac:(lia)).
                 rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
                 rewrite land_pow2_testbit, (ff_freed_i _ _ _ _ _ FFx) by lia. reflexivity. }
  constructor.
Qed.

Lemma ZF_sized : ltac2:(tb__ "0|1|
S3S8Z0S75Vam;A1M0A2SaG0Z30A2A2S94S37S17Vzr1;Vzl1;A2SbbA3F_;").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc.
  intros Hsc. pose proof R_all as R. pose proof bits_decomp as (_ & _ & _ & M & _).
  pose proof (proj1 asserts_unpack) as AU. destruct (am_sc am <? 48) eqn:E; [|apply Z.ltb_ge in E; lia]. destruct AU as [A1 A2].
  pose proof (znth_size_classes_range _ Hsc) as SZ. fold sz in SZ.
  assert (B1 : 0 <= sz * i <= 8191 * 31) by nia. assert (B2 : 0 <= sz * (i + 1) <= 8191 * 32) by nia.
  unfold bv_facts_sized, bv_off.
  constructor. { zfact. rewrite ze_lit, ze_sc. change (47 mod 2 ^ 64) with 47. rewrite Z.ltb_lt. lia. }
  constructor. { zfact. rewrite ze_bits3072, ze_lit, M. change (3072 mod 2 ^ 64) with 3072. rewrite land3072_lo by lia. reflexivity. }
  constructor. { zfact. rewrite ze131, ze_mul, (ze_scsize Hsc), ze_idx. rewrite Z.mod_small by lia.
                 apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze131, ze_mul, ze_alu, ze_idx, ze_lit, (ze_scsize Hsc). cbn [zalu]. change (1 mod 2 ^ 64) with 1.
                 rewrite (Z.mod_small (i + 1)) by lia. rewrite (Z.mul_comm (i + 1) sz). rewrite Z.mod_small by lia.
                 rewrite Bool.negb_true_iff. intros X. apply Z.ltb_ge in X. lia. }
  constructor.
Qed.

Lemma ZF_direct : ltac2:(tb__ "0|0|
S8Z30S75Vam;A1A2S94S37S17Vzr1;Vzl1;A2Sb8A3F_;").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  intros Hsc. pose proof R_all as R. pose proof bits_decomp as (_ & _ & _ & M & _).
  assert (E63 : am_sc am = 63) by lia.
  unfold bv_facts_direct.
  constructor. { zfact. rewrite ze_lit, ze_sc. change (47 mod 2 ^ 64) with 47. rewrite Z.ltb_lt. lia. }
  constructor. { zfact. rewrite ze_sc, ze_lit, E63. reflexivity. }
  constructor. { zfact. rewrite ze_bits3072, ze_lit, M. change (3072 mod 2 ^ 64) with 3072. rewrite land3072_hi by lia. cbn. intros X. discriminate X. }
  constructor.
Qed.

Lemma ZF_nomap : ltac2:(tb__ "0|0|
S4S0S76Vam;A1Z0A3S94S37S17Vzr1;Vzl1;A2SbaA3F_;").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  intros Hm. unfold bv_facts_nomap. constructor; [|constructor].
  zfact. rewrite ze_maplen, ze_lit, Hm. reflexivity.
Qed.

Lemma ZF_map : ltac2:(tb__ "0|0|
SaZ0S76Vam;A1A2S94S37S17Vzr1;Vzl1;A2Sb9A3F_;").
Proof using HMI Harea Hfr Hkind Hpv Hrc rho.
  intros Hm. pose proof (proj2 asserts_unpack Hm) as AU. pose proof R_all as R. pose proof bits_range. unfold bv_facts_map, bv_off.
  assert (AU' : h16 + 1 <= am_maplen am * 256).
  { replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) in AU by lia. rewrite Z.div_mul in AU by lia. lia. }
  constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. rewrite ze_alu, ze_alu, ze_maplen, !ze_lit, ze131. cbn [zalu].
                 change (8 mod 2 ^ 64 mod 64) with 8. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
                 rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
                 assert (B : am_maplen am * 256 < 2 ^ 60) by lia.

                 rewrite (Z.mod_small (am_maplen am * 256)) by lia.
                 replace (am_maplen am * 256 + (2 ^ 64 - 1)) with ((am_maplen am * 256 - 1) + 1 * 2 ^ 64) by lia.
                 rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
                 apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor.
Qed.

Definition xv : gm_variant := ltac2:(tb__ "0|1|
S45Sc3L_;M0S12S75Vam;A1Z30A2G0S11S76Vam;A1Z0A2Sb2Sb3X45x2Sb4X45x2").

Theorem ZF_all : ltac2:(tb__ "0|0|
S94S37S17Vzr1;Vzl1;A2Sa8S20S2eA2A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc.
  pose proof R_all as R. unfold bv_facts, xv.
  destruct (am_sc am <? 48) eqn:Esc; [apply Z.ltb_lt in Esc | apply Z.ltb_ge in Esc].
  - destruct (am_maplen am =? 0) eqn:Em; [apply Z.eqb_eq in Em | apply Z.eqb_neq in Em];
      (apply Forall_app; split; [apply ZF_common|]); apply Forall_app; split.
    + apply ZF_sized. lia. + apply ZF_nomap. exact Em.
    + apply ZF_sized. lia. + apply ZF_map. lia.
  - apply Forall_app; split; [apply ZF_common|]. apply Forall_app; split.
    + apply ZF_direct. lia. + apply ZF_map. lia.
Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
S94S37S3eS1eA1Sa8S20S2eA2A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc.
  apply Forall_holds_of_zholds; [|exact ZF_all].
  unfold xv. destruct (am_sc am <? 48); [destruct (am_maplen am =? 0)|]; vm_compute; reflexivity.
Qed.

Lemma addr_padd : ltac2:(tb__ "0|0|
S72S0S4S0S9dVL;S73R2R1A2A2S9S9dVL;R2A2R1A2A3Fz;Fq;").
Proof using pv zl1 zr1. intros [r o] z. unfold addr_of, loc_addr, padd. lia. Qed.

Lemma ZONES : ltac2:(tb__ "0|c|
S5S0S0S3S8S25S22A2S3S8S9S22Z10M0A2S24A2S3S8S9S24S28A2S9S25R1A2M1A2S3S8Z0M2S28A2S3S6S8S9S1fZ1000M3A2M4S25A2S8G1S1fA2A2S3S4S0S21S9S9S1fZ18A2SdZ28Vk;A2A2A3S3S3S8G2Vk;A2SaVk;Z65A2A2S3S6S8G1S9bVC;A1M5A2S8S9aVC;A1M6S25A2A2S3S6S8G4G5A2S8G6S1fA2A2S3S8G5S98VC;A1M7A2S3S8S9G7Z8A2M8G6A2S3S8G5S9cVC;A1M9A2S3S8S9G9Z4A2MaG6A2S3S6S8G8G9A2S8GaG7A2A2S3S8G3S25A2S3S8G1S97VL;A1MbA2S3S8G3S1fA2S3S8G4GbA2S3S8G3G7A2S3S8S9G6G0A2GbA2S8GbZ7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2LRL;A2").
Proof using HMI HSI Harea Hfr Hkind Hpv Hrc zl1 zr1.
  pose proof R_all as R. pose proof Hgrp as (rgm & Hr & Hk & Hl & Ho & He & _ & G1 & G2 & G3 & G4 & EM).
  pose proof HzA as (A1 & A2 & A3 & A4). pose proof Hctx as CT. pose proof Hrc as RC. destruct Harea as (Ha & Hk' & Hg & _).
  exists (rg_len rgm).

  assert (HEa : In (LMem a, PGSZ) (footprint s)).
  { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. split; [reflexivity | exact Ha]. }
  pose proof (footprint_region_In s _ rgm Hr Hk Hl) as HEg.
  assert (NE : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rgm)).
  { intros E. injection E as E1 E2. destruct Hareg as (r & o & rga & Ea & _ & Hpo & _). rewrite Ea in E1. injection E1 as _ Eo. unfold PGSZ in Hpo. lia. }
  destruct HLok as (_ & _ & PW & _).
  assert (DJ : zA + 4096 <= G0 \/ G0 + rg_len rgm <= zA).
  { destruct (pairwise_map_In _ (crange L) (footprint s) _ _ PW HEa HEg NE) as [DD|DD];
      unfold MallocInv.ranges_disjoint, crange in DD; cbn [fst snd] in DD; unfold zA, addr_of, G0 in *; unfold loc_addr in DD |- *; cbn [prid poff] in DD |- *;
      unfold PGSZ in DD; lia. }
  unfold group_extent, UNIT, IB, CTX_SIZE, PGSZ in *. fold st in He.
  repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma own_win : ltac2:(tb__ "0|2|
S0S56VL;Vs;R1A3S3S4S45Sc5Vsegs;Vm;S30Q40M0R2A2A3S4aA3S5S31Q8A1M1G1S4S4cG1A1Sc4Vsegs;Vm;S30G0R3A2A3S4dG1R1A2A3Lb;A2A2F_;Fx;").
Proof using HMI Hrc. intros x Hx. destruct (byteview_of_not_None _ _ x (HO x Hx)) as (_ & W & R). split; [exact W | exact R]. Qed.
Lemma cell_own : ltac2:(tb__ "0|1|
S53S44S53R1S59Vs;A1A3S0S3S8S58VL;S63R3A1A2M0R1A2SaR1S9G0S13S64R3A1A1A2A2A2S56VL;Vs;R2A3F_;Fx;F_;Fc;").
Proof using HMI Hrc. intros c Hc x Hx. exact (cell_bytes_owned s L HW HLok c (or_introl Hc) x Hx). Qed.
Lemma cell_view : ltac2:(tb__ "0|3|
S53S0S0S0S4bS36S44S53R6S59Vs;A1A3S4S4cS0A1Sd2VL;R7A2S4dS0R6A2A3S4S4bS64R8A1R4A3SccR5U8A2S4S0S58VL;S63RaA1A2S9R8R7A2A3S4S31Q40M0A1S34S1eR6A2S30G0RaA2A3S4bScdR1R9A2S4S4cS31Q8M1A1M2A1Sc4Vsegs;Vm;S30G0S9S9RcRbA2S13R2A1A2A2A3S4dG2S96G2R2S43RaS34S1eR9A2A2S30G1Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foff;Fb;Fz;Fc;").
Proof using HMI Hrc.
  intros c z b off kk e Hc Hz Hw Hk Ha He.
  exact (cell_in_view_of_image L (rd_of segs m) (wok_of segs m) c z rho1 b off kk e (proj1 (Forall_forall _ _) HI c Hc) Hz Hw Hk Ha He).
Qed.

Lemma ev1 : ltac2:(tb__ "0|1|
S36S4S45S1cR1A1S4aA3S4S31Q40M0A1S34S1eR2A2S30G0S16Vzr1;Vzl1;R2A3A2A3F_;Fe;").
Proof using . intros e He. unfold zr1, zl1. rewrite <- (eval_zeval rho1 e He). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma ev1u : ltac2:(tb__ "0|0|
S36S4S45S1cR1A1S4aA3S4S0S32Q40S34S1eR2A2A2S16Vzr1;Vzl1;R2A3A3F_;Fe;").
Proof using . intros e He. unfold zr1, zl1. exact (eval_zeval rho1 e He). Qed.
Lemma Z_to_bv64_mod : ltac2:(tb__ "0|1|
S0S4S31Q40M0A1S30G0SbR1ScZ2Z40A2A2A2S30G0R1A2A3Fz;").
Proof using pv zl1 zr1.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma ev_130 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P82A1A2S30G0S27A2A3"). Proof using . exact (proj1 (rw_bv_val rho _ _ _ _ _ _ _)). Qed.
Lemma ev_131 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P83A1A2S30G0S23A2A3"). Proof using . exact (proj1 (proj2 (rw_bv_val rho _ _ _ _ _ _ _))). Qed.
Lemma ev_132 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P84A1A2S30G0S21A2A3"). Proof using . exact (proj1 (proj2 (proj2 (rw_bv_val rho _ _ _ _ _ _ _)))). Qed.
Lemma ev_133 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P85A1A2S30G0S78Vam;A1A2A3"). Proof using . exact (proj1 (proj2 (proj2 (proj2 (rw_bv_val rho _ _ _ _ _ _ _))))). Qed.
Lemma ev_134 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P86A1A2S30G0S79Vam;A1A2A3"). Proof using . exact (proj1 (proj2 (proj2 (proj2 (proj2 (rw_bv_val rho _ _ _ _ _ _ _)))))). Qed.
Lemma ev_135 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P87A1A2S30G0S26A2A3"). Proof using . exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (rw_bv_val rho _ _ _ _ _ _ _))))))). Qed.
Lemma ev_136 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS33P88A1A2S30G0S2aA2A3").
Proof using pv. cbn [eval]. unfold rho1, vals. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (rw_bv_val rho _ _ _ _ _ _ _))))))). apply Z_to_bv64_mod. Qed.
Lemma ev_memm16 : ltac2:(tb__ "0|1|
S4S31Q40M0A1S34S1eS3aSc7Sa6S20A1S39N10A1A3A2S30G0S22A2A3").
Proof using HMI Harea Hfr Hkind Hp Hpv Hrc. rewrite ev1 by reflexivity. rewrite ze_memm16. reflexivity. Qed.
Lemma b_hdr : ltac2:(tb__ "0|0|
S4S0S32Q40S34S1eS20A2A2S24A3"). Proof using HMI Harea Hfr Hkind Hp Hpv Hrc. rewrite ev1u by reflexivity. exact ze_p. Qed.
Lemma b_grp : ltac2:(tb__ "0|0|
S4S0S32Q40S34S1eSa6S20A1A2A2S9S22Z10A2A3"). Proof using HMI Harea Hfr Hkind Hp Hpv Hrc. rewrite ev1u by reflexivity. exact ze_mem. Qed.
Lemma b_meta : ltac2:(tb__ "0|0|
S4S0S32Q40S34S1eSa9A2A2S21A3"). Proof using HMI Harea Hfr Hkind Hpv Hrc. unfold bv_g. rewrite ev1u by reflexivity. exact ze132. Qed.
Lemma b_area : ltac2:(tb__ "0|0|
S4S0S32Q40S34S1eS3aSc6Sa9S39SabA1A3A2A2S1fA3"). Proof using HMI Harea Hfr Hkind Hpv Hrc. rewrite ev1u by reflexivity. exact ze_area. Qed.
Lemma b_ctx : ltac2:(tb__ "0|1|
S4S0S32Q40S34S1eS39S98VC;A1M0A1A2A2G0A3").
Proof using HMI HSI Harea Hfr Hkind Hpv Hrc. cbn [eval]. pose proof ZONES as (RL & Z). apply u64. lia. Qed.

Lemma cov_hdr : ltac2:(tb__ "0|0|
S0S3S8SfS24Z4A2R1A2SaR1S24A2A2S56VL;Vs;R2A3F_;Fx;").
Proof using HMI Hfr Hrc pv zl1 zr1.
  intros x Hx. pose proof GM as (C4 & C3 & C2 & _).
  assert (E4 : loc_addr L (LMem (padd p (-4))) = zP - 4) by (unfold zP; fold (addr_of L (padd p (-4))); rewrite addr_padd; lia).
  assert (E3 : loc_addr L (LMem (padd p (-3))) = zP - 3) by (unfold zP; fold (addr_of L (padd p (-3))); rewrite addr_padd; lia).
  assert (E2 : loc_addr L (LMem (padd p (-2))) = zP - 2) by (unfold zP; fold (addr_of L (padd p (-2))); rewrite addr_padd; lia).
  assert (D : x = zP - 4 \/ x = zP - 3 \/ zP - 2 <= x < zP) by lia.
  destruct D as [D|[D|D]].
  - apply (cell_own _ C4). cbn [mc_loc mc_w]. rewrite E4. lia.
  - apply (cell_own _ C3). cbn [mc_loc mc_w]. rewrite E3. lia.
  - apply (cell_own _ C2). cbn [mc_loc mc_w]. rewrite E2. lia.
Qed.
Lemma cov_grp : ltac2:(tb__ "0|0|
S0S3S8S22R1A2SaR1S9S22Z8A2A2A2S56VL;Vs;R2A3F_;Fx;").
Proof using HMI Hfr Hrc pv zl1 zr1.
  intros x Hx. pose proof GM as (_ & _ & _ & CG & _). apply (cell_own _ CG). cbn [mc_loc mc_w]. fold (addr_of L (am_mem am)). fold zMem. lia.
Qed.
Lemma g_addrs : ltac2:(tb__ "0|0|
S3S4S0S58VL;S54S73Vg;S5eA2A1A2S9S21Z10A2A3S3S4S0S58VL;S54S73Vg;S5bA2A1A2S9S21Z18A2A3S3S4S0S58VL;S54S73Vg;S5dA2A1A2S9S21Z1cA2A3S4S0S58VL;S54S73Vg;S5cA2A1A2S9S21Z20A2A3A2A2A2").
Proof using pv zl1 zr1.
  unfold zG. fold (addr_of L (padd g META_mem)) (addr_of L (padd g META_avail)) (addr_of L (padd g META_freed)) (addr_of L (padd g META_bits)).
  rewrite !addr_padd. unfold META_mem, META_avail, META_freed, META_bits. lia.
Qed.
Lemma cov_meta : ltac2:(tb__ "0|0|
S0S3S8S9S21Z10A2R1A2SaR1S9S21Z28A2A2A2S56VL;Vs;R2A3F_;Fx;").
Proof using HMI Hfr Hrc pv zl1 zr1.
  intros x Hx. pose proof GM as (_ & _ & _ & _ & CM & CA & CF & CB & _). pose proof g_addrs as (EM & EA & EF & EB).
  assert (D : zG + 16 <= x < zG + 24 \/ zG + 24 <= x < zG + 28 \/ zG + 28 <= x < zG + 32 \/ zG + 32 <= x < zG + 40) by lia.
  destruct D as [D|[D|[D|D]]].
  - apply (cell_own _ CM). cbn [mc_loc mc_w]. rewrite EM. lia.
  - apply (cell_own _ CA). cbn [mc_loc mc_w]. rewrite EA. lia.
  - apply (cell_own _ CF). cbn [mc_loc mc_w]. rewrite EF. lia.
  - apply (cell_own _ CB). cbn [mc_loc mc_w]. rewrite EB. lia.
Qed.
Lemma cov_area : ltac2:(tb__ "0|0|
S0S3S8S1fR1A2SaR1S9S1fZ8A2A2A2S56VL;Vs;R2A3F_;Fx;").
Proof using HMI Harea Hrc pv zl1 zr1.
  intros x Hx. destruct Harea as (_ & _ & _ & CS & _). apply (cell_own _ CS). cbn [mc_loc mc_w]. fold (addr_of L a). fold zA. lia.
Qed.
Lemma cov_ctx : ltac2:(tb__ "0|1|
S0S3S8S98VC;A1M0R1A2SaR1S9G0Z8A2A2A2S56VL;Vs;R2A3F_;Fx;").
Proof using HMI Harea Hrc pv zl1 zr1.
  intros x Hx. destruct Harea as (_ & _ & _ & _ & CC). apply (cell_own _ CC). cbn [mc_loc mc_w]. unfold loc_addr. rewrite HC. unfold CTX_secret. lia.
Qed.

Lemma carv_hdr : ltac2:(tb__ "0|0|
Sa4Vsegs;S97VL;A1S1eVm;Sb0S20A1A5").
Proof using HMI HSI Harea Hfr Hkind Hp Hpv Hrc.
  unfold carvable, bv_hdr. rewrite b_hdr. pose proof ZONES as (RL & Z). pose proof GM as (C4 & C3 & C2 & _).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  split. { intros off Hoff. apply own_win. apply cov_hdr. lia. }
  unfold cells_in_view, bv_idxb, bv_off. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (cell_view _ 0 _ _ 1%nat _ C4); [reflexivity | reflexivity | lia | | reflexivity].
    cbn [mc_loc]. fold (addr_of L (padd p (-4))). rewrite addr_padd. fold zP. lia.
  - apply (cell_view _ h3 _ _ 1%nat _ C3); [reflexivity | reflexivity | lia | | exact ev_130].
    cbn [mc_loc]. fold (addr_of L (padd p (-3))). rewrite addr_padd. fold zP. lia.
  - apply (cell_view _ h16 _ _ 2%nat _ C2); [reflexivity | reflexivity | lia | | exact ev_131].
    cbn [mc_loc]. fold (addr_of L (padd p (-2))). rewrite addr_padd. fold zP. lia.
Qed.
Lemma carv_grp : ltac2:(tb__ "0|0|
Sa4Vsegs;S97VL;A1S1eVm;SafS20A1A5").
Proof using HMI HSI Harea Hfr Hkind Hp Hpv Hrc.
  unfold carvable, bv_grp. rewrite b_grp. pose proof ZONES as (RL & Z). pose proof GM as (_ & _ & _ & CG & _).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  split. { intros off Hoff. apply own_win. apply cov_grp. lia. }
  unfold cells_in_view, bv_g. constructor; [|constructor].
  apply (cell_view _ zG _ _ 8%nat _ CG); [reflexivity | reflexivity | lia | | exact ev_132].
  cbn [mc_loc]. fold (addr_of L (am_mem am)). fold zMem. lia.
Qed.
Lemma carv_meta : ltac2:(tb__ "0|0|
Sa4Vsegs;S97VL;A1S1eVm;Sb1S20A1A5").
Proof using HMI HSI Harea Hfr Hkind Hp Hpv Hrc.
  unfold carvable, bv_meta. rewrite b_meta. pose proof ZONES as (RL & Z). pose proof GM as (_ & _ & _ & _ & CM & CA & CF & CB & _).
  pose proof g_addrs as (EM & EA & EF & EB).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  split. { intros off Hoff. apply own_win. apply cov_meta. lia. }
  unfold cells_in_view, bv_avail, bv_freed, bv_bits. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (cell_view _ zMem _ _ 8%nat _ CM); [reflexivity | reflexivity | lia | | exact ev_memm16]. cbn [mc_loc]. rewrite EM. lia.
  - apply (cell_view _ (am_avail am) _ _ 4%nat _ CA); [reflexivity | reflexivity | lia | | exact ev_133]. cbn [mc_loc]. rewrite EA. lia.
  - apply (cell_view _ (am_freed am) _ _ 4%nat _ CF); [reflexivity | reflexivity | lia | | exact ev_134]. cbn [mc_loc]. rewrite EF. lia.
  - apply (cell_view _ bits _ _ 8%nat _ CB); [reflexivity | reflexivity | lia | | exact ev_135]. cbn [mc_loc]. rewrite EB. lia.
Qed.
Lemma carv_area : ltac2:(tb__ "0|0|
Sa4Vsegs;S97VL;A1S1eVm;SadA5").
Proof using HMI HSI Harea Hfr Hkind Hpv Hrc.
  unfold carvable, bv_area. rewrite b_area. pose proof ZONES as (RL & Z). destruct Harea as (_ & _ & _ & CS & _).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  split. { intros off Hoff. apply own_win. apply cov_area. lia. }
  unfold cells_in_view, bv_secret. constructor; [|constructor].
  apply (cell_view _ sec _ _ 8%nat _ CS); [reflexivity | reflexivity | lia | | exact ev_136].
  cbn [mc_loc]. fold (addr_of L a). fold zA. lia.
Qed.
Lemma carv_ctx : ltac2:(tb__ "0|0|
Sa4Vsegs;S97VL;A1S1eVm;SaeVC;A1A5").
Proof using HMI HSI Harea Hfr Hkind Hpv Hrc.
  unfold carvable, bv_ctx. rewrite b_ctx. pose proof ZONES as (RL & Z). destruct Harea as (_ & _ & _ & _ & CC).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  split. { intros off Hoff. apply own_win. apply cov_ctx. lia. }
  unfold cells_in_view, bv_secret. constructor; [|constructor].
  apply (cell_view _ sec _ _ 8%nat _ CC); [reflexivity | reflexivity | lia | | exact ev_136].
  cbn [mc_loc]. unfold loc_addr. rewrite HC. unfold CTX_secret. lia.
Qed.

Lemma ranges : ltac2:(tb__ "0|6|
S3S4S46S0S0A2M0Sa3S1eSb0S20A1A2S49S0S0S9S24N4A2S9S24Z0M1A2A4A3S3S4G0Sa3S1eSafS20A1A2S49S0S0S9S9S22Z10M2A2M3N10A2S9G3N8A2A4A3S3S4G0Sa3S1eSb1S20A1A2S49S0S0S9S21G2A2S9S21Z28A2A4A3S3S4G0Sa3S1eSadA2S49S0S0S9S1fG1A2S9S1fZ8M4A2A4A3S4G0Sa3S1eSaeVC;A1A2S49S0S0S9S98VC;A1M5G1A2S9G5G4A2A4A3A2A2A2A2").
Proof using HMI HSI Harea Hfr Hkind Hp Hpv Hrc. unfold d_range, bv_hdr, bv_grp, bv_meta, bv_area, bv_ctx. rewrite b_hdr, b_grp, b_meta, b_area, b_ctx. repeat split; reflexivity. Qed.

Ltac fa tac := repeat (apply Forall_cons; [tac|]); apply Forall_nil.
Ltac rng R1 R2 R3 R4 R5 := cbn beta; rewrite ?R1, ?R2, ?R3, ?R4, ?R5; unfold SymState.ranges_disjoint; cbn [fst snd].

Theorem blk_all : ltac2:(tb__ "0|6|
S3S4S4bS4fS0S2fA2U7A3S3S94S46S46S46S36S0A2S0A2S47S46S46S0S4bA2S36A2A1A2M0Sa4Vsegs;S97VL;A1S1eVm;A4SbfVC;S20A2M1A3S3Sc2S1eG1A2S3S94G0G0S3fSa3S1eR1A2M2S49S0S0S32Q40S35Vrho;Vpv;A2A2M3S9G3S28A2A4A2Ld;G1A3S3S94S37S3eS1eA1Sa8S20S2eA2A3S3S94G0G0S0S3S8S4eS0S0Sa3S1eR2A2M4A3R1A2SaR1S52S0S0G4A3A2A2Sa1VC;VL;Vs;R2A4F_;Fx;Ld;G1A3S94G0G0S3fG2S49S0S0S9cVC;A1M5S9G5Z4A2A4A2Ld;G1A3A2A2A2A2A2A2").
Proof using HMI HSI Harea Hfr Hkind Hp Hpv Hrc.
  pose proof ZONES as (RL & Z). pose proof ranges as (R1 & R2 & R3 & R4 & R5). rewrite Hp. unfold bv_ram.
  split; [reflexivity|].
  split. { apply Forall_cons; [apply carv_hdr|]. apply Forall_cons; [apply carv_grp|]. apply Forall_cons; [apply carv_meta|].
           apply Forall_cons; [apply carv_area|]. apply Forall_cons; [apply carv_ctx|]. apply Forall_nil. }
  split. { cbn [d_pairwise]. repeat split; fa ltac:(rng R1 R2 R3 R4 R5; lia). }
  split. { fa ltac:(rng R1 R2 R3 R4 R5; lia). }
  split; [exact facts_hold|].
  split. { apply Forall_cons; [rewrite R1; cbn [fst snd]; intros x Hx; left; apply cov_hdr; lia|].
           apply Forall_cons; [rewrite R2; cbn [fst snd]; intros x Hx; left; apply cov_grp; lia|].
           apply Forall_cons; [rewrite R3; cbn [fst snd]; intros x Hx; left; apply cov_meta; lia|].
           apply Forall_cons; [rewrite R4; cbn [fst snd]; intros x Hx; left; apply cov_area; lia|].
           apply Forall_cons; [rewrite R5; cbn [fst snd]; intros x Hx; left; apply cov_ctx; lia|]. apply Forall_nil. }
  fa ltac:(rng R1 R2 R3 R4 R5; lia).
Qed.
End Blk.

Theorem block_view : block_view_stmt segs C.
Proof using HSI Hrc.
  intros [s L] rho md pv zn HM Hin Hpv.
  unfold ma_blocks, blocks in Hin. cbn [ma_L ma_s] in Hin. apply in_map_iff in Hin as ([q n0] & E & Hub). cbn [fst snd] in E.
  injection E as E1 E2.
  destruct (user_block_frame s q n0 Hub) as (g & am & i & fr & Hfr & Hk & E3 & E4). subst q n0 zn.
  assert (HMI : MInv C (mkMA s L) (rd_of segs (rm rho)) (wok_of segs (rm rho)) (m_vmmaps md)) by exact HM.
  pose proof (get_meta_ok s g am i fr (proj1 HMI) Hfr) as X. cbn zeta in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (a & k & Harea) & _).
  exists (xv am), (vals L g am i fr).
  exact (blk_all s L g am i fr (m_vmmaps md) (rm rho) rho pv HMI Hfr Hk (eq_sym E1) Hpv a k Harea).
Qed.
End BV.

Lemma block_view_P : ltac2:(tb__ "0|0|
S47ScaA1SacR1S9eA2Fsegs;").
Proof. intros segs. apply block_view; [exact statics_in_image_P | unfold CTX_SIZE; cbn [mc_ctx mc_replaced C_P Z.add]; lia]. Qed.
Lemma block_view_U : ltac2:(tb__ "0|0|
S47ScaA1SacR1S9fA2Fsegs;").
Proof. intros segs. apply block_view; [exact statics_in_image_U | unfold CTX_SIZE; cbn [mc_ctx mc_replaced C_U Z.add]; lia]. Qed.

