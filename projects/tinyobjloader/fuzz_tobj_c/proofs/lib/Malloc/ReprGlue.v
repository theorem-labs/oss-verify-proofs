(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "iff"; "or"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "modulo"; "to_nat"; "shiftr"; "opp"; "mul"; "@Corelib.Init.Datatypes"; "bool"; "true"; "option"; "Some"; "list"; "nat"; "andb"; "prod"; "None"; "nil"; "pair"; "app"; "fst"; "false"; "length"; "snd"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "eval"; "SLit"; "obj_range"; "cell"; "smatch"; "obj_holds"; "ss_objs"; "sstate"; "mkObj"; "pairwise_disjoint"; "rl"; "rom_ok"; "enc_bytes"; "ranges_disjoint"; "rd"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "DRom"; "DUnknown"; "holds"; "image_byte"; "mkSS"; "odefault"; "rm"; "sfcsr"; "sprop"; "ss_lenient"; "ss_pc"; "swf"; "c_off"; "c_val"; "cell_holds"; "in_cell"; "mkCell"; "mkVal"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ro_addr"; "rw"; "tfact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "layout"; "loc_addr"; "mc_w"; "sval_num"; "cell_holds"; "le_byte"; "mc_loc"; "mcell"; "range_mapped"; "sval"; "LMem"; "VP"; "VSec"; "VZ"; "footprint"; "mc_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.WithSegs"; "sv_nolist"; "set_rl"; "obj_nolist"; "sprop_nolist"; "cell_nolist"; "dflt_nolist"; "state_nolist"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "addr_of"; "ledger_ok"; "mc_img_hi"; "mc_img_lo"; "mconsts"; "topL"; "vm_ok"; "@Stdlib.Lists.List"; "forallb"; "In"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "cells_in_view"; "cells_inside"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "astate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymFrame SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma byteview_of_Some : ltac2:(tb__ "0|5|
S8Q40M0A1M1S17S8Q8M2A1M3A1M4F_;G1S15F_;S0S0S2S17S0A1S74R4R3R2A3S18S0R1A2A3S3S3SbZ0R3A2SdR3SeZ2Z40A2A2A2S3S2S15R4S9G0R3A2A1S16A3S4G3G3S3S2G4R6S9G0R4A2A1S18G3R1A2A3S2S0R3SaG2R1A2A3A2Lb;A2A2A2F_;Fv;Fz;Fwok;Frd;").
Proof.
  intros rd wok z v H. unfold byteview_of in H.
  destruct (0 <=? z) eqn:E0; [|discriminate]. destruct (z <? 2 ^ 64) eqn:E1; [|discriminate].
  cbn [andb] in H. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  destruct (wok (Z_to_bv 64 z)) eqn:Ew; [|discriminate].
  destruct (rd (Z_to_bv 64 z)) as [b|] eqn:Er; [|discriminate].
  injection H as <-. split; [lia|]. split; [reflexivity|]. exists b. auto.
Qed.

Lemma byteview_of_not_None : ltac2:(tb__ "0|4|
S8Q40M0A1M1S17S8Q8A1M2A1M3F_;G1S15F_;S0S5S2S17S0A1S74R3R2R1A3S1dS0A1A3A1S3S3SbZ0R2A2SdR2SeZ2Z40A2A2A2S3S2S15R3S9G0R2A2A1S16A3S4G2G2S2G3R5S9G0R3A2A1S18G2R1A2A3Lb;A2A2A2F_;Fz;Fwok;Frd;").
Proof.
  intros rd wok z H. destruct (byteview_of rd wok z) as [v|] eqn:E; [|congruence].
  destruct (byteview_of_Some _ _ _ _ E) as (A & B & b & C & _). split; [exact A|]. split; [exact B|]. exists b. exact C.
Qed.

Definition cellZ (L : layout) (c : mcell) : option Z := ltac2:(tb__ "0|0|
S61S17S0A1Lx;S67Vc;A1S0S18S0S5bVL;S65R1A1A2A2Lz;S8bS18S0S5bVL;S63R1A1A2A2Lp;S0S1dS0A1Lz;S18S0S5bVL;S64A2A2X61x4").

Lemma cell_bytes : ltac2:(tb__ "0|7|
S58S8Q40M0A1M1S17S8Q8M2A1M3A1M4F_;G1S15F_;S5fS0S5cR5S74R4R3A2R2A3S2S17S0A1S8eR6R3A2S18S0R2A2A3S1aS7eR1S5aR5A1A2S3S3SbZ0ScS59R9S5eR6A1A2SfR2A1A2M5A2SdG5SeZ2Z40A2A2A2S3S2S15R7S9G0G5A2M6A1S16A3S2G4R8G6A1S18G3S9G2S5dR5S5aR6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;Fwok;Frd;FL;").
Proof.
  intros L rd wok [loc w val] z Hc Hz j Hj. cbn [mc_loc mc_w mc_val cellZ] in *.
  unfold MallocInv.cell_holds in Hc. cbn [mc_loc mc_w mc_val] in Hc.
  assert (H : byteview_of rd wok (loc_addr L loc + Z.of_nat j) = Some (le_byte z w j)).
  { destruct val; try (injection Hz as <-; exact (Hc j Hj)). discriminate. }
  destruct (byteview_of_Some _ _ _ _ H) as (R & W & b & Rd & E).
  split; [exact R|]. split; [exact W|]. rewrite Rd, E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma footprint_bytes : ltac2:(tb__ "0|5|
S58S8Q40M0A1M1S17S8Q8A1M2A1M3F_;G1S15F_;S1cS57S0A2S60R4S74R3R2A2R1A3S0S3SbS59R6S21S57S0R3A3A2M4R1A2SdR1ScG4S24S57S0R3A3A2A2A2S3S3SbZ0R2A2SdR2SeZ2Z40A2A2A2S3S2S15R5S9G0R2A2A1S16A3S4G2G2S2G3R7S9G0R3A2A1S18G2R1A2A3Lb;A2A2A2F_;Fx;F_;Frg;Fwok;Frd;FL;").
Proof.
  intros L rd wok rg Hm x Hx. apply byteview_of_not_None. apply Hm. exact Hx.
Qed.

Lemma nth_Z_to_le_bytes : ltac2:(tb__ "0|2|
S1aS1aS0S7eR2R3A2S2S8Q8M0A1M1S6fG1R3S90R4R2A2S9G0Z0A2A4S9G0S12R2S14Z8SfR3A1A2A2A2A3F_;Fx;Fj;Fk;").
Proof.
  induction k as [|k IH]; intros j x Hj; [lia|].
  destruct j as [|j].
  - cbn [Z_to_le_bytes nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma Z_to_bv8_eq : ltac2:(tb__ "0|2|
S0S0S2S0S10R2Z100M0A2S10R1G0A2A3S2S8Q8M1A1S9G1R3A2S9G1R2A2A3F_;Fb;Fa;").
Proof.
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. exact H.
Qed.

Lemma shiftr_mod_byte : ltac2:(tb__ "0|3|
S0S0S0SbZ0R2A2SbScR3Z8M0A2R2A2S2S0S10S12S10R5SeZ2M1R3A2A2R4A2SeG1G0A2M2A2S10S12R5R4A2G2A2A3F_;F_;FN;Fm;Fx;").
Proof.
  intros x m N Hm HN.
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 8) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma nth_enc_bytes : ltac2:(tb__ "0|2|
S1aS1aS0S7eR2R3A2S7fR4U8A2S2S8Q8M0A1M1S6fG1R4S35R5S9Q40R3A2A2S9G0Z0A2A4S9G0S5dR3R5R4A3A2A3F_;F_;Fz;Fj;Fk;").
Proof.
  intros k j z Hj Hk. unfold enc_bytes. rewrite nth_Z_to_le_bytes by exact Hj.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  unfold le_byte. apply Z_to_bv8_eq.
  change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
  rewrite (shiftr_mod_byte z (8 * Z.of_nat j) 64) by lia.
  rewrite (shiftr_mod_byte z (8 * Z.of_nat j) (8 * Z.of_nat k)) by lia.
  reflexivity.
Qed.

Lemma cell_in_view_of_image : ltac2:(tb__ "0|5|
S58S8Q40M0A1M1S17S8Q8M2A1M3A1M4F_;G1S15F_;S5fS0S28S0S0S1aS27S5cRaS74R9R8A2R7A3S2S17S0A1S8eRbR8A2S18S0R7A2A3S2S1aS5aR9A1R4A3S7fR5U8A2S2S0S59ReS5eRbA1A2ScR8R7A2A3S2G1S29RaR6A2S9G0RbA2A3S1aS7eR1R9A2S2G4R11S9G0ScScRcRbA2SfR2A1A2A2A1S18G3S6fG3R2S35RaS29RdR9A2A2S9G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fb;Frho;Fz;Fc;Fwok;Frd;FL;").
Proof.
  intros L rd wok c z rho b off k v Hc Hz Hw Hk Ha Hv j Hj.
  destruct (cell_bytes L rd wok c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, Hv, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Lemma window_view_of_footprint : ltac2:(tb__ "0|4|
S58S8Q40M0A1M1S17S8Q8A1M2A1M3F_;G1S15F_;S1cS57S0A2S0S0S0S60R7S74R6R5A2R4A3SbS59R8S21S57S0R5A3A2ScR4R3A2A2SbScR5R3A2ScS59R9S21S57S0R6A3A2S24S57S0R6A3A2A2S0S3SbR6R1A2SdR1R5A2A2S3S2S15RaS9G0ScR8R2A2A2A1S16A3S4G2G2S2G3RcS9G0ScR9R3A2A2A1S18G2R1A2A3Lx;A2A2F_;Foff;F_;F_;F_;Fhi;Flo;Fb;Frg;Fwok;Frd;FL;").
Proof.
  intros L rd wok rg b lo hi Hm H1 H2 off Hoff.
  destruct (footprint_bytes L rd wok rg Hm (b + off) ltac:(lia)) as (_ & W & R). auto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_rom : ltac2:(tb__ "0|7|
S28S30S1cS19S88A1S80A2S0S0S1S1S2dVsegs;R7R6R5A4S31S2aR5A1S2aZ0M0A1S2aR4A1S1eS2cA1S3dR3A1A5S26S41S47R8A1S3bR8A1S3aR8A1S39R8A1S3cR8A1S20S26S2fR8A1S25S26R1S1eS26A1A3A3S38R8A1R3S46R8A1A9S30S2S15S48R1A1S16A3S3SbG0R8A2M1SdR8SeZ2M2Z40A2M3A2A2S3G1SdR8SeG2Z3fA2A2A2SbScRaR9A2G3A2S2S0SfS23S8Q8M4A1M5S33ReR9A2A2A1RaA3S0S3SbG0R1A2SdR1RcA2A2S3S2S15S54Vsegs;S9Q40ScReR2A2A2M6A2S16A3S2S17G5A1S40Vsegs;G6A2S18G5S6fG5S11R2A1S33R11RcA2S9G4G0A2A4A2A3A2F_;Fk;S70S26S26S36S2bR11R1A2S1fS0S0ReScReRdA2A4A2Lo';S2fRfA1A3S2dVsegs;R11R8RfA4F_;F_;F_;F_;F_;F_;F_;TS';To;F_;Fnx;Fl;Fn;Fb;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] b n l nx Hsm o S' Hwf Hb Hn Hbn Hlen Hrom Hdisj.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hromok & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  assert (EB : bv_unsigned (eval rho (SLit b)) = b).
  { cbn [eval]. apply u64_of_sum. lia. }
  assert (RNG : obj_range rho o = (b, b + n)).
  { unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi]. rewrite EB.
    rewrite !soff_lit_small by lia. f_equal. lia. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hromok|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite EB.
    rewrite !soff_lit_small by lia.
    split; [lia|]. split; [intros off _ D; discriminate D|]. split; [constructor|]. split.
    + intros off Hoff _. cbn [dflt_holds]. rewrite Z.sub_0_r.
      destruct (Hrom off ltac:(lia)) as [R1 R2].
      unfold rd, ms_read_byte. rewrite (Hro _ R1). rewrite (Hromok _). exact R2.
    + cbn [dflt_inv]. lia.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite RNG. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Fixpoint sv_nolist (e : sv) : bool :=
  match e with
  | SLit _ | SVar _ => true
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_nolist a && sv_nolist b
  | SExt _ _ a => sv_nolist a
  | SLBytes _ _ _ => false
  end.

Fixpoint sprop_nolist (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_nolist a && sv_nolist b
  | SPNot p => sprop_nolist p
  | SPTrue | SPAlign _ _ => true
  end.

Definition dflt_nolist (d : odefault) : bool := ltac2:(tb__ "0|1|
S42S15Ld;Vd;S16S16S16S1S22Ll;M0G0S0S27S19S1cS0S0A2A1S19S56A1S22Ltmpl;Lflds;Lcnt;Lesz;X42x6").

Definition cell_nolist (c : cell) : bool := ltac2:(tb__ "0|0|
S1bS68S49Vc;A1A1S68S4aVc;A1A1A2").

Definition obj_nolist (o : sobj) : bool := ltac2:(tb__ "0|0|
S1bS1bS1bS1bS68S4fVo;A1A1S68S53Vo;A1A1A2S68S52Vo;A1A1A2S7cS2cS6cS50Vo;A1A3A2S6dS51Vo;A1A1A2").

Definition state_nolist (S : sstate) : bool := ltac2:(tb__ "0|1|
S1bS1bS1bS1bS1bS7cS27S68S3bVS;A1A3S7cS27S68S3aVS;A1A3A2S44S15Lx;S39VS;A1S16S27S68R1A1Lv;M0X44x2A2S17S27A1S15Lx;S3cVS;A1G0S16X17x2A2S7cS26S6aS2fVS;A1A3A2S7cS45S6bS38VS;A1A3A2").

Definition set_rl (rho : valuation) (f : positive -> list byte) : valuation := ltac2:(tb__ "0|0|
S4eS55Vrho;A1Vf;S43Vrho;A1A3").

Lemma eval_set_rl : ltac2:(tb__ "0|0|
S28S1S19S8Q8A1A1F_;S27S2S15S68R1A1S16A3S2S8Q40A1S29S69R4R3A2R2A2S29R4R2A2A3F_;Fe;Ff;Frho;").
Proof using .
  intros rho f e. induction e; cbn; intros H; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
  - rewrite (IHe H). reflexivity.
  - discriminate.
Qed.

Lemma holds_set_rl : ltac2:(tb__ "0|0|
S28S1S19S8Q8A1A1F_;S45S2S15S6bR1A1S16A3S6S3fS69R4R3A2R2A2S3fR4R2A2A2F_;Fp;Ff;Frho;").
Proof using .
  intros rho f p. induction p; cbn; intros H;
    try (apply andb_prop in H as [H1 H2]; rewrite !(eval_set_rl rho f) by assumption; tauto).
  - specialize (IHp H). tauto.
  - tauto.
  - tauto.
Qed.

Lemma forallb_nth : ltac2:(tb__ "0|1|
S27S15F_;S19S27A1S1aS2S15S7cS27R3R2A3S16A3S2S15R4S2aZ0A1M0A1S16A3S2S15R5S6fS27R3R4G0A4A1S16A3F_;F_;Fn;Fl;Ff;").
Proof using .
  intros f l. induction l as [|x t IH]; intros n Hl H0; destruct n; cbn in *; auto;
    apply andb_prop in Hl as [H1 H2]; auto.
Qed.

Lemma obj_range_set_rl : ltac2:(tb__ "0|0|
S28S1S19S8Q8A1A1F_;S26S2S15S6aR1A1S16A3S2S1cS0S0A2S2bS69R4R3A2R2A2S2bR4R2A2A3F_;Fo;Ff;Frho;").
Proof using .
  intros rho f o H. unfold obj_nolist in H.
  apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_set_rl rho f) by assumption. reflexivity.
Qed.

Lemma smatch_set_rl : ltac2:(tb__ "0|0|
S28S1S19S8Q8A1A1F_;S30S1cS19S88A1S80A2S2S15S6eR2A1S16A3S2dVsegs;R5R3R2A4S2dVsegs;S69R6R5A2R4R3A4F_;F_;Fw;FS;Ff;Frho;").
Proof using .
  intros rho f S [tr [ms md]] Hnl Hsm.
  unfold state_nolist in Hnl.
  apply andb_prop in Hnl as [Hnl Hfa]. apply andb_prop in Hnl as [Hnl Hob]. apply andb_prop in Hnl as [Hnl Hrv].
  apply andb_prop in Hnl as [Hnl Hfc]. apply andb_prop in Hnl as [Hrg Hfg].
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hromok & Hro & Hr & Hf & Hc & Hv & Hm & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hswf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hromok|]. split; [exact Hro|].
  split.
  { intros r Hr0. rewrite (Hr r Hr0). unfold reg_sv. destruct (bv_unsigned r =? 0); [reflexivity|].
    symmetry. apply eval_set_rl. apply forallb_nth; [exact Hrg|reflexivity]. }
  split.
  { intros r. rewrite (Hf r). unfold freg_sv. symmetry. apply eval_set_rl. apply forallb_nth; [exact Hfg|reflexivity]. }
  split.
  { unfold fcsr_match in *. destruct (ss_fcsr S); [exact Hc|]. cbn in Hc |- *. rewrite eval_set_rl by exact Hfc. exact Hc. }
  split.
  { unfold resv_match in *. destruct (ss_resv S); destruct (ms_resv ms); try exact Hv.
    rewrite eval_set_rl by exact Hrv. exact Hv. }
  split.
  2:{ apply Forall_forall. intros p Hp. apply holds_set_rl.
      - exact (proj1 (forallb_forall _ _) Hfa p Hp).
      - exact (proj1 (Forall_forall _ _) Hfacts p Hp). }
  destruct Hm as (Hall & Hpd & Hfr).
  assert (OBJ : forall o, obj_nolist o = true -> obj_holds segs rho ms o -> obj_holds segs (set_rl rho f) ms o).
  { intros o Ho Hh. pose proof Ho as Ho0. unfold obj_nolist in Ho.
    apply andb_prop in Ho as [Ho Hd]. apply andb_prop in Ho as [Ho Hcs]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hb Hlo].
    unfold obj_holds, obj_lo_of, obj_hi_of, soff in *.
    rewrite !(eval_set_rl rho f) by assumption.
    destruct Hh as (R1 & R2 & R3 & R4 & R5).
    split; [exact R1|]. split; [exact R2|]. split.
    { apply Forall_forall. intros c Hcin. pose proof (proj1 (Forall_forall _ _) R3 c Hcin) as CH.
      pose proof (proj1 (forallb_forall _ _) Hcs c Hcin) as Cn. unfold cell_nolist in Cn. apply andb_prop in Cn as [Cn1 Cn2].
      unfold SymState.cell_holds, soff, oaddr in *. rewrite !(eval_set_rl rho f) by assumption. exact CH. }
    split.
    { intros off Hoff Hnc.
      assert (Hnc' : ~ covered rho (ob_cells o) off).
      { intros Cv. apply Hnc. unfold covered, in_cell, soff in *. apply Exists_exists in Cv as (c & Hcin & Hcc).
        apply Exists_exists. exists c. split; [exact Hcin|].
        pose proof (proj1 (forallb_forall _ _) Hcs c Hcin) as Cn. unfold cell_nolist in Cn. apply andb_prop in Cn as [Cn1 Cn2].
        rewrite !(eval_set_rl rho f) by assumption. exact Hcc. }
      specialize (R4 off Hoff Hnc'). destruct (ob_dflt o); try exact R4; discriminate. }
    destruct (ob_dflt o); try exact R5; discriminate. }
  split; [|split].
  - apply Forall_forall. intros o Ho. apply OBJ.
    + exact (proj1 (forallb_forall _ _) Hob o Ho).
    + exact (proj1 (Forall_forall _ _) Hall o Ho).
  - clear Hall Hfr OBJ. induction (ss_objs S) as [|o t IH]; [exact I|].
    cbn in Hob. apply andb_prop in Hob as [Ho Ht].
    destruct Hpd as [P1 P2]. split; [|apply IH; assumption].
    apply Forall_forall. intros o' Ho'. rewrite !obj_range_set_rl; [| exact (proj1 (forallb_forall _ _) Ht o' Ho') | exact Ho].
    exact (proj1 (Forall_forall _ _) P1 o' Ho').
  - intros a Ha. cbn [set_rl rm]. apply Hfr.
    unfold outside_all in *. apply Forall_forall. intros o Ho.
    rewrite <- (obj_range_set_rl rho f o) by exact (proj1 (forallb_forall _ _) Hob o Ho).
    exact (proj1 (Forall_forall _ _) Ha o Ho).
Qed.

Lemma rd_with_mem : ltac2:(tb__ "0|2|
S71S8Q40A1M0S17S8Q8A1A1M1F_;G0S34Vsegs;R3A2S2G1S37S82R4R3A2R2A2S83Vsegs;R3R2A3A3F_;Fa;Fm;Fms;").
Proof using .
  intros ms m a Hrom. unfold rd, ms_read_byte, rd_of, with_mem. cbn [ms_mem ms_rom].
  destruct (m a); [reflexivity|]. apply Hrom.
Qed.

Lemma pairwise_disjoint_app : ltac2:(tb__ "0|1|
S28S19S26A1M0G0S32R3R2A2S32R4R2A2S70S26S26S70S26S26S36S2bR7R1A2S2bR7R2A2A2Lo';R5A3Lo;R3A3S32R6S20S26R5R4A3A2F_;F_;F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1 l2. induction l1 as [|h t IH]; intros H1 H2 HX; [exact H2|].
  cbn. destruct H1 as [Hh Ht]. split.
  - apply Forall_app. split; [exact Hh|].
    apply Forall_forall. intros o Ho.
    pose proof (proj1 (Forall_forall _ _) HX o Ho) as HXo.
    pose proof (proj1 (Forall_forall _ _) HXo h ltac:(left; reflexivity)) as D.
    unfold SymState.ranges_disjoint in *. lia.
  - apply IH; [exact Ht | exact H2 |].
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HX o Ho) as HXo.
    inversion HXo; assumption.
Qed.

Lemma smatch_extend_objs : ltac2:(tb__ "0|1|
S28S30S19S88A1M0S71S89S19S26A1S1S2dVsegs;R7R6S1fG0S80R5S81R4R3A2A4A4S41S47R7A1S3bR7A1S3aR7A1S39R7A1S3cR7A1S20S26S2fR7A1R3A3S38R7A1R2S46R7A1A9S30S2S15S48R1A1S16A3S70S26S2eVsegs;RaS82R7S43RaA1A2A3R5A3S70S26S26S70S26S26S36S2bRdR1A2S2bRdR2A2A2Lo';S2fRbA1A3Lo;R6A3S32RcR7A2S2dVsegs;RdR5S1fG0S80RbS81RaR9A2A4A4F_;F_;F_;F_;TS';F_;Fnx;FN;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md N nx Hsm S' Hwf HN HX HP.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|].
    apply Forall_forall. intros o Ho.
    pose proof (proj1 (Forall_forall _ _) HN o Ho) as Hoh.
    pose proof (proj1 (Forall_forall _ _) HX o Ho) as HXo.
    eapply obj_holds_mem_ext; [ | | exact Hoh].
    + intros a. reflexivity.
    + intros off Hoff. cbn [with_mem ms_mem]. apply Hfr.
      destruct Hoh as (Hb & _).
      eapply ranges_disjoint_outside; [exact HXo|].
      unfold obj_range. rewrite u64_of_sum by lia. lia.
  - apply pairwise_disjoint_app; assumption.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Lemma obj_holds_frame_lit : ltac2:(tb__ "0|5|
S28S71S8Q40M0A1S17S8Q8A1M1A1M2F_;S27S0S0S19S1cS1cS0S1aA2S27A2A1S34Vsegs;R6A2SaG0S29R8R5A2A2S0SbS13SeZ2M3Z3eA2M4A1R5A2SbR6R5A2SdR6G4A2SbZ0ScR4R8A2A2SbScR5R8A2SeG3Z40A2A2S87RaR9R8A3S0S3SbRcR1A2SdR1RbA2A2S3S2S15S84Vsegs;RfS9G0ScR9R2A2A2A3S16A3S4G1G1S2G2S83Vsegs;R10S9G0ScRaR3A2A2A3S18G1R1A2A3Lx;A2A2F_;Foff;S86R10S83Vsegs;ReA2R8RaA4S2eVsegs;R11S82R10RfA2S85ReRdRcRbA4A4F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;Fcs;Fhi;Flo;Fbase;Fm;Fms;Frho;").
Proof using .
  intros rho ms m base lo hi cs Hrom b Hlo Hlh Hhi Hb0 Hb1 Hins Hview Hcells.
  unfold obj_holds, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
  rewrite !soff_lit_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (Hview off Hoff) as [W R]. exact (wview_of_views segs m _ W R). }
  split.
  { revert Hins Hcells. induction cs as [|[[o k] v] t IH]; intros Hins Hcells; [constructor|].
    apply Forall_cons_iff in Hins as [(Ho1 & Ho2 & Hk) Hins'].
    apply Forall_cons_iff in Hcells as [Hcv Hcells'].
    constructor; [|apply IH; assumption].
    unfold SymState.cell_holds. cbn [c_off c_width c_val]. rewrite !soff_lit_small by lia. rewrite Nat2Z.id.
    split; [lia|]. split; [lia|].
    apply rd_bytes_of_nth.
    - apply enc_bytes_length.
    - rewrite oaddr_unsigned by lia. fold b. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. fold b. rewrite rd_with_mem by exact Hrom.
      exact (Hcv j Hj). }
  split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite rd_with_mem by exact Hrom.
  destruct (Hview off Hoff) as [_ [x Hx]]. exists x. exact Hx.
Qed.

Lemma obj_holds_frame_rom : ltac2:(tb__ "0|9|
S28S71S8Q40M0A1S17S8Q8M1A1M2A1M3Fx;S0S0S1S34Vsegs;R5A2S3SbZ0M4R4A2M5SdR4SeZ2M6Z40A2M7A2A2S3G5SdR4SeG6Z3fA2A2A2SbScR6R5A2G7A2S2S0SfS23G2S33RaR5A2A2A1R6A3S0S3SbG4R1A2SdR1R8A2A2S3S2G3RbS9G0ScRaR2A2A2M8A1S1dG2A1A3S2G3S40Vsegs;G8A2S18G2S6fG2S11R2A1S33RdR8A2S9G1G4A2A4A2A3A2F_;Fk;S2eVsegs;RcS82RbRaA2S31S2aR9A1S2aG4A1S2aR8A1S1eS2cA1S3dR7A1A5A4F_;F_;F_;F_;F_;F_;Fl;Fn;Fb;Fm;Fms;Frho;").
Proof using .
  intros rho ms m b n l Hrom Hb Hn Hbn Hlen Hby.
  assert (EB : bv_unsigned (eval rho (SLit b)) = b) by (cbn [eval]; apply u64_of_sum; lia).
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite EB.
  rewrite !soff_lit_small by lia.
  split; [lia|]. split; [intros off _ D; discriminate D|]. split; [constructor|]. split.
  - intros off Hoff _. cbn [dflt_holds]. rewrite Z.sub_0_r. rewrite rd_with_mem by exact Hrom.
    destruct (Hby off ltac:(lia)) as [R1 R2]. unfold rd_of. rewrite R1. exact R2.
  - cbn [dflt_inv]. lia.
Qed.

Lemma wok_of_wview : ltac2:(tb__ "0|3|
S8Q40A1M0S17S8Q8A1M1A1M2F_;G0S5S2G2S73Vsegs;R2R1A3S1dG1A1A3A1S2S15S84Vsegs;R3R2A3S16A3F_;Fa;Fm;").
Proof using .
  intros m a H. unfold wview in H. unfold wok_of, wseg_addr.
  destruct (m a); [reflexivity|].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|exfalso; apply H; reflexivity].
  destruct (seg_writable seg); [reflexivity|]. exfalso; apply H; reflexivity.
Qed.

Lemma rd_of_eq_rd : ltac2:(tb__ "0|2|
S71S8Q40A1M0S17S8Q8A1A1M1Fx;G0S34Vsegs;R3A2S2G1R3R2A1S72R4R2A2A3S2G1S83Vsegs;R4R3A3S37R5R3A2A3F_;F_;Fa;Fm;Fms;").
Proof using . intros ms m a Hrom E. unfold rd_of, rd, ms_read_byte. rewrite E. destruct (ms_mem ms a); [reflexivity|]. symmetry. apply Hrom. Qed.

Lemma cell_holds_bytes : ltac2:(tb__ "0|6|
S28S27S0S0S71S0S0S27S4bR8R7R6R5R4S4dS2aR3A1R2R1A3A6S3SbS13SeZ2M0Z3eA2M1A1R4A2SbR4G1A2A2SbZ0M2ScSaQ40M3S29RaR9A2A2R5A2A2SbScScSaG3S29RbRaA2A2R6A2R5A2SeG0Z40A2A2SbG2R6A2S1aS7eR1S11R8A1A2S2S17S8Q8M4A1M5A1S37RbS9G3ScScSaG3S29RfReA2A2RaA2SfR2A1A2A2A2S18G5S6fG5R2S35S11R9A1S29RfR8A2A2S9G4G2A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;Fval;Fk;Foff;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms off k val (H1 & H2 & H3) Hoff Hb0 Hb1 Hk j Hj. cbn [c_off c_width c_val] in *.
  rewrite soff_lit_small in H3 by lia.
  pose proof (rd_bytes_nth ms (Z.to_nat k) _ _ j H3 Hj) as R.
  rewrite oaddr_unsigned in R by lia. apply R. lia.
Qed.

Lemma in_cell_dec : ltac2:(tb__ "0|1|
S28S0S2cS8fS4cR3R2R1A3M0S5G0A1A2Fc;Foff;Frho;").
Proof.
  intros rho off c. unfold in_cell.
  destruct (Z_le_dec (soff rho (c_off c)) off); [|right; lia].
  destruct (Z_lt_dec off (soff rho (c_off c) + c_width c)); [left; lia|right; lia].
Defined.

Lemma obj_holds_drop_cells : ltac2:(tb__ "0|0|
S28S71S27S27S27S19S2cA1S2eVsegs;R6R5S31R4R3R2R1S3eA5A4S2eVsegs;R7R6S31R5R4R3S1eS2cA1S3eA5A4F_;Fcs;Fhi;Flo;Fbase;Fms;Frho;").
Proof using .
  intros rho ms base lo hi cs (Hb & Hw & Hc & Hd & _).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds].
  destruct (Exists_dec (in_cell rho off) cs (in_cell_dec rho off)) as [Hcov|Hncov].
  - apply Exists_exists in Hcov as (c & Hcin & Hic).
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as (C1 & C2 & C3).
    unfold in_cell in Hic.
    pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia)) as R.
    rewrite oaddr_unsigned in R by lia.
    replace (bv_unsigned (eval rho base) + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))
      with (bv_unsigned (eval rho base) + off) in R by lia.
    eexists. apply R. lia.
  - apply Hd; [exact Hoff|]. unfold covered. exact Hncov.
Qed.

End WithSegs.

Lemma footprint_mem_range : ltac2:(tb__ "0|2|
S79S58S8dS8aS8bS0S7bR5R4R3A3S76R7R4A2S7dS1cS57S0A2S1fS57S0S62R4A1R3A4S66R6A1A3SbZ0R4A2S3SbS8cS75R9R6A2M0A2S3SbScG0R5A2M1S7aR9A1A2S7SbG1S78RaA1A2SbS77RaA1G0A2A2A2A2F_;F_;F_;F_;Fn;Fp;Fvm;Fs;FL;FC;").
Proof.
  intros C L s vm p n HV HL Hin Hn. rewrite (vm_ok_top L s vm HV).
  destruct HV as (_ & _ & _ & Hcov & _). destruct (Hcov p n Hin) as (e & He & E1 & E2).
  destruct (HL e He) as (G1 & G2 & G3). lia.
Qed.

