(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sobj"; "eval"; "rw"; "holds"; "obj_holds"; "smatch"; "sstate"; "SVar"; "rl"; "SLit"; "cell"; "mkSS"; "obj_range"; "soff"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "DUnknown"; "SPUle"; "mkCell"; "mkObj"; "mkVal"; "ob_base"; "ob_lo"; "rm"; "rom_ok"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "nat"; "true"; "list"; "pair"; "cons"; "length"; "option"; "app"; "nil"; "false"; "andb"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "of_nat"; "opp"; "modulo"; "leb"; "ltb"; "sub"; "to_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "ln_rank"; "Vdown"; "lex_val"; "lmeas"; "lnode"; "ln_vars"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zr_of"; "toS"; "zeval"; "zl_of"; "zsupported"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.S"; "ro_view"; "zlen_obj"; "inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "cells_in_view"; "cells_inside"; "lit_cells"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "MInv"; "ma_blocks"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mconsts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface Contract Glue ObjBytes ReprGlue ZEval.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition coveredb (lo hi : Z) (cs : list (Z * nat * sv)) : bool := ltac2:(tb__ "0|3|
S5dS30S30S3fVlo;S41R1A1M0A2S0S5cS2fS2fS0S30A2M1S6A2M2G2G2S2eLc;R1G1S6G1S2eLp;R2S0S30S3aS44R2R6A2S45R6S3fR2G0A2A2A2Lk;Lo;X2fx1Ls;Lp;X2fx1Lc;Vcs;A3Toff;Lj;S53U0S47S46Vhi;Vlo;A2A1A2A3").

Lemma coveredb_cover : ltac2:(tb__ "0|2|
S0S0S32S2fS2fS0S30A2M0S6A2M1A1S0S2S2eS6dR4R3R2A3S31A3S3S3dR5R2A2S3eR2R4A2A2S4S0S0S4S30S30S4S6S6S3S5bG1S33G0S6S33S0S30R3R2A4R1A4R7A3S3S3dR3R6A2S3eR6S3fR3S41R2A1A2A2A2A2Lv;A2Lk;A2Lo;A2F_;F_;Foff;Fcs;Fhi;Flo;").
Proof.
  intros lo hi cs off H Hoff. unfold coveredb in H.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (off - lo)) ltac:(apply in_seq; lia)) as X. cbn beta in X.
  apply existsb_exists in X as (c & Hin & Hc). destruct c as [[o k] v].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists o, k, v. split; [exact Hin|]. rewrite Z2Nat.id in H1, H2 by lia. lia.
Qed.

Lemma lit_cells_In : ltac2:(tb__ "0|2|
S32S2fS2fS0S30A2M0S6A2M1A1S0S30S6S5bG1S33G0S6S33S0S30R3R2A4R1A4R4A3S5bS13S22S12R4A1S41R3A1R2A3S69R5A1A3F_;Fv;Fk;Fo;Fcs;").
Proof.
  induction cs as [|[[o' k'] v'] t IH]; intros o k v Hin; [destruct Hin|].
  destruct Hin as [E|Hin]; [injection E as -> -> ->; left; reflexivity | right; apply IH; exact Hin].
Qed.

Section S.
Variable segs : list Segment.

Definition ro_view (rho : valuation) (m : word -> option byte) (o : sobj) : Prop := ltac2:(tb__ "0|3|
S4S6S6S4S0S0S4S0S0S4S32S2fS2fS0S30A2S6A2A1M0G0S3S2S9Vo;S66R4R3R2R1A4A3S3S2S2eS6dR3R2R1A3S31A3S3S68R3R2R1A3S3S3S3dS42S40Z2Z3eA2M1A1R3A2S3dR3R2A2A2S3S3eR2G1A2S3S67Vrho;S64Vsegs;Vm;A2S48Q40M2SaVrho;R4A2A2R1A4S0S3S3dR4R1A2S3eR1R3A2A2S2S2eS65Vsegs;Vm;S4aG2S3fS48G2SaVrho;R6A2A2R2A2A2A3S31A3F_;Foff;A2A2A2A2A2A2Lcs;A2Lhi;A2Llo;A2Lbase;A2").

Lemma ro_view_agree_vars : ltac2:(tb__ "0|2|
S1S2eF_;S7S7S49Q40A1M0S36S49Q8A1M1A1F_;S9S1S2S2eR6R1A1S31A3S2G0SbR6R2A2SbR5R2A2A3F_;Fv;S1S2S32G1A1S11R6R1A2S11R5R1A2A3Fl;S2S2eS6fR7R3A2S31A3S61R7R5R4A3S61R7R6R5A3F_;F_;F_;F_;Fo;Fm;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' m o Hv Hl Ho (base & lo & hi & cs & -> & Hcov & Hins & Hlo & Hhi & Hview & Hwok).
  unfold obj_vars_all, carved in Ho. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Ho.
  apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho Hcs]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Hbase _].
  exists base, lo, hi, cs. split; [reflexivity|]. split; [exact Hcov|]. split; [exact Hins|]. split; [exact Hlo|]. split; [exact Hhi|].
  rewrite <- (eval_agree_vars f rho rho' base Hv Hl Hbase). split; [|exact Hwok].
  unfold cells_in_view in *. apply Forall_forall. intros [[o k] v] Hin j Hj.
  pose proof (proj1 (Forall_forall _ _) Hview (o, k, v) Hin j Hj) as X. cbn beta in X.
  assert (Hvv : sv_vars_all f v = true).
  { pose proof (lit_cells_In cs o k v Hin) as Hc. pose proof (proj1 (forallb_forall _ _) Hcs _ Hc) as Y.
    cbn [c_off c_val] in Y. apply andb_prop in Y as [_ Y]. exact Y. }
  rewrite <- (eval_agree_vars f rho rho' v Hv Hl Hvv). exact X.
Qed.

Lemma ro_view_release : ltac2:(tb__ "0|5|
S7S54S49Q40M0A1M1S36S49Q8A1A1M2F_;S9G1S28Vsegs;R4A2SdVsegs;R6R5R3A4S61R7R5R4A3S3S3dS3bS0S0S15R8R5A2M3A3S48G0R4A2M4A2S3eG4S3cS0S0G3A3A2A2G1G2Fx;S2G2R1R6A1S55R9R6A2A3S3S2G2S64Vsegs;R2R7A3S64Vsegs;R9R7A3A3S2S2eS65Vsegs;R2R7A3S65Vsegs;R9R7A3A3A2F_;Fm';F_;F_;F_;F_;Fa;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o a Hrom Hoh (base & lo & hi & cs & -> & Hcov & Hins & Hlo & Hhi & Hview & Hwok) Ha m' Hm'.
  unfold obj_range, obj_lo_of, obj_hi_of, carved in Ha. cbn [ob_base ob_lo ob_hi fst snd] in Ha.
  rewrite !soff_lit_small in Ha by lia.
  set (b := bv_unsigned (eval rho base)) in *.
  destruct (coveredb_cover lo hi cs (bv_unsigned a - b) Hcov ltac:(lia)) as (o & k & v & Hin & Hoff).
  pose proof (lit_cells_In cs o k v Hin) as Hc.
  pose proof (proj1 (Forall_forall _ _) Hins (o, k, v) Hin) as Hok. cbn beta iota in Hok.
  assert (Ea : a = Z_to_bv 64 (b + o + Z.of_nat (Z.to_nat (bv_unsigned a - b - o)))).
  { rewrite Z2Nat.id by lia. replace (b + o + (bv_unsigned a - b - o)) with (bv_unsigned a) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  split.
  - rewrite (rd_of_eq_rd segs ms m' a Hrom Hm').
    pose proof (cell_bytes_sym segs rho ms _ _ (Z.to_nat (bv_unsigned a - b - o)) Hoh Hc) as R.
    cbn [c_width c_off c_val ob_base carved] in R. rewrite soff_lit_small in R by lia. fold b in R. rewrite Nat2Z.id in R.
    specialize (R ltac:(lia)). rewrite <- Ea in R. rewrite R.
    pose proof (proj1 (Forall_forall _ _) Hview (o, k, v) Hin (Z.to_nat (bv_unsigned a - b - o)) ltac:(lia)) as V. cbn beta in V.
    rewrite <- Ea in V. rewrite V. reflexivity.
  - assert (W1 : wok_of segs m a = true).
    { specialize (Hwok (bv_unsigned a - b) ltac:(lia)). replace (b + (bv_unsigned a - b)) with (bv_unsigned a) in Hwok by lia.
      rewrite Z_to_bv_bv_unsigned in Hwok. exact Hwok. }
    rewrite W1. destruct (dunk_byte segs rho ms (carved base lo hi cs) (bv_unsigned a) Hoh eq_refl) as [_ W2].
    { unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd]. rewrite !soff_lit_small by lia. fold b. lia. }
    rewrite Z_to_bv_bv_unsigned in W2. unfold wok_of. rewrite Hm'.
    unfold wview in W2. destruct (ms_mem ms a); [reflexivity|]. unfold wseg_addr.
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|exfalso; apply W2; reflexivity].
    destruct (seg_writable sg); [reflexivity|]. exfalso. apply W2. reflexivity.
Qed.

Lemma blocks_init_done : ltac2:(tb__ "0|2|
S78S74S49Q40A1M0S36S49Q8A1A1F_;G0S2eF_;S6cS2fS0S0A2M1S75R6R5R4R3R2A5S5bG1R2S76R6A1A3S2S2eS79S77R7A1A1S31A3F_;F_;Fb;Fvm;Fwok;Frd;FA;FC;").
Proof using .
  intros C A rd wok vm b (HWF & _) Hin.
  destruct (st_init_done (ma_s A)) eqn:E; [reflexivity|]. exfalso.
  pose proof (inv_ctx HWF) as HC. unfold ctx_ok in HC.
  destruct HC as (_ & _ & _ & _ & HC).
  assert (HM : st_metas (ma_s A) = []).
  { clear Hin. revert HC E. generalize (ma_s A). intros s HC E.
    repeat match type of HC with _ /\ _ => let X := fresh in destruct HC as [X HC]; try (specialize (X E); tauto) end.
    all: try (specialize (HC E); tauto). all: tauto. }
  unfold ma_blocks, blocks, user_blocks, used_metas in Hin. rewrite HM in Hin. cbn in Hin. exact Hin.
Qed.

Theorem smatch_release_suffix : ltac2:(tb__ "0|6|
S7SfS32S6aA1M0S54S6bS32S9A1M1G1S1SeVsegs;R8R7S33G0S5fR6S60R5R4A2A4A4S2G1S1bR8A1S37S9R4R3A3A3S7aRaR4R7A3S49Q40A1M2S36S49Q8A1A1M3F_;S14S1cRaA1S1dRaA1S19RaA1S18RaA1S1eRaA1R6S17RaA1R4S1aRaA1A9SfS2S2eS1fR1A1S31A3S3SeVsegs;S24SbRdA1S11RdA1R3A3R2S33G0S5fRbS60RaR9A2A4A4S3G2S5S6eReR8R1A3M4A1S2G3R5R2A1M5S27RfR2A2A3F_;Fa;S3G2G4S2G3G5S55RcR2A2A3F_;Fa;S52S9SdVsegs;RdRaA3R7A3A2A2A2F_;TS';Tm';F_;F_;Fnx;FR2;FR1;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md R1 R2 nx Hsm Hobjs m' S' Hwf.
  assert (Hsm1 : smatch segs (mkVal (rw rho) (rl rho) m') S (tr, mkCfg ms md)).
  { apply smatch_set_rm; [|exact Hsm]. intros a Ha. unfold m'. apply release_out.
    intros (o & Ho & Hin). rewrite Hobjs in Ha. apply outside_all_app_iff in Ha as [_ Ha].
    exact (proj1 (Forall_forall _ _) Ha o Ho Hin). }
  split; [|split; [intros a Ha; apply release_out; exact Ha | split; [intros a Ha; apply release_in; exact Ha|]]].
  - apply (smatch_drop_suffix segs (mkVal (rw rho) (rl rho) m') S tr ms md R1 R2 nx Hsm1 Hobjs Hwf).
    intros a (o & Ho & Hin). cbn [rm]. unfold m'. symmetry. apply release_in. exists o. split; [exact Ho|].
    rewrite obj_range_set_rm' in Hin. exact Hin.
  - destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [snd cfg_ms] in Hall.
    rewrite Hobjs in Hall. apply Forall_app in Hall as [_ Hall]. exact Hall.
Qed.

Definition zlen_obj (base : sv) : sobj := ltac2:(tb__ "0|1|
S23Vbase;S12Z0A1M0G0S38S13A1S20A5").

Lemma zlen_obj_range : ltac2:(tb__ "0|1|
S7S6S2S2fS0S0A2S15R2S62R1A1A2S33S0S0S48Q40SaR2R1A2A2M0G0A4A3Fbase;Frho;").
Proof using . intros. unfold obj_range, obj_lo_of, obj_hi_of, zlen_obj. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. f_equal; lia. Qed.

Lemma zlen_obj_holds : ltac2:(tb__ "0|0|
S7S54S6SdVsegs;R3R2S62R1A1A4Fbase;Fms;Frho;").
Proof using .
  intros rho ms base. unfold obj_holds, zlen_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  rewrite !soff_lit_small by lia. pose proof (urange (eval rho base)).
  split; [lia|]. split; [intros; lia|]. split; [constructor|]. split; [intros; lia|]. exact I.
Qed.

Lemma smatch_add_zlen : ltac2:(tb__ "0|0|
S7SfS2fS32S6aA1S5fA2S6S1SeVsegs;R5R4R3A4S14S1cR5A1S1dR5A1S19R5A1S18R5A1S1eR5A1S37S9S1bR5A1S34S9S62R3A1S38S9A1A3A3S17R5A1R2S1aR5A1A9SfS2S2eS1fR1A1S31A3SeVsegs;R8R2R6A4F_;TS';F_;Fnx;Fbase;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] base nx Hsm S' Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa]. cbn [ss_objs].
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [apply zlen_obj_holds | constructor].
  - apply (proj2 (pairwise_disjoint_pdr rho _)). cbn [ss_objs S']. rewrite map_app. apply pdr_app.
    + apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
    + cbn. split; [constructor | exact I].
    + intros r1 r2 _ Hr2. cbn in Hr2. destruct Hr2 as [<- | []]. rewrite zlen_obj_range. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr. cbn [ss_objs S'] in Ha. rewrite Forall_app in Ha. exact (proj1 Ha).
Qed.

Definition inclb (l1 l2 : list sprop) : bool := ltac2:(tb__ "0|0|
S5dS8S8S5cS8S29R1A1Vl2;A3Lf;Vl1;A3").
Lemma inclb_incl : ltac2:(tb__ "0|1|
S32S8A1M0G0S2S2eS63R2R1A2S31A3S5eS8R3R2A3F_;Fl2;Fl1;").
Proof using .
  intros l1 l2 H f Hf. pose proof (proj1 (forallb_forall _ _) H f Hf) as X. cbn beta in X.
  apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g. exact Hg.
Qed.
Lemma Forall_inclb : ltac2:(tb__ "0|1|
S7S32S8A1M0G0S2S2eS63R2R1A2S31A3S52S8ScR4A1R2A3S52S8ScR5A1R4A3F_;F_;Fl2;Fl1;Frho;").
Proof using . intros rho l1 l2 H HF. apply Forall_forall. intros f Hf. exact (proj1 (Forall_forall _ _) HF f (inclb_incl l1 l2 H f Hf)). Qed.

Lemma toS_small : ltac2:(tb__ "0|0|
S0S3S3dZ0R1A2S3eR1S40Z2Z3fA2A2A2S2S0S57Z40R2A2R2A3F_;Fx;").
Proof using .
  intros x Hx. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  destruct (x <? 2 ^ 63) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia.
Qed.

Lemma soff_zeval : ltac2:(tb__ "0|0|
S7S6S2S2eS5aR1A1S31A3S2S0S16R3R2A2S57Z40S58S56R3A1S59R3A1R2A3A2A3F_;Fe;Frho;").
Proof using . intros rho e He. unfold soff. rewrite bv_signed_toS by (cbn; lia). rewrite (eval_zeval rho e He). reflexivity. Qed.

Lemma zr_of_u : ltac2:(tb__ "0|0|
S7S1S2S0S56R2R1A2S48Q40SbR2R1A2A2A3Fi;Frho;").
Proof using . reflexivity. Qed.

Lemma zvar : ltac2:(tb__ "0|0|
S7S1S2S0S43S56R2R1A2S40Z2Z40A2A2S48Q40SbR2R1A2A2A3Fi;Frho;").
Proof using . intros. unfold zr_of. apply Z.mod_small. apply urange. Qed.

Lemma ule_z : ltac2:(tb__ "0|3|
S7S6S6S2S2eS5aR2A1S31A3M0G0ScR5S21R4R3A2A2S3dS58S56R6A1M1S59R6A1M2R5A3S58G1G2R4A3A2F_;F_;F_;Fb;Fa;Frho;").
Proof using . intros rho a b Ha Hb H. cbn [SymState.holds] in H. rewrite !eval_zeval in H by assumption. exact H. Qed.

Lemma window_facts : ltac2:(tb__ "0|8|
S7S54S0S9S3S3eZ0M0R2A2S3eR2S40Z2M1Z28A2M2A2A2S52S8ScR5A1S37S8S34S8S71S34S8S72R3A1S38S8A1A3A3S70R3A1A3A3S2S6S25R3A1S10PaM3A1A3S2S6S26R4A1S10S73A1A3SdVsegs;R8R7R5A4S48Q40M4SbR9G3A2A2S0S57Z40M5S48G4SbRaPfM6A2A2A2S0S3S3dR1S42R9A1A2S3S3dS42G2A1R1A2S3S3dG0S3fR2R1A2M7A2S3S3dZ7fff7f800000G7A2S3S2S0S43R2Z10A2G0A3S3S3eR2S40G1G5A2A2S2S0S16RbS10G6A1A2R1A3A2A2A2A2A2A2TsD;Tu10;F_;F_;F_;F_;F_;Fo;Fd;Fms;Frho;").
Proof using .
  intros rho ms d o Hd F Hob Hol HO u10 sD.
  pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
  set (u15 := bv_unsigned (rw rho 15%positive)) in *.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- d)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2.
  assert (T1 : toS 64 ((- d) mod 2 ^ 64) = - d).
  { unfold toS. destruct (Z.eq_dec d 0) as [->|Hne]; [reflexivity|].
    rewrite (Z.mod_small ((- d) mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
    replace ((- d) mod 2 ^ 64) with (2 ^ 64 - d) by (Z.to_euclidean_division_equations; lia).
    destruct (2 ^ 64 - d <? 2 ^ (64 - 1)) eqn:E; [apply Z.ltb_lt in E; exfalso; change (2 ^ (64 - 1)) with (2 ^ 63) in E; lia | lia]. }
  rewrite T1 in H1. replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  assert (AL : u10 mod 16 = 0).
  { pose proof (proj1 (Forall_forall _ _) F F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H). }
  assert (SO : soff rho (SVar 15%positive) = sD).
  { unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). reflexivity. }
  assert (SL : 0 <= u10 + sD).
  { destruct HO as ((Hb & _) & _). unfold obj_lo_of in Hb. rewrite Hob, Hol in Hb. cbn [eval] in Hb. unfold V_DEPTH in Hb. rewrite SO in Hb. exact Hb. }
  assert (SH : aceil_lo <= u10 + sD).
  { pose proof (proj1 (Forall_forall _ _) F (F_sp_high d) ltac:(right; left; reflexivity)) as H.
    rewrite (holds_zholds rho) in H by reflexivity. unfold F_sp_high in H. cbn [zholds zeval zalu] in H. unfold zr_of, V_DEPTH in H. fold u10 u15 in H.
    rewrite (Z.mod_small u10), (Z.mod_small u15) in H by lia.
    rewrite (Z.mod_small aceil_lo) in H by lia.
    assert (E : u15 = sD + 2 ^ 64).
    { unfold sD, toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
      destruct (u15 <? 2 ^ 63) eqn:C; [|lia]. apply Z.ltb_lt in C. exfalso. unfold sD, toS in H1. rewrite Z.mod_small in H1 by lia.
      change (2 ^ (64 - 1)) with (2 ^ 63) in H1. rewrite (proj2 (Z.ltb_lt _ _) C) in H1. lia. }
    rewrite E in H. replace (u10 + (sD + 2 ^ 64)) with ((u10 + sD) + 1 * 2 ^ 64) in H by lia.
    rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. exact H. }
  repeat split; try lia.
Qed.

Lemma triple_skip : ltac2:(tb__ "0|0|
S2bOF_;S2aS2aS2bR3R1A1R3R2A1F_;Fw;S2dVsegs;R4R3R2A4F_;FQ';FP;Fok;").
Proof using . intros ok P Q' H. eapply triple_conseq; [exact H | intros w Hw; exact Hw | apply triple_refl]. Qed.
Lemma etriple_skip : ltac2:(tb__ "0|0|
S2aS2aS2bR3R1A1R3R2A1F_;Fw;S2cVsegs;R3R2A3F_;FQ';FP;").
Proof using . intros P Q' H w Hw. exists w. split; [apply wsteps_refl | exact (H w Hw)]. Qed.
Lemma triple_inh : ltac2:(tb__ "0|0|
S2bOF_;S2aS2aS2bR3R1A1S2dVsegs;R5R4R3A4F_;Fw;S2dVsegs;R4R3R2A4F_;FQ';FP;Fok;").
Proof using . intros ok P Q' H n Hg w Hw. exact (H w Hw n Hg w Hw). Qed.
Lemma etriple_inh : ltac2:(tb__ "0|0|
S2aS2aS2bR3R1A1S2cVsegs;R4R3A3F_;Fw;S2cVsegs;R3R2A3F_;FQ';FP;").
Proof using . intros P Q' H w Hw. exact (H w Hw w Hw). Qed.
Lemma triple_pre : ltac2:(tb__ "0|0|
S2bOF_;S2aS2aS2aS2bR3R1A1R5R2A1F_;Fw;S2dVsegs;R5R4R2A4S2dVsegs;R6R4R3A4F_;F_;FQ';FP';FP;Fok;").
Proof using . intros ok P P' Q' HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma etriple_pre : ltac2:(tb__ "0|0|
S2aS2aS2aS2bR3R1A1R5R2A1F_;Fw;S2cVsegs;R4R2A3S2cVsegs;R4R3A3F_;F_;FQ';FP';FP;").
Proof using . intros P P' Q' HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma triple_post : ltac2:(tb__ "0|0|
S2bOF_;S2aS2aS2aS2bR3R1A1R3R2A1F_;Fw;S2dVsegs;R5R4R3A4S2dVsegs;R6R5R3A4F_;F_;FQ';FQ0;FP;Fok;").
Proof using . intros ok P Q0 Q' HQ H. eapply triple_conseq; [intros w Hw; exact Hw | exact HQ | exact H]. Qed.
Lemma etriple_post : ltac2:(tb__ "0|0|
S2aS2aS2aS2bR3R1A1R3R2A1F_;Fw;S2cVsegs;R4R3A3S2cVsegs;R5R3A3F_;F_;FQ';FQ0;FP;").
Proof using . intros P Q0 Q' HQ H. eapply etriple_conseq; [intros w Hw; exact Hw | exact HQ | exact H]. Qed.

End S.

Lemma lex_val_lt_first : ltac2:(tb__ "0|4|
S7S6S6S32S2fS4bS6A2M0A1M1G1S2S30S35G0R2A2S35G0R1A2A3S3eS48Q40M2SaR6R5A2A2S48G2SaR6R4A2A2A2S3eS4eR7S34G0S33S4bS6S4dS39A1M3R6A4R4A3A2S4eR7S34G0S33S4bS6G3R5A4R3A3A2A2F_;F_;Ft2;Ft1;Fe2;Fe1;Frho;").
Proof.
  intros rho e1 e2 t1 t2 Hlen Hlt. cbn [lex_val comp_val fst snd base_val]. rewrite Hlen.
  pose proof (lex_val_range rho t1) as [_ B1]. pose proof (lex_val_range rho t2) as [B2 _].
  rewrite Hlen in B1. pose proof (B64_pos (length t2)) as P. nia.
Qed.

Lemma lmeas_lt_first : ltac2:(tb__ "0|6|
S50S50S7S7S6S6S32S2fS4bS6A2M0A1M1G1S2S0S4cR8A1S4cR7A1A3S3dZ0M2S4cR9A1A2S2G1S51RaA1S34G0S33S4bS6S4dS39A1R6A4R4A3A3M3G3S2S30S35G0R6A2S35G0R5A2A3S3eS48Q40M4SaRbR9A2A2S48G4SaRaR8A2A2A2S3S3dG2S4fReRcA2M5A2S3eG5S4fRdRbA2A2A2F_;F_;F_;F_;F_;F_;Ft2;Ft1;Fe2;Fe1;FrhoE;FrhoC;FnE;FnC;").
Proof.
  intros nC nE rhoC rhoE e1 e2 t1 t2 Hr H0 HvC HvE Hlen Hlt.
  split; [apply lmeas_nonneg; exact H0|].
  unfold lmeas. rewrite HvC, HvE, Hr. cbn [length]. rewrite Hlen.
  assert (L : lex_val rhoC ((Vdown false, e1) :: t1) < lex_val rhoE ((Vdown false, e2) :: t2)).
  { cbn [lex_val comp_val fst snd base_val]. rewrite Hlen.
    pose proof (lex_val_range rhoC t1) as [_ B1]. pose proof (lex_val_range rhoE t2) as [B2 _].
    rewrite Hlen in B1. pose proof (B64_pos (length t2)) as P. nia. }
  pose proof (B64_pos (LMAX - S (length t2))) as P2. nia.
Qed.
