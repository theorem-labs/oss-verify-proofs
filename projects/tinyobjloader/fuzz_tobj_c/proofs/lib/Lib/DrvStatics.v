(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "rm"; "smatch"; "SLit"; "sstate"; "valuation"; "ss_objs"; "swf"; "mkSS"; "ranges_disjoint"; "obj_range"; "rw"; "SVar"; "agree_below"; "enc_bytes"; "eval"; "sfcsr"; "sprop"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "prod"; "nat"; "pair"; "bool"; "list"; "true"; "cons"; "option"; "nil"; "app"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.S"; "a_guard"; "a_got"; "a_nl"; "statics_view"; "app_objs"; "static3"; "statics_objs"; "statics_disjoint"; "O_got"; "O_guard"; "O_nl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "carved"; "wok_of"; "wseg_addr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "holds"; "statics_ok"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "MInv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "le_byte"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundI SymSoundR SymFrame SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface Contract Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.
Variable C : mconsts.

Definition a_got : Z := mc_chk_guard_got C.
Definition a_guard : Z := mc_chk_guard C.
Definition a_nl : Z := mc_need_locks C.

Definition O_got : sobj := ltac2:(tb__ "0|2|
S41SbZ0A1S36S22S36Z8A2S30S2aS2aS0S2bA2M0S8A2M1S2cG0S8S2cS0S2bS36U8A4SbS35A1A4S32G1A1A3A4").
Definition O_guard (v : positive) : sobj := ltac2:(tb__ "0|2|
S41SbZ0A1S35S22S35Z8A2S30S2aS2aS0S2bA2M0S8A2M1S2cG0S8S2cS0S2bS35U8A4S14Vv;A1A4S32G1A1A3A4").
Definition O_nl : sobj := ltac2:(tb__ "0|3|
S41SbZ0A1M0S37S22S37Z1A2S30S2aS2aS0S2bA2M1S8A2M2S2cG1S8S2cS0S2bS37U1A4G0A4S32G2A1A3A4").
Definition statics_objs (v : positive) : list sobj := ltac2:(tb__ "0|0|
S30S7S3dS30S7S3eVv;A1S30S7S3fS32S7A1A3A3A3").

Definition static3 (a : Z) : Prop := ltac2:(tb__ "0|1|
S6S3S23S36Va;A2S24Va;S22S36Z8M0A2A2A2S6S3S23S35Va;A2S24Va;S22S35G0A2A2A2S3S23S37Va;A2S24Va;S22S37Z1A2A2A2A2A2").

Definition statics_layout : Prop := ltac2:(tb__ "0|1|
S3S23Z0S36A2S3S23S22S36Z8M0A2S35A2S3S23S22S35G0A2S37A2S24S22S37Z1A2S26Z2Z3eA2A2A2A2A2").
Definition statics_wseg : Prop := ltac2:(tb__ "0|0|
S0S3aR1A1S2S2dS43Vsegs;S28Q40R2A2A2S2fA3F_;Fa;").
Hypothesis HL : statics_layout.
Hypothesis HW : statics_wseg.

Definition statics_view (m : word -> option byte) (g : Z) : Prop := ltac2:(tb__ "0|2|
S3S49S48S40Vsegs;Vm;A2S27Q40A1S2fL_;A2M0S36U8M1S35A4S3S49G0S35G1Vg;A4S49G0S37U1Z0A4A2A2").

Lemma MInv_statics_ok : ltac2:(tb__ "0|1|
S51S27Q40A1M0S31S27Q8A1A1F_;G0S2dF_;S47S52VC;R4R3R2R1A5S4aVC;S48R4G0S2fL_;A2S48R4R3A2A3F_;Fvm;Fwok;Frd;FA;").
Proof using . intros A rd wok vm H. unfold MInv in H. decompose [and] H. assumption. Qed.

Lemma statics_view_of_MInvR : ltac2:(tb__ "0|0|
S51SdS46S55Vsegs;VC;R3R2R1A5S4S0S0S38S9R4A1R1A2Lg;A2F_;Fmd;Frho;FA;").
Proof using .
  intros A rho md H. unfold MInvR in H. apply MInv_statics_ok in H.
  destruct H as (Hnl & _ & _ & _ & _ & _ & _ & _ & g & Hgot & Hg).
  exists g. split; [exact Hgot|]. split; [exact Hg|exact Hnl].
Qed.

Lemma holds_rd_of : ltac2:(tb__ "0|5|
S27Q40M0A1M1S31S27Q8M2A1M3A1M4F_;S0S2bS0S2bS49S48S40Vsegs;R5A2G1S2fL_;A2R4R3R2A4S4eR2R4A2S23Z0R6A2S23S22R7S25R6A1A2S26Z2Z40A2A2S2G4S40Vsegs;R9S28G0S22R8S25R5A1A2A2A3S34G3S28G2S56R6R7R5A3A2A2A3F_;F_;F_;F_;Fk;Fv;Fw;Fa;Fm;").
Proof using .
  intros m a w v k H Hk Ha Hw. specialize (H k Hk).
  destruct (byteview_of_Some _ _ _ _ H) as (_ & _ & b & Hb & Hv). rewrite Hb. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hv.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_wrap. rewrite Z.mod_small; [reflexivity|].
  change (bv_modulus 8) with 256 in *. lia.
Qed.

Lemma rd_of_wok : ltac2:(tb__ "0|5|
S27Q40M0A1S31S27Q8A1M1A1M2F_;S0S3aR1A1S4G1G1S2G2S40Vsegs;R4S28G0R3A2M3A3S34G1R1A2M4A3Lx;A2S3S2S2dS42Vsegs;R4G3A3S2fA3S4G1G1S2G2S40Vsegs;R5S28G0R4A2A3G4A3Lx;A2A2F_;F_;Fa;Fm;").
Proof using HW.
  intros m a Hs Hx. split; [|exact Hx]. unfold wok_of. destruct (m (Z_to_bv 64 a)); [reflexivity|]. apply HW. exact Hs.
Qed.

Definition app_objs (S : sstate) (os : list sobj) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S10S1fVS;A1S20VS;A1S1cVS;A1S1bVS;A1S21VS;A1S33S7SeVS;A1Vos;A3S1aVS;A1Vnx;S1dVS;A1A9").

Lemma app_objs_app : ltac2:(tb__ "0|1|
ScS2eS7A1M0G0S1S1S2ScS39S39R5R4R2A3R3R1A3S39R5S33S7R4R3A3R1A3A3Fnx2;Fnx1;Fos2;Fos1;FS;").
Proof using . intros. unfold app_objs. cbn. rewrite app_assoc. reflexivity. Qed.

Lemma swf_objs_sub : ltac2:(tb__ "0|2|
S0S2eS8A1M0G0S18S31S8A1S2eS7A1M1G1S2eS19A1S1S2dS2S2dSfS10RaR9R8R7R6R5R3R2R1A9A1S2fA3S7S53S7R1R6A3S53S7R2R8A3F_;Fo;S2S2dSfS10RcRbRaR9R8R6R5R4R3A9A1S2fA3F_;F_;Fln;Fnx;Ffa;Fobjs2;Fobjs1;Frv;Ffc;Ffr;Frg;Fpc;").
Proof using .
  intros pc rg fr fc rv objs1 objs2 fa nx ln H Hsub. unfold swf in *. cbn [ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat (apply andb_true_intro; split); try assumption.
  apply forallb_forall. intros o Ho. exact (proj1 (forallb_forall _ _) H1 o (Hsub o Ho)).
Qed.

Ltac swf_sub H := eapply swf_objs_sub; [exact H|]; cbn [ss_objs app_objs]; unfold statics_objs, O_got, O_guard, O_nl; intros o; rewrite <- ?app_assoc; cbn [app]; rewrite ?in_app_iff; cbn [In]; tauto.

Definition statics_disjoint (rho : valuation) (objs : list sobj) : Prop := ltac2:(tb__ "0|2|
S3S4bS7S7S11S12Vrho;R1A2M0S2cS0S0S36S22S36Z8M1A2A4A2Lo';Vobjs;A3S3S4bS7S7S11G0S2cS0S0S35S22S35G1A2A4A2Lo';Vobjs;A3S4bS7S7S11G0S2cS0S0S37S22S37Z1A2A4A2Lo';Vobjs;A3A2A2").

Lemma obj_range_carved0 : ltac2:(tb__ "0|1|
SdS0S0S2eS2aS2aS0S2bA2S8A2A1S3S23Z0M0R3A2S23R3R2A2A2S24R3S26Z2Z3eA2A2S2S2aS0S0A2S12R6S41SbG0A1R5R4R3A4A2S2cS0S0R5R4A4A3F_;F_;Fcs;Fhi;Flo;Frho;").
Proof using .
  intros rho lo hi cs Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi eval].
  rewrite !soff_lit_small by lia. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity. reflexivity.
Qed.

Theorem carve_statics : ltac2:(tb__ "0|1|
SdScS2aS2eS45A1S44A2S0S1S1SaVsegs;R6R5R4A4S38S9R7A1R4A2S2S27Q40M0A1S13R8R4A2S28G0R5A2A3S3cR9SeR8A1A2S2S2dSfS39R9S3bR6A1R5A3A1S2fA3SaVsegs;RbS39RaS3bR7A1R6A3R9A4F_;F_;F_;F_;F_;Fnx;Fv;Fg;Fw;FS;Frho;").
Proof using HL HW.
  intros rho S w g v nx Hsm (Vgot & Vg & Vnl) Hv (D1 & D2 & D3) Hwf.
  destruct HL as (L0 & L1 & L2 & L3).
  assert (B0 : bv_unsigned (eval rho (SLit 0)) = 0) by reflexivity.

  assert (H1 : smatch segs rho (app_objs S [O_got] nx) w).
  { apply (smatch_carve_obj segs rho S w (SLit 0) a_got (a_got + 8) [(a_got, 8%nat, SLit a_guard)] nx Hsm).
    - swf_sub Hwf.
    - lia. - lia. - lia. - lia. - rewrite B0; lia. - rewrite B0; lia.
    - constructor; [|constructor]. cbn. lia.
    - rewrite B0, !Z.add_0_l. exact D1.
    - intros off Hoff. rewrite B0, Z.add_0_l. apply rd_of_wok; [unfold static3; lia|].
      replace off with (a_got + Z.of_nat (Z.to_nat (off - a_got))) by lia.
      eexists. apply (holds_rd_of _ _ 8); [exact Vgot | lia | lia | lia].
    - constructor; [|constructor]. intros j Hj. rewrite B0, Z.add_0_l.
      rewrite (holds_rd_of _ _ 8 _ _ Vgot Hj) by lia. cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity. }

  assert (H2 : smatch segs rho (app_objs S [O_got; O_guard v] nx) w).
  { replace (app_objs S [O_got; O_guard v] nx) with (app_objs (app_objs S [O_got] nx) [O_guard v] nx) by (rewrite app_objs_app; reflexivity).
    apply (smatch_carve_obj segs rho (app_objs S [O_got] nx) w (SLit 0) a_guard (a_guard + 8) [(a_guard, 8%nat, SVar v)] nx H1).
    - swf_sub Hwf.
    - lia. - lia. - lia. - lia. - rewrite B0; lia. - rewrite B0; lia.
    - constructor; [|constructor]. cbn. lia.
    - rewrite B0, !Z.add_0_l. cbn [app_objs ss_objs]. apply Forall_app. split; [exact D2|].
      constructor; [|constructor]. unfold O_got. rewrite obj_range_carved0 by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - intros off Hoff. rewrite B0, Z.add_0_l. apply rd_of_wok; [unfold static3; lia|].
      replace off with (a_guard + Z.of_nat (Z.to_nat (off - a_guard))) by lia.
      eexists. apply (holds_rd_of _ _ 8); [exact Vg | lia | lia | lia].
    - constructor; [|constructor]. intros j Hj. rewrite B0, Z.add_0_l.
      rewrite (holds_rd_of _ _ 8 _ _ Vg Hj) by lia. cbn [eval]. rewrite Hv. rewrite nth_enc_bytes by lia. reflexivity. }

  replace (app_objs S (statics_objs v) nx) with (app_objs (app_objs S [O_got; O_guard v] nx) [O_nl] nx) by (rewrite app_objs_app; reflexivity).
  apply (smatch_carve_obj segs rho (app_objs S [O_got; O_guard v] nx) w (SLit 0) a_nl (a_nl + 1) [(a_nl, 1%nat, SLit 0)] nx H2).
  - swf_sub Hwf.
  - lia. - lia. - lia. - lia. - rewrite B0; lia. - rewrite B0; lia.
  - constructor; [|constructor]. cbn. lia.
  - rewrite B0, !Z.add_0_l. cbn [app_objs ss_objs]. apply Forall_app. split; [exact D3|].
    constructor; [|constructor; [|constructor]]; unfold O_got, O_guard; rewrite obj_range_carved0 by lia; unfold SymState.ranges_disjoint; cbn [fst snd]; lia.
  - intros off Hoff. rewrite B0, Z.add_0_l. apply rd_of_wok; [unfold static3; lia|].
    replace off with (a_nl + Z.of_nat (Z.to_nat (off - a_nl))) by lia.
    eexists. apply (holds_rd_of _ _ 1); [exact Vnl | lia | lia | lia].
  - constructor; [|constructor]. intros j Hj. rewrite B0, Z.add_0_l.
    rewrite (holds_rd_of _ _ 1 _ _ Vnl Hj) by lia. cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Corollary carve_statics_fresh : ltac2:(tb__ "0|1|
SdScS2aS2eS45A1S44A2S0S1S1SaVsegs;R6R5R4A4S57S1eR6A1R3A2S38S9R8A1R5A2S3cR9SeR8A1A2S2S2dSfS39R9S3bR6A1R5A3A1S2fA3S3SaVsegs;S54RbR7S28Q40R8A2A3M0S39RaS3bR7A1R6A3R9A4S15R7RbG0A3A2F_;F_;F_;F_;F_;Fnx;Fv;Fg;Fw;FS;Frho;").
Proof using HL HW.
  intros rho S w g v nx Hsm Hv V D Hwf.
  assert (Hag : agree_below v rho (rho_set_rw rho v (Z_to_bv 64 g))) by (apply agree_below_set_rw; lia).
  split; [|exact Hag].
  apply (carve_statics _ S w g v nx).
  - eapply smatch_agree; [|exact Hsm]. exact (agree_below_le _ _ _ _ Hv Hag).
  - exact V.
  - cbn. rewrite Pos.eqb_refl. reflexivity.
  - destruct D as (D1 & D2 & D3).
    pose proof (swf_objs _ (smatch_swf segs _ _ _ Hsm)) as Hwo.
    assert (E : forall o, In o (ss_objs S) -> obj_range (rho_set_rw rho v (Z_to_bv 64 g)) o = obj_range rho o).
    { intros o Ho. eapply obj_range_agree; [|exact (proj1 (forallb_forall _ _) Hwo o Ho)].
      exact (agree_below_le _ _ _ _ Hv Hag). }
    split; [|split]; apply Forall_forall; intros o Ho; rewrite (E o Ho);
      [exact (proj1 (Forall_forall _ _) D1 o Ho) | exact (proj1 (Forall_forall _ _) D2 o Ho) | exact (proj1 (Forall_forall _ _) D3 o Ho)].
  - exact Hwf.
Qed.

Lemma release_one : ltac2:(tb__ "0|c|
SdScS2aS2eS45A1S44A2S2eS7A1M0S0S0S0S2bS8SaVsegs;R9R8R7A4S2G0SeR9A1S33S7R7S30S7S41SbZ0M1A1R6R5S30S2aS2aS0S2bA2M2S8A2M3S2cG2S8S2cS0S2bR4R3A4R2A4S32G3A1A3A4S32S7A1A3A3A3S23G1R7A2S24R7S26Z2Z3eA2A2S2S0R9R7A3S2S0R9S22R8S25R7A1A2A3S3S4dU1R8A2S4dR8U8A2A2S2bS4eR1RaA2S2S31S27Q8M4A1M5A1M6S40Vsegs;S9R12A1S28Q40M7S22RcS25R2A1A2A2A3S34G5S4cG5R2S16RbS17R12RaA2A2S28G4G1A2A4A2A3F_;Fj;S0S3S23ReR1A2S24R1RdA2A2S2S2dS43Vsegs;S28G7R2A2A2S2fA3F_;Fa;S4S27G7A1M8G6F_;M9G9S3SaVsegs;S4fR13R1A2S50R12R10A2R11A4S3G8S5S3S23R10S29G7R1A2MaA2S24GaRfA2A2A1S2G6R3R2A1S9R15R2A2A3F_;Fa;S3G8S2G6S40Vsegs;R2R1A3S40Vsegs;S9R14A1MbR1A3A3Fa;G8S2S2dS42Vsegs;R2R1A3S42Vsegs;GbR1A3A3Fa;A2A2A2Lm';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fval;Fk;Foff;Fhi;Flo;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S w objs lo hi off k val Hsm Hobjs Hlo Hhi Elo Ehi Hk Hrd Hws.
  destruct (smatch_release_obj segs rho S w objs _ (ss_next S) Hsm Hobjs
              (swf_drop_objs S objs _ Hobjs (smatch_swf segs _ _ _ Hsm))) as (m' & Hsm' & Hout & Hin & Hoh & Hrom).
  assert (RNG : obj_range rho (carved (SLit 0) lo hi [(off, k, val)]) = (lo, hi)) by (apply obj_range_carved0; lia).
  rewrite RNG in Hout, Hin. unfold in_rng in Hout, Hin. cbn [fst snd] in Hout, Hin.
  exists m'. split; [exact Hsm'|]. split; [exact Hout|].
  assert (IN : forall a, lo <= bv_unsigned a < hi -> rd_of segs m' a = rd_of segs (rm rho) a).
  { intros a Ha. rewrite (rd_of_eq_rd segs _ m' a Hrom (Hin a Ha)).
    destruct Hoh as (_ & _ & Hc & _). apply Forall_inv in Hc. cbn [carved lit_cells ob_base] in Hc.
    assert (B0 : bv_unsigned (eval rho (SLit 0)) = 0) by reflexivity.
    pose proof (cell_holds_bytes rho (SLit 0) _ _ _ off (Z.of_nat k) val Hc ltac:(lia)
                  ltac:(rewrite B0; lia) ltac:(rewrite B0; lia) ltac:(lia)
                  (Z.to_nat (bv_unsigned a - off)) ltac:(lia)) as R.
    rewrite B0, Nat2Z.id in R.
    replace (0 + off + Z.of_nat (Z.to_nat (bv_unsigned a - off))) with (bv_unsigned a) in R by lia.
    rewrite Z_to_bv_bv_unsigned in R. rewrite R.
    transitivity (rd_of segs (rm rho) (Z_to_bv 64 (off + Z.of_nat (Z.to_nat (bv_unsigned a - off))))).
    - rewrite (Hrd (Z.to_nat (bv_unsigned a - off))) by lia. reflexivity.
    - f_equal. set (ua := bv_unsigned a) in *. pose proof (Z_to_bv_bv_unsigned 64 a) as Ea. change (Z_to_bv 64 ua = a) in Ea.
      rewrite <- Ea. f_equal. lia. }
  split.
  - intros a. destruct (Z_le_dec lo (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) hi)|].
    + apply IN. lia.
    + unfold rd_of. rewrite Hout by lia. reflexivity.
    + unfold rd_of. rewrite Hout by lia. reflexivity.
  - intros a. destruct (Z_le_dec lo (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) hi)|].
    + unfold wok_of. pose proof (Hws (bv_unsigned a) ltac:(lia)) as W. rewrite Z_to_bv_bv_unsigned in W.
      destruct (m' a); destruct (rm rho a); rewrite ?W; reflexivity.
    + unfold wok_of. rewrite Hout by lia. reflexivity.
    + unfold wok_of. rewrite Hout by lia. reflexivity.
Qed.

Theorem release_statics : ltac2:(tb__ "0|6|
SdScS2aS2eS45A1S44A2S2eS7A1M0S0S1SaVsegs;R6R5R4A4S2G0SeR6A1S33S7R4S3bR2A1A3A3S38S9R8A1R4A2S2S27Q40M1A1M2S13R9R4A2S28G1R5A2A3S4G2S31S27Q8A1A1M3F_;M4G4S3SaVsegs;S4fRbR1A2S50RaR8A2R9A4S3G2S5S3aS29G1R1A2A1A1S2G3R3R2A1S9RdR2A2A3F_;Fa;S3G2S2G3S40Vsegs;R2R1A3S40Vsegs;S9RcA1M5R1A3A3Fa;S3G2S2S2dS42Vsegs;R2R1A3S42Vsegs;G5R1A3A3Fa;S38R1R7A2A2A2A2A2Lm';A2F_;F_;F_;F_;Fv;Fg;Fobjs;Fw;FS;Frho;").
Proof using HL HW.
  intros rho S w objs g v Hsm Hobjs (Vgot & Vg & Vnl) Hv.
  destruct HL as (L0 & L1 & L2 & L3).

  destruct (release_one rho S w (objs ++ [O_got; O_guard v]) a_nl (a_nl + 1) a_nl 1 (SLit 0) Hsm
              ltac:(rewrite Hobjs; unfold statics_objs; rewrite <- app_assoc; reflexivity)
              ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as (m1 & Hsm1 & Out1 & Rd1 & Wk1).
  { intros j Hj. rewrite (holds_rd_of _ _ 1 _ _ Vnl Hj) by lia. cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity. }
  { intros a Ha. apply HW. unfold static3. lia. }

  destruct (release_one (set_rm rho m1) (set_objs S (objs ++ [O_got; O_guard v])) w (objs ++ [O_got]) a_guard (a_guard + 8) a_guard 8 (SVar v) Hsm1
              ltac:(cbn [ss_objs set_objs]; rewrite <- app_assoc; reflexivity)
              ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as (m2 & Hsm2 & Out2 & Rd2 & Wk2).
  { intros j Hj. cbn [set_rm rm eval rw]. rewrite Rd1. rewrite (holds_rd_of _ _ 8 _ _ Vg Hj) by lia. rewrite Hv, nth_enc_bytes by lia. reflexivity. }
  { intros a Ha. apply HW. unfold static3. lia. }

  destruct (release_one (set_rm (set_rm rho m1) m2) (set_objs (set_objs S (objs ++ [O_got; O_guard v])) (objs ++ [O_got])) w objs a_got (a_got + 8) a_got 8 (SLit a_guard) Hsm2
              ltac:(reflexivity) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as (m3 & Hsm3 & Out3 & Rd3 & Wk3).
  { intros j Hj. cbn [set_rm rm eval]. rewrite Rd2. cbn [set_rm rm]. rewrite Rd1. rewrite (holds_rd_of _ _ 8 _ _ Vgot Hj) by lia. rewrite nth_enc_bytes by lia. reflexivity. }
  { intros a Ha. apply HW. unfold static3. lia. }
  cbn [set_rm rm] in Out2, Out3, Rd2, Rd3, Wk2, Wk3, Hsm3.
  exists m3.
  assert (RD : forall a, rd_of segs m3 a = rd_of segs (rm rho) a) by (intros a; rewrite Rd3, Rd2, Rd1; reflexivity).
  split; [exact Hsm3|]. split; [|split; [exact RD|split]].
  - intros a Ha. unfold static3 in Ha. rewrite Out3 by lia. rewrite Out2 by lia. apply Out1. lia.
  - intros a. rewrite Wk3, Wk2, Wk1. reflexivity.
  - unfold statics_view.
    assert (BV : forall a, byteview_of (rd_of segs m3) (fun _ => true) a = byteview_of (rd_of segs (rm rho)) (fun _ => true) a).
    { intros a. unfold byteview_of. rewrite RD. reflexivity. }
    unfold holds. split; [|split]; intros kk Hk; rewrite BV; [apply Vgot | apply Vg | apply Vnl]; exact Hk.
Qed.

Lemma statics_view_ext : ltac2:(tb__ "0|4|
S27Q40M0A1S31S27Q8A1A1M1F_;M2G2S0S0S3aR1A1S2G1S40Vsegs;R4S28G0R2A2M3A3S40Vsegs;R5G3A3A3F_;Fa;S38R4R2A2S38R4R3A2F_;F_;Fg;Fm';Fm;").
Proof using HL.
  intros m m' g E (A & B & D). destruct HL as (L0 & L1 & L2 & L3).
  assert (BV : forall a, static3 a -> byteview_of (rd_of segs m') (fun _ => true) a = byteview_of (rd_of segs m) (fun _ => true) a).
  { intros a Ha. unfold byteview_of. rewrite (E a Ha). reflexivity. }
  unfold statics_view, holds in *.
  split; [|split]; intros k Hk; rewrite BV by (unfold static3; lia); auto.
Qed.

Lemma statics_view_rm : ltac2:(tb__ "0|4|
S27Q40M0A1S31S27Q8A1A1M1Fx;M2G2S0S0S3aR1A1S2G1R4S28G0R2A2M3A1R5G3A1A3F_;Fa;S38R4R2A2S38R4R3A2F_;F_;Fg;Fm';Fm;").
Proof using HL. intros m m' g E. apply statics_view_ext. intros a Ha. unfold rd_of. rewrite (E a Ha). reflexivity. Qed.

End S.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma statics_layout_P : statics_layout C_P. Proof. unfold statics_layout, a_nl, a_got, a_guard, mc_need_locks; cbn; lia. Qed.
Lemma statics_layout_U : statics_layout C_U. Proof. unfold statics_layout, a_nl, a_got, a_guard, mc_need_locks; cbn; lia. Qed.

Lemma statics_wseg_P : statics_wseg P.Init.segsP C_P.
Proof.
  intros a Ha.
  assert (X : forallb (fun a => wseg_addr P.Init.segsP (Z_to_bv 64 a)) (zseq (mc_chk_guard_got C_P) 8 ++ zseq (mc_chk_guard C_P) 8 ++ zseq (mc_need_locks C_P) 1) = true)
    by (vm_cast_no_check (@eq_refl bool true)).
  rewrite forallb_forall in X. apply X. unfold static3, a_got, a_guard, a_nl in Ha.
  rewrite !in_app_iff, !In_zseq. lia.
Qed.
Lemma statics_wseg_U : statics_wseg U.Init.segsU C_U.
Proof.
  intros a Ha.
  assert (X : forallb (fun a => wseg_addr U.Init.segsU (Z_to_bv 64 a)) (zseq (mc_chk_guard_got C_U) 8 ++ zseq (mc_chk_guard C_U) 8 ++ zseq (mc_need_locks C_U) 1) = true)
    by (vm_cast_no_check (@eq_refl bool true)).
  rewrite forallb_forall in X. apply X. unfold static3, a_got, a_guard, a_nl in Ha.
  rewrite !in_app_iff, !In_zseq. lia.
Qed.
