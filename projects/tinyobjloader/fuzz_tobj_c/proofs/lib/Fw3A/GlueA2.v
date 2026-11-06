(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "div"; "opp"; "sub"; "ge"; "modulo"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "eval"; "ss_objs"; "DZero"; "cell"; "mkObj"; "obj_range"; "ranges_disjoint"; "sstate"; "valuation"; "mkSS"; "rm"; "smatch"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "sv_below"; "@Corelib.Init.Datatypes"; "pair"; "nil"; "bool"; "cons"; "list"; "true"; "app"; "Some"; "option"; "false"; "fst"; "prod"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "ax_X"; "ax_base"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_size"; "Model"; "event"; "m_vm_lazy"; "m_vmmaps"; "page_in_ranges"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA2.G2"; "zero_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymCFG SymCall Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section G2.
Variable segs : list Segment.

Definition zero_obj_at (eb : sv) : sobj := ltac2:(tb__ "0|0|
S13Veb;SeZ0A1SeS3fA1S26S12A1S11A5").

Lemma SPA_prepay_zero_at : ltac2:(tb__ "0|6|
S47S17S3cS37Q40M0A1M1SdS29G1A1S29S41A1M2S49S40S46Vsegs;R9R7R8R4S25G2S38R3S39R2R1A2A4A6S32SaS8S35G0R7A2S3fA2Z0M3A3S32S27S44R8S42R3A1A2S2aA3S34S4aG1R9R7A3A1SaS33S1G3R1A2S2R1S3fA2A2S32S27S4cS45S43R7A1A1S0S35G0RcA2R2A2A2S2eA3F_;Fj;S7S4eR6R9A2S3fA2S48ScScS15S14RfR1A2S25SaSaS35G0RdA2M4S0G4S3fA2A4A2Lo;S10S3aRdA1A1A3R10RfRbRaR8A4R11R10S28G1ReRcA3RbR9A4F_;S32S27S24S1fS3aRfA1A1RdA2S2aA3S32G1SfR11ReA2RfA3S46Vsegs;R13S3bR11S4bS3aR11A1M5S2bScS10G5A1S28ScS4dRfA1S26ScA1A3A3A2A2R12S28G1R10ReA3S25G2S38RdS39RcRbA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Feb;Fp;FA;Frho;FJ;").
Proof using .
  intros J rho A p eb tp tr ms md [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hal Hlz Hnin Hacc Hroom Hdisj HJ Heb Hevb.
  pose proof (urange p) as Rp. pose proof page_size_pos as Pps.
  pose proof (page_aligned_end p Hal) as Hp64. assert (Pv : page_size = 4096) by reflexivity.

  assert (Hhid : forall a, in_page p a -> hid md tp a = true).
  { intros a Ha. unfold hid. rewrite (page_base_in_page p a Hal Ha), Hlz. cbn.
    destruct (page_mem p tp) eqn:E; [|reflexivity]. apply page_mem_In in E. exfalso. exact (Hnin E). }
  assert (Hvis : forall a, in_page p a -> hid md (p :: tp) a = false).
  { intros a Ha. rewrite hid_cons, (page_base_in_page p a Hal Ha). unfold bv_eqb. rewrite Z.eqb_refl. cbn. apply andb_false_r. }
  assert (Hsame : forall a, hid md (p :: tp) a = true -> hid md tp a = true).
  { intros a Ha. rewrite hid_cons in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
  assert (Hother : forall a, ~ in_page p a -> hid md (p :: tp) a = hid md tp a).
  { intros a Hn. rewrite hid_cons. destruct (hid md tp a) eqn:E; [|reflexivity]. cbn.
    destruct (bv_eqb (page_base a) p) eqn:E2; [|reflexivity]. exfalso. apply Hn. apply in_page_of_base. apply bv_eqb_eq. exact E2. }
  assert (MEMold : forall a, ~ in_page p a -> ms_mem (vms md (p :: tp) ms) a = ms_mem (vms md tp ms) a).
  { intros a Ha. rewrite !vms_mem, (Hother a Ha). reflexivity. }
  assert (MEMnew : forall a, in_page p a -> ms_mem (vms md (p :: tp) ms) a = Some (Z_to_bv 8 0)).
  { intros a Ha. rewrite vms_mem, (Hvis a Ha). destruct (Hhz a (Hhid a Ha)) as [E|[_ Hc]]; [exact E|].
    exfalso. pose proof (Hacc (bv_unsigned a - bv_unsigned p) ltac:(unfold in_page in Ha; lia)) as X.
    replace (bv_unsigned p + (bv_unsigned a - bv_unsigned p)) with (bv_unsigned a) in X by lia.
    cbn [cfg_model snd] in Hc. rewrite X in Hc. discriminate. }
  assert (MEMnewj : forall j, 0 <= j < page_size -> ms_mem (vms md (p :: tp) ms) (Z_to_bv 64 (bv_unsigned p + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. apply MEMnew. unfold in_page. rewrite u64_lit by lia. lia. }
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in Hswf, Hpc, Hpend, Hhalt, Hrom, Hroc, Hregs, Hfregs, Hfcsr, Hresv, Hall, Hpd, Hfr, Hfacts.

  assert (SHout : forall sa v, rm rho sa = Some v -> outside_all rho (ss_objs (ax_S A)) sa -> ~ in_page p sa).
  { intros sa v Hv Hout Hin. pose proof (Hfr sa Hout) as E. rewrite vms_mem, (Hhid sa Hin) in E. congruence. }

  assert (Hzr : obj_range rho (zero_obj_at eb) = (bv_unsigned p, bv_unsigned p + page_size)).
  { unfold obj_range, obj_lo_of, obj_hi_of, zero_obj_at. cbn [ob_base ob_lo ob_hi]. rewrite Hevb.
    rewrite !soff_lit_small by (unfold page_size; lia). f_equal. lia. }
  split; [|exact (HJ Hk)]. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HMI, Hhz |- *.
  unfold smatchA. cbn [ax_S ax_setS fst snd cfg_ms cfg_model w_tr w_cfg].
  split; [|split; [apply MI_prepay; assumption | split; [unfold axwf in Hwf |- *; cbn [ax_S ax_X ax_base ax_setS ss_next set_objs] in Hwf |- *; exact Hwf | split]]].
  -
    unfold virt, smatch. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ss_pc ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
    split.
    {   unfold swf in Hswf |- *. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
      rewrite forallb_app. cbn [forallb].
      unfold zero_obj_at at 1. unfold obj_wf at 2. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb dflt_wf sv_below andb]. rewrite Heb.
      cbn [andb]. rewrite andb_true_r. exact Hswf. }
    split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
    split; [intros a; rewrite vms_rom; pose proof (Hrom a) as X; rewrite vms_rom in X; exact X|].
    split.
    {   intros a Hro. destruct (hid md tp a) eqn:E.
      - exfalso. pose proof (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) a E) as X.
        unfold ro_addr in Hro. rewrite X in Hro. discriminate.
      - rewrite vms_mem. destruct (hid md (p :: tp) a) eqn:E2; [reflexivity|].
        pose proof (Hroc a Hro) as X. rewrite vms_mem, E in X. exact X. }
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
    split; [|exact Hfacts].
    split; [|split].
    +   cbn [ss_objs set_objs]. apply Forall_app. split.
      * apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hall o Ho) as Hoh.
        pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as Hd.
        eapply (obj_holds_mem_ext segs rho (vms md tp ms)); [intros a; rewrite !vms_rom; reflexivity| |exact Hoh].
        intros off Hoff. apply MEMold. intros Hin. unfold in_page in Hin.
        pose proof (proj1 Hoh) as HB. unfold obj_range, ranges_disjoint in Hd. cbn [fst snd] in Hd.
        rewrite u64_lit in Hin by (unfold obj_lo_of, obj_hi_of in *; lia). unfold obj_lo_of, obj_hi_of in *. lia.
      * constructor; [|constructor]. unfold obj_holds. unfold obj_lo_of, obj_hi_of, zero_obj_at.
        cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. rewrite Hevb.
        rewrite !soff_lit_small by (unfold page_size; lia).
        split; [lia|]. split.
        { intros off Hoff _. unfold wview. rewrite (MEMnewj off Hoff). discriminate. }
        split; [constructor|]. split; [|exact I].
        intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEMnewj off Hoff). reflexivity.
    +   cbn [ss_objs set_objs]. apply pairwise_disjoint_app1; [exact Hpd|].
      apply Forall_forall. intros o Ho. rewrite Hzr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
    +   cbn [ss_objs set_objs]. intros a Hout. apply outside_all_app_iff in Hout as [Hout1 Hout2].
      assert (Hn : ~ in_page p a).
      { intros Hin. inversion Hout2 as [|x l Hx _]; subst. cbn zeta in Hx. rewrite Hzr in Hx. cbn [fst snd] in Hx.
        apply Hx. exact Hin. }
      rewrite (MEMold a Hn). exact (Hfr a Hout1).
  -
    apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs set_objs]. intros x _ Hout Hdef.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hzr. cbn [fst snd].
    intros Hin. destruct (rm rho x) as [v|] eqn:Hv; [|exact (Hdef eq_refl)]. exact (SHout _ v Hv Hout Hin).
  -
    intros a Ha. exact (Hhz a (Hsame a Ha)).
Qed.

Lemma smatch_carve_zero : ltac2:(tb__ "0|7|
S17S16S29S41A1M0S49S40SdSaSaSbS1aVsegs;R9R8S25G0S38R7S39R6R5A2A4A4S18S20R9A1S21R9A1S1dR9A1S1cR9A1S22R9A1S2bScS10R9A1S28ScS13R5SeR4A1SeR3A1S26S12A1S11A5S26ScA1A3A3S1bR9A1R2S1eR9A1A9S16S32S27S23R1A1S2aA3S35Q40M1SfRcR7A2A2SaS1S5S3Z2M2Z3fA2M3A1R7A2S33S1R8R7A2S2R7G3A2A2S2S6R8R9A2G3A2S1Z0M4S0R4RaA2A2S1S0R5RaA2S3G2Z40A2A2S48ScScS15S14R13R1A2S25SaSaS0R7RdA2S0R7RcA2A4A2Lo';S10R11A1A3SaS33S1S0R8ReA2R1A2S2R1S0R8RdA2A2A2S32S2dS37Q8M5A1M6A1S19R15S36G1R2A2A2S2cG6S36G5G4A2A2A3F_;Fa;S1aVsegs;R14RaS25G0S38R12S39R11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base lo hi nx Hsm S' Hwf' b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base (SLit lo) (SLit hi) [] DZero).
  assert (Hlo' : soff rho (SLit lo) = lo) by (rewrite soff_lit_small; lia).
  assert (Hhi' : soff rho (SLit hi) = hi) by (rewrite soff_lit_small; lia).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hlo', Hhi'. reflexivity. }
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. rewrite (Hfr _ (Hout a Ha)). exact (Hbytes a Ha). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. unfold wview. rewrite (MEM (b + off)) by lia. discriminate. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia. reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_zero : ltac2:(tb__ "0|c|
S47S17S3cS29S37Q40M0A1A1S29S41A1M1S49S40SdSaSaSbS46Vsegs;RbR9RaR8S25G1S38R7S39R6R5A2A4A6S18S20S3aRaA1M2A1S21G2A1S1dG2A1S1cG2A1S22G2A1S2bScS10G2A1S28ScS13R5SeR4A1SeR3A1S26S12A1S11A5S26ScA1A3A3S1bG2A1R2S1eG2A1A9S16S32S27S23R1A1S2aA3S4fS1fS3aRcA1A1R4A2S35G0SfReR8A2A2SaS1S5S3Z2M3Z3fA2M4A1R8A2S33S1R9R8A2S2R8G4A2A2S2S6R9RaA2G4A2S1Z0M5S0R4RbA2A2S1S0R5RbA2S3G3Z40A2A2S48ScScS15S14R15R1A2S25SaSaS0R7ReA2S0R7RdA2A4A2Lo';S10S3aR13A1A1A3SaS33S1S0R8RfA2R1A2S2R1S0R8ReA2A2A2S32S2dS37Q8M6A1M7A1S19R17S36G0R2A2A2S2cG7S36G6G5A2A2A3F_;Fa;S30SdSdA2M8SaSaS4aG8R3S3dR18A1A3S33S1S35G0SfR1aS2fSdSdR4A3A2A2M9R3A2S2R3S0G9S35G0SfR1aS31SdSdR4A3A2A2A2A2A2S33S1G5R3A2S2R3Z8MaA2A2S34S33S1S0ReR15A2S0S9S4S0S35G0SfR1cS3eR1bA1A2A2S4R5GaA2A2GaA2GaA2R4A2MbA2S2GbS0ReR14A2A2A2A1F_;F_;F_;Fj;Fy;Frr;S46Vsegs;R18S3bR16RcA2R17R15S25G1S38R14S39R13R12A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp tr ms md base lo hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes Hxs.
  split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_zero rho (ax_S A) tr (vms md tp ms) (vmd md) base lo hi nx Hsm Hwf' Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

End G2.
