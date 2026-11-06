(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "prod"; "Some"; "nat"; "false"; "pair"; "S"; "andb"; "length"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "valuation"; "ss_objs"; "soff"; "sv"; "ss_facts"; "obj_wf"; "c_off"; "c_val"; "in_cell"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_range"; "smatch"; "sprop"; "DZero"; "c_width"; "dflt_writable"; "holds"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "sstate"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "prov"; "is_zero_lit"; "pv_ok"; "mk_prov"; "pv_c0"; "pv_dg"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "leb"; "lt"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "sle_off_d"; "sle_off_pv"; "zero_chain"; "pick_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "sitv_d"; "fdig"; "sleq_d"; "uleq_d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL"; "dg_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition sle_off_d (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|4|
S3S4S2aS2aA2M0A1S0Lx;M1S45Vdg;Va;A2G0G0S0Lp;R1S2aS2aG1S45Vdg;Vb;A2G0G0S0Lp0;R1S2aS2aS0S0L_;M2S39S38R4Vk;A2R2A2S1G2G2SaS39Z0M3R5A2S39G3R2A2A2S48Vdg;Va;Vk;Vb;A4S7X0x2S1S47Vdg;Va;Vk;Vb;A4X0x2X0x2Lh3;Ll3;X4x1Lp0;S7X3x2Lh1;Ll1;X4x1Lp;S7X3x2").

Definition sle_off_pv (pv : prov) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S3fS33Vpv;A1Va;Vk;Vb;A4S1S3fS34Vpv;A1Va;Vk;Vb;A4X0x2").

Fixpoint pick_zero (strict : bool) (pv : prov) (cells : list cell) (f : sv) : option (cell * list cell) :=
  match cells with
  | [] => None
  | c :: rest =>
      if is_zero_lit (c_val c)
         &&& (sle_off_pv pv (c_off c) 0 f
              &&& (if strict then sle_off_pv pv f 1 (mk_addk (c_off c) (c_width c)) else true))
      then Some (c, rest)
      else match pick_zero strict pv rest f with
           | Some (c', rest') => Some (c', c :: rest')
           | None => None
           end
  end.

Fixpoint zero_chain (fuel : nat) (pv : prov) (cells : list cell) (f hi : sv) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      sle_off_pv pv hi 0 f
      ||| match (match pick_zero true pv cells f with Some r => Some r | None => pick_zero false pv cells f end) with
          | Some (c, rest) => zero_chain fuel' pv rest (mk_addk (c_off c) (c_width c)) hi
          | None => false
          end
  end.

Definition zero_covered (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;S20S25Vo;A1A1S41S9SbSeS24Vo;A1M0A2A1S32Vfacts;A1G0S19Vo;A1S18Vo;A1A5S7X0x2").

Definition zobj (o : sobj) : sobj := ltac2:(tb__ "0|0|
S22S23Vo;A1S19Vo;A1S18Vo;A1ScSeA1S1eA5").

Lemma sle_off_d_sound : ltac2:(tb__ "0|0|
SfS46S12S2aS12S56R5R4A2S37Z0R3A2S27S0S3fR6R5R4R3A4S1A3S37S38S11R8R6A2R5A2S11R8R4A2A2F_;F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd Hk H. unfold sle_off_d in H.
  destruct (sitv_d dg a) as [[l1 h1]|] eqn:S1; [|discriminate].
  destruct (sitv_d dg b) as [[l3 h3]|] eqn:S3; [|discriminate].
  pose proof (sitv_d_sound rho dg a l1 h1 Hd S1) as (A1 & B1 & _).
  pose proof (sitv_d_sound rho dg b l3 h3 Hd S3) as (A3 & B3 & _).
  apply lazy_orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
  apply lazy_orb_prop in H as [H|H].
  - apply StepA.lazy_andb_prop in H as [H Hu]. apply andb_prop in H as [P1 P3].
    apply Z.leb_le in P1. apply Z.leb_le in P3.
    pose proof (uleq_d_sound rho dg a k b Hd Hu). rewrite B1, B3 by lia. lia.
  - exact (sleq_d_sound rho dg a k b Hd H).
Qed.

Lemma sle_off_pv_sound : ltac2:(tb__ "0|0|
SfS2fS12S2aS12S31R5R4A2S37Z0R3A2S27S0S40R6R5R4R3A4S1A3S37S38S11R8R6A2R5A2S11R8R4A2A2F_;F_;F_;Fb;Fk;Fa;Fpv;Frho;").
Proof.
  intros rho pv a k b (Hf & Hc & Hd & _) Hk H. unfold sle_off_pv in H. apply lazy_orb_prop in H as [H|H];
    [exact (sle_off_d_sound rho _ a k b Hc Hk H) | exact (sle_off_d_sound rho _ a k b Hd Hk H)].
Qed.

Lemma pick_zero_sound : ltac2:(tb__ "0|2|
S0S2fS2SeA1M0S12SeG0S27S3S4SeG0A2M1A1S42R6R5R4R3A4S5G1S8SeG0R2R1A4A2A3S28S35SeR3R5A3S28S27S0S30S16R3A1A1S1A3S28S27S0S40R6S15R3A1Z0R4A4S1A3SeS35SeR1R3A3S35SeR2R7A3F_;Fx;A2A2A2F_;Frest;Fc;Ff;Fcells;Fpv;Fst;").
Proof.
  intros st pv cells. induction cells as [|c0 tl IH]; intros f c rest H; cbn [pick_zero] in H; [discriminate|].
  destruct (is_zero_lit (c_val c0) &&& _) eqn:E.
  - injection H as <- <-. apply StepA.lazy_andb_prop in E as [Ez E]. apply StepA.lazy_andb_prop in E as [E1 _].
    split; [left; reflexivity|]. split; [exact Ez|]. split; [exact E1|]. intros x Hx. right. exact Hx.
  - destruct (pick_zero st pv tl f) as [[c' rest']|] eqn:Hp; [|discriminate]. injection H as <- <-.
    destruct (IH f c' rest' Hp) as (Hin & Hz & Hs & Hsub).
    split; [right; exact Hin|]. split; [exact Hz|]. split; [exact Hs|].
    intros x [<-|Hx]; [left; reflexivity | right; apply Hsub; exact Hx].
Qed.

Section GZ.
Variable segs : list Segment.

Lemma zero_chain_sound : ltac2:(tb__ "0|5|
SfS2fS2SeA1M0S12S6G0S12S2aS31R8R7A2SeS35SeR1R8A3S28S37S3bS3cZ2Z3fA2M1A1S11RbS15R2A1A2M2A2S28S3aS38G2S1fR2A1M3A2G1A2S37Z0G3A2A2A2F_;Fc;SeS35SeR1R6A3S35SeR2RaA3F_;Fx;S27S0S41R7RaR6R5R8A5S1A3S2aS28S37R6R1A2S3aR1S11RdR7A2A2A2S29SeSeS28S35SeR1RdA3S28S27S0S30S16R1A1A1S1A3M4S17RfR3R1A3A2A2Lc;A2F_;Foff;S2aS28S37R7R1A2S3aR1S11ReRbA2A2A2S29SeSeS28S35SeR1ReA3S28G4S17R10R3R1A3A2A2Lc;A2F_;Foff;F_;F_;F_;F_;F_;FLO;Ff;Fcells;Ffuel;Fhi;Fall;Fpv;Frho;").
Proof using .
  intros rho pv all hi fuel. induction fuel as [|fuel IH]; intros cells f LO Hpv Hall Hsub H Hinv off Hoff; [discriminate|].
  cbn [zero_chain] in H. apply lazy_orb_prop in H as [H|H].
  - pose proof (sle_off_pv_sound rho pv hi 0 f Hpv ltac:(lia) H). apply Hinv. lia.
  - destruct (match pick_zero true pv cells f with Some r => Some r | None => pick_zero false pv cells f end)
      as [[c rest]|] eqn:Hp; [|discriminate].
    assert (PK : exists st, pick_zero st pv cells f = Some (c, rest)).
    { destruct (pick_zero true pv cells f) as [r|] eqn:E1; [exists true; rewrite E1; exact Hp | exists false; exact Hp]. }
    destruct PK as [st Hst]. destruct (pick_zero_sound _ _ _ _ _ _ Hst) as (Hin & Hz & Hs & Hrest).
    pose proof (sle_off_pv_sound rho pv (c_off c) 0 f Hpv ltac:(lia) Hs) as Hle.
    destruct (Hall c (Hsub c Hin)) as (R1 & R2 & R3).
    assert (Ef : soff rho (mk_addk (c_off c) (c_width c)) = soff rho (c_off c) + c_width c) by (apply soff_mk_addk; lia).
    eapply (IH rest (mk_addk (c_off c) (c_width c)) LO Hpv Hall); [intros x Hx; apply Hsub, Hrest; exact Hx | exact H | | exact Hoff].
    intros off' Hoff'. rewrite Ef in Hoff'.
    destruct (Z_lt_le_dec off' (soff rho f)) as [Hlt|Hge]; [apply Hinv; lia|].
    exists c. split; [apply Hsub; exact Hin|]. split; [exact Hz|]. unfold in_cell. lia.
Qed.

Lemma obj_holds_zero_fold : ltac2:(tb__ "0|0|
SfS4fS2S1dA1SdS2bS55S1dS21R5A1R3A3S1aVsegs;R6R5R3A4S27S0S14R3R4A2S1A3S27S0S3eR6R5A2S1A3S1aVsegs;R9R8S3dR6A1A4F_;F_;F_;F_;Fn;Fo;Ffacts;Fms;Frho;").
Proof using .
  intros rho ms facts o n Hf Hoh Hwf Hz.
  pose proof Hoh as (Hb & Hw & Hcells & Hd & Hdl). unfold obj_lo_of, obj_hi_of in *.
  unfold zero_covered in Hz. apply StepA.lazy_andb_prop in Hz as [Hdw Hch].
  pose proof (soff_range rho (ob_lo o)) as Rlo. pose proof (soff_range rho (ob_hi o)) as Rhi.
  assert (COV : forall off, soff rho (ob_lo o) <= off < soff rho (ob_hi o) ->
                exists c, In c (ob_cells o) /\ is_zero_lit (c_val c) = true /\ in_cell rho off c).
  { eapply (zero_chain_sound rho (mk_prov facts) (ob_cells o) (ob_hi o) _ (ob_cells o) (ob_lo o));
      [apply mk_prov_ok; exact Hf | | intros x Hx; exact Hx | exact Hch |].
    - intros c Hin. pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (B1 & B2 & _).
      destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & _ & _ & _). lia.
    - intros off Hoff. lia. }
  unfold obj_holds, zobj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | exact Hdw]|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. unfold dflt_holds.
  destruct (COV off Hoff) as (c & Hin & Hzc & Hic). unfold in_cell in Hic.
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (B1 & B2 & Brd).
  destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & C2 & _ & _).
  assert (Hca : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) = bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c))
    by (apply oaddr_unsigned; lia).
  set (j := Z.to_nat (off - soff rho (c_off c))).
  pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ j Brd ltac:(lia) ltac:(rewrite Hca, Z2Nat.id by lia; lia)) as R.
  rewrite Hca in R. replace (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c) + Z.of_nat j)
    with (bv_unsigned (eval rho (ob_base o)) + off) in R by lia.
  rewrite R. rewrite (StepA.enc_bytes_zero_nth (Z.to_nat (c_width c)) _ j (StepA.is_zero_lit_sound rho _ Hzc) ltac:(lia)). reflexivity.
Qed.

Lemma obj_range_zobj : ltac2:(tb__ "0|0|
SfSdS27S4S2aS2aA2S1bR2S3dR1A1A2S1bR2R1A2A3Fo;Frho;").
Proof. reflexivity. Qed.

Lemma obj_wf_zobj : ltac2:(tb__ "0|0|
S2bSdS27S0S14R2R1A2S1A3S27S0S14R3S3dR2A1A2S1A3F_;Fo;Fn;").
Proof.
  intros n o H. destruct (obj_wf_parts _ _ H) as (Hb & Hlo & Hhi & _).
  unfold obj_wf, zobj. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb dflt_wf]. rewrite Hb, Hlo, Hhi. reflexivity.
Qed.

Lemma smatch_zero_fold : ltac2:(tb__ "0|1|
SfS26S2S50A1M0S4fS51S6SdS1cVsegs;R7R6S8G0S4cR5S4dR4R3A2A4A4S27S3SdA1S36SdS10R7A1R3A3S5SdR2A2A3S27S0S3eS13R8A1R3A2S1A3S1cVsegs;RaS44R9S43SdS10R9A1R5S3dR4A1A4A2S8G0S4cR8S4dR7R6A2A4A4F_;F_;F_;Fo;Fn;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md n o Hsm Hnth Hz.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
  split.
  { unfold swf in Hwf |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
    repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
    repeat (apply andb_true_intro; split); try assumption.
    apply forallb_list_set; [assumption|]. apply obj_wf_zobj. exact Howf. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresvm|]. split; [|exact Hfacts].
  split; [|split].
  - apply Forall_forall. intros o2 Hin2. destruct (In_list_set _ _ _ _ Hin2) as [-> | (m & Hne & Hm2)].
    + eapply obj_holds_zero_fold; [exact Hfacts | exact (proj1 (Forall_forall _ _) Hall o (nth_error_In _ _ Hnth)) | exact Howf | exact Hz].
    + exact (proj1 (Forall_forall _ _) Hall o2 (nth_error_In _ _ Hm2)).
  - eapply pairwise_disjoint_set; [exact Hnth | apply obj_range_zobj | exact Hpd].
  - intros a Ha. apply Hfr. exact (proj1 (outside_all_set rho (ss_objs S) n o (zobj o) a Hnth (obj_range_zobj rho o)) Ha).
Qed.

Lemma smatchA_zero_fold : ltac2:(tb__ "0|1|
SfS2S4eQ40A1A1S2eS4S2S50A1S4cA2S6SdS4bVsegs;R6R5R4R3A5S27S3SdA1S36SdS10S2cR5A1A1R3A3S5SdR2A2A3S27S0S3eS13S2cR6A1A1R3A2S1A3S4bVsegs;R9R8S2dR7S44S2cR7A1M0S43SdS10G0A1R5S3dR4A1A4A2A2R6A5F_;F_;F_;Fo;Fn;Fw;FA;Ftp;Frho;").
Proof using .
  intros rho tp A [tr [ms md]] n o (Hsm & HMI & Hwf & Hsh & Hhz) Hnth Hz.
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  split; [|split; [exact HMI | split; [unfold axwf in Hwf |- *; cbn; exact Hwf | split; [|exact Hhz]]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg]. eapply smatch_zero_fold; eauto.
  - eapply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_S ax_setS ss_objs set_objs].
    intros x _ Hout _. exact (proj2 (outside_all_set rho (ss_objs (ax_S A)) n o (zobj o) x Hnth (obj_range_zobj rho o)) Hout).
Qed.

Lemma SPA_zero_fold : ltac2:(tb__ "0|1|
S4aSfS2eS2S4eQ40A1A1S53S6SdS27S3SdA1S36SdS10S2cR5A1A1R2A3S5SdR1A2A3S27S0S3eS13S2cR6A1A1R2A2S1A3S49Vsegs;R9R7R8R6R5A6S49Vsegs;RaS2dR8S44S2cR8A1M0S43SdS10G0A1R5S3dR4A1A4A2A2R9R7R6A6F_;F_;F_;Fo;Fn;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w n o Hnth Hz [Hsm Hk]. split; [eapply smatchA_zero_fold; eauto | exact Hk].
Qed.

Lemma triple_zero_fold : ltac2:(tb__ "0|1|
S53OF_;S4aSfS2eS2S4eQ40A1A1S6SdS54S27S3SdA1S36SdS10S2cR5A1A1R3A3S5SdR2A2A3S27S0S3eS13S2cR6A1A1R3A2S1A3S52Vsegs;RaS49Vsegs;R9S2dR7S44S2cR7A1M0S43SdS10G0A1R5S3dR4A1A4A2A2R8R6A5R3A4S52Vsegs;RbS49Vsegs;RaR8R9R7A5R4A4F_;F_;F_;FQ;Fo;Fn;Ftp;FA;Frho;FJ;Fok;").
Proof using .
  intros ok J rho A tp n o Q Hnth Hz HT. eapply triple_conseq; [| | exact HT]; [|intros w Hw; exact Hw].
  intros w Hw. eapply SPA_zero_fold; eauto.
Qed.

End GZ.
