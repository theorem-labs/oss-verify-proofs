(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "True"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "modulo"; "sub"; "eqb"; "opp"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "option"; "false"; "andb"; "list"; "true"; "cons"; "nil"; "prod"; "Some"; "app"; "orb"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ranges_disjoint"; "sv"; "obj_range"; "SLit"; "ss_objs"; "SVar"; "reg_sv"; "rw"; "ss_next"; "sstate"; "valuation"; "ob_base"; "ob_lo"; "ro_addr"; "ss_pc"; "ob_hi"; "ss_facts"; "holds"; "sprop"; "ss_lenient"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "VmMaps"; "alloc_top"; "iv_overlap"; "region_free"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "lit_of"; "blk_clear_b"; "high_clear_b"; "img_clear_b"; "obj_clear_b"; "var_of"; "K_nil"; "Kx"; "objs_clear_b"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "SP"; "ok_frame"; "ok_frameJ"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "model_idle"; "assn"; "etriple"; "triple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "mmap_obj"; "smatch_pending"; "ok_pframeJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "instr_at"; "uleq"; "RsCut"; "mkLeaf"; "sym_run"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "eqb"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Kx (m : Model) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S19S3bA1M0S3aS2S3G0R2S1cS3bA1A3S3S3aR1Vm;A3A2Lmd;Ltr;").
Definition K_nil (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|1|
S19S3bA1M0S3aVK;R2R1A2S3G0R3S1cS3bA1A3F_;Fmd;Ftr;").
Lemma Kx_nil : ltac2:(tb__ "0|0|
S3aS4aS4bR1A1A1Fm;").
Proof. intros m tr md [H _]; exact H. Qed.

Section Spin.
Variable segs : list Segment.

Lemma triple_spin : ltac2:(tb__ "0|1|
S57OF_;S19S3bA1S3aOF_;F_;S2dS2eS59S53Vsegs;R5R4A3S3S14S37R4A1S17A3S3S16S19S66A1M0A1S6bVsegs;U2S1bS0S32R5A1S1cS0A1A3R5S1aA5S1eG0S1bS66S6aR5S69A2S1cS66A1A3A2A3S5bVsegs;R8S52Vsegs;R7R6R5A4R4A4F_;F_;F_;FQ;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Q Hok Hstrict Hrun.
  apply (@triple_conseq segs ok (fun w => exists rho', agree_below (ss_next S) rho rho' /\ SP segs K S rho' w) _ Q Q);
    [ intros w Hw; exists rho; split; [apply agree_below_refl | exact Hw] | intros w Hw; exact Hw | ].
  apply triple_loop. apply triple1_ex. intros rho'. apply triple1_pure. intros Hag.
  eapply triple1_conseq; [intros w Hw; exact Hw | | eapply sym_run_sound; [exact Hrun | exact Hok | intros Hl; rewrite Hstrict in Hl; discriminate]].
  intros w (L & rho'' & Hin & Hag' & Hsm & Hk). destruct Hin as [<-|[]]. left.
  exists rho''. split; [eapply agree_below_trans; eauto | split; assumption].
Qed.

End Spin.

Lemma segments_reserved_A : ltac2:(tb__ "0|3|
S3S19S1dSaQ40M0A1M1G1A2M2A1S6eS62A1S1bG2S15G1G1S9G0Z10000A2S9G0Z2b000A2A4S1bG2S15G1G1S9G0Z3b000A2S9G0Za6000A2A4S1bG2S15G1G1S9G0Ze1000A2S9G0Z5000A2A4S1bG2S15G1G1S9G0Ze6000A2S9G0Z55d000A2A4S1cG2A1A3A3A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma iv_overlap_false : ltac2:(tb__ "0|a|
SaQ40M0A1M1G1G1G1S3S14S40R4R3R2R1A4S17A3S5SbScS8G0R5A2M2S8G0R4A2M3A2M4S8G0R3A2M5A2S5SbScG5S8G0R2A2M6A2G2A2M7S5S3S0G3Z0M8A3S5S3S0G6G8A3S5G7S7A2A2A2A2A2S4S6S0S0S2S2SbS8G0R7A2M9R1A2SdR1ScG9S8G0R6A2A2A2A2S2SbG2R1A2SdR1G4A2A2A2Lx;A2A1F_;F_;Fm;Fb;Fn;Fa;").
Proof.
  intros a n b m H _ [x [Hx Hy]]. unfold iv_overlap in H.
  apply Bool.andb_false_iff in H. destruct H as [H|H]; apply Z.ltb_ge in H; lia.
Qed.

Lemma region_free_disj : ltac2:(tb__ "0|5|
S19S1dSaQ40M0A1M1G1A2M2A1G1G1G1G1S3S14S41R5R4R3A3S1aA3S4dG2S15G1G1R3R2A4R6A3S0S2SbS8G0R7A2M3R1A2SdR1ScG3S8G0R6A2M4A2A2A2S4S2SbG4R2A2SdR2ScG4S8G0R5A2A2A2A2A1F_;Fx;F_;F_;Fm;Fb;Fn;Fa;Fmaps;").
Proof.
  intros maps a n b m Hf Hin x Hx Hy.
  pose proof (region_free_In maps a n b m Hf Hin) as H.
  unfold iv_overlap in H. apply Bool.andb_false_iff in H. destruct H as [H|H]; apply Z.ltb_ge in H; lia.
Qed.

Lemma grant_facts_A : ltac2:(tb__ "0|8|
SaQ40M0A1M1G1S3aG1G1S64R5R4R3R2R1A5S3S19S1dG1G1A2M2A1S43S3cR4A1A1S6eS62A1A3S2S3S0S10S8G0R3A2M3Z1000A2Z0M4A3S2SdG4G3A2S2SbScG3S63R4A1A2S3fS3cR5A1A1A2S2S0S2SbS8G0R4A2M5R1A2SdR1ScG5S63R5A1A2A2A2S4S2SbZ10000R2A2SdR2Z643000A2A2A1F_;Fx;G1G1S4dG2S15G1G1R2R1A4S42S3cR7A1A1A3S0S2SbS8G0R7A2M6R1A2SdR1ScG6S63R8A1A2A2A2S4S2SbS8G0R5A2M7R2A2SdR2ScG7G5A2A2A2A1F_;Fx;F_;Fm;Fb;A2A2A2A2F_;F_;Fa;Flen;Fmd;Fflags;Faddr;").
Proof.
  intros addr flags md len a (Hal & Hpos & Hceil & Hfree & _) Hres.
  destruct (mmap_nw (m_vmmaps md) a len Hceil) as [En _].
  split; [exact Hal|]. split; [exact Hpos|]. split; [exact Hceil|].
  rewrite Hres, segments_reserved_A in Hfree.
  assert (Hsegs : forall x, bv_unsigned a <= x < bv_unsigned a + mmap_nZ len -> ~ (0x10000 <= x < 0x643000)).
  { intros x Hx Himg. rewrite <- En in Hx.
    assert (R : forall b m, In (b, m) ([(Z_to_bv 64 0x10000, Z_to_bv 64 0x2b000); (Z_to_bv 64 0x3b000, Z_to_bv 64 0xa6000);
                             (Z_to_bv 64 0xe1000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xe6000, Z_to_bv 64 0x55d000)] ++ vm_maps (m_vmmaps md)) ->
                ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned m)).
    { intros b m Hin. exact (region_free_disj _ a (mmap_n len) b m Hfree Hin x Hx). }
    pose proof (R (Z_to_bv 64 0x10000) (Z_to_bv 64 0x2b000) (or_introl eq_refl)) as R1.
    pose proof (R (Z_to_bv 64 0x3b000) (Z_to_bv 64 0xa6000) (or_intror (or_introl eq_refl))) as R2.
    pose proof (R (Z_to_bv 64 0xe1000) (Z_to_bv 64 0x5000) (or_intror (or_intror (or_introl eq_refl)))) as R3.
    pose proof (R (Z_to_bv 64 0xe6000) (Z_to_bv 64 0x55d000) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as R4.
    assert (U1 : bv_unsigned (Z_to_bv 64 0x10000) = 0x10000) by reflexivity.
    assert (U2 : bv_unsigned (Z_to_bv 64 0x2b000) = 0x2b000) by reflexivity.
    assert (U3 : bv_unsigned (Z_to_bv 64 0x3b000) = 0x3b000) by reflexivity.
    assert (U4 : bv_unsigned (Z_to_bv 64 0xa6000) = 0xa6000) by reflexivity.
    assert (U5 : bv_unsigned (Z_to_bv 64 0xe1000) = 0xe1000) by reflexivity.
    assert (U6 : bv_unsigned (Z_to_bv 64 0x5000) = 0x5000) by reflexivity.
    assert (U7 : bv_unsigned (Z_to_bv 64 0xe6000) = 0xe6000) by reflexivity.
    assert (U8 : bv_unsigned (Z_to_bv 64 0x55d000) = 0x55d000) by reflexivity.
    rewrite U1, U2 in R1. rewrite U3, U4 in R2. rewrite U5, U6 in R3. rewrite U7, U8 in R4. lia. }
  split; [exact Hsegs|].
  intros b m Hin x Hx. rewrite <- En in Hx. eapply (region_free_disj _ a (mmap_n len) b m Hfree); [|exact Hx].
  apply in_app_iff. right. exact Hin.
Qed.

Lemma grant_no_ro_A : ltac2:(tb__ "0|5|
SaQ40M0A1M1S0S0S2SbS8G0R3A2M2R1A2SdR1ScG2R2A2A2A2S4S2SbZ10000R2A2SdR2Z643000A2A2A1F_;Fx;G1S2SbS8G0R4A2M3S8G0R1A2M4A2SdG4ScG3R3A2A2A2S3S14S31S62R2A2S17A3F_;Fx;F_;FnZ;Fa;").
Proof.
  intros a nZ H x Hx. unfold ro_addr.
  destruct (find_segment segsA (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. apply (H (bv_unsigned x) Hx).
  unfold segsA in E. cbn -[Z.leb Z.add Z.of_N] in E.
  change (Z.of_N 65536%N) with 65536 in E. change (Z.of_N 176128%N) with 176128 in E.
  change (Z.of_N 241664%N) with 241664 in E. change (Z.of_N 679936%N) with 679936 in E.
  change (Z.of_N 921600%N) with 921600 in E. change (Z.of_N 20480%N) with 20480 in E.
  change (Z.of_N 942080%N) with 942080 in E. change (Z.of_N 5623808%N) with 5623808 in E.
  repeat match type of E with context [if ?c then _ else _] =>
    destruct c eqn:?C; [apply andb_prop in C as [?C1 ?C2]; apply Z.leb_le in C1; apply Z.leb_le in C2; lia | clear C] end.
  discriminate.
Qed.

Section MmapObj.
Variable segs : list Segment.

Lemma with_vmmaps_idle' : ltac2:(tb__ "0|0|
S3eS3aS58R1A1S58S3dR3R2A2A1F_;Fmd;Fv;").
Proof using . intros v md [H1 H2]. split; assumption. Qed.

Theorem triple1_mmap_rw_objJ : ltac2:(tb__ "0|b|
S57OF_;S51S51SaQ40M0A1M1S51F_;S2dS2eS0S54Vsegs;R7R6A3S61Vsegs;R8R7A3S3S16S55A1S67Vsegs;S32R5A1A2S1eS55S56A2A3S3S25S2aR6Z11A2S27ZdeA1A3S3S25S2aR7ZbA2S27R5A1A3S3S0S10R6Z1000A2Z0M2A3S2SdG2R7A2SdR7SfZ2Z3eA2A2A2S19S3bA1M3S39S3aS60Vsegs;RcRdS15G3S6cR3S6dR2R1A2A4A4R11RdR4R2A3S2S3S14S6fS38R4U2A2S38R4U3M4A2M5S38R4U5A2A3S1aA3S2S3S14S70G5A1S17A3S2R11ReR5R3A3G1S64S38R5U0A2S38R5G4A2R4S38R5U1M6A2R1A5S2S23S4dS23R1S28R12A1A3S24S26R12R2A2S15S0S0S8G0R4A2M7ScG7R11A2A4A2F_;Fo;S2G1S2SbS8G0R3A2M8S8G0R1A2M9A2SdG9ScG8R10A2A2A2S3S14S31Vsegs;R2A2S17A3F_;Fx;R12R2S5dR10S2cR11A1R2A3R7S3dS65S3cR5A1S38R6G6A2R2A3R5A2A4A2A2F_;Fa;A2A2A2F_;F_;Fmd;Fms;Ftr;S5cVsegs;RfS50Vsegs;ReRbRaA4S57S5S50Vsegs;ReS74RcS75A2RbR1A5S6G1G1S50Vsegs;ReR1A1S5eRdS29S2cRdA1MaA1S1fS23S28RdA1S1bS23S5fGaRbA2S1cS23A1A3A3S71GaA1A4S5dRcGaR1A3R2A5La;A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho nlit Hokf Hokp Hi H17 H11 Hmod Hn HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite H11 in G1. cbn [eval] in G1.
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit).
  { rewrite G1, Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { intros E. rewrite E in Hlenv. rewrite Z_to_bv_unsigned in Hlenv. change (bv_wrap 64 0) with 0 in Hlenv. lia. }
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply (@mmap_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_inv Hp Hh H222 Hlen Hmodb Hnr Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw (m_vmmaps md) a (ms_gpr ms 1) Hceil) as [En Hnw].
      rewrite HnZ in En. rewrite En in Hnw.
      split.
      * eapply (smatch_after_mmap segs rho S tr ms md); [exact Hsp | apply with_vmmaps_idle'; exact Hh | exact En | lia | exact Hnw | exact Hdisj | exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem etriple_mmap_rw_objJ : ltac2:(tb__ "0|b|
S51SaQ40M0A1M1S51F_;S2dS2eS0S3S16S55A1S67Vsegs;S32R3A1A2S1eS55S56A2A3S3S25S2aR4Z11A2S27ZdeA1A3S3S25S2aR5ZbA2S27R3A1A3S3S0S10R4Z1000A2Z0M2A3S2SdG2R5A2SdR5SfZ2Z3eA2A2A2S19S3bA1M3S39S3aS60Vsegs;RaRbS15G3S6cR3S6dR2R1A2A4A4ReRbR4R2A3S2S3S14S6fS38R4U2A2S38R4U3M4A2M5S38R4U5A2A3S1aA3S2S3S14S70G5A1S17A3S6G1G1S2S64S38R5U0A2S38R5G4A2R4S38R5U1A2M6R1A5S2S23S4dS23R1S28RfA1A3S24S26RfR2A2S15S0S0S8G0R3A2M7ScG7ReA2A4A2F_;Fo;S2G1S2SbS8G0R2A2M8S8G0R1A2M9A2SdG9ScG8RdA2A2A2S3S14S31Vsegs;R2A2S17A3F_;Fx;RfR1S5dRdS2cReA1R1A3R6S3dS65S3cR4A1G6R1A3R4A2A4A2A2A2La;A2A2A2F_;F_;Fmd;Fms;Ftr;S5aVsegs;S50Vsegs;RbR9R8A4S57S6G1G1S50Vsegs;RcR1A1S5eRbS29S2cRbA1MaA1S1fS23S28RbA1S1bS23S5fGaR9A2S1cS23A1A3A3S71GaA1A4S5dRaGaR1A3R2A5La;A2Lw;A3F_;F_;F_;F_;F_;F_;Fnlit;Frho;FS;FJo;FJ;").
Proof using .
  intros J Jo S rho nlit Hi H17 H11 Hmod Hn HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite H11 in G1. cbn [eval] in G1.
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit).
  { rewrite G1, Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { intros E. rewrite E in Hlenv. rewrite Z_to_bv_unsigned in Hlenv. change (bv_wrap 64 0) with 0 in Hlenv. lia. }
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & a & Hpl & Hdisj & Hnro & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw (m_vmmaps md) a (ms_gpr ms 1) Hceil) as [En Hnw].
  rewrite HnZ in En. rewrite En in Hnw.
  eexists. split; [eapply (@wstep_mmap_intro_ok segs tr ms); eassumption|].
  exists a. split.
  - eapply (smatch_after_mmap segs rho S tr ms md); [exact Hsp | apply with_vmmaps_idle'; exact Hh | exact En | lia | exact Hnw | exact Hdisj | exact Hnro].
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.
End MmapObj.

Definition lit_of (e : sv) : option Z := match e with SLit z => Some z | _ => None end.
Definition var_of (e : sv) : option positive := match e with SVar i => Some i | _ => None end.

Lemma lit_of_sound : ltac2:(tb__ "0|0|
S25S0S3S16S0A1S44R2A1S1eS0R1A2A3S3S25R3S27R2A1A3F_;Fz;Fe;").
Proof. intros e z H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.
Lemma var_of_sound : ltac2:(tb__ "0|0|
S25S1S3S16S1A1S49R2A1S1eS1R1A2A3S3S25R3S29R2A1A3F_;Fi;Fe;").
Proof. intros e i H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.

Definition img_clear_b (o : sobj) : bool := ltac2:(tb__ "0|1|
S16S0A1S14Lx;M0S44S2fVo;A1A1S0G0S44S30Vo;A1A1S0G0S44S33Vo;A1A1S0S18S18S18S12R3Z0A2SeZ10000R2A2A2SeR2R1A2A2SeR1Z643000A2A2Lhi;S17X16x2Llo;S17X16x2Lb;S17X16x2").

Definition high_clear_b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|2|
S16S0A1S14Lx;S44S30Vo;A1A1S0S18S18S18SeS13SfZ2Z28A2M0A1R1A2SeR1G0A2A2S68Vfacts;S27Z7fff80000000A1Z0S29P1A1M1A4A2S68Vfacts;G1S11N800000R1A2S2fVo;A1A4A2Llo;S17X16x2").
Definition blk_clear_b (G : list (positive * Z)) (o : sobj) : bool := ltac2:(tb__ "0|3|
S16S1A1S14Lx;S49S2fVo;A1A1S1S16S0A1S14Lx;M0S44S30Vo;A1A1S0G0S44S33Vo;A1A1S0S4eS1dS1S0A2M1G1S18S18S18S18S72R4S21S1S0R1A3A2SeZ0R3A2A2SeR3R2A2A2SeR2S22S1S0R1A3M2A2A2SeG2SfZ2Z3eA2A2A2Lg;VG;A3Lhi;S17X16x2Llo;S17X16x2Li;S17X16x2").

Definition obj_clear_b (facts : list sprop) (G : list (positive * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S20S20S47Vo;A1S46Vfacts;Vo;A2A2S45VG;Vo;A2A2").

Definition objs_clear_b (G : list (positive * Z)) (S : sstate) : bool := ltac2:(tb__ "0|0|
S4fS23S48S34VS;A1VG;A2S28VS;A1A3").

Lemma pointwise_clear_disjoint : ltac2:(tb__ "0|0|
S0S0S0S0S0S0S0S2SbR7R1A2SdR1ScR7R6A2A2A2S4S2SbR6R2A2SdR2R5A2A2A1F_;Fx;SbR5R3A2SbR3R5A2S24S15S0S0R5R4A4S15S0S0R9ScR9R8A2A4A2F_;F_;F_;Fh;Fl;FH;FL;Fn;Fa;").
Proof.
  intros a n L H l h HP Hl Hh. unfold ranges_disjoint. cbn [fst snd].
  destruct (Z.le_gt_cases h l); [lia|]. destruct (Z.le_gt_cases n 0); [lia|].
  destruct (Z.le_gt_cases h a); [lia|]. destruct (Z.le_gt_cases (a + n) l); [lia|].
  exfalso. apply (HP (Z.max a l)); lia.
Qed.

Section ClearSound.
Variable rho : valuation.
Variable facts : list sprop.
Variable G : list (positive * Z).
Variable a : word.
Variable n : Z.
Hypothesis HF : Forall (holds rho) facts.
Hypothesis Hn : 0 <= n.

Hypothesis Hceil : ltac2:(tb__ "0|2|
S5SbScS8Q40M0Va;A2Vn;A2M1Z7fff7f800000A2SbG1S11S8G0S2bVrho;P1A2A2Z800000A2A2A2").
Hypothesis Himg : ltac2:(tb__ "0|1|
S0S2SbS8Q40Va;A2M0R1A2SdR1ScG0Vn;A2A2A2S4S2SbZ10000R2A2SdR2Z643000A2A2A1F_;Fx;").
Hypothesis HG : ltac2:(tb__ "0|3|
S1S0S4dS1dS1S0A2S15S1S0R2R1A4VG;A3S0S2SbS8Q40M0Va;A2M1R1A2SdR1ScG1Vn;A2A2A2S4S2SbS8G0S2bVrho;R5A2A2M2R2A2SdR2ScG2R4A2A2A2A1F_;Fx;F_;Fsz;Fi;").

Lemma img_clear_sound : ltac2:(tb__ "0|1|
S23S3S14S47R1A1S1aA3S24S26Vrho;R2A2S15S0S0S8Q40Va;A2M0ScG0Vn;A2A4A2F_;Fo;").
Proof using Himg.
  intros o Hb. unfold img_clear_b in Hb.
  destruct (lit_of (ob_base o)) as [b|] eqn:Eb; [|discriminate].
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate].
  destruct (lit_of (ob_hi o)) as [hi|] eqn:Ehi; [|discriminate].
  apply lit_of_sound in Eb. apply lit_of_sound in Elo. apply lit_of_sound in Ehi.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply Z.eqb_eq in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst b.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
  rewrite !soff_lit_small by lia. rewrite !Z.add_0_l. eapply pointwise_clear_disjoint; [exact Himg | lia | lia].
Qed.

Lemma high_clear_sound : ltac2:(tb__ "0|1|
S23S3S14S46Vfacts;R1A2S1aA3S24S26Vrho;R2A2S15S0S0S8Q40Va;A2M0ScG0Vn;A2A4A2F_;Fo;").
Proof using HF Hceil Hn.
  intros o Hb. unfold high_clear_b in Hb.
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate]. apply lit_of_sound in Elo.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (uleq_sound rho facts _ _ _ HF H3) as U1. pose proof (uleq_sound rho facts _ _ _ HF H4) as U2.
  unfold U in U1, U2. cbn [eval] in U1, U2. rewrite Z_to_bv_unsigned in U1. change (bv_wrap 64 0x7fff80000000) with 0x7fff80000000 in U1.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Elo. rewrite soff_lit_small by lia.
  unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma blk_clear_sound : ltac2:(tb__ "0|1|
S23S3S14S45VG;R1A2S1aA3S24S26Vrho;R2A2S15S0S0S8Q40Va;A2M0ScG0Vn;A2A4A2F_;Fo;").
Proof using HG.
  intros o Hb. unfold blk_clear_b in Hb.
  destruct (var_of (ob_base o)) as [i|] eqn:Eb; [|discriminate].
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate].
  destruct (lit_of (ob_hi o)) as [hi|] eqn:Ehi; [|discriminate].
  apply var_of_sound in Eb. apply lit_of_sound in Elo. apply lit_of_sound in Ehi.
  apply existsb_exists in Hb as ([j sz] & Hin & Hg). cbn [fst snd] in Hg.
  apply andb_prop in Hg as [Hg H4]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [Hg H2]. apply andb_prop in Hg as [H0 H1].
  apply Pos.eqb_eq in H0. subst j. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. cbn [eval].
  rewrite !soff_lit_small by lia.
  eapply pointwise_clear_disjoint; [exact (HG i sz Hin) | lia | lia].
Qed.

Lemma obj_clear_sound : ltac2:(tb__ "0|1|
S23S3S14S48Vfacts;VG;R1A3S1aA3S24S26Vrho;R2A2S15S0S0S8Q40Va;A2M0ScG0Vn;A2A4A2F_;Fo;").
Proof using HF HG Hceil Himg Hn.
  intros o Hb. unfold obj_clear_b in Hb.
  apply Bool.orb_prop in Hb as [Hb|Hb]; [apply Bool.orb_prop in Hb as [Hb|Hb]|].
  - apply img_clear_sound, Hb.
  - apply high_clear_sound, Hb.
  - apply blk_clear_sound, Hb.
Qed.
End ClearSound.

Lemma objs_clear_sound : ltac2:(tb__ "0|7|
S2eS19S1dS1S0A2M0A1S2dSaQ40M1A1S0S73S36S35R5A1S34R3A1A3S3S14S4cR5R4A2S1aA3SbZ0R3A2S5SbScS8G1R5A2R4A2M2Z7fff7f800000A2SbG2S11S8G1S2bR8P1A2A2Z800000A2A2A2S0S2SbS8G1R7A2M3R1A2SdR1ScG3R6A2A2A2S4S2SbZ10000R2A2SdR2Z643000A2A2A1F_;Fx;S1S0S4dG0S15S1S0R2R1A4RbA3S0S2SbS8G1RbA2M4R1A2SdR1ScG4RaA2A2A2S4S2SbS8G1S2bRfR5A2A2M5R2A2SdR2ScG5R4A2A2A2A1F_;Fx;F_;Fsz;Fi;S23S4dS23R1S28RaA1A3S24S26RdR2A2S15S0S0S8G1RaA2M6ScG6R9A2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;Fn;Fa;FS;FG;Frho;").
Proof.
  intros rho G S a n HF Hb Hn Hceil Hpw HG o Hin.
  eapply obj_clear_sound; eauto. exact (proj1 (forallb_forall _ _) Hb o Hin).
Qed.
