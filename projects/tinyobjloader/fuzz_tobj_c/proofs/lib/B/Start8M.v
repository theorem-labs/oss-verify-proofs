(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "ex"; "not"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "m_vm_lazy"; "vm_reserved"; "vm_noaccess"; "vm_init_sp"; "vm_limit"; "maps_subtract"; "page_in_ranges"; "region_free"; "VmMaps"; "alloc_top"; "iv_subtract"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "modulo"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "prod"; "list"; "cons"; "app"; "bool"; "pair"; "true"; "fst"; "snd"; "false"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M"; "minv8"; "apartW"; "ranges_apart"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "ivB"; "ivS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "band_covered"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_n"; "mmap_nZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3"; "null_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "LB_of"; "eager_model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA MmapA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac ulia := unfold SHADOW_BAND_LO, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, SHADOW_BAND_HI in *; lia.

Definition apartW (e1 e2 : word * word) : Prop := ltac2:(tb__ "0|4|
S3S18S1aS7Q40M0S25S8G0A1M1G1Ve1;A3A2M2S7G0S26G1G1Ve1;A3A2A2S7G0S25G1G1Ve2;A3A2M3A2S18S1aG3S7G0S26G1G1Ve2;A3A2A2G2A2A2").
Lemma apartW_sym : ltac2:(tb__ "0|2|
S1eS8Q40A1M0G0A2M1G1S2aR2R1A2S2aR2R3A2F_;Fe2;Fe1;").
Proof. intros e1 e2 [H|H]; [right|left]; exact H. Qed.

Lemma apartW_sub : ltac2:(tb__ "0|4|
S1eS8Q40M0A1M1G1A2M2G2G2S2aR3R2A2S18S7G0S25G1G1R3A3A2M3S7G0S25G1G1R2A3A2A2S18S1aG3S7G0S26G1G1R3A3A2A2S1aS7G0S25G1G1R4A3A2S7G0S26G1G1R4A3A2A2A2S2aR6R4A2F_;F_;F_;Fy;Fx;Fe;").
Proof. intros e x y [H|H] H1 H2; [left|right]; lia. Qed.

Fixpoint ranges_apart (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | e :: r => Forall (apartW e) r /\ ranges_apart r
  end.

Lemma ranges_apart_app : ltac2:(tb__ "0|4|
S1fS1eS8Q40A1M0G0A2M1A1M2G2S4S2bS21G1R2R1A3A1S2S2bR2A1S2S2bR1A1G1G1S2cG1R2R4A3M3G3S2aR4R3A2F_;F_;Fe2;Fe1;A2A2A2Fl2;Fl1;").
Proof.
  induction l1 as [|e l1 IH]; intros l2.
  - cbn. split; [intros H; split; [exact I | split; [exact H | intros e1 e2 []]] | intros (_ & H & _); exact H].
  - cbn [app ranges_apart]. rewrite IH, Forall_app. split.
    + intros ((F1 & F2) & R1 & R2 & X). split; [split; [exact F1 | exact R1]|]. split; [exact R2|].
      intros e1 e2 [<-|H1] H2; [exact (proj1 (Forall_forall _ _) F2 e2 H2) | exact (X e1 e2 H1 H2)].
    + intros ((F1 & R1) & R2 & X). split; [split; [exact F1 | apply Forall_forall; intros e2 H2; apply X; [left; reflexivity | exact H2]]|].
      split; [exact R1|]. split; [exact R2|]. intros e1 e2 H1 H2. apply X; [right; exact H1 | exact H2].
Qed.

Lemma ranges_apart_insert : ltac2:(tb__ "0|3|
S1fS1eS8Q40A1M0G0A2M1A1M2G2G1S2bS21G1R3R2A3A1G1S2cG1R1S21G1R5R4A3A3S2aR4R2A2F_;Fe;S2bS21G1R5S20G1R3R4A3A3A1F_;F_;Fx;Fl2;Fl1;").
Proof.
  intros l1 l2 x H HX. apply ranges_apart_app in H as (R1 & R2 & X). apply (proj2 (ranges_apart_app l1 (x :: l2))).
  split; [exact R1|]. split.
  - cbn [ranges_apart]. split; [apply Forall_forall; intros e He; apply HX; apply in_app_iff; right; exact He | exact R2].
  - intros e1 e2 H1 [<-|H2]; [apply apartW_sym; apply HX; apply in_app_iff; left; exact H1 | exact (X e1 e2 H1 H2)].
Qed.

Lemma ranges_apart_shrink : ltac2:(tb__ "0|5|
S1fS1eS8Q40M0A1M1G1A2M2A1M3G3G2G2S2bS21G2R4S20G2R2R3A3A3A1S18S7G0S25G1G1R3A3A2M4S7G0S25G1G1R2A3A2A2S18S1aG4S7G0S26G1G1R3A3A2A2S1aS7G0S25G1G1R4A3A2S7G0S26G1G1R4A3A2A2A2S2bS21G2R7S20G2R4R6A3A3A1F_;F_;F_;Fy;Fx;Fl2;Fl1;").
Proof.
  intros l1 l2 x y H H1 H2. apply ranges_apart_app in H as (R1 & R12 & X). cbn [ranges_apart] in R12. destruct R12 as [F R2].
  apply (proj2 (ranges_apart_app l1 (y :: l2))).
  split; [exact R1|]. split.
  - cbn [ranges_apart]. split; [|exact R2]. apply Forall_forall. intros e He. apply apartW_sym. apply (apartW_sub e x y); [apply apartW_sym; exact (proj1 (Forall_forall _ _) F e He) | exact H1 | exact H2].
  - intros e1 e2 He1 [<-|He2]; [|exact (X e1 e2 He1 (or_intror He2))]. apply (apartW_sub e1 x y); [exact (X e1 x He1 (or_introl eq_refl)) | exact H1 | exact H2].
Qed.

Lemma ranges_apart_mid : ltac2:(tb__ "0|3|
S1fS1eS8Q40A1M0G0A2M1A1M2G2G1G1S2bS21G1R4S20G1R2R3A3A3A1S2cG1R2S21G1R5R4A3A3S2aR4R3A2F_;F_;Fe;Fx;Fl2;Fl1;").
Proof.
  intros l1 l2 x e H He. apply ranges_apart_app in H as (R1 & R12 & X). cbn [ranges_apart] in R12. destruct R12 as [F R2].
  apply in_app_iff in He as [He|He]; [apply apartW_sym; exact (X e x He (or_introl eq_refl)) | exact (proj1 (Forall_forall _ _) F e He)].
Qed.

Lemma apart_of_region_free : ltac2:(tb__ "0|2|
S1fS1eS8Q40A1M0G0A2M1A1G0G0G1S1S22S14R4R3R2A3S24A3S2cG1R2R5A3S2aS23G0G0R5R4A4R3A2F_;F_;Fe;Fn;Fa;Fl;").
Proof.
  intros l a n [b s] Hf Hin. pose proof (State.region_free_In _ _ _ _ _ Hf Hin) as OV.
  unfold iv_overlap in OV. apply andb_false_iff in OV. unfold apartW. cbn [fst snd].
  destruct OV as [OV|OV]; apply Z.ltb_ge in OV; [right | left]; lia.
Qed.

Lemma iv_subtract_apart : ltac2:(tb__ "0|4|
S8Q40M0A1M1G1S0S0S19R2R1A2S19Z0S7G0R4A2A2S3S18S1aS7G0R6A2M2S7G0R5A2A2R4A2S18R3G2A2A2S1S1fS1eG1G1A2M3A1S17R7R6R5R4A4S20G3S23G1G1R7R6A4S28G3A1A3A3F_;F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hlh Hs Hd. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_apart : ltac2:(tb__ "0|6|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0S0S19R2R1A2G1G1S2cG2S23G1G1R2R1A4R6A3S2S19Z0S7G0R2A2M4A2S3S18S1aS7G0R3A2M5G4A2R6A2S18R5G5A2A2A2F_;Fs;Fb;S1G3S12R5R4R3A3R5A3F_;F_;Fhi;Flo;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros lo hi Hlh H; [reflexivity|]. cbn [maps_subtract].
  destruct (H b s (or_introl eq_refl)) as [Hs Hd]. rewrite (iv_subtract_apart b s lo hi Hlh Hs Hd). cbn [app].
  rewrite (IH lo hi Hlh); [reflexivity|]. intros b' s' Hin. apply H. right. exact Hin.
Qed.

Lemma covered_cons_iff8 : ltac2:(tb__ "0|3|
S1eS8Q40A1M0G0A2M1S1fG1A1S0S4S1S22S2dS20G1R3R2A3R1A2S24A3S3S2S18S2fR3A1M2R1A2S19R1S1aG2S30R3A1A2A2A2S1S22S2dR2R1A2S24A3A2A2Fz;Fl;Fr;").
Proof.
  intros r l z. unfold covered. cbn [existsb]. rewrite Bool.orb_true_iff. unfold in_iv, in_rng. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.
Lemma covered_cons_false8 : ltac2:(tb__ "0|3|
S1eS8Q40A1M0G0A2M1S1fG1A1S0S4S1S22S2dS20G1R3R2A3R1A2S27A3S2S6S2S18S2fR3A1M2R1A2S19R1S1aG2S30R3A1A2A2A2A1S1S22S2dR2R1A2S27A3A2A2Fz;Fl;Fr;").
Proof.
  intros r l z. unfold covered. cbn [existsb]. rewrite Bool.orb_false_iff. unfold in_iv, in_rng. rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge.
  split; [intros [H1 H2]; split; [lia | exact H2] | intros [H1 H2]; split; [lia | exact H2]].
Qed.
Lemma covered_subtract_false8 : ltac2:(tb__ "0|1|
S1fS1eS8Q40A1M0G0A2A1S0S0S0S2eR4A1S18R4R3A2S1S22S2dR6R3A2S27A3S1S22S2dS12R7R6R5A3R4A2S27A3F_;F_;F_;Fz;Fhi;Flo;Fl;").
Proof.
  intros l lo hi z Hwf Hlh Hc. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Cv). rewrite Cv, Hc. reflexivity.
Qed.
Lemma page_in_ranges_subtract_keep8 : ltac2:(tb__ "0|3|
S1fS1eS8Q40M0A1M1G1A2A1S0S0G1S2eR4A1S18R4R3A2S1S22S13R3R6A2S24A3S3S18S1aS7G0R4A2M2Z1000A2R6A2S18R5G2A2A2S1S22S13R5S12R8R7R6A3A2S24A3F_;F_;F_;F_;Fp;Fhi;Flo;Fl;").
Proof.
  intros l lo hi p Hwf Hlh Hin Hd. apply page_in_ranges_spec in Hin as ([a sz] & Hr & Hpr). apply page_in_range_spec in Hpr. cbn [fst snd] in Hpr.
  unfold page_size in Hpr. pose proof (Hwf _ Hr) as W. unfold iv_wf, ivB, ivS in W. cbn [fst snd] in W.
  destruct (iv_subtract_keeps a sz lo hi (bv_unsigned p) (bv_unsigned p + 4096) (Hwf _ Hr) Hlh ltac:(lia) ltac:(lia) ltac:(lia) Hd) as ([rb rs] & Hq & Q1 & Q2).
  cbn [fst snd] in Q1, Q2. apply page_in_ranges_spec. exists (rb, rs). split.
  - clear - Hr Hq. induction l as [|[a' s'] l IH]; [destruct Hr|]. cbn [maps_subtract]. apply in_app_iff.
    destruct Hr as [[= <- <-]|Hr]; [left; exact Hq | right; exact (IH Hr)].
  - apply page_in_range_spec. cbn [fst snd]. unfold page_size. lia.
Qed.
Lemma page_in_ranges_app_r : ltac2:(tb__ "0|3|
S8Q40A1M0S1fS1eG0G0A2M1A1M2G2S1S22S13R3R1A2S24A3S1S22S13R4S21G1R3R2A3A2S24A3F_;Fl2;Fl1;Fp;").
Proof. intros p l1 l2 H. rewrite page_in_ranges_app, H. apply Bool.orb_true_r. Qed.

Record minv8 (L : list (word * word)) (lim : Z) (isp : word) (HQ : Z) (mo : Model) : Prop := mkMinv8 {
  mi_res : vm_reserved (m_vmmaps mo) = segments_reserved segsA;
  mi_maps : vm_maps (m_vmmaps mo) = L;
  mi_lim : vm_limit (m_vmmaps mo) = lim;
  mi_isp : vm_init_sp (m_vmmaps mo) = isp;
  mi_top : init_sp_ok (m_vmmaps mo);
  mi_band : band_covered (segments_reserved segsA ++ L) SHADOW_BAND_LO SHADOW_BAND_HI;
  mi_apart : ranges_apart (segments_reserved segsA ++ L);
  mi_pos : forall b s, In (b, s) L -> 0 < bv_unsigned s;
  mi_wfm : ivs_wf L;
  mi_lzlow : forall p : word, SHADOW_BAND_LO <= bv_unsigned p -> bv_unsigned p + 4096 <= SHADOW_RW_LO_END -> page_in_ranges p (m_vm_lazy mo) = true;
  mi_acclow : forall z, SHADOW_BAND_LO <= z < SHADOW_RW_LO_END -> covered (vm_noaccess (m_vmmaps mo)) z = false;
  mi_lzhigh : forall p : word, HQ <= bv_unsigned p -> bv_unsigned p + 4096 <= SHADOW_BAND_HI -> page_in_ranges p (m_vm_lazy mo) = true;
  mi_acchigh : forall z, SHADOW_RW_HI_BEG <= z < SHADOW_BAND_HI -> covered (vm_noaccess (m_vmmaps mo)) z = false;
  mi_namaps : forall z, covered (vm_noaccess (m_vmmaps mo)) z = true ->
                exists b s, In (b, s) L /\ bv_unsigned b <= z < bv_unsigned b + bv_unsigned s;
  mi_wfn : ivs_wf (vm_noaccess (m_vmmaps mo));
  mi_wfl : ivs_wf (m_vm_lazy mo);
  mi_posn : ivs_pos (vm_noaccess (m_vmmaps mo)) }.

Arguments mi_res {L lim isp HQ mo} _.
Arguments mi_maps {L lim isp HQ mo} _.
Arguments mi_lim {L lim isp HQ mo} _.
Arguments mi_isp {L lim isp HQ mo} _.
Arguments mi_top {L lim isp HQ mo} _.
Arguments mi_band {L lim isp HQ mo} _.
Arguments mi_apart {L lim isp HQ mo} _.
Arguments mi_pos {L lim isp HQ mo} _.
Arguments mi_wfm {L lim isp HQ mo} _.
Arguments mi_lzlow {L lim isp HQ mo} _.
Arguments mi_acclow {L lim isp HQ mo} _.
Arguments mi_lzhigh {L lim isp HQ mo} _.
Arguments mi_acchigh {L lim isp HQ mo} _.
Arguments mi_namaps {L lim isp HQ mo} _.
Arguments mi_wfn {L lim isp HQ mo} _.
Arguments mi_wfl {L lim isp HQ mo} _.
Arguments mi_posn {L lim isp HQ mo} _.

Lemma minv8_ledger : ltac2:(tb__ "0|4|
S1fS1eS8Q40A1M0G0A2M1A1M2S0G0S0SbS29R5R4R3R2R1A5S1G2S21G1SeSaR2A1M3A1ScG3A1A3S21G1S34S35A1R6A3A3F_;Fmo;FHQ;Fisp;Flim;FL;").
Proof. intros L lim isp HQ mo HI. rewrite (mi_res HI), (mi_maps HI). reflexivity. Qed.

Lemma minv8_bandM : ltac2:(tb__ "0|3|
S1fS1eS8Q40A1M0G0A2M1A1S0G0S0SbS29R5R4R3R2R1A5S33S21G1SeSaR2A1M2A1ScG2A1A3S31S32A3F_;Fmo;FHQ;Fisp;Flim;FL;").
Proof. intros L lim isp HQ mo HI. rewrite (minv8_ledger _ _ _ _ _ HI). exact (mi_band HI). Qed.

Lemma minv8_top : ltac2:(tb__ "0|2|
S1fS1eS8Q40M0A1M1G1A2A1S0G1S0SbS29R5R4R3R2R1A5S1S0S16SaR2A1A1S1dS7G0R4A2Z800000A2A3F_;Fmo;FHQ;Fisp;Flim;FL;").
Proof. intros L lim isp HQ mo HI. unfold alloc_top. rewrite (mi_isp HI), stack_max_size_val. reflexivity. Qed.

Lemma minv8_in : ltac2:(tb__ "0|2|
S1fS1eS8Q40A1M0G0A2M1A1S0G0S0SbG1S29R6R5R4R3R2A5S2cG1R2R7A3S2cG1R3ScSaR4A1A1A3F_;F_;Fe;Fmo;FHQ;Fisp;Flim;FL;").
Proof. intros L lim isp HQ mo e HI He. rewrite (mi_maps HI). exact He. Qed.

Lemma minv8_wfM : ltac2:(tb__ "0|1|
S1fS1eS8Q40A1M0G0A2A1S0G0S0SbS29R5R4R3R2R1A5S2eScSaR2A1A1A1F_;Fmo;FHQ;Fisp;Flim;FL;").
Proof. intros L lim isp HQ mo HI. rewrite (mi_maps HI). exact (mi_wfm HI). Qed.

Lemma minv8_cong : ltac2:(tb__ "0|2|
S1fS1eS8Q40A1M0G0A2A1M1S0G0S0SbSbS1S15SaR1A1SaR2A1A3S1G1SdR2A1SdR3A1A3S29R8R7R6R5R4A5S29R9R8R7R6R4A5F_;F_;F_;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' E1 E2 HI. destruct HI. constructor; rewrite ?E1, ?E2; assumption.
Qed.

Lemma minv8_HQ_mono : ltac2:(tb__ "0|1|
S1fS1eS8Q40A1M0G0A2A1S0G0S0S0SbS29R6R5R4R3R1A5S18R4R3A2S29R8R7R6R4R3A5F_;F_;Fmo;FHQ';FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ HQ' mo HI Hle. pose proof HI as HI'. destruct HI'. constructor; try assumption. intros p H1 H2. apply (mi_lzhigh HI); lia.
Qed.

Lemma mmap_nZ_of_pages : ltac2:(tb__ "0|3|
S0S19Z0M0R1A2S1S0S1bR2Z1000A2G0A3S19R3S1cZ2Z3eA2A2S2S1S0S38S9Q40M1R4A2M2A1R4A3S1S8G1A1S37G2A1G2A3A2F_;F_;F_;FLz;").
Proof.
  intros Lz HL HLal HLs.
  assert (HnZ : mmap_nZ (Z_to_bv 64 Lz) = Lz).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite u64_of_lit by lia.
    pose proof HLal as Hm'. apply Z.mod_divide in Hm' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [exact HnZ | unfold mmap_n; rewrite HnZ; reflexivity].
Qed.

Lemma minv8_place : ltac2:(tb__ "0|7|
S1fS1eS8Q40M0A1M1G1A2M2A1S0G1S0SbS0G1S29R7R6R5R4R3A5S19Z0M3R3A2S1S0S1bR4Z1000M4A2G3A3S19R5S1cZ2Z3eA2A2S36S9G0G3A2R7S9G0R6A2R5A4S2S18S3aR7A1S7G0R6A2M5A2S2S3S18S1aG5R7A2M6Z10000A2S18Z643000G5A2A2S2S3S18G6S31A2S18S32G5A2A2S2S18G6S1dS7G0RaA2Z800000A2A2S2S1S0S1bG5G4A2G3A3S1S22S14S21G2S34S35A1RcA3R6S9G0R7A2A3S24A3A2A2A2A2A2F_;F_;F_;F_;F_;Fa;FLz;Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo Lz a HI HL HLal HLs Hpl.
  pose proof (place_LB_A mo Lz a (mi_top HI) (mi_res HI) (minv8_bandM _ _ _ _ _ HI) ltac:(lia) HLal Hpl) as (P1 & P2 & P3 & P4 & _).
  rewrite (minv8_top _ _ _ _ _ HI) in P4. pose proof Hpl as (Pal & _ & _ & Pfree).
  destruct (mmap_nZ_of_pages Lz HL HLal HLs) as [HnZ Hn]. rewrite Hn, (minv8_ledger _ _ _ _ _ HI) in Pfree.
  unfold page_size in Pal. repeat split; try assumption.
Qed.

Lemma minv8_fresh_acc : ltac2:(tb__ "0|4|
S1fS1eS8Q40M0A1M1G1A2M2A1S0G1S0SbG1G1S0S29R8R7R6R5R4A5S1S22S14S21G2S34S35A1R9A3R4R3A3S24A3S2S18S7G0R5A2M3R3A2S19R3S1aG3S7G0R4A2A2A2A2S1S22S2dSfSaR7A1A1R4A2S27A3F_;F_;F_;Fz;Fn;Fa;Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo a n z HI Hfree Hz.
  destruct (covered (vm_noaccess (m_vmmaps mo)) z) eqn:E; [|reflexivity]. exfalso.
  destruct (mi_namaps HI z E) as (b & s & Hin & Hb).
  pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ Hfree) Hin) as OV.
  unfold iv_overlap in OV. apply andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

Lemma free_not_image8 : ltac2:(tb__ "0|4|
S1fS1eS8Q40M0A1M1G1A2M2A1G1G1S1S22S14S21G2S34S35A1R3A3R2R1A3S24A3S19Z0S7G0R2A2A2S0S2S18S7G0R5A2M3R1A2S19R1S1aG3S7G0R4A2A2A2A2S6S2S18Z10000R2A2S19R2Z643000A2A2A1F_;Fy;F_;F_;Fn;Fa;Fl;").
Proof.
  intros l a n Hfree Hn y Hy Himg.
  pose proof (grant_avoids_band _ IMG_BAND_LO IMG_BAND_HI a n (img_band_covered _ ltac:(apply incl_appl; apply incl_refl)) ltac:(unfold IMG_BAND_LO, IMG_BAND_HI; lia) Hfree Hn) as X.
  unfold IMG_BAND_LO, IMG_BAND_HI in X. lia.
Qed.

Lemma minv8_grant_gen : ltac2:(tb__ "0|9|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0G1S0SbSbS0G1G3S29R9R8R7R6R5A5S19Z0M4R4A2S1S0S1bR5Z1000A2G4A3S19R6S1cZ2Z3eA2A2S36S9G0G4A2R9S9G0R7A2R6A4S1G3SeSaR9A1A1SeSaRaA1M5A1A3S1G3ScG5A1S20G2S23G1G1R8S9G0R9A2A4ScSaRbA1M6A1A3A3S1G3SfG6A1SfSaRcA1M7A1A3S1S0S11G7A1S11SaRdA1M8A1A3S1G1S10G8A1S10SaReA1A1A3S1G3SdReA1S21G2RbSdRfA1A3A3S2eRcA1S29S20G2S23G1G1ReS9G0RfA2A4R15A3R14R13R12R10A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Flz';Fa;FLz;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' Lz a lz' HI HL HLal HLs Hpl ER EM EN EL EI EZ WZ.
  pose proof (minv8_place _ _ _ _ _ Lz a HI HL HLal HLs Hpl) as (G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (urange isp) as UI. assert (Un : bv_unsigned (Z_to_bv 64 Lz) = Lz) by (apply u64_of_lit; lia).
  constructor; rewrite ?ER, ?EM, ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - rewrite (mi_maps HI). reflexivity.
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - apply band_covered_app_cons. exact (mi_band HI).
  - apply ranges_apart_insert; [exact (mi_apart HI)|]. intros e He. exact (apart_of_region_free _ _ _ e G6 He).
  - intros b s [[= <- <-]|Hin]; [rewrite Un; lia | exact (mi_pos HI b s Hin)].
  - apply ivs_wf_cons; [|exact (mi_wfm HI)]. unfold iv_wf, ivB, ivS. cbn [fst snd]. rewrite Un. lia.
  - intros p H1 H2. apply page_in_ranges_app_r. exact (mi_lzlow HI p H1 H2).
  - exact (mi_acclow HI).
  - intros p H1 H2. apply page_in_ranges_app_r. exact (mi_lzhigh HI p H1 H2).
  - exact (mi_acchigh HI).
  - intros z Hz. destruct (mi_namaps HI z Hz) as (b & s & Hin & Hb). exists b, s. split; [right; exact Hin | exact Hb].
  - exact (mi_wfn HI).
  - apply ivs_wf_app; [exact WZ | exact (mi_wfl HI)].
  - exact (mi_posn HI).
Qed.

Lemma minv8_eager : ltac2:(tb__ "0|4|
S1fS1eS8Q40M0A1M1G1A2M2A1S0G1S0SbS0G1S29R7R6R5R4R3A5S19Z0M3R3A2S1S0S1bR4Z1000A2G3A3S19R5S1cZ2Z3eA2A2S36S9G0G3A2R7S9G0R6A2R5A4S29S20G2S23G1G1R6S9G0R7A2A4RcA3RbRaR9S3bR7R8R6A3A5F_;F_;F_;F_;F_;Fa;FLz;Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo Lz a HI HL HLal HLs Hpl.
  assert (EM : m_vmmaps (eager_model Lz mo a) = eager_h Lz mo a) by (unfold eager_model; rewrite m_vmmaps_with_vmmaps; reflexivity).
  assert (EL : m_vm_lazy (eager_model Lz mo a) = [] ++ m_vm_lazy mo) by (unfold eager_model; rewrite m_vm_lazy_with_vmmaps; reflexivity).
  apply (minv8_grant_gen L lim isp HQ mo _ Lz a [] HI HL HLal HLs Hpl); rewrite ?EM; try reflexivity; try exact EL; try apply ivs_wf_nil.
Qed.

Lemma minv8_null_rw : ltac2:(tb__ "0|4|
S1fS1eS8Q40M0A1M1G1A2M2A1S0G1S0SbS0G1S29R7R6R5R4R3A5S19Z0M3R3A2S1S0S1bR4Z1000A2G3A3S19R5S1cZ2Z3eA2A2S36S9G0G3A2R7S9G0R6A2R5A4S29S20G2S23G1G1R6S9G0R7A2A4RcA3RbRaR9S39R7R8R6A3A5F_;F_;F_;F_;F_;Fa;FLz;Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo Lz a HI HL HLal HLs Hpl.
  pose proof (minv8_place _ _ _ _ _ Lz a HI HL HLal HLs Hpl) as (G1 & G2 & G3 & G4 & _). pose proof (urange isp) as UI.
  assert (EM : m_vmmaps (null_rw_model Lz mo a) = null_rw_h Lz mo a) by (unfold null_rw_model; rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps; reflexivity).
  assert (EL : m_vm_lazy (null_rw_model Lz mo a) = lazy_interior a (Z_to_bv 64 Lz) ++ m_vm_lazy mo)
    by (unfold null_rw_model; rewrite m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps; reflexivity).
  apply (minv8_grant_gen L lim isp HQ mo _ Lz a (lazy_interior a (Z_to_bv 64 Lz)) HI HL HLal HLs Hpl); rewrite ?EM; try reflexivity; try exact EL.
  apply lazy_interior_wf. rewrite u64_of_lit by lia. lia.
Qed.

Lemma null_rw_first_page : ltac2:(tb__ "0|4|
S0SbS8Q40M0A1S19Z0M1R3A2S1S0S1bR4Z1000M2A2G1A3S19R5S1cZ2M3Z3eA2A2S18G2R6A2S1S0S1bS7G0R5A2G2A2G1A3S18S1aS7G0R6A2R8A2S1cG3Z40A2A2S1S22S13R7SdS39R9R8R7A3A1A2S24A3F_;F_;F_;F_;F_;F_;Fa;Fmo;FLz;").
Proof.
  intros Lz mo a HL HLal HLs H4 Hal Hhi.
  unfold null_rw_model, vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_with_vmmaps. rewrite page_in_ranges_app. apply orb_true_intro. left.
  assert (PB : page_base a = a).
  { apply bv_eq. rewrite page_base_val. unfold page_size. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). lia. }
  rewrite <- PB at 1.
  apply (proj1 (in_interior_pages a (Z_to_bv 64 Lz) a ltac:(unfold page_size; exact Hal) ltac:(unfold page_size; rewrite u64_of_lit by lia; exact HLal)
            ltac:(rewrite u64_of_lit by lia; lia) ltac:(rewrite u64_of_lit by lia; lia))). rewrite u64_of_lit by lia. lia.
Qed.

Lemma minv8_cons_low : ltac2:(tb__ "0|8|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0G1S0SbSbG1G1G1S29R9R8R7R6R5A5S1S22S14S21G2S34S35A1RaA3R4R2A3S24A3S18S7G0R4A2S7G0R3A2A2S19Z0S7G0R5A2A2S18S1aS7G0R7A2S7G0R6A2A2S31A2S1G3SeSaR9A1A1SeSaRaA1M4A1A3S1G3ScG4A1S20G2S23G1G1R9R8A4ScSaRbA1M5A1A3A3S1G3SfG5A1SfSaRcA1M6A1A3S1S0S11G6A1S11SaRdA1M7A1A3S1G1S10G7A1S10SaReA1A1A3S1G3SdReA1SdRfA1A3S29S20G2S23G1G1ReRdA4R14A3R13R12R11RfA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fs;Fb;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' b s n HI Hfree Hsn Hs Hb ER EM EN EL EI EZ.
  constructor; rewrite ?ER, ?EM, ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - rewrite (mi_maps HI). reflexivity.
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - apply band_covered_app_cons. exact (mi_band HI).
  - apply ranges_apart_insert; [exact (mi_apart HI)|]. intros e He.
    apply apartW_sym. apply (apartW_sub e (b, n) (b, s)); [apply apartW_sym; exact (apart_of_region_free _ _ _ e Hfree He) | cbn [fst]; lia | cbn [fst snd]; lia].
  - intros b' s' [[= <- <-]|Hin]; [exact Hs | exact (mi_pos HI b' s' Hin)].
  - apply ivs_wf_cons; [|exact (mi_wfm HI)]. unfold iv_wf, ivB, ivS. cbn [fst snd]. unfold SHADOW_BAND_LO in Hb. lia.
  - exact (mi_lzlow HI).
  - exact (mi_acclow HI).
  - exact (mi_lzhigh HI).
  - exact (mi_acchigh HI).
  - intros z Hz. destruct (mi_namaps HI z Hz) as (b0 & s0 & Hin & Hb0). exists b0, s0. split; [right; exact Hin | exact Hb0].
  - exact (mi_wfn HI).
  - exact (mi_wfl HI).
  - exact (mi_posn HI).
Qed.

Lemma minv8_guard : ltac2:(tb__ "0|b|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0G1S0SbSbG1G1S0S0S29RaR9R8R7R6A5S1G3SeSaR6A1A1SeSaR7A1M4A1A3S1G3ScG4A1ScSaR8A1M5A1A3S1G3SfG5A1S20G2S23G1G1R7R6A4S12SfSaR9A1M6A1R5R4A3A3A3S1S0S11G6A1S11SaRaA1M7A1A3S1G1S10G7A1S10SaRbA1A1A3S1G3SdRbA1S12SdRcA1R8R7A3A3S18R9R8A2S18R9S31A2S18RaR10A2S18S1aS7G0ReA2M8S7G0RdA2A2S31A2S19Z0G8A2S5G1G1S5G1G1S2S2cG2S23G1G1R2R1A4R18A3S2S18S7G0R2A2M9S7G0R12A2MaA2S18S1aGaS7G0R11A2A2S1aG9S7G0R1A2A2A2A2A2Ls';A2Lb';A2S29R17R16R15R14R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fn;Fb;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' b n lo hi HI ER EM EN EL EI EZ Hlh Hhi HhQ Hbn Hn0 Hin.
  pose proof (urange n) as Un. pose proof (mi_wfn HI) as W2. pose proof (mi_wfl HI) as W3.
  constructor; rewrite ?ER, ?EM, ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - exact (mi_maps HI).
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - exact (mi_band HI).
  - exact (mi_apart HI).
  - exact (mi_pos HI).
  - exact (mi_wfm HI).
  - intros p H1 H2. apply page_in_ranges_subtract_keep8; [exact W3 | exact Hlh | exact (mi_lzlow HI p H1 H2) | right; ulia].
  - intros z Hz. apply covered_cons_false8. split; [unfold ivB, ivS; cbn [fst snd]; ulia | apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acclow HI z Hz)]].
  - intros p H1 H2. apply page_in_ranges_subtract_keep8; [exact W3 | exact Hlh | exact (mi_lzhigh HI p H1 H2) | right; ulia].
  - intros z Hz. apply covered_cons_false8. split; [unfold ivB, ivS; cbn [fst snd]; ulia | apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acchigh HI z Hz)]].
  - intros z Hz. apply covered_cons_iff8 in Hz as [Hz|Hz].
    + unfold ivB, ivS in Hz. cbn [fst snd] in Hz. destruct Hin as (b' & s' & H1 & H2 & H3). exists b', s'. split; [exact H1 | lia].
    + destruct (maps_subtract_sem _ lo hi W2 Hlh) as (_ & _ & Cv). rewrite Cv in Hz. apply andb_prop in Hz as [Hz _]. exact (mi_namaps HI z Hz).
  - apply ivs_wf_cons; [|apply maps_subtract_wf; [exact W2 | exact Hlh]].
    destruct Hin as (b' & s' & H1 & H2 & H3). pose proof (mi_wfm HI _ H1) as X. unfold iv_wf, ivB, ivS in X |- *. cbn [fst snd] in X |- *. lia.
  - apply maps_subtract_wf; [exact W3 | exact Hlh].
  - apply ivs_pos_cons; [exact Hn0 | apply ivs_pos_subtract; exact (mi_posn HI)].
Qed.

Lemma minv8_dead : ltac2:(tb__ "0|b|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0G1S0SbSbG1G1S0S29S20G2S23G1G1R3R2A4R9A3R8R7R6R5A5S19S7G0R4A2M4R2A2S19R3S1aS7G0R5A2M5G4A2A2S18S1aS7G0R6A2G5A2S31A2S18R5RaA2S1G3SeSaR9A1A1SeSaRaA1M6A1A3S1G3ScG6A1S12ScSaRbA1M7A1S7G0R9A2R7A3A3S1G3SfG7A1S12SfSaRcA1M8A1S7G0RaA2R8A3A3S1S0S11G8A1S11SaRdA1M9A1A3S1G1S10G9A1S10SaReA1A1A3S1G3SdReA1S12SdRfA1S7G0RdA2MaRbA3A3S29S20G2S23G1G1S9G0RcA2S9G0S1dS1aS7G0ReA2GaA2RcA2A2A4R14A3R13R12R11RfA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Fs0;Fb0;Fmo';Fmo;FHQ;Fisp;Flim;FL0;").
Proof.
  intros L0 lim isp HQ mo mo' b0 s0 hi HI Hlo Hhi Hband HhQ ER EM EN EL EI EZ.
  pose proof (urange b0) as Ub. pose proof (urange s0) as Us.
  pose proof (mi_wfn HI) as W2. pose proof (mi_wfl HI) as W3. pose proof (mi_wfm HI) as W1.
  pose proof (W1 _ (or_introl eq_refl)) as W0. unfold iv_wf, ivB, ivS in W0. cbn [fst snd] in W0.
  assert (Uh : bv_unsigned (Z_to_bv 64 hi) = hi) by (apply u64_of_lit; lia).
  assert (Ur : bv_unsigned (Z_to_bv 64 (bv_unsigned b0 + bv_unsigned s0 - hi)) = bv_unsigned b0 + bv_unsigned s0 - hi) by (apply u64_of_lit; lia).
  assert (Hlh : bv_unsigned b0 <= hi) by lia.

  assert (AP : forall b s, In (b, s) L0 -> 0 < bv_unsigned s /\ (bv_unsigned b + bv_unsigned s <= bv_unsigned b0 \/ hi <= bv_unsigned b)).
  { intros b s Hin. split; [exact (mi_pos HI b s (or_intror Hin))|].
    pose proof (ranges_apart_mid (segments_reserved segsA) L0 (b0, s0) (b, s) (mi_apart HI) ltac:(apply in_app_iff; right; exact Hin)) as [A|A]; cbn [fst snd] in A; [right | left]; lia. }
  assert (EM' : vm_maps (m_vmmaps mo') = (Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned b0 + bv_unsigned s0 - hi)) :: L0).
  { rewrite EM, (mi_maps HI). cbn [maps_subtract]. rewrite (maps_subtract_apart L0 (bv_unsigned b0) hi ltac:(lia) AP).
    unfold iv_subtract. cbv zeta. rewrite (proj2 (Z.ltb_ge (bv_unsigned b0) (bv_unsigned b0))) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b0 + bv_unsigned s0))) by lia.
    cbn [app]. rewrite Z.max_r by lia. reflexivity. }
  constructor; rewrite ?ER, ?EM', ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - reflexivity.
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - apply (band_covered_transfer (segments_reserved segsA ++ (b0, s0) :: L0)); [exact (mi_band HI)|].
    intros b s z Hin Hz Hbs. apply in_app_iff in Hin as [Hin|[[= <- <-]|Hin]]; apply in_app_iff; [left; exact Hin | exfalso; ulia | right; right; exact Hin].
  - apply (ranges_apart_shrink (segments_reserved segsA) L0 (b0, s0)); [exact (mi_apart HI) | cbn [fst]; rewrite Uh; lia | cbn [fst snd]; rewrite Uh, Ur; lia].
  - intros b s [[= <- <-]|Hin]; [rewrite Ur; lia | exact (mi_pos HI b s (or_intror Hin))].
  - apply ivs_wf_cons; [unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Uh, Ur; lia | intros q Hq; exact (W1 q (or_intror Hq))].
  - intros p H1 H2. apply page_in_ranges_subtract_keep8; [exact W3 | exact Hlh | exact (mi_lzlow HI p H1 H2) | right; ulia].
  - intros z Hz. apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acclow HI z Hz)].
  - intros p H1 H2. apply page_in_ranges_subtract_keep8; [exact W3 | exact Hlh | exact (mi_lzhigh HI p H1 H2) | right; ulia].
  - intros z Hz. apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acchigh HI z Hz)].
  - intros z Hz. destruct (maps_subtract_sem _ (bv_unsigned b0) hi W2 Hlh) as (_ & _ & Cv). rewrite Cv in Hz. apply andb_prop in Hz as [Hz Hnz].
    unfold in_rng in Hnz. apply Bool.negb_true_iff in Hnz. apply andb_false_iff in Hnz.
    assert (Hout : z < bv_unsigned b0 \/ hi <= z) by (destruct Hnz as [Hnz|Hnz]; [apply Z.leb_gt in Hnz | apply Z.ltb_ge in Hnz]; lia).
    destruct (mi_namaps HI z Hz) as (b & s & [[= <- <-]|Hin] & Hb).
    + exists (Z_to_bv 64 hi), (Z_to_bv 64 (bv_unsigned b0 + bv_unsigned s0 - hi)). split; [left; reflexivity|]. rewrite Uh, Ur. lia.
    + exists b, s. split; [right; exact Hin | exact Hb].
  - apply maps_subtract_wf; [exact W2 | exact Hlh].
  - apply maps_subtract_wf; [exact W3 | exact Hlh].
  - apply ivs_pos_subtract. exact (mi_posn HI).
Qed.

Lemma minv8_reserve : ltac2:(tb__ "0|9|
S1fS1eS8Q40M0A1M1G1A2M2A1M3S0G1S0SbSbS0G1S29R8R7R6R5R4A5S19Z0M4R3A2S1S0S1bR4Z1000A2G4A3S19R5S1cZ2Z3eA2A2S36S9G0G4A2R8S9G0R6A2R5A4S1G3SeSaR8A1A1SeSaR9A1M5A1A3S1G3ScG5A1S20G2S23G1G1R7S9G0R8A2A4ScSaRaA1M6A1A3A3S1G3SfG6A1S20G2S23G1G1R8S9G0R9A2A4SfSaRbA1M7A1A3A3S1S0S11G7A1S11SaRcA1M8A1A3S1G1S10G8A1S10SaRdA1A1A3S1G3SdRdA1SdReA1A3S29S20G2S23G1G1RcS9G0RdA2A4R13A3R12R11R10ReA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;FLz;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' Lz a HI HL HLal HLs Hpl ER EM EN EL EI EZ.
  pose proof (minv8_place _ _ _ _ _ Lz a HI HL HLal HLs Hpl) as (G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (urange isp) as UI. assert (Un : bv_unsigned (Z_to_bv 64 Lz) = Lz) by (apply u64_of_lit; lia).
  assert (Wa : iv_wf (a, Z_to_bv 64 Lz)) by (unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Un; lia).
  constructor; rewrite ?ER, ?EM, ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - rewrite (mi_maps HI). reflexivity.
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - apply band_covered_app_cons. exact (mi_band HI).
  - apply ranges_apart_insert; [exact (mi_apart HI)|]. intros e He. exact (apart_of_region_free _ _ _ e G6 He).
  - intros b s [[= <- <-]|Hin]; [rewrite Un; lia | exact (mi_pos HI b s Hin)].
  - apply ivs_wf_cons; [exact Wa | exact (mi_wfm HI)].
  - exact (mi_lzlow HI).
  - intros z Hz. apply covered_cons_false8. split; [unfold ivB, ivS; cbn [fst snd]; rewrite Un; ulia | exact (mi_acclow HI z Hz)].
  - exact (mi_lzhigh HI).
  - intros z Hz. apply covered_cons_false8. split; [unfold ivB, ivS; cbn [fst snd]; rewrite Un; ulia | exact (mi_acchigh HI z Hz)].
  - intros z Hz. apply covered_cons_iff8 in Hz as [Hz|Hz].
    + unfold ivB, ivS in Hz. cbn [fst snd] in Hz. exists a, (Z_to_bv 64 Lz). split; [left; reflexivity | lia].
    + destruct (mi_namaps HI z Hz) as (b & s & Hin & Hb). exists b, s. split; [right; exact Hin | exact Hb].
  - apply ivs_wf_cons; [exact Wa | exact (mi_wfn HI)].
  - exact (mi_wfl HI).
  - apply ivs_pos_cons; [rewrite Un; lia | exact (mi_posn HI)].
Qed.

Lemma minv8_expose : ltac2:(tb__ "0|6|
S1fS1eS8Q40A1M0G0A2A1M1S0G0S0SbSbS0S0S29R8R7R6R5R4A5S1G1SeSaR4A1A1SeSaR5A1M2A1A3S1G1ScG2A1ScSaR6A1M3A1A3S1G1SfG3A1S12SfSaR7A1M4A1R5R4A3A3S1S0S11G4A1S11SaR8A1M5A1A3S1G0S10G5A1S10SaR9A1A1A3S1G1SdR9A1SdRaA1A3S18R9R8A2S29R10RfReRdRbA5F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fmo';Fmo;FHQ;Fisp;Flim;FL;").
Proof.
  intros L lim isp HQ mo mo' lo hi HI ER EM EN EL EI EZ Hlh. pose proof (mi_wfn HI) as W2.
  constructor; rewrite ?ER, ?EM, ?EN, ?EL, ?EI, ?EZ.
  - exact (mi_res HI).
  - exact (mi_maps HI).
  - exact (mi_lim HI).
  - exact (mi_isp HI).
  - pose proof (mi_top HI) as T. unfold init_sp_ok in *. rewrite EI. exact T.
  - exact (mi_band HI).
  - exact (mi_apart HI).
  - exact (mi_pos HI).
  - exact (mi_wfm HI).
  - exact (mi_lzlow HI).
  - intros z Hz. apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acclow HI z Hz)].
  - exact (mi_lzhigh HI).
  - intros z Hz. apply covered_subtract_false8; [exact W2 | exact Hlh | exact (mi_acchigh HI z Hz)].
  - intros z Hz. destruct (maps_subtract_sem _ lo hi W2 Hlh) as (_ & _ & Cv). rewrite Cv in Hz. apply andb_prop in Hz as [Hz _]. exact (mi_namaps HI z Hz).
  - apply maps_subtract_wf; [exact W2 | exact Hlh].
  - exact (mi_wfl HI).
  - apply ivs_pos_subtract. exact (mi_posn HI).
Qed.
