(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MFree"; "st_free_meta_head"; "st_init_done"; "st_avail_meta_count"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@Corelib.Init.Logic"; "eq"; "not"; "@Corelib.Init.Datatypes"; "Some"; "list"; "option"; "prod"; "bool"; "pair"; "true"; "None"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "ok_frame"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "JL_am_ok"; "J_am_pre"; "L_am_ok"; "Pre_am"; "@Stdlib.Lists.List"; "In"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "Kexact"; "@Stdlib.ZArith.BinInt.Z"; "lt"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail SymHeap Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import WalkLink ReabKit ObjBytes GapGeneric MallocLaws
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfArith MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom MallocWfSurgery MallocLayout MallocFooter
  MallocIface MallocIfaceI Contract ContractI ContractAM Glue ReprGlue ZEval ZBits WalkArith FpLaws Zones2 AllocMetaPost AllocMetaImage AllocMetaGrow ClientLaws ContractS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_H3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ok_frame_exactF : ltac2:(tb__ "0|1|
S20OF_;SbS1cA1M0S1bOF_;F_;G0S1bS1dS6R4R3A3R4R3R2A2S1dS6R6S27R4R3A2A3F_;F_;Fmd;Ftr;FKc;Fok;").
Proof. intros ok Kc tr md HF HK tr' ms md' ms' [-> ->] Hi Hp Hs. exact (HF tr ms md ms' HK Hi Hp Hs). Qed.

Module S_H1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_H1.
Theorem am_H1_sound_in : ltac2:(tb__ "0|2|
S20OF_;SbS0A1ScSdS0S14A2A1S14S14F_;S13SbS1cA1S1bOF_;F_;S16SbSdS15S17A2M0A1S1dS6R8R3A3S26G0SfS15S17S24S19A1S22S6S1aR8R7R6R5R4A7A4R2A3S0S8ScS0A1S3S12R7A1A1SaS0R1A2A3S8ScS1A1S1fS12R8A1R2A2SaS1S2SaS0R2A2M1G1A2A2A3S8SeS4S12R9A1A1S10A3S21S6ReS1eS6S23S6S1aRdRcRbRaR9A7S25S19A1R8A4S18S6S7R8R7A4A4F_;F_;F_;Fm;F_;F_;Fposts;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho posts HOK HINP m Hhd HmH Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H1 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head1 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exactF ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head1) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m Hhd HmH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

End S_H1.

Module S_H2.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_H2.
Theorem am_H2_sound_in : ltac2:(tb__ "0|4|
S20OF_;SbS0A1ScSdS0S14A2A1S14S14F_;S13SbS1cA1S1bOF_;F_;S16SbSdS15S17A2M0A1S1dS6R8R3A3S26G0SfS15S17S24S19A1S22S6S1aR8R7R6R5R4A7A4R2A3S0S0S8ScS0A1S3S12R8A1A1SaS0R2A2A3S9S8S0R2R3A3A1S8ScS1A1M1S1fS12RaA1R4A2SaS1S2SaS0R3A2M2G2A2A2A3S8G1S1fS12RbA1R4A2SaS1S2SaS0R5A2M3G3A2A2A3S8SeS4S12RcA1A1S10A3S21S6R11S1eS6S23S6S1aR10RfReRdRcA7S25S19A1RbA4S18S6S7RbRaA4A4F_;F_;F_;F_;F_;Fn;Fm;F_;F_;Fposts;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho posts HOK HINP m nn Hhd Hnm HmH HnH Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H2 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head2 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exactF ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head2) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn Hhd Hnm HmH HnH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

End S_H2.

Module S_H3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_H3.
Theorem am_H3_sound_in : ltac2:(tb__ "0|3|
S20OF_;SbS0A1ScSdS0S14A2A1S14S14F_;S13SbS1cA1S1bOF_;F_;S16SbSdS15S17A2M0A1S1dS6R8R3A3S26G0SfS15S17S24S19A1S22S6S1aR8R7R6R5R4A7A4R2A3S0S0S0S0S0S8ScS0A1S3S12RbA1A1SaS0R5A2A3S9S8S0R5R6A3A1S9S8S0R5R7A3A1S9S8S0R6R7A3A1S8ScS1A1M1S1fS12RfA1R9A2SaS1S2SaS0R7A2SaS0R8A2M2A2A2A3S8G1S1fS12R10A1R9A2SaS1S2SaS0RaA2SaS0R6A2A2A2A3S8G1S1fS12R11A1R9A2SaS1S2G2SaS0RbA2A2A2A3S8SeS4S12R12A1A1S10A3S21S6R17S1eS6S23S6S1aR16R15R14R13R12A7S25S19A1R11A4S18S6S7R11R10A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fn2;Fpp;Fp;Fn;Fm;F_;F_;Fposts;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho posts HOK HINP m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H3 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head3 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exactF ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head3) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

End S_H3.

Module S_AV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G3.Mal_ameta_AV.
Theorem am_AV_sound_in : ltac2:(tb__ "0|1|
S20OF_;SbS0A1ScSdS0S14A2A1S14S14F_;S13SbS1cA1S1bOF_;F_;S16SbSdS15S17A2M0A1S1dS6R8R3A3S26G0SfS15S17S24S19A1S22S6S1aR8R7R6R5R4A7A4R2A3S8ScS0A1S3S12R6A1A1S11S0A1A3S28Z0S5S12R7A1A1A2S8SeS4S12R8A1A1S10A3S21S6RdS1eS6S23S6S1aRcRbRaR9R8A7S25S19A1R7A4S18S6S7R7R6A4A4F_;F_;F_;F_;F_;Fposts;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho posts HOK HINP Hhd Hcnt Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_AV s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_avail ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exactF ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_avail) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_AV) by (unfold LF_AV; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

End S_AV.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Theorem alloc_meta_avail_P_proof : alloc_meta_avail_U.
Proof.
  intros ok X R U A Kc rho HF Havail Hinit n HQ [tr [ms md]] [Hsm HJ].
  pose proof HJ as (HMI & HXr & HKc & Hauxv & Htp & Htop). cbn [w_tr w_cfg fst snd cfg_model] in HMI.
  assert (HI : Inv X R U (ma_s A)).
  { unfold MInvIR, MInvI in HMI. pose proof (mig_I HMI) as HI. destruct A; exact HI. }
  assert (HINP : In (L_am_ok IEC_U, JL_am_ok segsU C_U X R U A Kc) [ (L_am_ok IEC_U, JL_am_ok segsU C_U X R U A Kc) ]) by (left; reflexivity).
  destruct (st_free_meta_head (ma_s A)) as [m|] eqn:Hhd.
  - destruct (free_head_cases X R U (ma_s A) HI m Hhd) as [H1 | [(n' & Hne & Hm & Hn) | (p & n' & pp & n2 & Hne1 & Hne2 & Hne3 & Hm & Hn & Hp)]].
    + exact (S_H1.am_H1_sound_in ok X R U A Kc rho _ HF HINP m Hhd H1 Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (S_H2.am_H2_sound_in ok X R U A Kc rho _ HF HINP m n' Hhd Hne Hm Hn Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
    + exact (S_H3.am_H3_sound_in ok X R U A Kc rho _ HF HINP m n' p pp n2 Hhd Hne1 Hne2 Hne3 Hm Hn Hp Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
  - destruct Havail as [Hne|Hcnt]; [exfalso; exact (Hne eq_refl)|].
    exact (S_AV.am_AV_sound_in ok X R U A Kc rho _ HF HINP Hhd Hcnt Hinit n HQ (tr, mkCfg ms md) (conj Hsm HJ)).
Qed.
