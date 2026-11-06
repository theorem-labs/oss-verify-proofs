(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2 i2 i4.

(* [comment removed for export] *)
Module SecReveal.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "mul"; "lt"; "pow"; "modulo"; "ge"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "nat"; "bool"; "true"; "pair"; "option"; "false"; "None"; "Some"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "sobj"; "ss_objs"; "obj_range"; "ranges_disjoint"; "rl"; "rw"; "image_byte"; "outside_all"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_base"; "Model"; "page_mem"; "event"; "m_vm_lazy"; "page_in_ranges"; "m_vmmaps"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal"; "JT"; "revealed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "w_tr"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymObj SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition JT : jpredA := fun _ _ _ _ => True.

Lemma SPA_J_out : ltac2:(tb__ "0|0|
SfS3cA1S28S35S1aSfS24Q40A1A1S41S27R6R5R4R3R2R1A6S1S27R7S32R5R4R3R2A6R6R4R3S40R2A1S3aS3fR2A1A1A4A2F_;Fw;Ftp;Frho;FA;FJ;Fsegs;").
Proof. intros segs J A rho tp w [H1 H2]. split; [split; [exact H1 | exact I] | exact H2]. Qed.

Lemma SPA_J_in : ltac2:(tb__ "0|0|
SfS3cA1S28S35S1aSfS24Q40A1A1S41S27R6S32R4R3R2R1A6R6R4R3S40R2A1S3aS3fR2A1A1A4S27R8R7R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;FJ;Fsegs;").
Proof. intros segs J A rho tp w [H1 _] H2. split; [exact H1 | exact H2]. Qed.

Lemma JT_blind : ltac2:(tb__ "0|1|
S1aS1aSfS24Q40A1A1M0G0SfS2cA1S2aS32R6R4R2R1A4S32R6R4R3R2A4F_;Fmd;Ftr;Ft';Ft;Fr';Fr;").
Proof. intros. exact I. Qed.

Lemma pageZ_u : ltac2:(tb__ "0|1|
SdS10S5Z0R2A2S5S6S6R3S8Z1000M0S7R2A1A2A2G0A2SaZ2Z40A2A2S0SdS25Q40S31R4R3A2A2S6R4S8G0S7R3A1A2A2A3F_;F_;Fk;Fq;").
Proof. intros q k H0 H1. unfold pageZ. apply u64_lit. lia. Qed.

Lemma page_base_run : ltac2:(tb__ "0|7|
SdS10S24Q40M0A1M1S0SdSbR3Z1000M2A2Z0M3A3S5G3R4A2S5S6R5S8G2S7R4A1A2A2SaZ2Z40A2A2S1S5R6S25G0R4A2M4A2S9G4S6R6S8G2S7R5A1A2A2A2A2S2S10S10S1S37R1R7A2S1S0G1S29R6A1S31R8R1A2A3S1S5S6R8S8G2S7R1A1A2A2M5S25G0R6A2M6A2S9G6S6G5G2A2A2A2A2A2Lk;A2F_;F_;F_;F_;Fa;Fn;Fq;").
Proof.
  intros q n a Hal H0 Hhi Ha.
  set (kz := (bv_unsigned a - q) / 4096).
  assert (Hk : 0 <= kz < Z.of_nat n).
  { subst kz. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Hr : q + 4096 * kz <= bv_unsigned a < q + 4096 * kz + 4096).
  { subst kz. pose proof (Z.div_mod (bv_unsigned a - q) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a - q) 4096 ltac:(lia)). lia. }
  exists (Z.to_nat kz). split; [lia|].
  assert (EK : Z.of_nat (Z.to_nat kz) = kz) by lia.
  split; [|rewrite EK; exact Hr].
  apply page_base_in_page.
  - rewrite pageZ_u by lia. rewrite EK. replace (q + 4096 * kz) with (q + kz * 4096) by lia.
    change page_size with 4096. rewrite Z_mod_plus_full. exact Hal.
  - unfold in_page. rewrite pageZ_u by lia. rewrite EK. change page_size with 4096. lia.
Qed.

Definition revealed (q : Z) (n : nat) (rho : valuation) (tp : list word) (rho' : valuation) (tp1 : list word) : Prop := ltac2:(tb__ "0|b|
S1SeS0S24Q40M0A1M1S21Vrho';R1A2S21Vrho;R1A2A3Fi;S1SeS0SfS24Q8M2A1M3A1S20Vrho';R1A2S20Vrho;R1A2A3Fl;S1G1S3bG1R1Vtp1;A3S1S2S10S10S1S37R1Vn;A2M4S0G1R3S31Vq;R1A2A3A2Lk;A2S3S3bG1R2Vtp;A3A1A2F_;Fp;S1S5S7S19G1Vtp1;A2A1S7Vn;A1M5A2S1S10G4S0S11S2bS31Vq;R2A2S18G1Vtp1;Vtp;A3A2S12A3F_;Fk;S1G1S1S5Vq;S25G0R1A2M6A2S9G6S6Vq;S8Z1000G5A2A2A2A2M7S0S11S2bS29R2A1Vtp;A2M8S15A3S0S14G3A1M9S1bVrho';R3A2MaS17G3S26G2Z0A2A2A3F_;F_;Fa;S1G1G7S0S11G8S12A3S0G9GaS1bVrho;R3A2A3F_;F_;Fa;G1S3G7A1S0G9S1bVrho';R2A2S1bVrho;R2A2A3F_;Fa;A2A2A2A2A2A2A2").

Lemma SPA_reveal_pages : ltac2:(tb__ "0|5|
S35SdS10S1aSfS24Q40A1M0A1M1SfS2cA1M2S3dS2aS27S34S32R8R5R4S13G2S38R3S39R2R1A2A4A6S0SdSbR8Z1000M3A2Z0A3S5Z643000R9A2S5S6RaS8G3S7R9A1A2A2SaZ2Z40A2A2S10S37R1RbA2S0S11S2eS31RdR2A2S2dR7A1A2S12A3F_;Fk;SdS1S5RdR1A2S9R1S6RdS8G3S7RcA1A2M4A2A2A2S0S11S44S30S2fR8A1A1R2A2S15A3F_;Fz;ScS43R7RaA2G4A2S3eS1cS1cS1fS1eRdR1A2S13SdSdRfS6RfS8G3S7ReA1A2A2A4A2Lo;S1dS36RfA1A1A3S2G1G1S2S1aS1aS1S27S34S32R12R1S18G0R2ReA3S13G2S38RdS39RcRbA2A4A6S33R11R10RfReR1R2A6A2Lrho';A2Ltp1;A2F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fn;Fq;FA;").
Proof.
  intros A q n. induction n as [|n IH]; intros rho tp tr ms md Hsp Hqal Hqlo Hqhi Hlz Hacc Hroom Hdisj.
  - exists [], rho. split; [exact Hsp|]. unfold revealed. cbn [app length Z.of_nat].
    split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros p []|]. split; [lia|].
    split; [intros k Hk; lia|]. split; [intros a Ha; lia|]. split; [intros a Ha; lia|]. intros; reflexivity.
  - rewrite Nat2Z.inj_succ in *.
    destruct (IH rho tp tr ms md Hsp Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia)
                 ltac:(intros z Hz; apply Hacc; lia) ltac:(lia)) as (tp1 & rho1 & Hsp1 & HR).
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia. }
    destruct HR as (Hrw1 & Hrl1 & Htp1 & Hlen1 & Hvis1 & Hz1 & Hk1 & Ho1).
    set (p := pageZ q n).
    assert (Up : bv_unsigned p = q + 4096 * Z.of_nat n) by (unfold p; apply pageZ_u; lia).
    assert (Hobj : forall o, In o (ss_objs (ax_S A)) -> obj_range rho1 o = obj_range rho o).
    { intros o Ho. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }

    assert (PB : forall a : word, q + 4096 * Z.of_nat n <= bv_unsigned a < q + 4096 * Z.of_nat n + 4096 -> page_base a = p).
    { intros a Ha. apply page_base_in_page; [rewrite Up; replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia;
        change page_size with 4096; rewrite Z_mod_plus_full; exact Hqal |].
      unfold in_page. rewrite Up. change page_size with 4096. lia. }
    destruct (page_mem p (tp1 ++ tp)) eqn:Hpm.
    +
      assert (Hptp : page_mem p tp = true).
      { rewrite page_mem_app in Hpm. apply orb_prop in Hpm as [H|H]; [|exact H].
        exfalso. apply (proj1 (page_mem_In _ _)) in H. destruct (Htp1 p H) as ((k & Hk & E) & _).
        apply (f_equal bv_unsigned) in E. rewrite Up in E. rewrite pageZ_u in E by lia. lia. }
      exists tp1, rho1. split; [exact Hsp1|]. unfold revealed.
      split; [exact Hrw1|]. split; [exact Hrl1|].
      split; [intros p' Hp'; destruct (Htp1 p' Hp') as ((k & Hk & E) & Hn); split; [exists k; split; [lia | exact E] | exact Hn]|].
      split; [lia|].
      split.
      { intros k Hk. destruct (Nat.eq_dec k n) as [->|Hne]; [|apply Hvis1; lia]. fold p. exact Hpm. }
      split.
      { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge]; [apply Hz1; [lia | exact Hpa]|].
        exfalso. rewrite (PB a ltac:(lia)) in Hpa. rewrite Hptp in Hpa. discriminate. }
      split.
      { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge]; [apply Hk1; [lia | exact Hpa]|].
        apply Ho1. lia. }
      intros a Ha. apply Ho1. lia.
    +
      pose proof (proj1 (page_mem_false p (tp1 ++ tp)) Hpm) as Hnin.
      destruct (SPA_prepay_page_rm JT rho1 A p (tp1 ++ tp) tr ms md Hsp1) as (Hsp2 & Hz2 & Ho2).
      * rewrite Up. change page_size with 4096. replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia. rewrite Z_mod_plus_full. exact Hqal.
      * apply Hlz. lia.
      * exact Hnin.
      * intros j Hj. rewrite Up. apply Hacc. unfold page_size in Hj. lia.
      * unfold headroom in Hroom |- *. pose proof (paid_app_le md tp1 tp) as PL. unfold page_size in PL |- *. lia.
      * apply Forall_forall. intros o Ho. rewrite (Hobj o Ho). pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
        rewrite Up. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. unfold page_size. lia.
      * intros; exact I.
      * rewrite Up. lia.
      * cbv zeta in Hsp2, Hz2, Ho2.
        set (rho2 := rho_absorb rho1 [zero_page_obj p] (vms md (p :: tp1 ++ tp) ms)) in *.
        assert (Hptp : page_mem p tp = false).
        { rewrite page_mem_app in Hpm. apply orb_false_elim in Hpm as [_ H]. exact H. }
        exists (p :: tp1), rho2. split; [exact Hsp2|]. unfold revealed.
        split; [intros i; unfold rho2; rewrite rw_absorb; apply Hrw1|].
        split; [intros l; unfold rho2; rewrite rl_absorb; apply Hrl1|].
        split.
        { intros p' [<-|Hp'].
          - split; [exists n; split; [lia | reflexivity]|]. intros Hin. apply Hnin. apply in_app_iff. right. exact Hin.
          - destruct (Htp1 p' Hp') as ((k & Hk & E) & Hn). split; [exists k; split; [lia | exact E] | exact Hn]. }
        split; [cbn [length]; lia|].
        split.
        { intros k Hk. cbn [app]. unfold page_mem. cbn [existsb]. fold (page_mem (pageZ q k) (tp1 ++ tp)).
          destruct (Nat.eq_dec k n) as [->|Hne].
          - fold p. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
          - rewrite (Hvis1 k ltac:(lia)). apply orb_true_r. }
        split.
        { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
          - unfold rho2. rewrite Ho2; [apply Hz1; [lia | exact Hpa]|]. rewrite Up. unfold page_size. lia.
          - rewrite <- (Z_to_bv_bv_unsigned 64 a). unfold rho2. apply Hz2. rewrite Up. unfold page_size. lia. }
        split.
        { intros a Ha Hpa. destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
          - unfold rho2. rewrite Ho2; [apply Hk1; [lia | exact Hpa]|]. rewrite Up. unfold page_size. lia.
          - exfalso. rewrite (PB a ltac:(lia)) in Hpa. rewrite Hptp in Hpa. discriminate. }
        intros a Ha. unfold rho2. rewrite Ho2; [apply Ho1; lia|]. rewrite Up. unfold page_size. lia.
Qed.

Lemma revealed_paid : ltac2:(tb__ "0|2|
SdS10S1aSfS24Q40A1M0A1M1S1aG1S2aS33R7R6R5R4R3R2A6S5S42R2S18G0R3R5A3A2S6S42R2R5A2S8Z1000S7R7A1A2A2A2F_;Fmd;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof.
  intros q n rho tp rho' tp1 md (_ & _ & _ & Hlen & _). pose proof (paid_app_le md tp1 tp) as PL. unfold page_size in PL. nia.
Qed.

Lemma revealed_pages : ltac2:(tb__ "0|5|
SdS10S1aSfS24Q40M0A1M1A1M2S1aG2G1S33R7R6R5R4R3R2A6S3bG1R2R3A3S5Z0R9A2S5S6RaS8Z1000M3S7R9A1A2A2SaZ2Z40A2A2S1S5RbS25G0R5A2M4A2S1S5S6G4G3A2S6RbS8G3S7RaA1A2A2A2S1S0SdSbG4G3A2SbRbG3A2A3S3S3bG1R5R8A3A1A2A2A2F_;F_;F_;F_;Fp;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof.
  intros q n rho tp rho' tp1 p (_ & _ & Htp1 & _) Hp H0 Hhi. destruct (Htp1 p Hp) as ((k & Hk & ->) & Hn).
  rewrite pageZ_u by lia. split; [lia|]. split; [lia|]. split; [|exact Hn].
  replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma reveal_bytes : ltac2:(tb__ "0|7|
SfS3cA1SdS10S1aSfS24Q40M0A1M1A1M2S1aG2S33R6R5R4R3R2R1A6S5Z0R7A2S5S6R8S8Z1000M3S7R7A1A2A2SaZ2Z40A2A2G1S1S5RaS25G0R1A2M4A2S9G4S6RaS8G3S7R9A1A2A2A2A2S0S11S2bS29R2A1R8A2S12A3S3S0S14S24Q8A1M5A1M6S1bRaR3A2S16G5A1A3A1F_;F_;Fa;SdS1S5RbR1A2S9R1S6RbS8G3S7RaA1A2A2A2A2S1S0S11S46RdS1bR8A1S26G0R2A2A3S12A3S2G5G5S0G6S45ReS1bR9A1S26G0R3A2A3S17G5R1A2A3Lx;A2A2F_;Fz;F_;F_;F_;F_;Ftp1;Frho';Ftp;Frho;Fn;Fq;Fsegs;").
Proof.
  intros segs q n rho tp rho' tp1 (_ & _ & _ & _ & _ & Hz & Hk & _) H0 Hhi Hdef z Hzr.
  assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; lia).
  assert (E : exists v, rm rho' (Z_to_bv 64 z) = Some v).
  { destruct (page_mem (page_base (Z_to_bv 64 z)) tp) eqn:Hp.
    - rewrite (Hk _ ltac:(rewrite Uz; exact Hzr) Hp).
      destruct (rm rho (Z_to_bv 64 z)) as [v|] eqn:E; [exists v; reflexivity|]. exfalso. exact (Hdef _ ltac:(rewrite Uz; exact Hzr) Hp E).
    - exists (Z_to_bv 8 0). exact (Hz _ ltac:(rewrite Uz; exact Hzr) Hp). }
  destruct E as [v Ev]. unfold wok_of, rd_of. rewrite Ev. split; [reflexivity | exists v; reflexivity].
Qed.

Lemma reveal_zero : ltac2:(tb__ "0|6|
SdS10S1aSfS24Q40M0A1M1A1M2S1aG2G1S33R7R6R5R4R3R2A6S1S5R8S25G0R2A2M3A2S9G3S6R8S8Z1000S7R7A1A2A2A2A2S0S11S2bS29R3A1R6A2S15A3S0S14S24Q8M4A1M5A1S1bR6R4A2S17G5S26G4Z0A2A2A3F_;F_;F_;Fa;Ftp1;Frho';Ftp;Frho;Fn;Fq;").
Proof. intros q n rho tp rho' tp1 a (_ & _ & _ & _ & _ & Hz & _) Ha Hp. exact (Hz a Ha Hp). Qed.

Lemma SPA_hidden_none : ltac2:(tb__ "0|3|
S28S35S1aSfS24Q40A1M0A1SfS2cA1M1S3dS2aG0S27S34R8R7R6R5S13G1S38R4S39R3R2A2A4A6S0S11S2eS29R2A1S2dR3A1A2S12A3S0S11S2bS29R3A1R7A2S15A3S23R9S1dS36RaA1A1R4A3S0S14S24Q8A1M2A1S1bRaR5A2S16G2A1A3F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md a [(Hsm & _) _] Hlz Hpm Hout.
  unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  rewrite <- (Hfr a Hout). rewrite vms_mem. unfold hid. rewrite Hlz, Hpm. reflexivity.
Qed.

Lemma revealed_ext : ltac2:(tb__ "0|8|
S28S35SdS10S1aSfS24Q40A1M0A1M1S1aG1SfS2cA1M2S3dS2aS27S34RbRaR7R6S13G2S38R3S39R2R1A2A4A6S33RaR9R8R7R6R5A6S0SdSbRbZ1000M3A2Z0A3S5Z643000RcA2S5S6RdS8G3S7RcA1A2A2SaZ2Z40A2A2S10S37R1ReA2S0S11S2eS31R10R2A2S2dR8A1A2S12A3F_;Fk;S3eS1cS1cS1fS1eReR1A2S13SdSdR10S6R10S8G3S7RfA1A2A2A4A2Lo;S1dS36R10A1A1A3G0S4S0S14S24Q8A1M4A1M5S1bRdR1A2S1bRfR1A2M6A3S1S0G5G6S16G4A1M7A3S0G5S22S34R1A2G7A3A2A2Fa;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp1;Frho';Ftp;Frho;Fn;Fq;FA;FJ;").
Proof.
  intros J A q n rho tp rho' tp1 tr ms md Hsp HR Hqal Hqlo Hqhi Hlz Hdisj a.
  destruct HR as (_ & _ & _ & _ & _ & Hz & Hk & Ho).
  destruct (Z_le_dec q (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) (q + 4096 * Z.of_nat n))|]; [|left; apply Ho; lia|left; apply Ho; lia].
  destruct (page_mem (page_base a) tp) eqn:Hpm; [left; apply Hk; [lia | exact Hpm]|].
  right. split.
  - destruct (page_base_run q n a Hqal ltac:(lia) Hqhi ltac:(lia)) as (k & Hk' & Ek & _).
    apply (SPA_hidden_none J A rho tp tr ms md a Hsp); [rewrite Ek; apply Hlz; exact Hk' | exact Hpm |].
    apply Forall_forall. intros o Ho'. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho') as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
  - apply image_byte_none_A. lia.
Qed.
End SecReveal.

(* [comment removed for export] *)
Module InvInitF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "nat"; "list"; "bool"; "pair"; "None"; "false"; "fst"; "option"; "prod"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rm"; "rw"; "obj_range"; "sobj"; "ss_objs"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "m_vm_lazy"; "page_in_ranges"; "vm_limit"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.InvInitF"; "band_out"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition band_out (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|1|
S6S7S17S0S0S1dVrho;Vo;A2M0A3S33A2S7S32S14S0S0G0A3A2A2").

Lemma obj_range_ext : ltac2:(tb__ "0|0|
S19S19S1eS1S2S21Q40A1S1cR3R1A2S1cR4R1A2A3Fi;S1S2SfS21Q8A1A1S1aR4R1A2S1aR5R1A2A3Fl;S2S16S0S0A2S1dR4R3A2S1dR5R3A2A3F_;F_;Fo;Frho';Frho;").
Proof.
  intros rho rho' o Hrw Hrl. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite !(eval_ext_rwrl rho rho' _ Hrw Hrl). reflexivity.
Qed.

Lemma pageZ_u : ltac2:(tb__ "0|1|
S0SeS7Z0R2A2SbS8R3S9Z1000M0SaR2A1A2A2SdZ2Z40A2A2S2S0S22Q40S24R4R3A2A2S8R4S9G0SaR3A1A2A2A3F_;F_;Fk;Fq;").
Proof. intros q k H1 H2. unfold pageZ. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Theorem ensure_band_pages : ltac2:(tb__ "0|e|
S38S28SeS0S0S19SfS21Q40M0A1M1A1M2SfS2aA1M3S35S28S30S31S2fR9R7A2RaR5R4S11G3S26R3S27R2R1A2A4A6S2S0ScR7Z1000M4A2Z0A3S7S33R8A2S7S8R9S9G4SaRbA1A2A2S32A2SeS25R1RdA2S2S10S2cS24RcR2A2S2bRfA1A2S18A3F_;Fk;S0S3S7RcR1A2SbR1S8RcS9G4SaReA1A2M5A2A2A2S2S10S36S2eS29R10A1A1R2A2S13A3F_;Fz;S7S8RdG5A2S2dS29RfA1A1A2S34S1eS39RcA1S1fS37R11A1A1A3G1S20G1R1RdA3S3S7R10S22G0R2A2M6A2SbG6S8R10S9G4SaR12A1A2A2A2A2S0S3S7S22G0R4A2M7R1A2SbR1S8G7G4A2A2A2S5S2S15S21Q8A1M8A1M9S1bR12S23G0R2A2MaA2S12G8A1MbA3A1F_;Fz;F_;F_;Fp;S4S19S19S4G2G2S3S30S31S2fR14S8R12S9G4SaR13A1A2A2A2R15R2R1S11G3S26ReS27RdRcA2A4A6S3S1S2G1S1cR3R1A2S1cR11R1A2A3Fi;S3S1S2SfG8A1S1aR3R1A2S1aR11R1A2A3Fl;S3G1S5S3S7R12S22G0R1A2McA2SbGcS8R12S9G4SaR14A1A2A2MdA2A2A1S2G9S1bR4R2A2S1bR12R2A2A3F_;Fa;S3S0S3S7R12R1A2SbR1GdA2A2S5S2G9S1bR4GaA2GbA3A1F_;Fz;S3G1S20G1R1R10A3S20G1R2R3A3F_;Fp;G1S20G1R1R2A3S6S20G1R2R11A3S4SeSeS3S25R1R16A2S2G1R3S24R14R1A2A3A2Lk;A2A2F_;Fp;A2A2A2A2A2A2Ltp';A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fq;FBm;Fn;FMm;FA;").
Proof.
  intros A Mm n. induction n as [|n IH]; intros Bm q rho tp tr ms md Hsp Hqal Hqlo Hqhi Hlz Hacc Hlim Hobj Hdef.
  - exists rho, tp. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|]. split; [intros z Hz; lia|]. split; [intros p Hp; exact Hp | intros p Hp; left; exact Hp].
  - rewrite Nat2Z.inj_succ in *.
    assert (BLO : 0x643000 <= SHADOW_BAND_LO) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia).
    assert (BHI : SHADOW_BAND_HI < 2 ^ 63) by (unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia).
    destruct (IH Bm q rho tp tr ms md Hsp Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia) ltac:(intros z Hz; apply Hacc; lia) ltac:(lia) Hobj
                ltac:(intros p Hp Hr; apply (Hdef p Hp); lia))
      as (rho1 & tp1 & Hsp1 & RW1 & RL1 & OUT1 & DEF1 & INC1 & ORG1).
    set (qn := q + 4096 * Z.of_nat n) in *.
    assert (Upn : bv_unsigned (pageZ q n) = qn) by (apply pageZ_u; lia).
    assert (UZ : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
    { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
    pose proof Hsp1 as [Hsm1 (Htr1 & Hem1 & Hpaid1)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr1, Hem1, Hpaid1.
    pose proof (erase_mat_eq_fields md Mm Hem1) as (Evm & Elz & _).
    destruct (page_mem (pageZ q n) tp1) eqn:Epm.
    +
      apply page_mem_In in Epm.
      exists rho1, tp1. split.
      { split; [exact Hsm1|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact Htr1|]. split; [exact Hem1 | lia]. }
      split; [exact RW1|]. split; [exact RL1|].
      split; [intros a Ha; apply OUT1; lia|].
      split.
      { intros z Hz. destruct (Z_lt_dec z qn) as [Hlt|Hge]; [apply DEF1; lia|].
        destruct (ORG1 _ Epm) as [Hin|(k & Hk & Ek)].
        - rewrite (OUT1 (Z_to_bv 64 z)) by (rewrite UZ by lia; lia). apply (Hdef _ Hin); rewrite ?Upn; lia.
        - exfalso. apply (f_equal bv_unsigned) in Ek. rewrite Upn, (pageZ_u q k) in Ek by lia. unfold qn in Ek. lia. }
      split; [exact INC1|].
      intros p Hp. destruct (ORG1 p Hp) as [H|(k & Hk & Ek)]; [left; exact H | right; exists k; split; [lia | exact Ek]].
    +
      apply page_mem_false in Epm.
      set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) =>
                   KxA Mm (Bm + 4096 * Z.succ (Z.of_nat n)) r (pageZ qn 0 :: tp1) tr0 md0).
      assert (HJ' : forall r r' t t', J' r t tr md -> J' r' t' tr md) by (intros r r' t t' X; exact X).
      assert (EP0 : pageZ qn 0 = pageZ q n) by (unfold pageZ, qn; f_equal; lia).
      assert (PB : paid md (pageZ qn 0 :: tp1) <= Bm + 4096 * Z.succ (Z.of_nat n)).
      { pose proof (paid_cons_le md (pageZ qn 0) tp1) as X. unfold page_size in X. lia. }
      assert (Hsp0 : SPA segsA J' A rho1 tp1 (tr, mkCfg ms md)).
      { split; [exact Hsm1|]. subst J'. cbv beta. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact Htr1|]. split; [exact Hem1 | exact PB]. }
      destruct (SPA_prepay_pages_rm J' A qn 1 rho1 tp1 tr ms md Hsp0 HJ') as (rho2 & Hsp2 & RW2 & RL2 & Z2 & O2).
      * unfold qn. rewrite Z.add_mod, Hqal, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      * lia.
      * change (Z.of_nat 1) with 1. lia.
      * intros k Hk. replace k with 0%nat by lia. rewrite EP0, Elz. apply Hlz. lia.
      * intros k Hk. replace k with 0%nat by lia. rewrite EP0. exact Epm.
      * intros z Hz. change (Z.of_nat 1) with 1 in Hz. rewrite Evm. apply Hacc. lia.
      * unfold headroom. rewrite Evm. change (Z.of_nat 1) with 1. unfold page_size. lia.
      * apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hobj o Ho) as D. unfold band_out in D.
        rewrite (obj_range_ext rho rho1 o RW1 RL1). unfold ranges_disjoint. cbn [fst snd]. change (Z.of_nat 1) with 1. lia.
      * change (Z.of_nat 1) with 1 in *. cbn [pages_rev app] in Hsp2. rewrite Z.mul_1_r in *.
        exists rho2, (pageZ qn 0 :: tp1). split; [exact Hsp2|].
        split; [intros i; rewrite RW2; apply RW1|]. split; [intros l; rewrite RL2; apply RL1|].
        split; [intros a Ha; rewrite O2 by lia; apply OUT1; lia|].
        split.
        { intros z Hz. destruct (Z_lt_dec z qn) as [Hlt|Hge].
          - rewrite O2 by (rewrite UZ by lia; lia). apply DEF1. lia.
          - rewrite Z2 by lia. discriminate. }
        split; [intros p Hp; right; apply INC1; exact Hp|].
        intros p [<-|Hp]; [right; exists n; split; [lia | exact EP0]|].
        destruct (ORG1 p Hp) as [H|(k & Hk & Ek)]; [left; exact H | right; exists k; split; [lia | exact Ek]].
Qed.
End InvInitF.

(* [comment removed for export] *)
Module SegD_refl.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "list"; "prod"; "cons"; "option"; "nil"; "Some"; "fst"; "length"; "snd"; "app"; "nat"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sv_eqb"; "cell"; "sprop"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "RsEcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl"; "leqb"; "cellb"; "sobjb"; "svp_eqb"; "andc"; "cut1"; "cut1e"; "cut2"; "is_ecall"; "sd_eqb"; "skel_eqb"; "tailb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "leaf"; "@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "@Stdlib.Bool.Bool"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_states.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma land_inv : ltac2:(tb__ "0|0|
S0S0SfS0S0S0L_;R2R1S1X0x2S2A3S10SfS0R3S2A3SfS0R2S2A3A2F_;Fb;Fa;").
Proof. intros [|] b; cbn; intros H; [split; [reflexivity|exact H] | discriminate]. Qed.

Definition andc (a b : bool) : bool := if a then b else false.
Lemma andc_inv : ltac2:(tb__ "0|0|
S0S0SfS0S29R2R1A2S2A3S10SfS0R3S2A3SfS0R2S2A3A2F_;Fb;Fa;").
Proof. intros [|] b; cbn; intros H; [split; [reflexivity|exact H] | discriminate]. Qed.

Definition cut1 (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1S1G0S0Ll1;R3S2S11G0S1Ll3;Ll2;X3x2S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut1_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2aR1A1S2A3SfG0R2S5S11S13S31U0R2A2S23A2S7S11A1A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition cut2 (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1S1G0S0Ll1;R3S1S11G0S11S0Ll2;R2S12S22S22S0Lla_reason0;R1S1G0S0Ll3;R3S2S11G0S1Ll5;Ll4;X3x2S1S1S1S1S1X22x7Lla_reason0;Lla_state0;X11x1Ll3;Ll2;X3x2S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut2_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2cR1A1S2A3SfG0R2S5S11S13S31U0R2A2S23A2S5S11S13S31U1R2A2S23A2S7S11A1A3A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l as [|[S' r'] l]; [cbn; discriminate|].
  destruct r'; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition cut1e (l : list leafA) : bool := ltac2:(tb__ "0|1|
S3S11A1M0S0Ll;Vl;S1S11G0S11S0Ll0;R2S12S22S22S0Lla_reason;R1G0S0Ll1;R3S2S11G0S1Ll3;Ll2;X3x2S1S1S1S1S1S1X22x7Lla_reason;Lla_state;X11x1Ll1;Ll0;X3x2").
Lemma cut1e_sound : ltac2:(tb__ "0|1|
S3S11A1M0SfS0S2bR1A1S2A3SfG0R2S5S11S13S31U0R2A2S24A2S7S11A1A3A3F_;Fl;").
Proof.
  intros [|[S r] l]; [cbn; discriminate|]. destruct r; try (cbn; discriminate). destruct l; cbn; [reflexivity | discriminate].
Qed.

Definition is_ecall (o : option instr) : bool := match o with Some Ecall => true | _ => false end.
Lemma is_ecall_sound : ltac2:(tb__ "0|1|
S6S34A1M0SfS0S2dR1A1S2A3SfG0R2S8S34S35A2A3F_;Fo;").
Proof. intros [i|]; [|discriminate]. destruct i; cbn; intros; try discriminate. reflexivity. Qed.

Definition isnil {A : Type} (l : list A) : bool := match l with [] => true | _ => false end.
Lemma isnil_sound : forall {A : Type} (l : list A), isnil l = true -> l = [].
Proof. intros A [|x l]; cbn; [reflexivity | discriminate]. Qed.

Fixpoint leqb {A : Type} (f : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | x :: l, y :: l' => f x y &&& leqb f l l'
  | _, _ => false
  end.
Lemma leqb_sound : forall {A : Type} (f : A -> A -> bool), (forall x y, f x y = true -> x = y) ->
  forall l l', leqb f l l' = true -> l = l'.
Proof.
  intros A f Hf l. induction l as [|x l IH]; intros [|y l']; cbn; intros H; try discriminate; [reflexivity|].
  apply land_inv in H as [H1 H2]. rewrite (Hf _ _ H1), (IH _ H2). reflexivity.
Qed.

Definition skel_eqb (a b : sv * sv * sv) : bool := ltac2:(tb__ "0|3|
S4S4S14S14A2M0S14A2M1S0La;Va;G0S14G0S0Lp;R2S14S14G1S0Lb;Vb;G0S14G0S0Lp0;R2S14S14S0S0L_;M2S16R6R2A2G2S16R5R1A2S16R7R3A2S1X0x2S1X0x2Lb2;Lb1;X4x1Lb3;Lp0;X4x1La2;La1;X4x1La3;Lp;X4x1").
Lemma skel_eqb_sound : ltac2:(tb__ "0|1|
S4S4S14S14A2S14A2M0G0SfS0S2fR2R1A2S2A3SfG0R3R2A3F_;Fb;Fa;").
Proof.
  intros [[a1 a2] a3] [[b1 b2] b3] H. cbn in H. apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H3].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2), (sv_eqb_sound _ _ H3). reflexivity.
Qed.

Definition svp_eqb (a b : sv * sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S16S9S14S14Va;A3S9S14S14Vb;A3A2S16SbS14S14Va;A3SbS14S14Vb;A3A2S1X0x2").
Lemma svp_eqb_sound : ltac2:(tb__ "0|1|
S4S14S14A2M0G0SfS0S28R2R1A2S2A3SfG0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold svp_eqb in H. cbn [fst snd] in H. apply land_inv in H as [H1 H2].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2). reflexivity.
Qed.

Definition sd_eqb (o : option (list (sv * sv) * list sprop)) (l : list (sv * sv)) (F : list sprop) : bool := ltac2:(tb__ "0|4|
S6S4S3S4S14S14A2M0A1M1S3S18A1M2A2M3A1S0Lo;Vo;G3G3S0Lp;R1G1G2S0S0L_;S25G0S28R2Vl;A4S25S18S21R1VF;A4S1X0x2LF';Ll';X4x1Lp;S1X6x2").
Lemma sd_eqb_sound : ltac2:(tb__ "0|4|
S6S4S3S4S14S14A2A1M0S3S18A1M1A2M2A1M3G0G1SfS0S2eR3R2R1A3S2A3SfG3R4S8G2SeG0G1R3R2A4A2A3F_;FF;Fl;Fo;").
Proof.
  intros [[l' F']|] l F H; cbn [sd_eqb] in H; [|discriminate]. apply land_inv in H as [H1 H2].
  rewrite (leqb_sound _ svp_eqb_sound _ _ H1), (leqb_sound _ sprop_eqb_sound _ _ H2). reflexivity.
Qed.

Definition cellb (c c' : cell) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S16S19Vc;A1S19Vc';A1A2G0S3bS1bVc;A1S1bVc';A1A2S16S1aVc;A1S1aVc';A1A2S1X0x2S1X0x2").
Lemma cellb_sound : ltac2:(tb__ "0|0|
S17S17SfS0S26R2R1A2S2A3SfS17R3R2A3F_;Fc';Fc;").
Proof.
  intros [o w v] [o' w' v'] H. unfold cellb in H. cbn [c_off c_width c_val] in H.
  apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H3].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H3), (proj1 (Z.eqb_eq _ _) H2). reflexivity.
Qed.

Definition sobjb (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S16S1cVo;A1S1cVo';A1A2G0S16S20Vo;A1S20Vo';A1A2G0S16S1fVo;A1S1fVo';A1A2G0S25S17S26S1dVo;A1S1dVo';A1A4S38S1eVo;A1S1eVo';A1A2S1X0x2S1X0x2S1X0x2S1X0x2").
Lemma sobjb_sound : ltac2:(tb__ "0|0|
S15S15SfS0S27R2R1A2S2A3SfS15R3R2A3F_;Fo';Fo;").
Proof.
  intros [b lo hi cs d] [b' lo' hi' cs' d'] H. unfold sobjb in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  apply land_inv in H as [H1 H]. apply land_inv in H as [H2 H]. apply land_inv in H as [H3 H]. apply land_inv in H as [H4 H5].
  rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2), (sv_eqb_sound _ _ H3), (leqb_sound _ cellb_sound _ _ H4), (odefault_eqb_sound _ _ H5).
  reflexivity.
Qed.

Definition tailb (objs : list sobj) (k : nat) (L : list sobj) : bool := ltac2:(tb__ "0|0|
S25S15S27S37S15S33SaS15Vobjs;A2Vk;A2Vobjs;A3VL;A4").
Lemma tailb_sound : ltac2:(tb__ "0|1|
S3S15A1M0SdG0SfS0S30R3R2R1A3S2A3SfG0R4ScS15S36S15S33SaS15R4A2R3A2R4A3R2A3A3F_;FL;Fk;Fobjs;").
Proof.
  intros objs k L H. unfold tailb in H. rewrite <- (leqb_sound _ sobjb_sound _ _ H). symmetry. apply firstn_skipn.
Qed.

Lemma poseqb_sound : ltac2:(tb__ "0|0|
S32S32SfS0S3aR2R1A2S2A3SfS32R3R2A3F_;Fb;Fa;").
Proof. intros a b. apply Pos.eqb_eq. Qed.

Lemma eqb_false_sound : ltac2:(tb__ "0|0|
S0SfS0S39R1S1A2S2A3SfS0R2S1A3F_;Fb;").
Proof. intros [|]; cbn; [discriminate | reflexivity]. Qed.

Ltac splitC H :=
  lazymatch type of H with
  | andc _ _ = true => let C := fresh "C" in apply andc_inv in H as [C H]; splitC C; splitC H
  | _ => idtac
  end.

Ltac convC :=
  repeat match goal with
  | H : cut1 _ = true |- _ => apply cut1_sound in H
  | H : cut2 _ = true |- _ => apply cut2_sound in H
  | H : isnil _ = true |- _ => apply isnil_sound in H
  | H : leqb skel_eqb _ _ = true |- _ => apply (leqb_sound _ skel_eqb_sound) in H
  | H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H
  | H : sd_eqb _ _ _ = true |- _ => apply sd_eqb_sound in H
  | H : Pos.eqb _ _ = true |- _ => apply poseqb_sound in H
  | H : tailb _ _ _ = true |- _ => apply tailb_sound in H
  | H : Bool.eqb _ false = true |- _ => apply eqb_false_sound in H
  | H : cut1e _ = true |- _ => apply cut1e_sound in H
  | H : is_ecall _ = true |- _ => apply is_ecall_sound in H
  end.

Ltac dispC :=
  lazymatch goal with
  | |- runA ?f ?c _ = _ =>
      match goal with H : runA ?f' ?c' _ = _ |- _ => constr_eq f f'; constr_eq c c'; exact H end
  | |- entailsA ?a ?b _ = true =>
      match goal with H : entailsA ?a' ?b' _ = true |- _ => constr_eq a a'; constr_eq b b'; exact H end
  | |- ?g => match goal with H : ?t |- _ => constr_eq t g; exact H end
  end.
End SegD_refl.

(* [comment removed for export] *)
Module SegQ_wf3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "qb_addr"; "qb_items"; "@Corelib.Init.Datatypes"; "list"; "app"; "prod"; "snd"; "bool"; "false"; "fst"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "qitems"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "is_primary"; "kQuarantineBatchCount"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "set_q"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv SegQ_defs SegQ_wf2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition KQ_secband (K : AA -> jpredA) : Prop := ltac2:(tb__ "0|2|
S2S16S5S18Q40A1A1S5S15A1S14VK;R5R4R3R2R1A5S7S0S0A2M0S21G0R1SeSdR7A1A1A3S19S9S1dS8S0S0R2A3A1SaA3S1aSfSbS0S0R3A3M1S1cA2SfS1bS11G1S1fS8S0S0R3A3A1A2A2A2F_;F_;Fit;F_;Fmd;Ftr;Ftp;Frho;FA;").

Definition KQ_regroup (K : AA -> jpredA) : Prop := ltac2:(tb__ "0|2|
S2S5S1A1M0G0S16S5S18Q40A1A1S5S15A1S14S17S0S12S1S0S3SdR7A1A4S12S1S0S3S6S1R6R5A3A4A3S17S7S0S0A2M1SeSdR8A1A1SeS6S1R7R6A3A1A3S13S1S1SfS10ScG1S4R1A1A2A1S1eA2Lb;S6S1R8R7A3A3VK;RaR7R6R5R4A5VK;S20RbRaR9A3R8R7R6R5A5F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fg;Ft;FA;").
End SegQ_wf3.

(* [comment removed for export] *)
Module CertMallocM0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SVar"; "SLit"; "sprop"; "FcsrFrm0"; "mkSS"; "SAlu"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "O_T3168"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0"; "E_m1"; "P0_m"; "RT_m0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "O_T0"; "O_T40"; "O_cfa"; "O_ctx8"; "O_ctx98"; "O_mcs"; "O_pga"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "Wcan"; "malloc_depth"; "mkA"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "AE_A"; "ae_malloc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0.M0"; "M1_regs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition RT_m0 : list sobj := ltac2:(tb__ "0|0|
S0S8S2bS0S8S2cS0S8S2fS0S8S30S0S8S31S0S8S2dS0S8S2eS0S8S26S0S8S27S0S8S23S0S8S24S0S8S1eS0S8S25S0S8S29S0S8S2aS0S8S28S3S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Section M0.
Variable W : list ulink.
Variable st : ustop.
Definition P0_m : axst := ltac2:(tb__ "0|1|
S35SeS3bS3aA1S19S1bS0S5S1S9A2M0S2S1S9U4SbS22A1A4S3G0A1A3A2S18SdS6S9A1S4S8S0S8S37S4S8S39VW;A1S32A3A3S21A3S4ScS4ScS38VW;Vst;A2S36S34A1A3S1cA3S1dS7A9S3S5S9S9A2A1A2").

Definition M1_regs : list sv := ltac2:(tb__ "0|4|
S19S1aS16A1S0S5S1S9A2M0S2S1S9U1SbZ5e4f8A1A4S0G0S2S1S9U2SfS3cSaPaA1M1SbN850A1A3M2A4S0G0S2S1S9U4SbS22A1A4S0G0S2S1S9U8G1A4S0G0S2S1S9U9SaPcA1M3A4S0G0S2S1S9UaG3A4S0G0S2S1S9UbG2A4S0G0S2S1S9U12SaPb2A1A4S0G0S2S1S9U13SaPb3A1A4S0G0S2S1S9U14SaPb4A1A4S0G0S2S1S9U15SaPb5A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A2").
Definition E_m1 : axst := ltac2:(tb__ "0|0|
S35SeZ5e504S3dS18SdS6S9A1S4S8S0S8S37S4S8S39VW;A1S32A3A3S21A3S4ScS4ScS38VW;Vst;A2S36S34A1A3S1cA3S1dS7A9S3S5S9S9A2A1A2").
End M0.

Definition m0_cert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|2|
S13S17Ubb8S0S10Z5e504S3S10A1A3S16S0S15S20S33Vn;A1M0Vst;A2S3S15A1M1A3S0S15S1fG0Vst;A2G1A3A6").
Definition m0_ecert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|4|
S14S17Ubb8S0S10Z5e504S3S10A1A3S16S0S11S12S20S33Vn;A1M0Vst;A2Z1SbZ0M1A1M2A3S3S11A1M3A3S0S11S12S1fG0Vst;A2G1G2A3G3A3A6").

Lemma m0_cert_0 : m0_cert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma m0_cert_1 : m0_cert 1 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma m0_ecert_0 : m0_ecert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertMallocM0.

(* [comment removed for export] *)
Module GlueMZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "div"; "sub"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "eval"; "ss_objs"; "sstate"; "valuation"; "DZero"; "cell"; "mkObj"; "rm"; "smatch"; "covered"; "mkSS"; "obj_range"; "ranges_disjoint"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "ss_next"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "nil"; "true"; "Some"; "app"; "option"; "cons"; "nat"; "fst"; "snd"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "lit_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_zero_rd : ltac2:(tb__ "0|9|
S14S13S27S3cA1M0S3aS3bSfS0S0S1S19Vsegs;R9R8S28G0S37R7S38R6R5A2A4A4S1bS22R9A1S23R9A1S20R9A1S1fR9A1S24R9A1S2eSeS12R9A1S30SeS17R5S10R4A1S10R3A1S2bS16A1S15A5S2bSeA1A3A3S1eR9A1R2S21R9A1A9S13ScS2aS25R1A1S2cA3S35Q40M1S11RcR7A2A2S0S3S6S5Z2M2Z3fA2M3A1R7A2SbS3R8R7A2S4R7G3A2A2S4S8R8R9A2G3A2S3Z0M4S2R4RaA2A2S3S2R5RaA2S5G2Z40A2A2S39SeSeS1dS1cR13R1A2S28S0S0S2R7RdA2S2R7RcA2A4A2Lo';S12R11A1A3S0SbS3S2R8ReA2R1A2S4R1S2R8RdA2A2A2SbScS2aS43Vsegs;S18R15A1M5S34G1R2A2M6A3S2cA3ScS2fS36Q8M7A1M8A1S42Vsegs;G5G6A3S2dG8S34G7G4A2A2A3A2F_;Fa;S19Vsegs;R14RaS28G0S37R12S38R11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
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
  assert (MEM : forall a, b + lo <= a < b + hi -> ms_mem ms (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros a Ha. exact (Hfr _ (Hout a Ha)). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. destruct (Hbytes (b + off) ltac:(lia)) as [Hw Hb].
      unfold wview. rewrite (MEM (b + off)) by lia.
      pose proof (wview_of_views segs (rm rho) (Z_to_bv 64 (b + off)) Hw (ex_intro _ _ Hb)) as X. unfold wview in X. exact X. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia.
    destruct (Hbytes (b + off) ltac:(lia)) as [_ Hb]. unfold rd_of in Hb.
    destruct (rm rho (Z_to_bv 64 (b + off))) as [x|]; [exact Hb|]. rewrite <- Hb. first [apply Hrom | symmetry; apply Hrom].
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_zero_rd : ltac2:(tb__ "0|e|
S46S14S41S27S36Q40M0A1A1S27S3cA1M1S3aS3bSfS0S0S1S45Vsegs;RbR9RaR8S28G1S37R7S38R6R5A2A4A6S1bS22S3dRaA1M2A1S23G2A1S20G2A1S1fG2A1S24G2A1S2eSeS12G2A1S30SeS17R5S10R4A1S10R3A1S2bS16A1S15A5S2bSeA1A3A3S1eG2A1R2S21G2A1A9S13ScS2aS25R1A1S2cA3S49S26S3dRcA1A1R4A2S35G0S11ReR8A2A2S0S3S6S5Z2M3Z3fA2M4A1R8A2SbS3R9R8A2S4R8G4A2A2S4S8R9RaA2G4A2S3Z0M5S2R4RbA2A2S3S2R5RbA2S5G3Z40A2A2S39SeSeS1dS1cR15R1A2S28S0S0S2R7ReA2S2R7RdA2A4A2Lo';S12S3dR13A1A1A3S0SbS3S2R8RfA2R1A2S4R1S2R8ReA2A2A2SbScS2aS43Vsegs;S18R17A1M6S34G0R2A2M7A3S2cA3ScS2fS36Q8M8A1M9A1S42Vsegs;G6G7A3S2dG9S34G8G5A2A2A3A2F_;Fa;S29SfSfA2MaS0S0S47GaR3S3eR18A1A3SbS3S35G0S11R1aS32SfSfR4A3A2A2MbR3A2S4R3S2GbS35G0S11R1aS33SfSfR4A3A2A2A2A2A2SbS3G5R3A2S4R3Z8McA2A2SdSbS3S2ReR15A2S2S9S7S2S35G0S11R1cS3fR1bA1A2A2S7R5GcA2A2GcA2GcA2R4A2MdA2S4GdS2ReR14A2A2A2A1F_;F_;F_;Fj;Fy;Frr;S45Vsegs;R18S40R16RcA2R17R15S28G1S37R14S38R13R12A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp tr ms md base lo hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes Hxs.
  split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_zero_rd rho (ax_S A) tr (vms md tp ms) (vmd md) base lo hi nx Hsm Hwf' Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes).
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

Lemma absorb_zero_dflt : ltac2:(tb__ "0|6|
S14S13S27S3cA1M0S3aS3bS27SeA1M1G1SfS0S0S27S16A1S19Vsegs;RbRaS28G0S37R9S38R8R7A2A4A4ScG1S12RbA1S2eSeR7R6A3A3S47SeS17R6S10R5A1S10R4A1R3S15A5R7A3S35Q40M2S11ReR7A2A2S0S3S6S5Z2Z3fA2M3A1R7A2S3R8R7A2S4R8G3A2S0SbS3RbR1A2S4R1RaA2A2SdS1aR14RaR2A3A1ScS2fS36Q8M4A1M5A1S42Vsegs;S18S48R15RfR12A3A1S34G2S2R7R3A2A2A3S2dG5S34G4Z0A2A2A3F_;F_;Foff;F_;F_;F_;Tb;F_;F_;F_;Fcs;Fhi;Flo;Fbase;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R base lo hi cs Hsm Ho Hin b Hs1 Hs3 Hs2 off Hoff Hnc.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ Hin) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh. fold b in Hoh.
  rewrite !soff_lit_small in Hoh by lia.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : in_ranges rho R (Z_to_bv 64 (b + off))).
  { exists (mkObj base (SLit lo) (SLit hi) cs DZero). split; [exact Hin|].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. fold b.
    rewrite !soff_lit_small by lia. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  rewrite (rd_of_absorb_in segs rho R ms _ Hrom RNG).
  specialize (Hdf off Hoff Hnc). unfold dflt_holds in Hdf. exact Hdf.
Qed.

Lemma not_covered_lits : ltac2:(tb__ "0|3|
S14S27S29S29S0S31A2M0SfA2M1A1S0S39G1G1G1OLc;R1G0SfG0OLp;R2S0S31SbSbS3S6S5Z2Z3eA2M2A1R2A2S4R2G2A2A2SdSbS3R2R6A2S4R6S2R2SaR1A1A2A2A2A1A2Lk;Lo;X29x1Ls;Lp;X29x1Lc;R2A3SdS1aR4S44R3A1R2A3A1F_;Foff;Fcs;Frho;").
Proof.
  intros rho cs off HF Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hic).
  induction cs as [|[[o k] v] t IH]; [destruct Hc|].
  cbn [lit_cells] in Hc. destruct Hc as [<-|Hc].
  - apply Forall_inv in HF. destruct HF as [Ho Hn]. unfold in_cell in Hic. cbn [c_off c_width] in Hic.
    rewrite soff_lit_small in Hic by lia. apply Hn. lia.
  - apply IH; [apply Forall_inv_tail in HF; exact HF | exact Hc].
Qed.
End WithSegs.
End GlueMZ.

