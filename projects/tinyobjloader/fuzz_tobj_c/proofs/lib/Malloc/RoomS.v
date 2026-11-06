(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "sub"; "modulo"; "mul"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_reserved"; "vm_maps"; "vm_limit"; "m_vm_materialized"; "vm_init_sp"; "alloc_top"; "with_vmmaps"; "VmMaps"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "WTOP"; "ROOMC"; "WSPAN"; "lcount"; "ledger"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok_none"; "mmap_n"; "mmap_place_ok"; "mmap_none_vm"; "mmap_rw_vm"; "munmap_model"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "false"; "true"; "app"; "length"; "pair"; "nil"; "snd"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "PG"; "zpair"; "total"; "disjoint"; "@Stdlib.Lists.List"; "In"; "filter"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "vm_gap_available"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_pot"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundA SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout FreeGap ContractDrv VmRoom GapCount.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ROOMC : Z := 2 ^ 29.
Definition WTOP : Z := 0x600000000000.
Definition WSPAN : Z := 2 ^ 46.

Definition ledger (md : Model) : list (word * word) := ltac2:(tb__ "0|2|
S2cS28S25Q40A1M0G0A2SeScVmd;A1M1A1SfG1A1A3").
Definition lcount (md : Model) : Z := Z.of_nat (length (ledger md)).

Definition vm_roomS (md : Model) (X : Z) : Prop := ltac2:(tb__ "0|2|
S9S1Z0VX;A2S9S1S3S7S32S1cVmd;A1A2VX;A2S1aA2S9S1S3S40Vmd;A1VX;A2S10ScVmd;A1M0A1M1A2S9S1G1S4Z2Z28A2A2S1Z7fff7f800000S13G0A1A2A2A2A2A2").

Lemma vm_roomS_nonneg : ltac2:(tb__ "0|0|
SdS0S18R2R1A2S1Z0R2A2F_;FX;Fmd;").
Proof. intros md X (H & _). exact H. Qed.

Lemma vm_roomS_mono : ltac2:(tb__ "0|0|
SdS0S0S9S1Z0R1A2S1R1R2A2A2S18R4R3A2S18R5R3A2F_;F_;FX';FX;Fmd;").
Proof. intros md X X' HX (H0 & HC & HP & HL & HT). unfold vm_roomS. repeat split; try lia. Qed.

Lemma vm_roomS_frame : ltac2:(tb__ "0|0|
SdSdS0S8S15ScR2A1ScR3A1A3S8S29S25Q40A1A1S11R3A1S11R4A1A3S18R5R3A2S18R5R4A2F_;F_;F_;FX;Fmd';Fmd;").
Proof.
  intros md md' X Hv Hm H. unfold vm_roomS, lcount, ledger, vm_pot in *. rewrite Hv, Hm. exact H.
Qed.

Lemma vm_roomS_vmmaps_le : ltac2:(tb__ "0|5|
SdSdS0S8S29S28S25Q40A1M0G0A2A1M1SeScR2A1A1SeScR3A1M2A1A3S8G1SfG2A1SfScR4A1M3A1A3S8S0S10G3A1S10ScR5A1M4A1A3S8G0S12G4A1S12ScR6A1A1A3S3dS2dG0S11R6A1A2S2dG0S11R7A1A2A2S18R8R6A2S18R8R7A2F_;F_;F_;F_;F_;F_;FX;Fmd';Fmd;").
Proof.
  intros md md' X Hr Hm Hl Hsp Hlen (H0 & HC & HP & HL & HT). unfold vm_roomS, lcount, ledger, vm_pot in *.
  rewrite Hr, Hm, Hl. split; [exact H0|]. split; [exact HC|]. split; [|split; [exact HL| unfold alloc_top in *; rewrite Hsp; exact HT]].
  apply Nat2Z.inj_le in Hlen. unfold PGSZ in *. set (T := total _) in *. nia.
Qed.

Lemma total_map_zpair_nonneg : ltac2:(tb__ "0|3|
S29S28S25Q40A1M0G0A2M1A1S28S0S0A2M2S36G2R1S38G1G2S33R2A4A3S1Z0S30S0S0R2A3A2F_;Fe;Fl;").
Proof. intros l e He. apply in_map_iff in He as (e' & <- & _). unfold zpair. cbn [snd]. pose proof (urange (snd e')). lia. Qed.

Lemma total_zpair_ge0 : ltac2:(tb__ "0|2|
S29S28S25Q40A1M0G0A2M1A1S1Z0S34S38G1S28S0S0A2S33R1A4A1A2Fl;").
Proof.
  induction l as [|e t IH]; [unfold total; cbn; lia|]. cbn [map]. change (total (zpair e :: map zpair t)) with (snd (zpair e) + total (map zpair t)).
  unfold zpair at 1. cbn [snd]. pose proof (urange (snd e)). lia.
Qed.

Theorem vm_roomS_gap : ltac2:(tb__ "0|3|
SdS0S0S18R3R2A2S9S1S32R2A2S1R2R3A2A2S8S0S6R3S32A2Z0M0A3SbS0S0S9S1S5S19S1bA2R1A2S9S1S3R1R5A2S19A2S9S8S0S6R1S32A2G0A3S28S25Q40A1M1G1A2M2S36G2R1S1dR8A1A3S35S2eS0S0R3R7A4S33R2A1A2F_;Fe;A2A2A2La;A2F_;F_;F_;FnZ;FX;Fmd;").
Proof.
  intros md X nZ (H0 & HC & HP & HL & HT) HnX Hal.
  assert (Hn : 0 < nZ) by (unfold PG in HnX; lia).
  set (l := map zpair (ledger md)).
  assert (Hlen : Z.of_nat (length l) = lcount md) by (subst l; unfold lcount; rewrite length_map; reflexivity).
  assert (Htot : total l <= 2 ^ 40).
  { subst l. unfold vm_pot, ledger in *. pose proof (Zle_0_nat (length (m_vm_materialized md))). unfold PGSZ in HP. nia. }
  assert (HC0 : 0 <= lcount md) by (unfold lcount; lia).
  set (M := WSPAN / nZ).
  assert (HM : 0 <= M) by (subst M; apply Z.div_pos; unfold WSPAN; lia).
  assert (HK : total l / nZ + 2 * Z.of_nat (length l) < M).
  { rewrite Hlen. subst M.

    assert (HcX : nZ * lcount md <= 2 ^ 44).
    { unfold ROOMC, PG in *. pose proof (Zle_0_nat (length (ledger md))) as C0. unfold lcount in *.
      set (c := Z.of_nat (length (ledger md))) in *.
      assert (nZ <= 2 ^ 29 - 4096 * c) by lia.
      transitivity ((2 ^ 29 - 4096 * c) * c); [apply Z.mul_le_mono_nonneg_r; lia|].

      replace ((2 ^ 29 - 4096 * c) * c) with (2 ^ 44 - 4096 * ((c - 2 ^ 16) * (c - 2 ^ 16))) by ring.
      pose proof (Z.square_nonneg (c - 2 ^ 16)). lia. }

    assert (E : (2 ^ 40 + 2 * nZ * lcount md + nZ) / nZ = (2 ^ 40) / nZ + 2 * lcount md + 1).
    { replace (2 ^ 40 + 2 * nZ * lcount md + nZ) with ((2 * lcount md + 1) * nZ + 2 ^ 40) by ring.
      rewrite (Z.div_add_l (2 * lcount md + 1) nZ (2 ^ 40)) by lia. lia. }
    assert (H1 : total l / nZ + 2 * lcount md < (2 ^ 40 + 2 * nZ * lcount md + nZ) / nZ).
    { rewrite E. pose proof (Z.div_le_mono (total l) (2 ^ 40) nZ Hn Htot). lia. }
    assert (H2 : (2 ^ 40 + 2 * nZ * lcount md + nZ) / nZ <= WSPAN / nZ).
    { apply Z.div_le_mono; [exact Hn|]. unfold WSPAN, ROOMC, PG in *. lia. }
    lia. }
  destruct (gap_by_count_base WTOP nZ Hn l M PG (total_map_zpair_nonneg (ledger md)) HM HK ltac:(unfold PG; lia) eq_refl Hal)
    as (a & Hlo & Hhi & Hpg & Hdisj).
  exists a. split; [|split; [exact Hhi|split; [exact Hpg|]]].
  - subst M. pose proof (Z.mul_div_le WSPAN nZ Hn) as D. nia.
  - intros e He. apply Hdisj. subst l. apply in_map. exact He.
Qed.

Lemma WTOP_facts : ltac2:(tb__ "0|1|
S9S8S0S5S19S1bA2S4Z2M0Z2dA2A3S9S1S3S19S4G0Z1fA2A2Z7fff7f800000A2S8S0S6S19S32A2Z0A3A2A2").
Proof. unfold WTOP, WSPAN, PG. repeat split; reflexivity || (cbn; lia). Qed.

Theorem vm_roomS_place : ltac2:(tb__ "0|9|
SdS0S25Q40M0A1M1S18R3R2A2S2Z0M2S26G0R2A2A2S1S1eR3A1R4A2SbG1G1S9S8S0S6S26G0R1A2M3S16A2G2A3S9S2G2G3A2S9S1S4Z2Z2dA2G3A2S9S1S3G3S1eR5A1M4A2S19A2S9S8S0S26G0S20R5A1M5A2G4A3S9S8S27S17S2cS28G1G1A2M6SeScR7A1M7A1SfG7A1A3R1G5A3S2bA3S9G6S36G6R1S2cG6SeScR8A1M8A1SfG8A1A3A3S35S2eS0S0S26G0R3A2S1eR7A1A4S33R2A1A2F_;Fe;S9G1G1S8S27S39R1A1S2aA3S21R3R2RaR8R4A5F_;Fflags;Fhint;G1S1fR1R8R6R2A4Fhint;A2A2A2A2A2A2A2A2La;A2F_;F_;F_;Flen;FX;Fmd;").
Proof.
  intros md X len HR Hlen HX. pose proof HR as (H0 & HC & HP & HL & HT).
  pose proof (mmap_nZ_page_len len Hlen) as [Hnpos Hnal]. unfold PG in Hnal.
  pose proof WTOP_facts as (W1 & W2 & W3).
  assert (HPG : PG <= mmap_nZ len <= X).
  { split; [|exact HX]. unfold PG. unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange len).
    Z.to_euclidean_division_equations. nia. }
  destruct (vm_roomS_gap md X (mmap_nZ len) HR HPG ltac:(unfold PG; exact Hnal)) as (aZ & Hlo & Hhi & Hpg & Hdisj).
  assert (two64_eq' : bv_modulus 64 = 2 ^ 64) by reflexivity.
  assert (Ha : bv_unsigned (Z_to_bv 64 aZ) = aZ).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64_eq'. unfold WTOP in *. lia. }
  assert (Hn : bv_unsigned (mmap_n len) = mmap_nZ len).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64_eq'. unfold WTOP in *. lia. }
  assert (Hrf : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (Z_to_bv 64 aZ) (mmap_n len) = true).
  { unfold mmap_n. apply region_free_of_disjoint; [lia | lia | unfold WTOP in *; lia |]. exact Hdisj. }
  assert (Hbud : vm_backing_used md + mmap_nZ len <= vm_limit (m_vmmaps md)).
  { pose proof (vm_backing_used_le_pot md). lia. }
  exists (Z_to_bv 64 aZ). rewrite Ha. unfold PG in Hpg.
  split; [unfold page_size; exact Hpg|]. split; [lia|]. split; [lia|]. split; [exact Hhi|]. split; [exact Hn|]. split; [exact Hrf|].
  split; [exact Hdisj|]. split.
  - intros hint flags Hnr. unfold mmap_place_ok. rewrite Ha. split; [exact Hpg|]. split; [lia|]. split; [lia|]. split; [exact Hrf|].
    unfold mmap_noreserve_backed_ok. rewrite Hnr. apply Z.leb_le. exact Hbud.
  - intros hint. unfold mmap_place_ok_none. rewrite Ha. split; [exact Hpg|]. split; [lia|]. split; [lia | exact Hrf].
Qed.

Lemma vm_gap_available_of_place_noneS : ltac2:(tb__ "0|1|
S25Q40A1M0SdG0G0S1fR4R3R2R1A4S8S27S3cScR4A1S1eR3A1A2S2bA3F_;Fa;Flen;Fmd;Fhint;").
Proof.
  intros hint md len a (Hal & Hpos & Htop & Hfree).
  apply (proj2 (vm_gap_available_iff (m_vmmaps md) (mmap_nZ len))).
  exists a. split; [exact Hal|]. split; [exact Hpos|]. split; [exact Htop|]. unfold mmap_n in Hfree. exact Hfree.
Qed.

Theorem vm_roomS_rw_not_refusable : ltac2:(tb__ "0|2|
SdS0S25Q40M0A1M1G1S18R4R3A2S2Z0S26G0R3A2A2S1S1eR4A1R5A2S8S27S39R4A1S2aA3S8S27S3aR5R8S1eR6A1A3S2aA3F_;F_;F_;F_;Fflags;Flen;FX;Fmd;").
Proof.
  intros md X len flags HR Hlen HX Hnr.
  destruct (vm_roomS_place md X len HR Hlen HX) as (a & _ & _ & _ & _ & _ & _ & _ & Hpl & Hpln).
  pose proof (Hpl (Z_to_bv 64 0) flags Hnr) as P. unfold mmap_grant_refusable.
  rewrite (vm_gap_available_of_place_noneS _ _ _ _ (Hpln (Z_to_bv 64 0))). destruct P as (_ & _ & _ & _ & Hb). rewrite Hb. reflexivity.
Qed.

Theorem vm_roomS_none_not_refusable : ltac2:(tb__ "0|1|
SdS0S25Q40M0A1S18R3R2A2S2Z0S26G0R2A2A2S1S1eR3A1R4A2S8S27S3bR6S1eR4A1A2S2aA3F_;F_;F_;Flen;FX;Fmd;").
Proof.
  intros md X len HR Hlen HX.
  destruct (vm_roomS_place md X len HR Hlen HX) as (a & _ & _ & _ & _ & _ & _ & _ & _ & Hpln).
  unfold mmap_reserve_refusable. rewrite (vm_gap_available_of_place_noneS _ _ _ _ (Hpln (Z_to_bv 64 0))). reflexivity.
Qed.

Theorem vm_roomS_mprotect : ltac2:(tb__ "0|1|
SdS0S25Q40A1M0G0S18R4R3A2S9S8S27S3eR5R3R2A3S2bA3S18S3fR5R3R2A3R4A2A2F_;Fn;Faddr;FX;Fmd;").
Proof.
  intros md X addr n HR.
  assert (HR' : vm_roomS (mprotect_model_next md addr n) X).
  { eapply vm_roomS_vmmaps_le; [ | | | | | exact HR]; reflexivity. }
  split; [|exact HR'].
  unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  pose proof (vm_backing_used_le_pot (mprotect_model_next md addr n)).
  destruct HR' as (H0' & _ & HP' & _). lia.
Qed.

Corollary vm_roomS_rw_refused_False : ltac2:(tb__ "0|2|
SdS0S25Q40M0A1M1G1S18R4R3A2S2Z0S26G0R3A2A2S1S1eR4A1R5A2S8S27S39R4A1S2aA3S8S27S3aR5R8S1eR6A1A3S2bA3SaF_;F_;F_;F_;F_;Fflags;Flen;FX;Fmd;").
Proof. intros md X len flags HR Hl HX Hnr Hrf. rewrite (vm_roomS_rw_not_refusable md X len flags HR Hl HX Hnr) in Hrf. discriminate. Qed.

Corollary vm_roomS_none_refused_False : ltac2:(tb__ "0|1|
SdS0S25Q40M0A1S18R3R2A2S2Z0S26G0R2A2A2S1S1eR3A1R4A2S8S27S3bR6S1eR4A1A2S2bA3SaF_;F_;F_;F_;Flen;FX;Fmd;").
Proof. intros md X len HR Hl HX Hrf. rewrite (vm_roomS_none_not_refusable md X len HR Hl HX) in Hrf. discriminate. Qed.

Corollary vm_roomS_mprotect_refused_False : ltac2:(tb__ "0|1|
SdS0S25Q40A1M0G0S18R4R3A2S8S27S3eR5R3R2A3S2aA3SaF_;F_;Fn;Faddr;FX;Fmd;").
Proof. intros md X addr n HR Hb. rewrite (proj1 (vm_roomS_mprotect md X addr n HR)) in Hb. discriminate. Qed.

Lemma vm_roomS_grant_vm : ltac2:(tb__ "0|4|
SdS0S25Q40M0A1M1G1S15S18R5R4A2S2Z0S26G0R4A2A2S1S1eR5A1R6A2S1S3S26G0R5A2S1eR6A1A2S13ScR8A1A1A2S8S29S28G1G1A2M2A1M3SeR5A1SeScR9A1A1A3S8G3SfR6A1S31G2S2eG1G1R7S20R8A1A4SfScRaA1A1A3A3S8S0S10R7A1S10ScRbA1A1A3S8G1S12R8A1S12ScRcA1A1A3S18S14R9RdA2S5RcS1eRbA1A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fh';Fa;Flen;FX;Fmd;").
Proof.
  intros md X len a h' (H0 & HC & HP & HL & HT) Hlen HX Hceil Hr Hm Hl Hsp.
  destruct (mmap_nw _ a len Hceil) as [En _].
  assert (HPG : PG <= mmap_nZ len).
  { unfold PG. unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange len). Z.to_euclidean_division_equations. nia. }
  unfold vm_roomS, lcount, ledger, vm_pot in *.
  change (m_vmmaps (with_vmmaps h' md)) with h'. change (m_vm_materialized (with_vmmaps h' md)) with (m_vm_materialized md).
  rewrite Hr, Hm, Hl. split; [lia|]. split; [|split; [|split; [exact HL| unfold alloc_top in *; rewrite Hsp; exact HT]]].
  - rewrite length_app in *. cbn [length] in *. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. unfold PG in *. lia.
  - rewrite map_app, total_app in *. cbn [map].
    change (total (zpair (a, mmap_n len) :: map zpair (vm_maps (m_vmmaps md)))) with (snd (zpair (a, mmap_n len)) + total (map zpair (vm_maps (m_vmmaps md)))).
    change (snd (zpair (a, mmap_n len))) with (bv_unsigned (mmap_n len)). rewrite En. lia.
Qed.

Theorem vm_roomS_grant_rw : ltac2:(tb__ "0|2|
SdS0S25Q40M0A1M1G1G1G1S18R6R5A2S2Z0S26G0R5A2A2S1S1eR6A1R7A2S21R5R4R9R7R6A5S18S14S23ScRaA1R8R7A3RaA2S5R9S1eR8A1A2A2F_;F_;F_;F_;Fflags;Fhint;Fa;Flen;FX;Fmd;").
Proof.
  intros md X len a hint flags HR Hlen HX (_ & _ & Hceil & _). eapply vm_roomS_grant_vm; eauto; reflexivity.
Qed.

Theorem vm_roomS_grant_none : ltac2:(tb__ "0|2|
SdS0S25Q40M0A1M1G1G1S18R5R4A2S2Z0S26G0R4A2A2S1S1eR5A1R6A2S1fR4R8R6R5A4S18S14S22ScR9A1R7R6A3R9A2S5R8S1eR7A1A2A2F_;F_;F_;F_;Fhint;Fa;Flen;FX;Fmd;").
Proof.
  intros md X len a hint HR Hlen HX (_ & _ & Hceil & _). eapply vm_roomS_grant_vm; eauto; reflexivity.
Qed.

Lemma total_filter_le0 : ltac2:(tb__ "0|1|
S28S0S0A2M0S27F_;S29G0A1G0S36G0R1R2A3S1Z0S30S0S0R2A3A2F_;Fe;S1S34S37G0R3R2A3A1S34R2A1A2F_;Fl;Ff;").
Proof.
  induction l as [|e t IH]; intros Hl; [unfold total; cbn; lia|].
  cbn [List.filter]. pose proof (Hl e ltac:(left; reflexivity)). specialize (IH ltac:(intros x Hx; apply Hl; right; exact Hx)).
  change (total (e :: t)) with (snd e + total t).
  destruct (f e); [change (total (e :: List.filter f t)) with (snd e + total (List.filter f t))|]; lia.
Qed.

Theorem vm_roomS_munmap : ltac2:(tb__ "0|1|
SdS0S25Q40A1M0G0S18R4R3A2S18S24R5R3R2A3R4A2F_;Fn;Faddr;FX;Fmd;").
Proof.
  intros md X addr n (H0 & HC & HP & HL & HT).
  set (md' := munmap_model md addr n).
  assert (Hr : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by reflexivity.
  assert (Hm : vm_maps (m_vmmaps md') = map_remove (vm_maps (m_vmmaps md)) addr) by reflexivity.
  assert (Hl : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by reflexivity.
  assert (Hmat : m_vm_materialized md'
                 = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized md)) by reflexivity.
  assert (Hsp : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by reflexivity.
  unfold vm_roomS, lcount, ledger, vm_pot. rewrite Hr, Hm, Hl, Hmat, Hsp. unfold vm_pot, lcount, ledger in HP, HC.
  split; [exact H0|]. split; [|split; [|split; [exact HL|exact HT]]].
  - rewrite length_app, Nat2Z.inj_add in *. unfold map_remove.
    pose proof (filter_length_le (fun p : word * word => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps md))) as FL. apply Nat2Z.inj_le in FL.
    unfold PG in *. nia.
  - rewrite map_app, total_app, map_zpair_filter_base. rewrite map_app, total_app in HP.
    pose proof (total_filter_le0 (fun p : Z * Z => negb (fst p =? bv_unsigned addr)) (map zpair (vm_maps (m_vmmaps md))) (total_map_zpair_nonneg _)) as Hf.
    pose proof (filter_length_le (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized md)) as Hlen.
    apply Nat2Z.inj_le in Hlen. unfold PGSZ in *. nia.
Qed.

Theorem vm_roomS_init : ltac2:(tb__ "0|4|
SdS0S8S29S28S25Q40A1M0G0A2M1A1SfScR2A1A1S2fG1A1A3S8S29G0A1S11R3A1S2fG0A1A3S3dS2dG1SeScR4A1A1A2U8A2S1S34S38G1S28S0S0A2S33SeScR5A1A1A4A1S4Z2M2Z14A2M3A2S1Z0R5A2S1S3R6G3A2S10ScR7A1A1A2S1S10ScR8A1A1S4G2Z28A2A2S1S3R8S4G2Z10A2A2S1aA2S1Z7fff7f800000S13ScRaA1A1A2S18RbRaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FX;Fmd;").
Proof.
  intros md X Hmaps Hmat Hres Htot HX Hlim Hlim' HXC Htop.
  unfold vm_roomS, lcount, ledger, vm_pot. rewrite Hmaps, Hmat, app_nil_r. cbn [length Z.of_nat].
  apply Nat2Z.inj_le in Hres. unfold PG, ROOMC in *.
  split; [exact HX|]. split; [lia|]. split; [lia|]. split; [exact Hlim' | exact Htop].
Qed.
