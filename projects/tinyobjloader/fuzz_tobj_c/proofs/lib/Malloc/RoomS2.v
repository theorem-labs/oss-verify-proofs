(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "m_vm_materialized"; "vm_init_sp"; "vm_limit"; "vm_maps"; "vm_reserved"; "VmMaps"; "with_vmmaps"; "vm_forget_range"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@Corelib.Init.Datatypes"; "length"; "snd"; "list"; "prod"; "cons"; "bool"; "false"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "PG"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_fixed_ok_model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout FreeGap ContractDrv VmRoom RoomS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Theorem vm_roomS_cons : ltac2:(tb__ "0|4|
S2SbS10S14Q40M0A1M1G1A2M2S8ScR4R3A2S16S19S15G0SeG1G1R3A3A2A2S16S15G0SeG1G1R4A3A2R5A2S0SfG2A1M3S7R4A1S7S1R7A1A1A3S0G3S6R5A1S11G2R6S6S1R8A1A1A3A3S0SbS5R6A1S5S1R9A1A1A3S0G1S4R7A1S4S1RaA1A1A3ScS9R8RbA2S17RaS15G0SeG1G1R9A3A2A2A2F_;F_;F_;F_;F_;F_;F_;Fh';Fe;FX;Fmd;").
Proof.
  intros md X e h' (H0 & HC & HP & HL & HT) HPG HX Hr Hm Hl Hsp.
  unfold vm_roomS, lcount, ledger, vm_pot in *.
  change (m_vmmaps (with_vmmaps h' md)) with h'. change (m_vm_materialized (with_vmmaps h' md)) with (m_vm_materialized md).
  rewrite Hr, Hm, Hl. split; [lia|]. split; [|split; [|split; [exact HL| unfold alloc_top in *; rewrite Hsp; exact HT]]].
  - rewrite length_app in *. cbn [length] in *. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. unfold PG in *. lia.
  - rewrite map_app, total_app in *. cbn [map].
    change (total (zpair e :: map zpair (vm_maps (m_vmmaps md)))) with (snd (zpair e) + total (map zpair (vm_maps (m_vmmaps md)))).
    change (snd (zpair e)) with (bv_unsigned (snd e)). lia.
Qed.

Theorem vm_roomS_same_maps : ltac2:(tb__ "0|5|
S2S2SbS0SfS10S14Q40A1M0G0A2A1M1S7S1R2A1A1S7S1R3A1M2A1A3S0G1S6G2A1S6S1R4A1M3A1A3S0SbS5G3A1S5S1R5A1M4A1A3S0G0S4G4A1S4S1R6A1A1A3S18SdG0S3R6A1A2SdG0S3R7A1A2A2ScR8R6A2ScR8R7A2F_;F_;F_;F_;F_;F_;FX;Fmd';Fmd;").
Proof. exact vm_roomS_vmmaps_le. Qed.

Lemma m_vm_materialized_with_vmmaps : ltac2:(tb__ "0|0|
S8S2S0SfS14Q40A1A1S3S9R2R1A2A1S3R1A1A3Fm;Fh;").
Proof. intros h m. destruct m; reflexivity. Qed.

Theorem vm_roomS_cons_md : ltac2:(tb__ "0|7|
S2S2SbS10S14Q40M0A1M1G1A2M2ScR4R2A2S16S19S15G0SeG1G1R2A3A2A2S16S15G0SeG1G1R3A3A2R4A2S0SfG2A1M3S7S1R6A1A1S7S1R7A1M4A1A3S0G3S6G4A1S11G2R5S6S1R8A1M5A1A3A3S0SbS5G5A1S5S1R9A1M6A1A3S0G1S4G6A1S4S1RaA1A1A3S18SdG1S3RaA1A2SdG1S3RbA1A2A2ScRbS17RaS15G0SeG1G1R9A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fe;FX;Fmd';Fmd;").
Proof.
  intros md md' X e HR HPG HX Hr Hm Hl Hsp Hlen.
  apply (vm_roomS_same_maps (with_vmmaps (m_vmmaps md') md) md').
  - rewrite m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vmmaps'. reflexivity.
  - destruct md; exact Hlen.
  - exact (vm_roomS_cons md X e (m_vmmaps md') HR HPG HX Hr Hm Hl Hsp).
Qed.

Lemma length_m_vm_materialized_forget : ltac2:(tb__ "0|1|
SbSbS2S18SdS14Q40A1M0S3SaR3R2R1A3A1A2SdG0S3R1A1A2A2Fm;Fhi;Flo;").
Proof. intros lo hi m. unfold vm_forget_range. destruct m; cbn. apply filter_length_le. Qed.

Theorem vm_roomS_fixed_ok : ltac2:(tb__ "0|1|
S14Q40A1M0S2G0G0SbS0S12S1aR5A1S13A3ScR5R2A2ScS1bR7R6R5R4A4R3A2F_;F_;FX;Fn;Faddr;Fmd;Fflags;").
Proof.
  intros flags md addr n X Hnr HR.
  unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr. unfold vm_forget_range.
  apply (vm_roomS_same_maps md).
  - rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps'. reflexivity.
  - rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps'. reflexivity.
  - destruct md; cbn. apply filter_length_le.
  - exact HR.
Qed.
