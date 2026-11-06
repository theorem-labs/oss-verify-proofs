(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "option"; "prod"; "Some"; "pair"; "true"; "None"; "false"; "list"; "andb"; "fst"; "length"; "negb"; "nil"; "option_map"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "region"; "ameta"; "malloc"; "ret"; "bind"; "kreq"; "prid"; "FAssert"; "M"; "RkMap"; "am_last"; "am_maplen"; "am_sc"; "class_size"; "fail"; "find_frame_in"; "get"; "poff"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_metas"; "st_regions"; "stride_of"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "iff"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "leb"; "add"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "WF"; "yields"; "lookup_used"; "region_of"; "safe"; "usedX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCalloc"; "calloc_overflows"; "calloc_m"; "is_allzero_am"; "is_allzero_m"; "@Corelib.Init.Peano"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition is_allzero_am (am : ameta) : bool := ltac2:(tb__ "0|1|
SfS35Z30S1eVam;A1M0A2S38S2aVam;A1S1fG0A1A2A2").

Definition is_allzero_m (s : astate) (p : sptr) : option bool := ltac2:(tb__ "0|3|
S1S2S10S2bA2M0A1S1S0A1M1Lx;S21S28Vs;A1Vp;A2G0G0G1Lp0;R1S10S2bS1S13A1G1Lx;S3bVs;R2A2S13S3S0S41R1A1A2Lam;S6S0A1M2X1x2Lz;Lg;X2x1Lp0;G2X1x2").

Definition calloc_overflows (m n : Z) : bool := ltac2:(tb__ "0|0|
S9ScS37Vn;Z0A2A1S35S33Z2Z40A2S32Vm;Vn;A2A2A2").

Lemma calloc_overflows_iff : ltac2:(tb__ "0|3|
S2bS2bS2cS31Z0M0R2A2S34R2S33Z2Z40A2M1A2A2M2G2S2fS2dS0S3fR4R3A2S5A3S2cS30S2dS2bR3G0A3A1S31G1S32R4R3A2A2A2A2F_;F_;Fn;Fm;").
Proof.
  intros m n Hm Hn. unfold calloc_overflows.
  rewrite andb_true_iff, negb_true_iff, Z.eqb_neq, Z.leb_le. tauto.
Qed.

Definition calloc_m (m n : Z) : M (option (sptr * bool)) := ltac2:(tb__ "0|5|
S0S1aS1S2S10S0A2M0A1M1A1M2L_;S3fVm;Vn;A2S15G1S6G0A1A2M3S16S1S10A1M4G1S14S32Vm;Vn;A2A1G4G4G2Lop;R1S10S16S11G1S22S11S1S0A1G2Lx;S42R1R2A2S0S0G2Lb;R1S15G1S3G0S4S10S0R3S7A4A2A2S15G1S3G0S4S10S0R3S5A4A2A2X0x2Lb;S20G1S19Z64A1A2X1x2Ls;A4Lp;G3X1x2Lop;A4X0x2").

Definition calloc_is_malloc_stmt : Prop := ltac2:(tb__ "0|4|
S11S2bS2bS8S2S17S2bA2A1S1S2S10S0A2M0A1M1S11S39R6A1S2cS31Z0R6A2S34R6S33Z2Z40A2A2A2M2G2S2dS0S3fR8R7A2S7A3S3aS2G1S11A2S40R9R8RaA3R7S4G1S11R6R5A4A4S3aS2S1S10A1M3S11A2S14S32RaR9A2RbA2R8S4G3S11SeG0S10SaS10S0A2R7A4R6A4A4F_;F_;F_;F_;F_;Fs';Fr;Ftr;Fn;Fm;Fs;").

Definition calloc_safe_stmt : Prop := ltac2:(tb__ "0|1|
S11S2bS2bS39R3A1S2cS31Z0R3A2S34R3S33Z2Z40A2A2A2M0G0S3dS2S1S2S10S0A2A1S11A2S40R5R4R6A3A2F_;F_;F_;Fn;Fm;Fs;").

Definition allzero_fresh_stmt : Prop := ltac2:(tb__ "0|3|
S11S2bS8S2S17S2bA2A1S10S11S39R5A1S31Z0M0R5A2S3aS2S1S10A1M1S11A2S14R6R7A2R5S4G1S11S3S10R4A2R3A4A4S2dS1S0A1S42R4R5A2S3S0S5A2A3S2cS43SbS12S29R9A1A2S18R6A1A2S2eS12S12S2cS2dS1S12A1S3cR6S18R7A1A2S3S12R1A2A3S2cS2dS27S24R1A1S1bA3S2cS2dS0S26R1A1S5A3S2cS31G0S23R7A1M2A2S31S36G2R9A2S25R1A1A2A2A2A2A2Lrg;A2A2F_;F_;F_;F_;Fs';Fp;Ftr;Fn;Fs;").

Lemma is_allzero_single_slot : ltac2:(tb__ "0|0|
S11S10S13S39R3A1S3eSdS10A1R4R3R2A4S2dS0S41R3A1S5A3S2cS2dS2bS1cR4A1Z0A3S31Z1S1dR4A1A2A2F_;F_;F_;Fam;Fg;Fs;").
Proof.
  intros s g am HWF Hu Hz.
  pose proof (inv_groups HWF g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  unfold is_allzero_am in Hz. apply orb_prop in Hz.
  destruct Gcl as [(C63 & Cl & Cml & _) | (Csc & Cund & C26 & Cbig)].
  - split; [exact Cl | exact Cml].
  - destruct Hz as [Hz | Hz].
    + apply Z.leb_le in Hz. lia.
    + apply Z.ltb_lt in Hz. destruct (Cund Hz) as [Hl _]. split; [exact Hl|].

      unfold stride_of in Hz. rewrite Hl in Hz. cbn [Z.eqb] in Hz.
      destruct (am_maplen am =? 0) eqn:E; cbn in Hz.
      * unfold class_size in Hz. lia.
      * apply Z.eqb_neq in E. lia.
Qed.
