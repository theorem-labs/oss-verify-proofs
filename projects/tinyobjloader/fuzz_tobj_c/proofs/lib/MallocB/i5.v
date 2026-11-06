(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From LinuxProcessSemantics.Riscv Require Prelude Sem.

(* [comment removed for export] *)
Module InvInitH0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "leb"; "sub"; "div"; "mul"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "false"; "bool"; "option"; "andb"; "list"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ob_base"; "ob_hi"; "ob_lo"; "rw"; "sobj"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "lit_small"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.InvInitH0"; "fsq"; "bo_ok"; "fse"; "fsn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.InvInitF"; "band_out"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.InvInitF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fsq (F : Z) : Z := ltac2:(tb__ "0|0|
S1cS4VF;Z9000A2A1S0S7R1S5R1Z1000A2A2Ts;").
Definition fse (F : Z) : Z := ltac2:(tb__ "0|0|
S4S1cS4VF;Zb09000A2A1ZfffA2S0S7R1S5R1Z1000A2A2Ts;").
Definition fsn (F : Z) : nat := ltac2:(tb__ "0|0|
SbS8S7S20VF;A1S1eVF;A1A2Z1000A2A1").

Lemma fs_range_arith : ltac2:(tb__ "0|7|
S0S0S13S0S5R2Z1000M0A2Z0M1A3S3Z643000R3A2S3S4R4Zb09000M2A2R3A2S3R4Z7fffff800000A2S14S3S4R6G2A2Z7fff7000A2S3Z10007fff8000M3R6A2A2S12S13S0S5S1eR7A1M4G0A2G1A3S12S3G4S1cS4R7Z9000A2A1A2S12S3S1cS4R7G2A2A1S4G4S9G0SaS21R7A1A1M5A2A2M6A2S12S3G5Z161A2S12S3Z800c1000G4A2S12S3G6S4S1cR6A1G0A2A2S14S3G6Z8fff7000A2S12S3Z2008fff7000G4A2S3G6G3A2A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;Ftop;FF;").
Proof.
  intros F top Hal Hlo Htop Htop2 Hband.
  assert (EF : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 4096 ltac:(lia)) as D; rewrite Hal in D; rewrite D at 2; rewrite Z.add_0_r;
                                     replace (4096 * (F / 4096)) with ((512 * (F / 4096)) * 8) by lia; rewrite Z.div_mul by lia; lia).
  set (f := F / 8) in *.
  assert (S1 : Sh (F + 36864) = f + 4608 + 0x7fff8000).
  { unfold Sh, SHADOW_OFF. rewrite EF. replace (8 * f + 36864) with ((f + 4608) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (S2 : Sh (F + 11571200) = f + 1446400 + 0x7fff8000).
  { unfold Sh, SHADOW_OFF. rewrite EF. replace (8 * f + 11571200) with ((f + 1446400) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (ST : Sh (F + 11571200) <= Sh top) by (unfold Sh; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Htop); lia).
  assert (STB : Sh top <= 0x10007fff8000 - 1048576).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Htop2) as D. change (140737479966720 / 8) with 17592184995840 in D. lia. }
  unfold fsn, fsq, fse. cbn zeta. rewrite S1, S2 in *.
  set (s1 := f + 4608 + 2147450880) in *. set (s2 := f + 1446400 + 2147450880 + 4095) in *.
  pose proof (Z.div_mod s1 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound s1 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod s2 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound s2 4096 ltac:(lia)) as M2.
  assert (Q : s1 - s1 mod 4096 = 4096 * (s1 / 4096)) by lia. assert (E : s2 - s2 mod 4096 = 4096 * (s2 / 4096)) by lia.
  rewrite Q, E. replace (4096 * (s2 / 4096) - 4096 * (s1 / 4096)) with ((s2 / 4096 - s1 / 4096) * 4096) by lia. rewrite Z.div_mul by lia.
  assert (NN : 0 <= s2 / 4096 - s1 / 4096) by (unfold s1, s2 in *; lia).
  rewrite Z2Nat.id by exact NN.
  split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
  split; [lia|]. split; [unfold s1, s2 in *; lia|]. split; [unfold s1, s2 in *; lia|].
  assert (FLO : 820736 <= f) by (unfold f; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Hlo) as D; change (6565888 / 8) with 820736 in D; exact D).
  split; [unfold s1 in *; lia|]. split; [unfold s1, s2 in *; lia|].
  destruct Hband as [HB|HB].
  - left. assert (f + 1446400 <= 268434944) by (rewrite EF in HB; lia). unfold s1, s2 in *. lia.
  - right. assert (2199090364416 <= f) by (unfold f; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) HB) as D; change (17594333495296 / 8) with 2199291686912 in D; lia).
    unfold s1, s2 in *. lia.
Qed.

Definition bo_ok (vs : list positive) (o : sobj) : bool := ltac2:(tb__ "0|6|
S15SdLx;S16Vo;A1S0S0SdLz;R1SeS0A1SdLx;M0S1dS18Vo;A1A1M1S0G0S1dS17Vo;A1A1S0SfS6Z0R2A2S6R1Z643000A2A2Lhi;ScXex2Llo;ScXex2S1ScLp;M2G2X0x3Lz;S1G0G1S0SfS26S1S27R2A1Vvs;A3S6N100000R1A2A2Llo;ScXex2Li;S22S15S15ScLb;La;M3Lop;M4G4S23G3Lop;M5G5SdS2S15ScLa;Lw;Lsgn;S1S15S0ScLk;Li;Ll;X15x8").
Lemma bo_ok_sound : ltac2:(tb__ "0|0|
S1bS10S1A1S1aS1S25S1R1R3A3S3Z7fff80000000S28Q40S19R5R2A2A2A2F_;Fi;S13SdS1fR3R2A2S11A3S24R5R3A2F_;F_;Fo;Fvs;Frho;").
Proof.
  intros rho vs o Hvs H. unfold bo_ok in H. unfold band_out, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  destruct (ob_base o) as [z| i | | | | | |] eqn:Eb; try discriminate.
  - destruct z; try discriminate. destruct (lit_small (ob_lo o)) as [lo|] eqn:El; [|discriminate]. destruct (lit_small (ob_hi o)) as [hi|] eqn:Eh; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite (soff_small rho _ _ Eh). left. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG. lia.
  - destruct (lit_small (ob_lo o)) as [lo|] eqn:El; [|discriminate]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2.
    apply existsb_exists in H1 as (j & Hj & Ej). apply Pos.eqb_eq in Ej. subst j.
    rewrite (soff_small rho _ _ El). right. cbn [eval]. pose proof (Hvs i Hj). unfold SHADOW_BAND_HI, HIGH_SHADOW_END. lia.
Qed.
End InvInitH0.

(* [comment removed for export] *)
Module CertMallocS1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "prod"; "nil"; "app"; "bool"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "mkCell"; "SVar"; "sprop"; "sobj"; "SAlu"; "SPUle"; "SPUlt"; "FcsrFrm0"; "SPBranch"; "mkSS"; "DUnknown"; "SPAlign"; "SPNot"; "mkObj"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "rup8"; "P0_s1"; "V_TSZ"; "rzf_rz"; "s1_cuts"; "s1_exits"; "vRIS"; "E_s1"; "F_hi"; "F_lo"; "F_s1"; "O_afl"; "O_cfb"; "O_cfc"; "O_cft"; "O_csd"; "O_die"; "O_hooks"; "O_insta"; "O_insta2"; "O_instb"; "O_lsan"; "O_ppf"; "O_rms"; "O_rss"; "RT_m1"; "neededx"; "rzf_hi"; "rzf_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "mkVNA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "vTOP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "mkA"; "AE_A"; "A_globals"; "V_DEPTH"; "ae_malloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0"; "RT_m0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.S1"; "E_regs"; "F_fam"; "sw_s1"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition vSB : sv := SVar 155.
Definition vRIS : sv := SVar 156.
Definition O_insta : sobj := ltac2:(tb__ "0|3|
S1bS9Z0A1Zeaa78M0Zeaa84S0S3S3S1aS2A2M1SaA2M2S1G1SaS1S1aS2G0U8A4S20A4S0G2S1G1SaS1S1aS2Zeaa80U4A4S9ZffffffffA1A4S4G2A1A3A3A4").
Definition O_insta2 : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Zeaa88M1Zeaa91S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U8A4S27A4S0G3S1G2SaS1S1aS2Zeaa90U1A4G0A4S4G3A1A3A3A4").
Definition O_instb : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1Zeb878M0Zeb884S0S3S3S1aS2A2M1SaA2M2S1G1SaS1S1aS2G0U8A4S9S42Z2Z28A2A1A4S0G2S1G1SaS1S1aS2Zeb880U2M3A4S9Z10A1A4S0G2S1G1SaS1S1aS2Zeb882G3A4S9Z800A1A4S4G2A1A3A3A3A4").
Definition O_rss : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z170322M1Z170323S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U1A4G0A4S4G3A1A3A4").
Definition O_cfb : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z17fc78M1Z17fc80S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U8A4G0A4S4G3A1A3A4").
Definition O_cfc : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z17fcecM1Z17fcedS0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U1A4G0A4S4G3A1A3A4").

Definition O_rms : sobj := ltac2:(tb__ "0|3|
S1bS9Z0A1Ze6780M0Ze6788S0S3S3S1aS2A2M1SaA2M2S1G1SaS1S1aS2G0U8A4S9Zdb004A1A4S4G2A1A3A4").
Definition O_ppf : sobj := ltac2:(tb__ "0|3|
S1bS9Z0A1Zeb90dM0Zeb90eS0S3S3S1aS2A2M1SaA2M2S1G1SaS1S1aS2G0U1A4S9Z1A1A4S4G2A1A3A4").
Definition O_hooks : sobj := ltac2:(tb__ "0|5|
S1bS9Z0A1M0Z17fb80M1Z17fb90S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U8M4A4G0A4S0G3S1G2SaS1S1aS2Z17fb88G4A4G0A4S4G3A1A3A3A4").
Definition O_lsan : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z621288M1Z62128cS0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U4A4G0A4S4G3A1A3A4").
Definition O_cft : sobj := ltac2:(tb__ "0|3|
S1bS9Z0A1Z17fc60M0Z17fc68S0S3S3S1aS2A2M1SaA2M2S1G1SaS1S1aS2G0U8A4S9ZffffffffffffffffA1A4S4G2A1A3A4").
Definition O_afl : sobj := ltac2:(tb__ "0|5|
S1bS9Z0A1M0Zeb8e4M1Zeb8f0S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U4M4A4S9Z1000A1A4S0G3S1G2SaS1S1aS2Zeb8e8G4A4G0A4S0G3S1G2SaS1S1aS2Zeb8ecG4A4S9ZbeA1A4S4G3A1A3A3A3A4").
Definition O_csd : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z17fcd8M1Z17fcdcS0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U4A4G0A4S4G3A1A3A4").
Definition O_die : sobj := ltac2:(tb__ "0|4|
S1bS9Z0A1M0Z17fbdcM1Z17fbe0S0S3S3S1aS2A2M2SaA2M3S1G2SaS1S1aS2G1U4A4G0A4S4G3A1A3A4").
Definition RT_m1 : list sobj := ltac2:(tb__ "0|0|
S5SfS5eS0SfS33S0SfS34S0SfS35S0SfS39S0SfS2dS0SfS2eS0SfS38S0SfS37S0SfS32S0SfS36S0SfS2fS0SfS2cS0SfS30S0SfS31S4SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_s1 : list sprop := ltac2:(tb__ "0|1|
S0SeS17P9bZ10A2S0SeS11S9S52A1S20A2S0SeS11S20S9S43S43Z7fffff800000S51A2Z1000A2A1A2S0SeS14S1dS27S10S1cS20S9S51A1A3A3S0SeS11S9Z1A1SdPcA1M0A2S0SeS12G0S9S42Z2Z27A2A1A2S0SeS18S14S1dS10S1cSdPaA1S9N850A1A3S9Z0A1A3A1S4SeA1A3A3A3A3A3A3A3").

Definition rup8 : sv := ltac2:(tb__ "0|0|
S10S1eS10S1cSdPcA1S9Z7A1A3S9Zfffffffffffffff8A1A3").
Definition F_hi : list sprop := ltac2:(tb__ "0|0|
S0SeS11S9Zfc01A1SdPcA1A2S4SeA1A3").
Definition F_lo : list sprop := ltac2:(tb__ "0|0|
S0SeS12SdPcA1S9Zfc01A1A2S0SeS11S21S9Zfc00A1A2S4SeA1A3A3").

Definition rzf_lo (k : Z) : Z :=
  match k with 0 => 1 | 1 => 9 | 2 => 49 | 3 => 97 | 4 => 449 | 5 => 3969 | 6 => 16129 | 7 => 32257 | _ => 64513 end.
Definition rzf_hi (k : Z) : Z :=
  match k with 0 => 9 | 1 => 49 | 2 => 97 | 3 => 449 | 4 => 3969 | 5 => 16129 | 6 => 32257 | 7 => 64513 | _ => 2 ^ 39 end.
Definition rzf_rz (k : Z) : Z :=
  match k with 0 => 16 | 1 => 16 | 2 => 32 | 3 => 64 | 4 => 128 | 5 => 256 | 6 => 512 | 7 => 1024 | _ => 2048 end.

Definition neededx (k : Z) : sv := ltac2:(tb__ "0|1|
S6SaL_;M0S41Vk;Z0A2S9Z18A1G0S41Vk;Z8A2S10S1cS21S9Z1000A1A3S10S1cS21S9S24Vk;A1A1A3X6x2X6x2").
Definition V_TSZ : positive := 192%positive.

Section S1.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.
Let FACTS : list sprop := ltac2:(tb__ "0|0|
S5SeS5SeS5SeS5cVW;Vst;A2S5aS59A1A3S4dA3S2bA3").
Let OBJS (sw : sobj) : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfVsw;S5SfS5dVW;A1S56A3A3S3aA3").

Definition P0_s1 (fx : list sprop) : axst := ltac2:(tb__ "0|1|
S54S15S58S55A1S45S47S0S3S2SaA2M0S1S2SaU4S9S4eA1A4S4G0A1A3A2S44S13S7SaA1VOBJS;S5bA1S5SeVFACTS;Vfx;A3S4cS8A9S4S3SaSaA2A1A2").

Definition sw_s1 : sobj := ltac2:(tb__ "0|8|
S19SdPaA1M0SdS57A1S9Z0A1M1S0SbScS9N8e8A1Z8M2S9Z3c5f8A1A3S0SbScS9N8e0A1G2S50A3S0SbScS9N8d8A1G2S9Z1A1M3A3S0SbScS9N8d0A1G2S9Z10A1A3S0SbScS9N8c8A1G2SdP2fA1A3S0SbScS9N8c0A1G2SdP2eA1A3S0SbScS9N8b8A1G2SdP2dA1A3S0SbScS9N8b0A1G2SdP2cA1A3S0SbScS9N8a8A1G2SdP2bA1A3S0SbScS9N8a0A1G2SdP2aA1A3S0SbScS9N898A1G2S10S1cG0S9N51A1A3A3S0SbScS9N890A1G2S10S1cG0S9N850A1M4A3A3S0SbScS9N888A1G2G3A3S0SbScS9N880A1G2S9Z5e49cA1M5A3S0SbScS9N878A1G2SdPcA1A3S0SbScS9N870A1G2G0A3S0SbScS9N868A1G2S9Z3c344A1A3S0SbScS9N860A1G2G0A3S0SbScS9N858A1G2S9Z5e508A1A3S0SbScG4G2S10S1cG0S9N840A1M6A3A3S0SbScS9N848A1Z4M7SdS23A1A3S0SbScS9N844A1G7G1A3S0SbScG6G2G5A3S0SbScS9N48A1G2G0A3S0SbScS9N38A1G2SdP29A1A3S0SbScS9N30A1G2SdP28A1A3S0SbScS9N28A1G2SdP27A1A3S0SbScS9N20A1G2SdP26A1A3S0SbScS9N18A1G2SdP1dA1A3S0SbScS9N10A1G2SdP1cA1A3S0SbScS9N8A1G2SdPbA1A3S4SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S16A5").

Definition E_regs (k : Z) : list sv := ltac2:(tb__ "0|8|
S45S46S3fA1S0S3S2SaA2M0S1S2SaU1S9Z3c614A1A4S0G0S1S2SaU2S10S1cSdPaA1M1S9N8e0A1A3A4S0G0S1S2SaU4S9S4eA1A4S0G0S1S2SaU8S9S6S1aL_;S41Vk;Z8M2A2Z0Z1M3X6x2A1A4S0G0S1S2SaU9SdPcA1M4A4S0G0S1S2SaUaS9Zeaa58A1M5A4S0G0S1S2SaUbS10S1cS4fS9Zd0A1A3A4S0G0S1S2SaUcS3bVk;A1M6A4S0G0S1S2SaUdS9G2A1M7A4S0G0S1S2SaU12G7A4S0G0S1S2SaU13G6A4S0G0S1S2SaU14S9S24Vk;A1A1A4S0G0S1S2SaU15G4A4S0G0S1S2SaU16G5A4S0G0S1S2SaU17S10S1cG1S9N850A1A3A4S0G0S1S2SaU18S9Zfffffffffffffff8A1A4S0G0S1S2SaU19S9Z7A1A4S0G0S1S2SaU1aS4fA4S0G0S1S2SaU1bS9G3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition F_fam (k : Z) : list sprop := ltac2:(tb__ "0|2|
S0SeS11S9S3dVk;A1A1SdPcA1M0A2S0SeS12G0S9S3cVk;A1A1A2S0SeS11S9Z1A1SdS23A1M1A2S0SeS11G1S9Vtmax;A1A2S4SeA1A3A3A3A3").
Definition E_s1 (k : Z) : axst := ltac2:(tb__ "0|0|
S54S15Z40bacS5fVk;A1S44S13S7SaA1VOBJS;S61A1S5SeVFACTS;S60Vk;A1A3S4cS8A9S4S3SaSaA2A1A2").
End S1.

Definition s1_cuts (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|1|
S0S1fS22S53Vn;A1M0Vst;S29A3S0S1fS22G0Vst;S2aA3S4S1fA1A3A3").
Definition s1_exits (n : nat) (st : ustop) (tmax : Z) : list axst := ltac2:(tb__ "0|0|
S3eS1aS1fS28S53Vn;A1Vst;Vtmax;A3S0S1aZ0S0S1aZ1S0S1aZ2S0S1aZ3S0S1aZ4S0S1aZ5S0S1aZ6S0S1aZ7S0S1aZ8S4S1aA1A3A3A3A3A3A3A3A3A3A4").
Definition s1_cert (n : nat) (st : ustop) (tmax : Z) : bool := ltac2:(tb__ "0|0|
S4aS40Ufa0S0S1aZ40bacS4S1aA1A3S3fS25Vn;Vst;A2S26Vn;Vst;Vtmax;A3A6").
Definition s1_ecert (n : nat) (st : ustop) (tmax : Z) : bool := ltac2:(tb__ "0|2|
S4bS40Ufa0S0S1aZ40bacS4S1aA1A3S3fS3eS1fS49S1fS48R1Z1S9Z0M0A1M1A3Lc;S25Vn;Vst;A2A4S3eS1fS49S1fS48R1G0G1A3Le;S26Vn;Vst;Vtmax;A3A4A6").

Lemma s1_cert_0 : s1_cert 0 UStopLe 2 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s1_ecert_0 : s1_ecert 0 UStopLe 2 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertMallocS1.

(* [comment removed for export] *)
Module SegQ3_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "bool"; "true"; "false"; "None"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SVar"; "SPBranch"; "SPNot"; "FcsrFrm0"; "SPAlign"; "mkSS"; "ss_lenient"; "ss_next"; "swf"; "SPUle"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"; "ZQ"; "vTN"; "O_gmax"; "O_gq"; "O_tq"; "RECY"; "gsz"; "vTB"; "vTF"; "PreQ3e"; "PreQ3n"; "LSLOW"; "O_mtx"; "mkPost3"; "vGB"; "vGF"; "vGN"; "F_T"; "F_Tn"; "KEEP3"; "O_glb"; "F_T0"; "F_gt"; "F_le"; "NX3"; "O_mtx0'"; "RETD"; "mkPre3"; "re_ru"; "regs3"; "run_Te"; "run_Tn"; "vGS"; "vMIN"; "vTS"; "DEPTH_R"; "DRAIN"; "PostQ3e"; "PostQ3n"; "ReQ3e"; "ReQ3n"; "TsTe"; "TsTn"; "cbC"; "vGBN"; "vSTKq"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "add"; "NPRE"; "post_ru"; "NXQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "chkNK"; "@Stdlib.PArith.BinPos.Pos"; "le"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition DRAIN : Z := 0x3e120.
Definition RETD : Z := 0x3e250.
Definition RECY : Z := 0x3e2c4.
Definition LSLOW : Z := 0x3e274.
Definition QG : Z := 0xead30.

Definition NX3 : positive := 216%positive.
Definition vTN := SVar 200.
Definition vTF := SVar 201.
Definition vTB := SVar 202.
Definition vTS := SVar 203.
Definition vGN := SVar 204.
Definition vGF := SVar 205.
Definition vGB := SVar 206.
Definition vGS := SVar 207.
Definition vMIN := SVar 208.
Definition vGBN := SVar 209.

Definition O_tq (qn qf qb qs : sv) : sobj := ltac2:(tb__ "0|4|
S51SfPdA1Z0M0Z20S0S4S4S19S2A2M1SbA2M2S1G1SbS1S19S2G0U8M3A4Vqn;A4S0G2S1G1SbS1S19S2Z8G3A4Vqf;A4S0G2S1G1SbS1S19S2Z10G3A4Vqb;A4S0G2S1G1SbS1S19S2Z18G3A4Vqs;A4S3G2A1A3A3A3A3A4").
Definition O_mtx (w : sv) : sobj := ltac2:(tb__ "0|3|
S51SeZ0A1S4aS1bZ98A2M0S4aS1bZ9cA2S0S4S4S19S2A2M1SbA2M2S1G1SbS1S19S2G0U4A4Vw;A4S3G2A1A3A4").

Definition O_mtx0' : sobj := ltac2:(tb__ "0|4|
S51SeZ0A1M0S4aS1bZ98A2M1S4aS1bZ9cA2S0S4S4S19S2A2M2SbA2M3S1G2SbS1S19S2G1U1A4G0A4S0G3S1G2SbS1S19S2S4aS1bZ99A2U3A4G0A4S3G3A1A3A3A4").
Definition O_gq (gn gf gb gs : sv) : sobj := ltac2:(tb__ "0|4|
S51SeZ0A1S4aS1bZa0A2M0S4aS1bZc0A2S0S4S4S19S2A2M1SbA2M2S1G1SbS1S19S2G0U8M3A4Vgn;A4S0G2S1G1SbS1S19S2S4aS1bZa8A2G3A4Vgf;A4S0G2S1G1SbS1S19S2S4aS1bZb0A2G3A4Vgb;A4S0G2S1G1SbS1S19S2S4aS1bZb8A2G3A4Vgs;A4S3G2A1A3A3A3A3A4").
Definition O_gmax : sobj := ltac2:(tb__ "0|4|
S51SeZ0A1S4aS1bZ40A2M0S4aS1bZ50A2S0S4S4S19S2A2M1SbA2M2S1G1SbS1S19S2G0U8M3A4SeS59A1A4S0G2S1G1SbS1S19S2S4aS1bZ48A2G3A4S3dA4S3G2A1A3A3A4").
Definition O_glb (nx : sv) : sobj := ltac2:(tb__ "0|3|
S51S2aZ0M0Z8S0S4S4S19S2A2M1SbA2M2S1G1SbS1S19S2G0U8A4Vnx;A4S3G2A1A3A4").

Definition DEPTH_R : Z := 1536.

Definition F_T0 : list sprop := ltac2:(tb__ "0|2|
S5SdS61S3fA1S0SdS13PdM0Z3A2S0SdS11S10S52SeS4aS1bZa0A2A1SfG0A1M1A3A1S0SdS10S52G1S55S66SeZ50A1A2A3S3SdA1A3A3A3A3").
Definition F_T : list sprop := ltac2:(tb__ "0|0|
S5SdS31S0SdS11S10S52S1dSeZ0A1A3A1S3SdA1A3A3").
Definition F_Tn : list sprop := ltac2:(tb__ "0|1|
S5SdS31S0SdS11S10S52S1dSeZ0A1M0A3A1S0SdS13PceZ3A2S0SdS11S10S52S2cG0A3A1S0SdS18SeS5aA1S2aA2S3SdA1A3A3A3A3A3").

Definition cbC : sv := add vT (SLit 208).
Definition vSTKq : sv := SVar 142.
Definition regs3 : list sv := ltac2:(tb__ "0|1|
S5cS5dS0S4S2SbA2M0S1S2SbUaSeS1bA1A4S0G0S1S2SbU4SeS65A1A4S0G0S1S2SbUcS47A4S0G0S1S2SbUdS49A4S3G0A1A3A3A3A3A2").
Definition mkPre3 (objs : list sobj) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S5fS14S40S39S5bS12S9SbA1S5ScS0ScS60S5eA3Vobjs;A3VF;S34S8A9S3S4SbSbA2A1A2").

Definition PreQ3n : axst := ltac2:(tb__ "0|0|
S37S0ScS20S1dS24S23S3eA4S0ScS28SeZ0A1A1S0ScS1fS2cS2bS2aS3cA4S0ScS1eS0ScS30S48A1S3ScA1A3A3A3A3A3S2eA2").
Definition PreQ3e : axst := ltac2:(tb__ "0|1|
S37S0ScS20S1dS24S23S3eA4S0ScS28SeZ0A1M0A1S0ScS1fG0S2bS2aS3cA4S0ScS1eS3ScA1A3A3A3A3S2dA2").

Definition gsz : sv := add vGS vTS.
Definition F_le : sprop := ltac2:(tb__ "0|0|
S10S53SeS59A1S22A3").
Definition F_gt : sprop := ltac2:(tb__ "0|0|
S11S10S53SeS59A1S22A3A1").
Definition mkPost3 (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S5fS14Vpc;S5cS39Vru;A2S5bS12S9SbA1S5ScS0ScS60S5eA3Vobjs;A3VF;S58S8A9S3S4SbSbA2A1A2").
Definition ZQ : sv := SLit 0.
Definition PostQ3n : axst := ltac2:(tb__ "0|0|
S29S36S57S0ScS20S1cS1cS1cS1cA4S0ScS35S0ScS1fS55S2cS1dA2S2bS23S22A4S0ScS1eS0ScS30S24A1S3ScA1A3A3A3A3A3S5SdS2eS0SdS33S3SdA1A3A3A4").
Definition PostQ3e : axst := ltac2:(tb__ "0|0|
S29S36S57S0ScS20S1cS1cS1cS1cA4S0ScS35S0ScS1fS1dS24S23S22A4S0ScS1eS3ScA1A3A3A3A3S5SdS2dS0SdS33S3SdA1A3A3A4").

Definition re_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SbA2M0S1S2SbU5SfPb9A1A4S0G0S1S2SbU6SfPbaA1A4S0G0S1S2SbUaSeS1bA1A4S0G0S1S2SbUbS3dA4S0G0S1S2SbUeSfPc0A1A4S0G0S1S2SbUfSfPc1A1A4S0G0S1S2SbU10SfPc2A1A4S0G0S1S2SbU11SfPc3A1A4S3G0A1A3A3A3A3A3A3A3A3").
Definition ReQ3n : axst := ltac2:(tb__ "0|0|
S29S21S38S0ScS20S1cS1cS1cS1cA4S0ScS28SeZ100A1A1S0ScS1fS55S2cS1dA2S2bS23S22A4S0ScS1eS0ScS30S24A1S3ScA1A3A3A3A3A3S5SdS2eS0SdS32S3SdA1A3A3A4").
Definition ReQ3e : axst := ltac2:(tb__ "0|0|
S29S21S38S0ScS20S1cS1cS1cS1cA4S0ScS28SeZ100A1A1S0ScS1fS1dS24S23S22A4S0ScS1eS3ScA1A3A3A3A3S5SdS2dS0SdS32S3SdA1A3A3A4").

Definition run_Tn : list leafA := ltac2:(tb__ "0|0|
S54U258S0S19S21S0S19S27S3S19A1A3A3S26A3").
Definition run_Te : list leafA := ltac2:(tb__ "0|0|
S54U258S0S19S21S0S19S27S3S19A1A3A3S25A3").
Lemma run_Tn_eq : ltac2:(tb__ "0|0|
S4bSaS50A1S54U258S0S19S21S0S19S27S3S19A1A3A3S26A3S3bA3"). Proof. unfold run_Tn. reflexivity. Qed.
Lemma run_Te_eq : ltac2:(tb__ "0|0|
S4bSaS50A1S54U258S0S19S21S0S19S27S3S19A1A3A3S25A3S3aA3"). Proof. unfold run_Te. reflexivity. Qed.
Definition TsTn : list axst := ltac2:(tb__ "0|0|
S0S4dS42S0S4dS44S3S4dA1A3A3").
Definition TsTe : list axst := ltac2:(tb__ "0|0|
S0S4dS41S0S4dS43S3S4dA1A3A3").
Definition KEEP3 : list positive := ltac2:(tb__ "0|0|
S0S1aPc8S0S1aPc9S0S1aPcaS0S1aPcbS0S1aPccS0S1aPcdS0S1aPceS0S1aPcfS0S1aPd0S0S1aPd1S3S1aA1A3A3A3A3A3A3A3A3A3A3").
Lemma chk_Tn : ltac2:(tb__ "0|0|
S4bS6S62S3bS46S2fA3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_Te : ltac2:(tb__ "0|0|
S4bS6S62S3aS45S2fA3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma keep3_lt : ltac2:(tb__ "0|0|
S4bS6S67S1aS1aS64R1S34A2Lv;S2fA3S7A3"). Proof. reflexivity. Qed.
Lemma nxs3 : ltac2:(tb__ "0|2|
S4cS4cS4bS6S15S4eS26A1M0A1S8A3S63S56S16G0A1A2A2S4cS4bS6S15S4eS25A1M1A1S8A3S63S56S16G1A1A2A2A2").
Proof. repeat split; try reflexivity; unfold Pos.le; cbn; discriminate. Qed.
Lemma pre3_wf : ltac2:(tb__ "0|0|
S4cS4bS6S4fS26A1S7A3S4bS6S4fS25A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pre3_swf : ltac2:(tb__ "0|0|
S4cS4bS6S17S4eS26A1A1S7A3S4bS6S17S4eS25A1A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQ3_states.

(* [comment removed for export] *)
Module F0A_mstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "None"; "false"; "prod"; "nat"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sobj"; "cell"; "mkCell"; "FcsrFrm0"; "mkSS"; "SAlu"; "DUnknown"; "mkObj"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "NF"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates.FI"; "FACTSi"; "PREOBJSi"; "Lcut_i"; "REGS0i"; "stack_win_mid"; "OBJSi"; "regs_mid"; "Lregs_i"; "win_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "MIDPC"; "RT_i"; "L1i"; "L2i"; "L3i"; "L4i"; "MIDx"; "O_blkP"; "P0i"; "fi_cutpcs"; "fi_cuts"; "fi_vcuts"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit"; "O_inst"; "O_iaw"; "bytef"; "IA_LO"; "O_iaw_done"; "O_iaw_locked"; "inst_cells"; "wordf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "Wcan"; "ae_free"; "mkA"; "stack_win"; "A_globals"; "unwind_objs"; "V_DEPTH"; "V_FREE_A1"; "free_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "O_pga"; "O_pgb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit.
Import ListNotations.
Open Scope Z_scope.

Definition MIDPC : Z := 0x5e238.
Definition O_blkP : sobj := ltac2:(tb__ "0|0|
S12S9PcA1SaZ0A1S9PdA1S1ScA1S11A5").

Definition RT_i : list sobj := ltac2:(tb__ "0|0|
S0SbS4bS0SbS4cS1SbA1A3A3").

Section FI.
Variable W : list ulink.
Variable st : ustop.

Definition FACTSi : list sprop := ltac2:(tb__ "0|0|
S2S13S49VW;Vst;A2S48S47A1A3").

Definition OBJSi (win : sobj) (rt1 rt2 : list sobj) : list sobj := ltac2:(tb__ "0|0|
S2SbS2SbS0SbVwin;S2SbS44VW;A1S2SbS0SbS2eS1SbA1A3S43A3A3A3Vrt1;A3Vrt2;A3").
Definition REGS0i : list sv := ltac2:(tb__ "0|1|
S17S16S0S5S6S8A2M0S7S6S8U4SaS4aA1A4S0G0S7S6S8UbS9S46A1A4S1G0A1A3A3A2").

Definition P0i : axst := ltac2:(tb__ "0|1|
S41SfS40S3eA1S20S14SeS3S8A1S22S42S0SbS37Z0M0G0A2S28A3S0SbS36S1ScA1A1S1SbA1A3A3S1dS26S4A9S1S5S8S8A2A1A2").

Definition win_cells : list cell := ltac2:(tb__ "0|3|
S0ScSdSaN878A1Z8M0S9P27A1M1A3S0ScSdSaN870A1G0S9PbA1M2A3S0ScSdSaN868A1G0S9PcA1A3S0ScSdSaN860A1G0S9PaA1A3S0ScSdSaN858A1G0SaS27A1A3S0ScSdSaN38A1G0S9P29A1A3S0ScSdSaN30A1G0S9P28A1A3S0ScSdSaN28A1G0G1A3S0ScSdSaN20A1G0S9P26A1A3S0ScSdSaN18A1G0S9P1dA1A3S0ScSdSaN10A1G0S9P1cA1A3S0ScSdSaN8A1G0G2A3S1ScA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition stack_win_mid : sobj := ltac2:(tb__ "0|0|
S12S9PaA1S9S45A1SaZ0A1S25S11A5").

Definition Lregs_i (ra dst fin : Z) (s2 s3 : sv) : list sv := ltac2:(tb__ "0|0|
S0S8S9P14A1S0S8SaVra;A1S0S8S10S35S9PaA1SaN880A1A3S0S8S9P17A1S0S8SaS4aA1S0S8S9P19A1S0S8S9P1aA1S0S8S9P1bA1S0S8SaZ17db48A1S0S8SaS39A1S0S8SaVdst;A1S0S8SaZ0A1S0S8SaVfin;A1S0S8S9Pa0A1S0S8S9PaeA1S0S8S9PafA1S0S8S9Pb0A1S0S8S9P25A1S0S8Vs2;S0S8Vs3;S0S8S9P28A1S0S8S9P29A1S0S8S9P2aA1S0S8S9P2bA1S0S8S9P2cA1S0S8S9P2dA1S0S8S9P2eA1S0S8S9P2fA1S0S8S9P30A1S0S8S9P31A1S0S8S9P32A1S0S8S9P33A1S1S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition Lcut_i (pc ra dst fin : Z) (s2 s3 : sv) (lf : list sprop) : axst := ltac2:(tb__ "0|0|
S41SfVpc;S24Vra;Vdst;Vfin;Vs2;Vs3;A5S14SeS3S8A1S22S21S0SbS3bS28A3S0SbS36S1ScA1A1S1SbA1A3A3S2S13Vlf;S1dA3S26S4A9S1S5S8S8A2A1A2").
Definition L1i : axst := ltac2:(tb__ "0|2|
S1fZ6feb4Z6a324Z1702c8M0Z1702f0M1S9PbA1S9P27A1S38G0G1A2A7").
Definition L2i : axst := ltac2:(tb__ "0|2|
S1fZ6feb4Z6a33cZef2c8M0Z12f2c8M1S9PbA1SaZ40000A1S38G0G1A2A7").
Definition L3i : axst := ltac2:(tb__ "0|2|
S1fZ6fee8Z6a354Z12f300M0Z130080M1S9PbA1SaZ40000A1S3dG0G1A2A7").
Definition L4i : axst := ltac2:(tb__ "0|2|
S1fZ6feb4Z6a36cZ130080M0Z1702c8M1SaZ41000A1SaZ40000A1S38G0G1A2A7").

Definition regs_mid : list sv := ltac2:(tb__ "0|1|
S0S8S9P14A1S0S8SaS27A1S0S8S10S35S9PaA1M0SaN850A1A3S0S8S9P17A1S0S8SaS4aA1S0S8S9P19A1S0S8S9P1aA1S0S8S9P1bA1S0S8G0S0S8S9PcA1S0S8SaS39A1S0S8S9Pa1A1S0S8S9Pa2A1S0S8S9Pa3A1S0S8S9Pa4A1S0S8S9Pa5A1S0S8S9Pa6A1S0S8S9P25A1S0S8S9PbA1S0S8S9P27A1S0S8S9P28A1S0S8S9P29A1S0S8S9P2aA1S0S8S9P2bA1S0S8S9P2cA1S0S8S9P2dA1S0S8S9P2eA1S0S8S9P2fA1S0S8S9P30A1S0S8S9P31A1S0S8S9P32A1S0S8S9P33A1S1S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition MIDx : axst := ltac2:(tb__ "0|0|
S41SfS27S23S14SeS3S8A1S22S21S0SbS3aS28A3S0SbS36S3cA1S1SbA1A3A3S1dS26S4A9S1S5S8S8A2A1A2").

Definition PREOBJSi (win : sobj) : list sobj := ltac2:(tb__ "0|0|
S0SbVwin;S2SbS44VW;A1S2SbS0SbS2eS1SbA1A3S43A3A3A3").
Definition sa_i : sstate := ltac2:(tb__ "0|0|
SfS40S3eA1S20S14SeS3S8A1S1eS42A1S1dS15S4A9").
Definition sb_i : sstate := ltac2:(tb__ "0|1|
SfS40S3eA1S20S14SeS3S8A1S2SbS1eS42A1S0SbS37Z0M0G0A2S28A3A3S1dS26S4A9").
Definition sc_i : sstate := ltac2:(tb__ "0|1|
SfS40S3eA1S20S14SeS3S8A1S2SbS2SbS1eS42A1S0SbS37Z0M0G0A2S28A3A3S0SbS36S1ScA1A1S1SbA1A3A3S1dS26S4A9").
Definition stJ_i : sstate := ltac2:(tb__ "0|0|
SfS27S23S14SeS3S8A1S2SbS1eS21A1S0SbS3aS28A3A3S1dS26S4A9").
Definition Pre_mid : axst := ltac2:(tb__ "0|0|
S41SfS27S23S14SeS3S8A1S1eS21A1S1dS26S4A9S1S5S8S8A2A1A2").
End FI.

Definition fi_cuts (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|1|
S0S1cS2fS3fVn;A1M0Vst;A2S0S1cS29G0Vst;A2S0S1cS2aG0Vst;A2S0S1cS2bG0Vst;A2S0S1cS2cG0Vst;A2S1S1cA1A3A3A3A3A3").
Definition fi_cutpcs : list Z := ltac2:(tb__ "0|0|
S0S33Z6feb4S0S33Z6fee8S0S33S27S1S33A1A3A3A3").
Definition fi_cert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|0|
S1aS4eUbb8S30S4dS31Vn;Vst;A2S0S1cS2dS3fVn;A1Vst;A2S1S1cA1A3A6").
Definition fi_vcuts (n : nat) (st : ustop) : list vnodeA := ltac2:(tb__ "0|2|
S0S18S19S2fS3fVn;A1M0Vst;A2Z5SaZ0A1A3S0S18S19S29G0Vst;A2Z4S10S34SaZ1702f0A1S9Pa0A1M1A3A3S0S18S19S2aG0Vst;A2Z3S10S34SaZ12f2c8A1G1A3A3S0S18S19S2bG0Vst;A2Z2S10S34SaZ130080A1G1A3A3S0S18S19S2cG0Vst;A2Z1S10S34SaZ1702c8A1G1A3A3S1S18A1A3A3A3A3A3").
Definition fi_ecert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|1|
S1bS4eUbb8S30S4dS32Vn;Vst;A2S0S18S19S2dS3fVn;A1Vst;A2Z0M0SaG0A1A3S1S18A1A3A6").
End F0A_mstates.

(* [comment removed for export] *)
Module SegQpieceM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "agree_below"; "ss_next"; "eval"; "rm"; "rw"; "sv_below"; "sv_eqb"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "chk_leavesM"; "keepsM"; "mapon"; "entsM"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "pair"; "andb"; "false"; "fst"; "option"; "snd"; "Some"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "runA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece.
Import ListNotations.
Open Scope Z_scope.

Definition vmap : Type := list (positive * sv).

Definition mapon (nx : positive) (s : wsub) (M : vmap) : bool := ltac2:(tb__ "0|2|
S2aS1eS4S5A2M0G0S20SdS35Vs;S22S4S5R1A3A2S24S4S5R1A3M1A2ScVnx;G1A2A2Lp;VM;A3").
Lemma mapon_get : ltac2:(tb__ "0|0|
S4S37S15S4S5S0S1bS19R5R4R3A3S1dA3S29S1eS4S5A2S1fS4S5R3R2A4R4A3S1S0S5S35R6R4A2R3A3S0S1bScR7R3A2S1dA3A2F_;F_;Fe;Fv;FM;Fs;Fnx;").
Proof.
  intros nx s M v e H Hin. unfold mapon in H. pose proof (proj1 (forallb_forall _ _) H (v, e) Hin) as X. cbn [fst snd] in X.
  apply andb_prop in X as [X1 X2]. split; [apply sv_eqb_sound; exact X1 | exact X2].
Qed.

Fixpoint chk_leavesM (nx : positive) (l : list leafA) (Ts : list (axst * vmap)) : bool :=
  match l, Ts with
  | [], [] => true
  | L :: l', (T, M) :: Ts' => entsI (la_state L) T && mapon nx (infer_sub NPRE (ax_S (la_state L)) (ax_S T)) M && chk_leavesM nx l' Ts'
  | _, _ => false
  end.
Definition chkNM (nx : positive) (l : list leafA) (Ts : list (axst * vmap)) : bool := ltac2:(tb__ "0|1|
S1cS11A1M0S1bLl;Vl;S21S11G0S17Vnx;Vl;VTs;A3Ll1;Ll0;X1cx2").
Lemma chk_leavesM_In : ltac2:(tb__ "0|2|
S4S1cS11A1S1cS1eSfS15A2M0A1S11S0S1bS17R4R3R2A3S1dA3S29S11R2R4A3S2SfSfS2S15S15S1S29G0S1fSfS15R2R1A4R6A3S1S0S1bS38S12R5A1M1R2A2S1dA3S0S1bS19R8S2fS27S10G1A1S10R2A1A3R1A3S1dA3A2A2LM;A2LT;A2F_;F_;FL;FTs;Fl;Fnx;").
Proof.
  induction l as [|L0 l IH]; intros [|[T M] Ts] L H Hin; cbn in H; try discriminate H; [destruct Hin|].
  apply andb_prop in H as [H HR]. apply andb_prop in H as [HE HI]. destruct Hin as [<-|Hin].
  - exists T, M. split; [left; reflexivity | split; [exact HE | exact HI]].
  - destruct (IH Ts L HR Hin) as (T' & M' & HT' & HE' & HI'). exists T', M'. split; [right; exact HT' | split; [exact HE' | exact HI']].
Qed.
Lemma chkNM_ne : ltac2:(tb__ "0|1|
S4S1cS11A1M0S1cS1eSfS15A2A1S0S1bS16R3R2R1A3S1dA3S3S0G0R3S26S11A1A3A1F_;FTs;Fl;Fnx;"). Proof. intros nx [|L l] Ts H; [discriminate H | discriminate]. Qed.
Lemma chkNM_leaves : ltac2:(tb__ "0|0|
S4S1cS11A1S1cS1eSfS15A2A1S0S1bS16R3R2R1A3S1dA3S0S1bS17R4R3R2A3S1dA3F_;FTs;Fl;Fnx;"). Proof. intros nx [|L l] Ts H; [discriminate H | exact H]. Qed.

Definition keepsM (M : vmap) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|0|
S1S7S27Vrho;Vrho';A3S4S5S29S1eS4S5A2S1fS4S5R2R1A4VM;A3S0S30Q40A1SbVrho';R3A2S9Vrho;R2A2A3F_;Fe;Fv;A2").

Section PieceM.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (Ts : list (axst * vmap)).
Hypothesis RUNL : ltac2:(tb__ "0|0|
S0S1cS11A1S28Vfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S0S1bS16S8S10VPre;A1A1Vl;VTs;A3S1dA3").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S1bSeS10VPre;A1A1S21A3").
Hypothesis HNX : ltac2:(tb__ "0|0|
S39S27S8S10VPre;A1A1A2").

Lemma pieceM_run_some : ltac2:(tb__ "0|1|
S0S23S1cS11A1M0A1S13S14Vfuel;Vcuts;VPre;S1dA5S25G0Vl;A2A3").
Proof using RUNL CHK. pose proof RUNL as R. unfold runA in R. destruct (sym_runA segsA fuel cuts Pre true) as [l'|]; [congruence|]. exfalso. apply (chkNM_ne _ l Ts CHK). symmetry. exact R. Qed.

Lemma leafM_keeps : ltac2:(tb__ "0|1|
S11SfS15S6S6S0S1bS38S12R5A1R4A2S1dA3S0S1bS19S8S10VPre;A1A1M0S2fS27S10S12R6A1A1S10R5A1A3R4A3S1dA3S7G0R4R3A3S18R6R5S36R4S2fS27S10S12R8A1A1S10R7A1A3A2A3F_;F_;F_;FrhoL;Frho;FM;FT;FL;").
Proof using HNX.
  intros L T M rho rhoL HE HM Hag. split.
  - eapply agree_below_trans; [exact (agree_below_le _ _ _ _ HNX Hag)|]. apply rho_sub_agree.
    unfold entsI in HE. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [HE _]. apply andb_prop in HE as [_ HIb]. exact HIb.
  - intros v e Hin. destruct (mapon_get _ _ M v e HM Hin) as [E B]. cbn [rho_sub rw]. rewrite E. symmetry. exact (eval_agree _ rho rhoL e Hag B).
Qed.

Theorem piece_soundM : ltac2:(tb__ "0|0|
S2cS31OF_;S6S1cS30Q40A1A1S34S2eS14R4R5A3S2dS14S27R6A3SfS15S6S29S1eSfS15A2S1fSfS15R3R2A4VTs;A3S18R3R9R2A3S33S14RbS2bS14RcR5R3R9A5R8A4F_;F_;Frho';FM;FT;S33S14R7S2bS14R8VPre;R6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;").
Proof using RUNL CHK HLEN HNX.
  intros J ok rho tp Q HOK HST HC. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp pieceM_run_some HOK HLEN (stableA_mono segsA NPRE _ J HNX HST)).
  - apply triple_LQA_of_leaves. intros L0 rhoL Hin Hag.
    destruct (chk_leavesM_In _ l Ts L0 (chkNM_leaves _ l Ts CHK) Hin) as (T & M & HT & HE & HM).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (HC T M (rho_sub rhoL (infer_sub NPRE (ax_S (la_state L0)) (ax_S T))) HT)].
    + intros w Hw. exact (proj1 (ent_SPA J (la_state L0) T rhoL tp w HE HST Hw)).
    + exact (leafM_keeps L0 T M rho rhoL HE HM Hag).
Qed.
Theorem piece_completeM : ltac2:(tb__ "0|0|
S2cS6S1cS30Q40A1A1S31OF_;S2dS14S27R4A3SfS15S6S29S1eSfS15A2S1fSfS15R3R2A4VTs;A3S18R3R8R2A3S32S14S2bS14RaR5R3R8A5R7A3F_;F_;Frho';FM;FT;S32S14S2bS14R6VPre;R5R4A5R3A3F_;F_;FQ;Ftp;Frho;FJ;").
Proof using RUNL CHK HLEN HNX.
  intros J rho tp Q HST HC. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN (stableA_mono segsA NPRE _ J HNX HST) pieceM_run_some).
  - apply etriple_LQA_of_leaves. intros L0 rhoL Hin Hag.
    destruct (chk_leavesM_In _ l Ts L0 (chkNM_leaves _ l Ts CHK) Hin) as (T & M & HT & HE & HM).
    eapply etriple_conseq; [| intros w Hw; exact Hw | apply (HC T M (rho_sub rhoL (infer_sub NPRE (ax_S (la_state L0)) (ax_S T))) HT)].
    + intros w Hw. exact (proj1 (ent_SPA J (la_state L0) T rhoL tp w HE HST Hw)).
    + exact (leafM_keeps L0 T M rho rhoL HE HM Hag).
Qed.
End PieceM.

Definition entsM (L T : axst) (M : vmap) : bool := ltac2:(tb__ "0|1|
S20S38VL;VT;A2S2aS1eS4S5A2M0G0SdS35S2fS27S10VL;A1S10VT;A1A3S22S4S5R1A3A2S24S4S5R1A3A2Lp;VM;A3A2").
Lemma entM_SPA : ltac2:(tb__ "0|1|
S2cSfSfS15S6S1cS30Q40A1M0A1S31S0S1bS1aR6R5R4A3S1dA3S2dS14S27R8A3S2bS14R9R8R5R4R3A6S36R6S2fS27S10R9A1S10R8A1A3A2S6S1S2bS14RbR9R1R6R5A6S1S7S27R7R1A3S1S4S5S29S1eS4S5A2S1fS4S5R2R1A4RaA3S0G0SbR4R3A2S9RaR2A2A3F_;Fe;Fv;S0G0S23S30Q8A1A1F_;SaR1A1SaR7A1A3A2A2A2Trho';F_;F_;F_;Fw;Ftp;Frho;FM;FT;FL;FJ;").
Proof.
  intros J L T M rho tp w H HST HS rho'. unfold entsM in H. apply andb_prop in H as [HE HM].
  destruct (ent_SPA J L T rho tp w HE HST HS) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. split; [|reflexivity].
  intros v e Hin. pose proof (proj1 (forallb_forall _ _) HM (v, e) Hin) as X. cbn [fst snd] in X. apply sv_eqb_sound in X.
  unfold rho'. cbn [rho_sub rw]. rewrite X. reflexivity.
Qed.
End SegQpieceM.

