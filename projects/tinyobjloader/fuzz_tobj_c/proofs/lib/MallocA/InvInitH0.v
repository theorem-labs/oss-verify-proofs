(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "leb"; "sub"; "div"; "mul"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "false"; "bool"; "option"; "andb"; "list"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ob_base"; "ob_hi"; "ob_lo"; "rw"; "sobj"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "lit_small"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitH0"; "fsq"; "bo_ok"; "fse"; "fsn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitF"; "band_out"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry InvInitF.
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
S0S0S13S0S5R2Z1000M0A2Z0M1A3S3Z646000R3A2S3S4R4Zb09000M2A2R3A2S3R4Z7fffff800000A2S14S3S4R6G2A2Z7fff7000A2S3Z10007fff8000M3R6A2A2S12S13S0S5S1eR7A1M4G0A2G1A3S12S3G4S1cS4R7Z9000A2A1A2S12S3S1cS4R7G2A2A1S4G4S9G0SaS21R7A1A1M5A2A2M6A2S12S3G5Z161A2S12S3Z800c1000G4A2S12S3G6S4S1cR6A1G0A2A2S14S3G6Z8fff7000A2S12S3Z2008fff7000G4A2S3G6G3A2A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;Ftop;FF;").
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
  assert (FLO : 822272 <= f) by (unfold f; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Hlo) as D; change (6578176 / 8) with 822272 in D; exact D).
  split; [unfold s1 in *; lia|]. split; [unfold s1, s2 in *; lia|].
  destruct Hband as [HB|HB].
  - left. assert (f + 1446400 <= 268434944) by (rewrite EF in HB; lia). unfold s1, s2 in *. lia.
  - right. assert (2199090364416 <= f) by (unfold f; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) HB) as D; change (17594333495296 / 8) with 2199291686912 in D; lia).
    unfold s1, s2 in *. lia.
Qed.

Definition bo_ok (vs : list positive) (o : sobj) : bool := ltac2:(tb__ "0|6|
S15SdLx;S16Vo;A1S0S0SdLz;R1SeS0A1SdLx;M0S1dS18Vo;A1A1M1S0G0S1dS17Vo;A1A1S0SfS6Z0R2A2S6R1Z646000A2A2Lhi;ScXex2Llo;ScXex2S1ScLp;M2G2X0x3Lz;S1G0G1S0SfS26S1S27R2A1Vvs;A3S6N100000R1A2A2Llo;ScXex2Li;S22S15S15ScLb;La;M3Lop;M4G4S23G3Lop;M5G5SdS2S15ScLa;Lw;Lsgn;S1S15S0ScLk;Li;Ll;X15x8").
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
