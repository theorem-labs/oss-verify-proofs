(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop.

(* [comment removed for export] *)
Module StartHandoffBlocks.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "or"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "list"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "alloc_top"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "q12x"; "LIMz"; "m16"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart"; "GMe"; "ZLOW"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "kHighMemBeg"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "m10"; "m11"; "m8"; "m9"; "n7"; "n9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5"; "m12"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "rhoOK"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7 Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac blia := unfold SHADOW_BAND_LO, SHADOW_BAND_HI, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, kHighMemBeg in *; lia.

Lemma LIMz_le_q12x : ltac2:(tb__ "0|0|
S8S0Z0R1A2S0S1cR2A1S1bR2A1A2F_;Fx;").
Proof.
  intros x Hx. unfold LIMz, q12x, shx.
  pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)).
  assert ((x - x mod 4096) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma LIMz_lt_top : ltac2:(tb__ "0|0|
S8S0Z7fff80000000R1A2S0S1S1cR2A1S4Z2Z14A2A2S3R2Z800000A2A2F_;Fx;").
Proof.
  intros x Hx. unfold LIMz.
  pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert ((x - x mod 4096) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S8S9S0Z0R1A2S2R1S4Z2Z40A2A2A2SbS8S6Q40M0S5G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Section Blocks.
Variables (m : Model) (a1 a2 : word).
Hypothesis Hres : ltac2:(tb__ "0|1|
SbS12S11S7Q40A1M0G0A2A1S18S15Vm;A1A1S23S24A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
SbS12S11S7Q40M0A1M1G1A2M2A1S17S15Vm;A1A1S10G2SfG1G1Va2;S5G0Z38e000A2A4S10G2SfG1G1Va1;S5G0Z10000A2A4S10G2SfG1G1S5G0Z2008fff7000A2S5G0Zdfff0001000A2A4S10G2SfG1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S10G2SfG1G1S5G0Z7fff7000A2S5G0Z10000000A2A4S13G2A1A3A3A3A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S9S0Z643000S6Q40Va1;A2M0A2S9SaS0S1G0Z10000A2M1S1aA2S0S19G0A2A2S0G1S16S15Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S9S0Z643000S6Q40Va2;A2M0A2S9SaS0S1G0Z38e000A2M1S1aA2S0S19G0A2A2S0G1S16S15Vm;A1A1A2A2A2").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S14S5Q40Z0A2Vm;S29VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S14S5Q40Z0A2S27Vm;VP;A2S2aVb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S28Vm;VP;Vb4;A3S5G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S25Vm;VP;Vb4;Vb5;A4S5G0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S26Vm;VP;Vb4;Vb5;Vb6;A5S5G0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S2bVm;VP;Vb4;Vb5;Vb6;Vb7;A6S5G0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S2cVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S5G0Z1000A2Vb9;A4").
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : ltac2:(tb__ "0|0|
SbS8S16S15Vm;A1A1S3Vx;Z800000A2A3").
Hypothesis HPL10 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S1dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S5G0S1eA2Vb10;A4").

Variables (rho : valuation) (b12 b13 b14 : word).
Hypothesis HROK : ltac2:(tb__ "0|0|
S2dVm;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vrho;Ad").
Hypothesis H159 : rw rho 159%positive = b12.
Hypothesis H160 : rw rho 160%positive = b13.
Hypothesis H161 : rw rho 161%positive = b14.
Hypothesis W12 : ltac2:(tb__ "0|2|
S9SaS0S1S6Q40Vb12;A2M0Z100000A2M1S1aA2S0S19G0A2A2S0G1S3Vx;Z800000A2A2A2").
Hypothesis W13 : ltac2:(tb__ "0|3|
S9SaS0S1S6Q40Vb13;A2M0Z800000M1A2M2S1aA2S0S19G0A2A2S0G2S3Vx;G1A2A2A2").
Hypothesis W14 : ltac2:(tb__ "0|2|
S9SaS0S1S6Q40Vb14;A2M0Z1000A2M1S1aA2S0S19G0A2A2S0G1S3Vx;Z800000A2A2A2").

Local Notation blocks16 := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.blocks16 m a1 a2 Hres Hmaps Htop Ha1 Ha2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation b10_facts := (Start7.b10_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) (only parsing).
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).

Definition prof (rho : valuation) (e : sv) (sz : Z) : Prop :=
  let b := bv_unsigned (eval rho e) in
  ((b + sz <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= b) /\ b + sz <= x - 8388608)
  \/ (0x2008fff7000 <= b /\ b + sz <= LIMz x)
  \/ (e = SLit LOWPG /\ sz = 0x4600) \/ (e = SLit 0x7fffc000 /\ sz = 4096) \/ (e = SLit 0x80015000 /\ sz = 4096).

Lemma GM_prof : forall e sz, In (e, sz) GMe -> prof rho e sz.
Proof.
  intros e sz Hin. pose proof HROK as (HV & H36 & H77 & H78 & H83 & Hx1 & V35 & _).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  unfold GMe, G24, G23b, G22b, G18, G17 in Hin. rewrite <- !app_assoc in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  -
    assert (Hin14 : In (e, sz) G14b) by (unfold G14b; apply in_app_iff; left; exact Hin).
    destruct (blocks16 rho HV H36 H77 H78 e sz Hin14) as [Hb|(-> & -> & Hl & Hh)].
    + left. split; [exact Hb|].

      pose proof P_facts as (Pal & Pceil & _ & PLB & _). pose proof RI_val as RV. pose proof RI_range as (R1 & R2 & R3). pose proof SB_val as SB.
      pose proof b4_facts as (_ & _ & C4 & _). pose proof b5_facts as (_ & _ & _ & C5 & _). pose proof (b6_facts) as (_ & _ & C6 & _).
      pose proof b7_facts as (_ & _ & C7 & _). pose proof b8_facts as (_ & _ & C8 & _).
      pose proof Ha1 as (_ & _ & C1). pose proof Ha2 as (_ & _ & C2). rewrite Hxtop in *.
      unfold G13b, G12b, G11c in Hin. rewrite <- !app_assoc in Hin. cbn [List.app In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; cbn [eval].
      * rewrite H27. lia.
      * rewrite H28. lia.
      * unfold ri30. cbn [eval]. rewrite H30. pose proof (urange (spacebeg P)). rewrite U_add_small by lia. lia.
      *
        pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.priZ_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL rho HV) as (PR1 & _). rewrite Hx1 in PR1.
        unfold shRI_base. cbn [eval]. pose proof (urange (rw rho 31%positive)). unfold priZ in PR1.
        pose proof (LIMz_lt_top x ltac:(lia)). rewrite U_add_small by lia. lia.
      * rewrite H33. lia.
      * rewrite H34. lia.
      * rewrite H36. lia.
      * rewrite H77. lia.
    + right. left. rewrite Hx1 in Hl. split; [exact Hh | exact Hl].
  - cbn [List.app In] in Hin. pose proof b10_facts as (_ & L2 & L3 & _). unfold Start7.TOPz in L3.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-|]); [..|destruct Hin]; unfold prof; cbv zeta; cbn [eval];
    first [ left; rewrite H83; split; [exact L2 | lia]
          | left; rewrite H159; exact W12
          | left; rewrite H160; exact W13
          | left; rewrite H161; exact W14
          | right; right; left; split; reflexivity
          | right; right; right; left; split; reflexivity
          | right; right; right; right; split; reflexivity ].
Qed.

Lemma q12x_lo : ltac2:(tb__ "0|1|
S9S0Z10006fef9000S1bVx;A1M0A2S0G0S22A2A2").
Proof.
  clear - Hx. unfold q12x, shx, kHighMemBeg.
  pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)).
  assert (17591917608960 <= x / 8) by (apply Z.div_le_lower_bound; lia).
  assert (x / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
  split; lia.
Qed.

Lemma GM_low : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S20R1A1ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof, ZLOW in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.

Lemma GM_high : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S9S0S1bVx;A1R1A2S2R1S22A2A2ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.

Lemma GM_argf : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S9S0Vx;R1A2S2R1S4Z2Z2fA2A2A2ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.
End Blocks.
End StartHandoffBlocks.

(* [comment removed for export] *)
Module StartMainFds.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_fds"; "m_fs"; "Model"; "FdEntry"; "VmMaps"; "vm_add_lazy"; "vm_forget_range"; "with_vmmaps"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartMainFds"; "FF"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "out18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "eager_model"; "lazy_none_model"; "lazy_rw_model"; "null_none_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3"; "null_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "Mmain"; "mS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Definition FF (f : Model -> Model) : Prop := ltac2:(tb__ "0|1|
S4S1S0ScSdSbQ40A1S5A2A1S2Vf;R1A1M0A1S2R1A1A3S0SeS3G0A1S3R1A1A3A2Fmd;").
Lemma FF_comp : ltac2:(tb__ "0|2|
S4S4F_;M0G0SfR2A1M1G1SfS4R5R4R1A1A1Lmd;A1F_;F_;Fg;Ff;").
Proof. intros f g Hf Hg md. destruct (Hf (g md)) as [A B]. destruct (Hg md) as [C D]. rewrite A, B, C, D. auto. Qed.
Lemma FF_with_vmmaps : ltac2:(tb__ "0|0|
S6SfS9R1A1A1Fh;"). Proof. intros h md. destruct md; split; reflexivity. Qed.
Lemma FF_vm_add_lazy : ltac2:(tb__ "0|1|
SbQ40A1M0G0SfS7R2R1A2A1Fn;Fa;"). Proof. intros a n md. destruct md; split; reflexivity. Qed.
Lemma FF_vm_forget_range : ltac2:(tb__ "0|0|
SaSaSfS8R2R1A2A1Fhi;Flo;"). Proof. intros lo hi md. destruct md; split; reflexivity. Qed.
Lemma FF_lazy_rw : ltac2:(tb__ "0|0|
SaSaSfS15R2R1A2A1Fn;Fa;"). Proof. intros a n md. unfold lazy_rw_model. destruct md; split; reflexivity. Qed.
Lemma FF_lazy_none : ltac2:(tb__ "0|0|
SaSaSfS14R2R1A2A1Fn;Fa;"). Proof. intros a n md. unfold lazy_none_model. destruct md; split; reflexivity. Qed.
Lemma FF_null_none : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S16R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold null_none_model. destruct md; split; reflexivity. Qed.
Lemma FF_eager : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S13R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold eager_model. destruct md; split; reflexivity. Qed.
Lemma FF_null_rw : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S17R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold null_rw_model. destruct md; split; reflexivity. Qed.
Lemma FF_munmap : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S1aR3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;").
Proof. intros md a n. unfold munmap_model, with_mmap_destroyed. destruct md; split; reflexivity. Qed.
Lemma FF_fixed_rw : ltac2:(tb__ "0|2|
SbQ40A1M0S4G0G0S1S0ScSdG0S5A2A1S2S11R4R3R2R1A4M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;Ffl;").
Proof. intros fl md a n. unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b fl); destruct md; split; reflexivity. Qed.
Lemma FF_mprotect : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S10R3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;").
Proof. intros md a n. unfold mprotect_model_next. destruct md; split; reflexivity. Qed.

Lemma FF_mS : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S19R3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fa2;Fa1;Fm;").
Proof.
  intros m a1 a2. unfold StartTop.mS, StartTop.mA1, StartTop.mB, m6, m5, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m3, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m2.
  destruct (FF_eager 0x38e000 (eager_model 0x10000 (lazy_rw_model 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) a1) a2) as [-> ->].
  destruct (FF_eager 0x10000 (lazy_rw_model 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) a1) as [-> ->].
  destruct (FF_lazy_rw 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) as [-> ->].
  destruct (FF_lazy_none 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m)) as [-> ->]. apply FF_lazy_rw.
Qed.
Ltac ffstep := first
  [ rewrite (proj1 (FF_eager _ _ _)) | rewrite (proj2 (FF_eager _ _ _))
  | rewrite (proj1 (FF_null_none _ _ _)) | rewrite (proj2 (FF_null_none _ _ _))
  | rewrite (proj1 (FF_null_rw _ _ _)) | rewrite (proj2 (FF_null_rw _ _ _))
  | rewrite (proj1 (FF_munmap _ _ _)) | rewrite (proj2 (FF_munmap _ _ _))
  | rewrite (proj1 (FF_fixed_rw _ _ _ _)) | rewrite (proj2 (FF_fixed_rw _ _ _ _))
  | rewrite (proj1 (FF_mprotect _ _ _)) | rewrite (proj2 (FF_mprotect _ _ _))
  | rewrite (proj1 (FF_with_vmmaps _ _)) | rewrite (proj2 (FF_with_vmmaps _ _))
  | rewrite (proj1 (FF_vm_forget_range _ _ _)) | rewrite (proj2 (FF_vm_forget_range _ _ _))
  | rewrite (proj1 (FF_vm_add_lazy _ _ _)) | rewrite (proj2 (FF_vm_add_lazy _ _ _))
  | rewrite (proj1 (FF_mS _ _ _)) | rewrite (proj2 (FF_mS _ _ _)) ].
Lemma Mmain_fds : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0G0G0G0G0G0G0G0SaG0S12G0G0G0S1S0ScSdG0S5A2A1S2S18R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A10M1A1S2R10A1A3S0SeS3G1A1S3R10A1A3A2Fb14;Fb13;Fb12;Fo;Fb10;Fx;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fa2;Fa1;Fm;").
Proof.
  intros. unfold StartTop.Mmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22, Start7.out18_model, out0_model, out1_model, mgrant, mf_exp, mf_res, mg_dead, mg_ok, mg,
    Start7.mE, m17, m16, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.mF, m15, m14, m13, m12, m11, m10, m9, m8, m7.
  destruct o as [[|a]|[| | |a]|[| | |a] g]; cbn beta iota; split; repeat ffstep; reflexivity.
Qed.
End StartMainFds.

