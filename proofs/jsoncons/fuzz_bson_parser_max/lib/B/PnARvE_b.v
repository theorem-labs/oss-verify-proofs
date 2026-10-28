(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVE.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Definition dregs (R R3 : bvmap 5 word) (sp fb t F : Z) : Prop :=
  getr R3 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R3 (reg 3) = getr R (reg 3) /\ getr R3 (reg 4) = getr R (reg 4)
  /\ getr R3 (reg 8) = Z_to_bv 64 sp /\ getr R3 (reg 9) = Z_to_bv 64 (sp - 160) /\ getr R3 (reg 10) = Z_to_bv 64 18 /\ getr R3 (reg 13) = Z_to_bv 64 (t - 1)
  /\ getr R3 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R3 (reg 19) = Z_to_bv 64 F /\ getr R3 (reg 20) = Z_to_bv 64 (fb + 464)
  /\ getr R3 (reg 21) = Z_to_bv 64 (fb + 1024) /\ getr R3 (reg 22) = Z_to_bv 64 (fb + 432) /\ getr R3 (reg 23) = Z_to_bv 64 t
  /\ getr R3 (reg 26) = Z_to_bv 64 2147450880 /\ getr R3 (reg 27) = Z_to_bv 64 F.

(* [comment removed for export] *)
Definition at_disp : Prop :=
  forall K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3,
    rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t ->
    rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
    rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr ->
    dregs R R3 sp fb t F -> spill M3 sp F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.

Theorem rv_entry : at_disp -> PNRAa.read_value_spec L ar HI.
Proof.
  intros DISP. unfold PNRAa.read_value_spec, PNRA.read_value_spec, PNRA.brun_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  destruct ARGS as (A10 & A11 & A13 & (w & Hw & A12) & ROOM).
  assert (ARGS : rv_args R fb s sm w) by (exact (conj A10 (conj A11 (conj A13 (conj A12 ROOM))))).
  assert (CTX : rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *. change (28672 / 8) with 3584 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl13 in A13.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 28672 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 28672 224 HH ASTK ltac:(lia)) as (SL160 & SH160 & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 28672 160 HH ASTK ltac:(lia)) as (_ & _ & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  assert (QA : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= w < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 Hw; unfold op, ov, oec in *; lia).
  destruct QA as (QAs & QAo & QAv & QAe & QAw).
  LeanFeed.pfeed P (PNARVTP.awvA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 35%nat => w | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption | clear - SL160 SHI SPT; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T22 & T23 & T26
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_read_value PMA.AN) with 0xaff88.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xaff88 R1 0x5df30 M1v (fun a => sp - 160 <= a < sp - 160 + 160) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 28672 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 28672 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 28672 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M M1 (fun a => sp - 160 <= a < sp - 160 + 160) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 28672 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 28672 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 28672 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 3 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 8 FF LK 3 FRM); [clear; lia| right; right; left; reflexivity]).
  change 0x5df30 with (PMA.SM_PC 3).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 3 LBX (PNM.bparser_own s) FF LK cr Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb0004 ltac:(right; right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 160) with (sp + (-10) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. change (512 - 8) with 504 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 28672 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 28672 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 3, sp - 160 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 28672 160 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 op) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 oec) by (rewrite (R2c 21%nat) by inl; exact T26).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 ov) by (rewrite (R2c 22%nat) by inl; exact T22).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 w) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T21).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 504) fl) by (replace (F + 504) with (F + 512 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64) by (clear - GFR GFLR; lia).
  destruct Q0 as (Q0f & Q0g).
  assert (Q1 : 140735332487392 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Q2 : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  assert (Q3 : 6905856 <= F <= 140737488354816) by (clear - GFR; lia).
  assert (Q4 : (sp - 160) + 160 <= F \/ F + 512 <= (sp - 160)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  assert (Q8 : (65536 + 6840320 <= F \/ F + 512 <= 65536)) by (left; clear - GFR; lia).
  assert (Q9 : (65536 + 6840320 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= 65536)) by (left; clear - GFR; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
  assert (Q10 : (65536 + 6840320 <= fl \/ fl + 1 <= 65536)) by (left; clear - GFLR; lia).
  LeanFeed.pfeed P (PNARVTP.awvB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 35%nat => w | 36%nat => oec | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y19 & Y27
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SH0 & HPC & HDESC & HMAG & SAVF & D24).
  set (W3 := fun a => (sp - 128 <= a < sp - 128 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb0004 R3 0xb016c M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia
                    | intros X; apply Hn; right; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|[X|X]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 3 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|[X|X]]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 28672 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 28672 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|[X|X]]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 160) (own sp R) F 3 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 28672 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 28672 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 28672 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 28672 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 3 / 8) with 64. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 64 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 28672 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 28672 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV4 : avis H2 (F / 8 + 2147450880) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 64); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044352 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450880) 241 AV4 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450880) 241) by (apply (proj1 UV); exact SH0). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNBKA.pre_after_call L ar LB FF sp 28672 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold rv_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| exact I]. }
  assert (SAVF3 : L5.u64_at RSEGS M3 (sp - 128) F).
  { pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (_ & _ & _ & _ & _ & _ & SVr3).
    apply (SVr3 (sp - 128) F ltac:(clear; lia) ltac:(clear; lia)). fold H2 in HID3. rewrite HID3. rewrite VIS3. exact SAVF. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  apply (DISP K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 fx3 R3 M3 model3 CTX G LM3); [| exact SAVF3| exact EC3].
  unfold dregs. split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [exact R3gp|]. split; [exact R3tp|].
  split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|]. split; [exact Y10|]. split; [exact Y13|].
  split; [exact Y18|]. split; [exact Y19|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|]. split; [rewrite (KS3 21%nat) by inl; exact B21R|].
  split; [rewrite (KS3 22%nat) by inl; exact B22R|]. split; [rewrite (KS3 23%nat) by inl; exact B23R|]. split; [rewrite (KS3 26%nat) by inl; exact B26R|]. exact Y27.
Qed.

End WithHeap.
End PNARVE.
