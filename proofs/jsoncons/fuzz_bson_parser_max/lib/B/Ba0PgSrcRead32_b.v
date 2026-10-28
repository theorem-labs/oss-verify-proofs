(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadEB_b Ba0PgSrcReadA0f_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRD32.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Definition vS (R0 R2 : bvmap 5 word) (sp qc de os p k ois F fl : Z) : nat -> Z := fun i =>
  match i with
  | 1%nat => bv_unsigned (getr R0 (reg 1)) | 2%nat => sp | 8%nat => bv_unsigned (getr R0 (reg 8)) | 9%nat => bv_unsigned (getr R0 (reg 9))
  | 18%nat => bv_unsigned (getr R0 (reg 18)) | 19%nat => bv_unsigned (getr R0 (reg 19)) | 20%nat => bv_unsigned (getr R0 (reg 20))
  | 21%nat => bv_unsigned (getr R0 (reg 21)) | 22%nat => bv_unsigned (getr R0 (reg 22)) | 23%nat => bv_unsigned (getr R0 (reg 23))
  | 24%nat => bv_unsigned (getr R0 (reg 24)) | 25%nat => bv_unsigned (getr R0 (reg 25)) | 26%nat => bv_unsigned (getr R0 (reg 26))
  | 27%nat => bv_unsigned (getr R0 (reg 27))
  | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | 45%nat => ois | 50%nat => F / 32 | 51%nat => fl
  | 61%nat => bv_unsigned (getr R2 (reg 1)) | 62%nat => bv_unsigned (getr R2 (reg 5)) | 63%nat => bv_unsigned (getr R2 (reg 6))
  | 64%nat => bv_unsigned (getr R2 (reg 7)) | 65%nat => bv_unsigned (getr R2 (reg 11)) | 66%nat => bv_unsigned (getr R2 (reg 12))
  | 67%nat => bv_unsigned (getr R2 (reg 13)) | 68%nat => bv_unsigned (getr R2 (reg 14)) | 69%nat => bv_unsigned (getr R2 (reg 15))
  | 70%nat => bv_unsigned (getr R2 (reg 16)) | 71%nat => bv_unsigned (getr R2 (reg 17)) | 72%nat => bv_unsigned (getr R2 (reg 28))
  | 73%nat => bv_unsigned (getr R2 (reg 29)) | 74%nat => bv_unsigned (getr R2 (reg 30)) | 75%nat => bv_unsigned (getr R2 (reg 31))
  | _ => 0
  end.

Lemma one_cell (P : Z -> Prop) a : (forall j, 0 <= j < 1 -> P (a + j)) -> P a.
Proof. intros X. specialize (X 0 ltac:(lia)). rewrite Z.add_0_r in X. exact X. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma srd_entry_sm : PGSRDK.srd_entry_body_T L ar HI 0 -> PGSA.src_read_specG_al RSEGS PMA.AD L ar HI PNRA.FCB 0.
Proof using LY HIok ICok ILY.
  intros EB. unfold PGSA.src_read_specG_al, PGSA.src_specG.
  intros O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra HH AM K0 ENT FRM FRS OFR A10 ARGS WX PA IA BASE INCS KONT.
  destruct src as [qc de rem]. destruct sm as [g eg sst].
  assert (CTX : PGSRDK.srd_ctx L ar HI 0 O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra).
  { destruct ARGS as (SP32 & ARGS). exact (conj OK (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj OFR (conj A10 (conj SP32 (conj ARGS (conj WX (conj PA (conj IA (conj BASE (conj INCS KONT)))))))))))))))). }
  destruct ARGS as (SP32 & p & k & A11 & A12 & Hk & DST).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *.
  pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M _ OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ _ sp 20480 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str _ sp 20480 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & _ & _ & ICE & _ & _).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (GV0 & GV1 & GV2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 160 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in S264, S272, S280, S288, G1, G2, G3, G16, DCH, ACH.
  unfold PM.CHUNK in S272, G3, DCH, ACH.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  assert (PR : 0 <= p /\ p + k <= 2 ^ 47).
  { destruct DST as [(AOD & _)|DW].
    - pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Y2. split; [clear - X1 Y1 FSI FSAPP; lia| clear - X2 Y2 FSCEIL SLO SHI SPT; lia].
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M _ OB p k PA DW) as (_ & _ & [(B & m & Hin & X1 & X2)|(X1 & X2 & _)] & _).
      + assert (BIN : In (B, m) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
        destruct (WB _ BIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. split; [clear - X1 B0; lia| clear - X2 B4 SLO SHI SPT; lia].
      + split; [clear - X1; lia| clear - X2; lia]. }
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (O1' : 0 <= os /\ os + 296 <= 2 ^ 64) by (clear - O1; lia).
  assert (C264 : L5.u64_at RSEGS MV (os + 264) qc).
  { apply (proj2 (L5A.u64_at_vis H M (os + 264) qc (OAV (os + 264) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S264. }
  assert (C272 : L5.u64_at RSEGS MV (os + 272) 16384).
  { apply (proj2 (L5A.u64_at_vis H M (os + 272) 16384 (OAV (os + 272) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S272. }
  assert (C280 : L5.u64_at RSEGS MV (os + 280) de).
  { apply (proj2 (L5A.u64_at_vis H M (os + 280) de (OAV (os + 280) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S280. }
  assert (D256 : L5.defined MV (os + 256) 8).
  { apply (proj2 (L5A.defined_vis H M (os + 256) 8 (OAV (os + 256) 8 ltac:(clear; lia) ltac:(clear; lia)))). exact SD256. }
  assert (K11 : (sp - 160) + 160 <= os \/ os + 296 <= sp - 160) by (right; clear - OCE SL160; lia).
  assert (SPR : 0 <= sp < 2 ^ 64) by (clear - SL160 SHI SPT; lia).
  assert (Q34 : 0 <= qc < 2 ^ 64) by (clear - Q0 Q4 SLO SHI SPT; lia).
  assert (Q35 : 0 <= de < 2 ^ 64) by (clear - G1 G2 G3 Q0 Q4 SLO SHI SPT; lia).
  assert (Q36 : 0 <= os < 2 ^ 64) by (clear - O1; lia).
  assert (Q37 : 0 <= p < 2 ^ 64) by (clear - PR Hk; lia).
  assert (Q38 : 0 <= k < 2 ^ 64) by (clear - Hk; lia).
  (let T := type of (PMASRP.asrS_conc fx R MV (fun j : nat => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) in
   let T := eval cbn beta iota in T in
   LeanFeed.pfeed_at P (PMASRP.asrS_conc fx R MV (fun j : nat => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) T
     ltac:(cbn beta iota) ltac:(idtac; first [assumption | unfold PMASRP.aligned; assumption | clear - SL160 SHI SPT; lia | clear - O1; lia])).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T13 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T27
                 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C136 & C104 & C96 & C88 & C160).
  unfold PMSP.cfg.
  set (Wf := fun a => sp - 160 <= a < sp - 160 + 160).
  match goal with |- srealizes _ _ (@mkCfg (@mkst _ _ (Z_to_bv 64 ?pc0) _ _) _) _ => change (@mkCfg (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) model) with (@L5A.cfg fx R pc0 M model) end.
  match type of MS1 with msteps _ (@mkst _ _ (Z_to_bv 64 ?a) _ _) (@mkst _ _ (Z_to_bv 64 ?b) _ _) =>
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R a R1 b M1v Wf K HH AM MS1 MG1) end.
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold Wf in Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; unfold app_mem, FS_BYTES in *; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. fold H in HID1, VIS1, VV1.
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 20480 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 20480 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M M1 Wf FR1). intros a Ha Hc _ X. unfold Wf in X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01 : L5SAR.dk L ar LB FF sp 20480 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : PNACSK.own sp R M1).
  { unfold PNACSK.own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  assert (FRk0 : ff_room 1 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 4 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
  match type of T1 with _ = Z_to_bv 64 ?rr0 =>
  match goal with |- srealizes _ _ (@L5A.cfg _ _ ?b _ _) _ => change b with (PMA.SM_PC 1) end;
  apply (PMAUAR.uar_sm L ar C HI LY HIok 1 LB [] FF LK cr Aw sp 20480 (sp - 160 - 0) (sp - 104) sp (PNACSK.ocell sp) (PNACSK.own sp R)
           fx1 R1 M M1 model model1 K rr0 ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01) end.
  { rewrite L5K.rl2, Z.sub_0_r. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 160 - 0) with (sp + (-10) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW1 AG. apply (PNACSK.own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW1 AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ GHH2) as (_ & WF2 & _).
  destruct (WF2 (F, 1, sp - 160 - 0 + 32) ltac:(left; reflexivity)) as (_ & _ & F128 & _). cbn [ff_addr ff_class fst snd] in F128. change (ff_bytes 1) with 128 in F128.
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (E3 : getr R2 (reg 3) = getr R (reg 3)) by (rewrite (R2c 3%nat) by inl; apply KS1; inl).
  assert (E4 : getr R2 (reg 4) = getr R (reg 4)) by (rewrite (R2c 4%nat) by inl; apply KS1; inl).
  assert (E18 : getr R2 (reg 18) = getr R (reg 18)) by (rewrite (R2c 18%nat) by inl; exact T18).
  assert (E20 : getr R2 (reg 20) = getr R (reg 20)) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (E21 : getr R2 (reg 21) = getr R (reg 21)) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (E23 : getr R2 (reg 23) = getr R (reg 23)) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (E24 : getr R2 (reg 24) = getr R (reg 24)) by (rewrite (R2c 24%nat) by inl; exact T24).
  assert (E25 : getr R2 (reg 25) = getr R (reg 25)) by (rewrite (R2c 25%nat) by inl; apply KS1; inl).
  assert (E26 : getr R2 (reg 26) = getr R (reg 26)) by (rewrite (R2c 26%nat) by inl; apply KS1; inl).
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 os) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 k) by (rewrite (R2c 22%nat) by inl; exact T22).
  pose proof T27 as B27R. rewrite <- (R2c 27%nat) in B27R by inl.
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (OWN2 : PNACSK.own sp R M2).
  { apply (PNACSK.own_agree sp R M1 M2 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold PNACSK.ocell in Ha. apply AGF. clear - Ha; lia. }
  assert (EKW : L5SAR.ek L ar LB FF sp 20480 (PGS.W_srcG os ois (PM.SRC qc de rem) ++ Wextra) M M2).
  { apply (L5SAR.ek_mono L ar LB FF sp 20480 sp 20480 _ [] M M2 EK02); [intros x Hx; exact Hx| intros a _ rr Hr; destruct Hr]. }
  assert (DSH : L5.defined M2 (F / 8 + SB) 16).
  { apply (proj1 (L5A.defined_vis (ahid Aw model2) M2 (F / 8 + SB) 16 VSH)). apply L5KA.zeros_at_defined. exact FSHZ. }
  assert (BI : PGSRDK.srd_body L ar HI 0 O R M model OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M2 model2 LK2 cr Aw).
  { unfold PGSRDK.srd_body, PMAUK.binv.
    exact (conj GHH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ MRT1 MRT2) (conj (incl_refl Aw) (conj GLKI2 (conj ASTK2 (conj EKW (conj DK02 (conj OWN2 DSH))))))))). }
  assert (VIS2 : forall i, (sp - 160 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16) \/ (os <= i < os + 296)
                    \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36) -> ahid Aw model2 (Z_to_bv 64 i) = false).
  { intros i Hi. exact (PGSRDC.srd_vis L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2 M2 model2 LK2 Aw i CTX G BI Hi). }
  assert (WP0 : PMKA.wapp []) by (intros rr Hr; destruct Hr).
  assert (AGO : PMFA.agA M M2 os 296) by (apply (PMKA.agA_obj L ar LB FF sp 20480 [] M M2 EK02 WP0 FRB os 296 AO); intros i _ rr Hr; destruct Hr).
  assert (AGQ : PMFA.agsh M M2 qc 16384) by (apply (PMASK.agsh_blk L ar LB FF sp 20480 [] M M2 qc 16384 EK02 WP0 QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia]).
  assert (DQ2 : L5.defined M2 qc 16384).
  { apply (PMASK.defined_dk L ar LB FF sp 20480 M M2 qc 16384 DK02); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
    intros i Hi. apply PMASR1.cl_of_bf. left. exact (PMASR1.in_block_of LB qc 16384 i QIN Hi). }
  pose proof (PGSKA.src_fields_keepG M M2 os ois (ois + 16) (PM.SRC qc de rem) PSRC0 ltac:(clear - O1'; lia) ltac:(clear - O1'; lia) AGO AGQ DQ2) as PSRC2.
  pose proof (PMFA.nullis_at_agreeA RSEGS PMA.AD M M2 (os + 8) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia) ltac:(eapply PMFA.agA_sub; [exact AGO| clear; lia| clear; lia]) PNI) as PNI2.
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB ((F, 1, sp - 160 - 0 + 32) :: FF) LK2 cr Aw M2 model2 os _ _ _ sp 20480 GHH2 (PMAUAR.aobjA_push _ _ _ _ AO) O8 PSRC2 PNI2 ASTK2)
    as (_ & OZ2 & OW2 & _ & OAV2 & _).
  pose proof PSRC2 as PSRC2'. destruct PSRC2' as (_ & _ & SD256' & S264' & S272' & S280' & S288' & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in S264', S272', S280', S288'. unfold PM.CHUNK in S272'.
  assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by exact (PMASK.base_keep L ar C LY LB FF sp 20480 [] M M2 EK02 (fun a _ rr Hr => match Hr with end) BASE).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M2 model2 GHH2 BASE2) as (GW0 & GW1 & GW2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ _ _ _ M2 model2 sp 20480 160 GHH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (C264' : L5.u64_at RSEGS MV2 (os + 264) qc).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (os + 264) qc (OAV2 (os + 264) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S264'. }
  assert (C272' : L5.u64_at RSEGS MV2 (os + 272) 16384).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (os + 272) 16384 (OAV2 (os + 272) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S272'. }
  assert (C280' : L5.u64_at RSEGS MV2 (os + 280) de).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (os + 280) de (OAV2 (os + 280) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S280'. }
  assert (C288' : L5.u64_at RSEGS MV2 (os + 288) rem).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (os + 288) rem (OAV2 (os + 288) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1'; lia) ltac:(clear - O1'; lia))). exact S288'. }
  assert (D256' : L5.defined MV2 (os + 256) 8).
  { apply (proj2 (L5A.defined_vis H2 M2 (os + 256) 8 (OAV2 (os + 256) 8 ltac:(clear; lia) ltac:(clear; lia)))). exact SD256'. }
  assert (AGS : forall i, sp - 160 <= i < sp -> MV2 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. unfold MV2. rewrite (mrestrict_visible H2 M2 _ (VIS2 i ltac:(left; clear - Hi; lia))).
    rewrite (AGF i ltac:(clear - Hi; lia)). rewrite <- VIS1.
    rewrite (mrestrict_visible H M1 _ (one_cell (fun x => H (Z_to_bv 64 x) = false) i (VISs i 1 ltac:(clear - Hi SL160 SPT; lia) ltac:(clear - Hi SHI SPT; lia)))).
    reflexivity. }
  assert (IA2 : PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str (PM.STRM g eg sst)).
  { apply (PMFA.iss_at_agreeA RSEGS PMA.AD M M2 ois str (PM.STRM g eg sst)); [clear - I1; lia| clear - I1; lia| split| | exact IA].
    - intros i Hi. apply EK02. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| intros rr Hr; destruct Hr].
    - exact (PMKA.agsh_obj L ar LB FF sp 20480 [] M M2 EK02 WP0 FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0' & _ & _ & _ & T4' & _) & _).
      cbn [fst snd] in T0', T4'. split.
      + intros i Hi. apply EK02. split; [clear - Hi T0' T4' SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| intros rr Hr; destruct Hr].
      + apply (PMASK.agsh_blk L ar LB FF sp 20480 [] M M2 q1 c1 EK02 WP0 TIN); clear - T0' T4' SLO SHI SPT; lia. }
  assert (DFO : F + 128 <= os \/ os + 296 <= F).
  { destruct (Z_le_gt_dec (F + 128) os) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (os + 296) F) as [Y|Y]; [right; exact Y|].
    exfalso. apply (GNCF (Z.max os F)); [left; clear - X Y; lia|].
    apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 _ AO). clear - X Y; lia. }
  assert (DFLO : fl + 1 <= os \/ os + 296 <= fl).
  { destruct (Z_le_gt_dec (fl + 1) os) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (os + 296) fl) as [Y|Y]; [right; exact Y|].
    exfalso. apply GFLNC. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA _ os 296 fl (PMAUAR.aobjA_push _ _ _ _ AO)). clear - X Y; lia. }
  assert (F32e : 32 * (F / 32) = F) by (clear - GF32; lia).
  assert (F8e : 4 * (F / 32) = F / 8) by (clear - GF32; lia).
  assert (Q50 : 0 <= F / 32 < 2 ^ 64) by (clear - GFR; lia).
  assert (Q51 : 0 <= fl < 2 ^ 64) by (clear - GFLR; lia).
  assert (FLC' : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
  pose proof (conj SL160 (conj SHI SPT)) as KB.
  assert (STA : PGSRDK.srd_stA (vS R R2 sp qc de os p k ois F fl) R2 MV2).
  { unfold PGSRDK.srd_stA, vS. cbn beta iota.
    rewrite ?F32e, ?F8e. rewrite ?E18, ?E20, ?E21, ?E23, ?E24, ?E25, ?E26.
    PGSRDC.sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                         | PGSRDC.carry M1v AGS KB | (clear - SL160 SHI SPT; lia) | (clear - O1; lia) | (clear - GFR GFS1 GFS2 GF32 F128; lia)
                         | (clear - GFLR; lia) | (clear - GFCEIL GFLR SL160; lia)
                         | (clear - GFR GFBIG GFLR GFLBIG O1 OBIG DFO DFLO GF32 F128 O8; lia)
                         | (clear - GFR GF8 GFCEIL GSLO GSPC GSPT SL160 SHI SPT GFS1 GFS2 F128; try unfold SB in *; lia)]). }
  assert (POST : PGSRDK.srd_post_sm L ar HI 0 O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k F fl LK2 M2 model2 R2 M2 model2 LK2 Aw (vS R R2 sp qc de os p k ois F fl)).
  { unfold PGSRDK.srd_post_sm.
    split; [exact CTX|]. split; [exact A11|]. split; [exact A12|]. split; [exact G|]. split; [exact BI|].
    split; [cbn; clear; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn; exact F32e|]. split; [reflexivity|].
    split; [intros i Hi; cbn in Hi; repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]|].
    split; [exact E3|]. split; [exact E4|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact IA2|]. split; [exact STA|]. exact C288'. }
  exact (EB O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k F fl LK2 M2 model2 fx1 R2 M2 model2 LK2 Aw _ POST).
Qed.

Theorem src_read_ok32 : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PMA.xsgetn_spec L ar HI ->
  PGSA.src_read_specG_al RSEGS PMA.AD L ar HI PNRA.FCB 0.
Proof using LY HIok ICok ILY.
  intros FB XS.
  exact (srd_entry_sm (PGSRDEB.srd_entry_body_ok L ar C HI LY HIok IL ICok ILY FB XS (PGSRDA0F.srd_a0f_ok L ar C HI LY HIok IL ICok ILY FB))).
Qed.

End WithHeap.
End PGSRD32.
