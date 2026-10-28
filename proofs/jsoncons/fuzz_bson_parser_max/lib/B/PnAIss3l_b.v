(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAIssStmts_b PnAIssP_b PnAIss1_b PnAStr_b Ba0_code_ra806c_a8070_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMAIS3L.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).


Lemma odd_byte c : c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros E. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by Lia.lia.
  replace (c + 1) with (2 * (c / 2) + 1) by (pose proof (Z.div_mod c 2 ltac:(Lia.lia)); Lia.lia).
  apply Z.testbit_odd_0.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cap_long n : 23 <= n < 2 ^ 26 -> let c := if Z.leb n 44 then 48 else 8 * (n / 8) + 8 in
  n < c /\ c <= n + 32 /\ 48 <= c <= 67108872 /\ c mod 8 = 0 /\ c mod 2 = 0 /\ 47 <= c - 1 <= 67108871.
Proof. intros Hn c. unfold c. destruct (Z.leb_spec n 44); Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem long : PMA.opnew_spec L ar HI -> forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r c0 n p0 b R2 M2 model2 LK2 Aw2,
    PMAIS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r (PM.VLong c0 n p0) b ->
    PMAIS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois sp r (PM.VLong c0 n p0) b ->
    PMAIS.mid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr ois os sp (PM.VLong c0 n p0) b R2 M2 model2 LK2 Aw2 ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R2 0xac2e4 M2 model2) K.
Proof.
  intros NEW fx R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r c0 n p0 b R2 M2 model2 LK2 Aw2 PRE KONT MID.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & A10 & A11 & A12 & AO & AOS & EOS & O8 & OS8 & ODEF0 & ACC0 & VS0 & INCL & SZ & LNG & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  assert (EOS' : os = ois - 64) by lia. subst os.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27 & MCSK & V16 & Z32 & Z80 & MC).
  destruct MC as (SVI & SVB & HC & ODEF & ACC & VS & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI). unfold PMAIS.SCR in *. change (20480 / 8) with 2560 in STKSH.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw2 model2) in *. set (MV := mrestrict H M2) in *.
  pose proof (PMKA.aobj_of_aobjA FF ois 272 AO O8) as AOB.
  pose proof (PMKA.aobj_of_aobjA FF (ois - 64) 24 AOS OS8) as AOSB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 sp 20480 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & _ & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 (ois - 64) 24 sp 20480 HH AOSB ltac:(lia) ltac:(reflexivity))
    as (OSR & OSBIG & OSDEF & OSVIS & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M2 LYa ST) as (GOT & CSB & CUAR & _).
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M2 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M2 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M2 (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 20480); [exact ASTK| lia| lia| lia]. }
  assert (OZv : L5KA.zeros_at MV (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (OWv : L5.writable RSEGS MV ois 272).
  { apply (proj2 (L5A.writable_vis H M2 ois 272 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  destruct VS as (VSD & VSA & W0 & W8 & W16 & Hn & Hc0 & Hc0e & PD & PA).
  assert (N23 : 23 <= n) by (apply (LNG c0 n p0); reflexivity). cbn [PM.vs_size] in SZ.
  assert (INB : In (p0, c0) LB) by (apply INCL; left; reflexivity).
  pose proof (WB _ INB) as ((BQ0 & BQ1 & BQ2 & BQ3 & BQ4 & BQ5) & BDEF & BSH & _ & BBA & BFA & BFS). cbn [fst snd] in BQ0, BQ1, BQ2, BQ3, BQ4, BQ5, BDEF, BSH, BBA, BFA, BFS.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BQ5. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BQ1.
  assert (Y0b : L5.u8_at RSEGS MV (ois - 64) ((c0 + 1) mod 256)).
  { apply (proj2 (L5A.u8_at_vis H M2 (ois - 64) _ ltac:(eapply L5A.avis_sub; [exact OSVIS| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMF.u8_of_u64 RSEGS M2 (ois - 64) (c0 + 1)); [lia| exact W0]. }
  assert (VU64 : forall a v, ois - 64 <= a -> a + 8 <= ois - 40 -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb X. apply (proj2 (L5A.u64_at_vis H M2 a v ltac:(eapply L5A.avis_sub; [exact OSVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X. }
  assert (YW8 : L5.u64_at RSEGS MV (ois - 56) n) by (apply VU64; [lia| lia| replace (ois - 56) with (ois - 64 + 8) by lia; exact W8]).
  assert (YW16 : L5.u64_at RSEGS MV (ois - 48) p0) by (apply VU64; [lia| lia| replace (ois - 48) with (ois - 64 + 16) by lia; exact W16]).
  assert (Y80 : L5.u8_at RSEGS MV (ois + 80) 0).
  { apply (proj2 (L5A.u8_at_vis H M2 (ois + 80) 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMCG.u8_of_zeros RSEGS M2 (ois + 80)); [apply (PMCG.zeros_sub M2 (ois + 80) 24); [exact Z80| lia| lia]| lia| lia]. }
  assert (TB : Z.testbit ((c0 + 1) mod 256) 0 = true) by (apply odd_byte; exact Hc0e).
  assert (B256 : 0 <= (c0 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)); lia).
  pose proof (cap_long n ltac:(lia)) as CAPR. cbv zeta in CAPR.
  set (c := if Z.leb n 44 then 48 else 8 * (n / 8) + 8) in *.
  (* [comment removed for export] *)
  assert (HEAD : exists fx1 R3 M3v, mem_grows MV M3v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 240 <= i < sp - 240 + 48) -> ~ (ois + 104 <= i < ois + 104 + 8) -> ~ (ois + 112 <= i < ois + 112 + 4) -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R2 0xac2e4 MV) (st fx1 R3 0x130338 M3v)
      /\ (forall x, In x [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
      /\ getr R3 (reg 1) = Z_to_bv 64 876768 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 240) /\ getr R3 (reg 8) = Z_to_bv 64 n
      /\ getr R3 (reg 9) = Z_to_bv 64 (ois + 80) /\ getr R3 (reg 10) = Z_to_bv 64 c /\ getr R3 (reg 19) = Z_to_bv 64 p0 /\ getr R3 (reg 20) = Z_to_bv 64 (c - 1)
      /\ L5.u64_at RSEGS M3v (sp - 240) (ois - 64) /\ L5.u64_at RSEGS M3v (sp - 232) 8 /\ L5.u64_at RSEGS M3v (sp - 224) (ois + 80)
      /\ L5.u64_at RSEGS M3v (sp - 216) (ois + 24) /\ L5.u64_at RSEGS M3v (sp - 208) (ois + 16) /\ L5.u64_at RSEGS M3v (sp - 200) 705312
      /\ L5.u32_at RSEGS M3v (ois + 112) 8).
  { destruct (Z.leb_spec n 44) as [N44|N45].
    - LeanFeed.pfeed P (PMAISP.aicCl1a_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R2 MV
                    (fun j => match j with 2%nat => sp | 33%nat => ois | 36%nat => p0 | 38%nat => (c0 + 1) mod 256 | 40%nat => n | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
      destruct P as (fx1 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & dR1 & dR2 & dR8 & dR9 & dR10 & dR11 & dR12 & dR13 & dR14 & dR19 & dR20
                     & E240 & E232 & E224 & E216 & E208 & E200 & E112).
      exists fx1, R3, M3v. unfold c. cbn iota.
      split; [exact MG3|]. split; [exact FZ3|]. split; [exact MS3|].
      split. { intros x Hx. apply KS3. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption.
    - assert (ELOR : 47 <= Z.lor n 7 <= 67108871) by (rewrite PMASTR.lor7 by lia; lia).
      LeanFeed.pfeed P (PMAISP.aicCl1b_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R2 MV
                    (fun j => match j with 2%nat => sp | 33%nat => ois | 36%nat => p0 | 38%nat => (c0 + 1) mod 256 | 40%nat => n | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
      destruct P as (fx1 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & dR1 & dR2 & dR8 & dR9 & dR10 & dR11 & dR12 & dR13 & dR14 & dR19 & dR20
                     & E240 & E232 & E224 & E216 & E208 & E200 & E112).
      exists fx1, R3, M3v. unfold c. cbn iota.
      replace (8 * (n / 8) + 8 - 1) with (8 * (n / 8) + 7) by lia.
      split; [exact MG3|]. split; [exact FZ3|]. split; [exact MS3|].
      split. { intros x Hx. apply KS3. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption. }
  destruct HEAD as (fx1 & R3 & M3v & MG3 & FZ3 & MS3 & KS3 & dR1 & dR2 & dR8 & dR9 & dR10 & dR19 & dR20 & E240 & E232 & E224 & E216 & E208 & E200 & E112).
  set (W3 := fun a => (sp - 240 <= a < sp - 240 + 48) \/ ((ois + 104 <= a < ois + 104 + 8) \/ (ois + 112 <= a < ois + 112 + 4))).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx fx1 R2 0xac2e4 R3 0x130338 M3v W3 K HH AM MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (CS3 : forall k, In k [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k) = getr R2 (reg k)) by exact KS3.
  assert (WAPP : PMKA.wapp (PMAIS.WF ois b)).
  { unfold PMAIS.WF. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    destruct b; [apply PMKA.wapp_nil|]. unfold PMSPA.loc_W. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (EK23 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M3 W3 FR3). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK MGM3)).
  (* [comment removed for export] *)
  destruct (PMASTR.credit_facts L ar C LY cr (n + 16) c) as (CROK & CRKEEP & _).
  { unfold PMAIS.cost in CRED. cbn [PM.vs_size] in CRED. replace (n + 16 + 16) with (n + 32) by lia. exact CRED. } { lia. } { lia. }
  unfold PMA.opnew_spec, PMSPA.opnew_spec in NEW. cbn [pa_opnew PMA.AD ADDR_A] in NEW.
  apply (NEW fx1 R3 M3 model3 K LB FF LK2 Aw2 cr c (sp - 240) 0xd60e0 HH3 AM3 K0).
  { rewrite L5K.rl10. exact dR10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact dR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact dR2. }
  { rewrite L5K.rl4, (CS3 4%nat) by (right; left; reflexivity). rewrite (MCSK 4%nat) by (right; left; reflexivity). exact Rtp. }
  { apply (L5SAR.astk_sub ar M3 M3 sp 20480 240 PMSPA.OPNEW_SCR ASTK3 (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (sp - 240) with (sp + (-15) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx4 R4 M4 model4 Aw4 p nR10 RP4 (BRp & BAp & FAp & DEFp & SHBp) PRES4 RT4 IA4 AM4 HH4.
  set (LB2 := (p, c) :: LB) in *. set (cr2 := adebit L cr c) in *.
  pose proof AM4 as (Mh4 & MI4).
  pose proof BRp as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1.
  pose proof (PMASTR.shb_bound p c ltac:(lia) ltac:(lia) ltac:(lia)) as PSH.
  assert (P8 : p mod 8 = 0) by (apply PMFA.mod16_8; exact Q2).
  assert (ASTK4 : L5CA.astk ar M4 sp 20480).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK2 cr Aw2 M3 M3 M4 _ sp 20480 (sp - 240) PMSPA.OPNEW_SCR [] HH3 ASTK3 (fun x X => X) PRES4);
    unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia. }
  assert (CS4 : forall k, In k L5SAR.cs_all -> getr R4 (reg k) = getr R3 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R3 R4 k RP4 Hk)).
  assert (EK34 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M4).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 240) PMSPA.OPNEW_SCR (PMAIS.WF ois b) [] M3 M4 PRES4); [unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (PO : p + c <= ois \/ ois + 272 <= p).
  { destruct AO as (g' & Hg' & Y1 & Y2). pose proof (FAp g' ltac:(apply in_or_app; left; exact Hg')) as Z2. cbn [fst snd] in *. clear - Y1 Y2 Z2. Lia.lia. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (F2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 240)) by (rewrite CS4 by inl; exact dR2).
  assert (F8 : getr R4 (reg 8) = Z_to_bv 64 n) by (rewrite CS4 by inl; exact dR8).
  assert (F10 : getr R4 (reg 10) = Z_to_bv 64 p) by (rewrite <- L5K.rl10; exact nR10).
  assert (F19 : getr R4 (reg 19) = Z_to_bv 64 p0) by (rewrite CS4 by inl; exact dR19).
  LeanFeed.pfeed P (PMAISP.aicCl2_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx4 R4 MV4
                (fun j => match j with 2%nat => sp | 36%nat => p0 | 40%nat => n | 41%nat => p | _ => 0 end)) ltac:(first [assumption | lia]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & eR1 & eR11 & eR12 & eR18).
  assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; exact FZ5). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M4 model4 fx4 fx5 R4 0xd60e0 R5 0x77c90 MV4 K HH4 AM4 MS5 MG5 FZ5).
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
  assert (E5' : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
  pose proof AM5 as (Mh5 & MI5).
  assert (CS5 : forall k, In k PMAISP.KS_aicCl2 -> getr R5 (reg k) = getr R4 (reg k)) by exact KS5.
  (* [comment removed for export] *)
  assert (AGS4 : forall a, (p0 <= a < p0 + n \/ S p0 <= a <= S (p0 + n - 1)) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Hq.
    pose proof (PMASTR.shb_bound p0 c0 ltac:(lia) ltac:(lia) ltac:(lia)) as BSB.
    pose proof (PMASTR.shadow_sub p0 c0 p0 n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BSS.
    assert (Ca : aclient L ar LB FF 0 0 a).
    { destruct Hq as [Hq|Hq]; [apply (L5SAR.block_client L ar LB FF 0 0 p0 c0); [exact INB| lia]|].
      do 6 right. exists (p0, c0). split; [exact INB|]. unfold in_shadow_of, S, SB in *. cbn [fst snd]. lia. }
    assert (Ra : 0 <= a < 2 ^ 64 /\ a < ahl_ceil ar /\ ~ (ois <= a < ois + 116) /\ ~ (sp - 240 <= a < sp - 192)).
    { destruct AO as (g' & Hg' & Y1 & Y2). pose proof (BFA g' ltac:(apply in_or_app; left; exact Hg')) as Z2.
      destruct Hq as [Hq|Hq]; [lia|]. unfold S, SB in Hq. destruct OBIG; lia. }
    destruct Ra as (R0a & R1a & R2a & R3a).
    rewrite (proj1 PRES4 a). 2:{ split; [exact R0a|]. split; [|intros rr []]. apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Ca| unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia]. }
    apply FR3; [exact R0a| unfold W3; lia]. }
  destruct (PMCG.rdn_some RSEGS M4 (Z.to_nat n) p0 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN & _).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. rewrite AGS4 by lia. replace (p0 + i) with (p0 + i) by lia. apply PD. lia. }
  (* [comment removed for export] *)
  pose proof (aic_memcpy_libc _ _ _ _ _ ICok) as MC. unfold amemcpy_libc_spec, amemcpy_spec_at, amem_pre, amem_post in MC.
  rewrite (L5A.aly_segs L C LYa), (aicl_memcpy IL ILY), (L5A.aly_scr_mem L C LYa) in MC.
  assert (U52 : bv_unsigned (getr R5 2%bv) = sp - 240) by (rewrite L5K.rl2, (CS5 2%nat) by inl; rewrite F2; apply L5.unsigned_lit; lia).
  apply (MC fx5 R5 M4 model5 LB2 FF LK2 cr2 Aw4 p p0 n bs K); clear MC.
  { split; [exact HH5|]. split; [exact Mh5|]. split; [exact MI5|].
    split; [rewrite L5K.rl10, (CS5 10%nat) by inl; exact F10|]. split; [rewrite L5K.rl12; exact eR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (CS5 4%nat) by inl; rewrite (CS4 4%nat) by inl; rewrite (CS3 4%nat) by (right; left; reflexivity); rewrite (MCSK 4%nat) by (right; left; reflexivity); exact Rtp|].
    split; [rewrite L5K.rl1, eR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite U52. apply (L5SAR.astack_ok_of_astk L ar C LYa M4 M4 sp 20480 240 2560 ASTK4 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 240) with (sp + (-15) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split. { apply (PMASTR.aacc_of_block M4 p c p n SHBp); [exact P8| lia| lia| lia]. }
    split. { intros i Hi. rewrite U52. apply (L5SAR.block_client L ar LB2 FF _ _ p c); [left; reflexivity| lia]. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M4 p c); [exact DEFp| lia| lia| lia| lia]. }
    split; [exact K0|]. apply (L5SAR.app_rng_block L ar C HI HIok LB2 FF LK2 cr2 Aw4 M4 _ p c p n HH5 ltac:(left; reflexivity)); lia. }
  { rewrite L5K.rl11. exact eR11. }
  { intros a Ha. unfold byte_at. rewrite AGS4 by (right; unfold S; split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia). apply PA. lia. }
  { lia. }
  { apply (L5SAR.app_rng_block L ar C HI HIok LB2 FF LK2 cr2 Aw4 M4 _ p0 c0 p0 n HH5 ltac:(right; exact INB)); lia. }
  { intros i Hi. right. apply (L5SAR.block_client L ar LB2 FF _ _ p0 c0); [right; exact INB| lia]. }
  { exact RDN. }
  { intros _. pose proof (BAp _ INB) as X. cbn [fst snd] in X. lia. }
  intros R6 M6 model6 mR10 RP6 BYTES PRES6 SDEF6 RT6 MI6 HH6. rewrite U52 in PRES6, SDEF6. rewrite L5K.rl1, eR1.
  assert (AM6 : L5CA.amodel_ok Aw4 model6) by (split; [rewrite (L5LZ.model_rt_halted _ _ RT6); exact Mh5| exact MI6]).
  assert (CS6 : forall k, In k L5SAR.cs_all -> getr R6 (reg k) = getr R5 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R5 R6 k RP6 Hk)).
  assert (ASTK6 : L5CA.astk ar M6 sp 20480).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK2 cr2 Aw4 M4 M4 M6 _ sp _ (sp - 240) 2560 HH5 ASTK4 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES6. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF6.
    - lia. - lia. - lia. }
  assert (FAF : fframes_apart p c FF) by (eapply L5SAR.fframes_apart_incl; [exact FAp| apply incl_appl; apply incl_refl]).
  assert (PNC : forall a, p <= a < p + c -> ~ aclient L ar LB FF sp 20480 a).
  { intros a Ha. exact (L5SAR.fresh_block_not_client L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 _ sp 20480 p c a HH3 SPT BRp BAp FAF Ha). }
  assert (PRES6' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 240) 2560 a -> ~ (p <= a < p + n) -> M6 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hc Hn'. apply PRES6. exact Ha. apply L5SAR.aclient_consb. exact Hc. exact Hn'. }
  assert (EK46 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M4 M6).
  { apply (L5SAR.ek_mem L ar LB FF sp 20480 (sp - 240) 2560 (fun a => p <= a < p + n) (PMAIS.WF ois b) M4 M6 PRES6'); [lia| lia|].
    intros a Hc Ho X. apply (PNC a); [lia| exact Hc]. }
  assert (EK26 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M6).
  { apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M4 M6); [apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M3 M4 EK23 EK34)| exact EK46]. }
  assert (ACC6 : PMSPA.accA M6 ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M2 M6 EK26 WAPP FRB ois 272 AO ACC)).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
  set (H6 := ahid Aw4 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M6 model6 ois 272 sp 20480 HH6 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF6 & OVIS6 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as ST6. rewrite (L5A.aly_segs L C LYa) in ST6.
  pose proof (L5A.statics_facts L C M6 LYa ST6) as (GOT6 & CSB6 & CUAR6 & _).
  assert (Y0 : L5.img_clear MV6 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT6).
  assert (Y1 : L5.u64_at RSEGS MV6 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H6 M6 1309752 2147450880 (VIMG6 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB6).
  assert (Y2 : L5.u32_at RSEGS MV6 1309760 1) by (apply (proj2 (L5A.u32_at_vis H6 M6 1309760 1 (VIMG6 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR6).
  assert (Y3 : L5.writable RSEGS MV6 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H6 M6 (sp - 4096) 4096 (VIS6 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M6 sp 20480); [exact ASTK6| lia| lia| lia]. }
  assert (YZ : L5KA.zeros_at MV6 (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M6 model6 ois 272 HH6 AO O8 ltac:(lia) ltac:(reflexivity) ACC6). }
  assert (YW : L5.writable RSEGS MV6 ois 272).
  { apply (proj2 (L5A.writable_vis H6 M6 ois 272 OVIS6 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF6. lia. lia. }
  assert (DEF6 : L5.defined M6 p c).
  { intros i Hi. destruct (Z_lt_le_dec i n) as [X|X].
    - destruct (BYTES i ltac:(lia)) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
    - rewrite PRES6; [apply DEFp; lia| lia| apply (L5SAR.block_client L ar LB2 FF _ _ p c); [left; reflexivity| lia]| lia]. }
  assert (PV6 : L5A.avis H6 p c) by (apply (VBLK6 p c); [left; reflexivity| lia| lia]).
  assert (YPN : L5.writable RSEGS MV6 (p + n) 1).
  { apply (proj2 (L5A.writable_vis H6 M6 (p + n) 1 ltac:(eapply L5A.avis_sub; [exact PV6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M6 p c); [exact DEF6| lia| lia]. lia. lia. }
  (* [comment removed for export] *)
  assert (T36 : forall a v, sp - 240 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV6 a v).
  { intros a v Ha Hb X. rewrite <- VIS3 in X.
    apply (proj1 (L5A.u64_at_vis H M3 a v (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in X.
    apply (proj2 (L5A.u64_at_vis H6 M6 a v (VIS6 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M3 M6); [|lia|lia|exact X]. intros i Hi.
    rewrite PRES6'; [| lia| apply L5SAR.stack_client; lia| lia].
    apply (proj1 PRES4). split; [lia|]. split; [apply L5SAR.stack_client; unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| intros rr []]. }
  assert (J2 : getr R6 (reg 2) = Z_to_bv 64 (sp - 240)) by (rewrite CS6 by inl; rewrite (CS5 2%nat) by inl; exact F2).
  assert (J8 : getr R6 (reg 8) = Z_to_bv 64 n) by (rewrite CS6 by inl; rewrite (CS5 8%nat) by inl; exact F8).
  assert (J9 : getr R6 (reg 9) = Z_to_bv 64 (ois + 80)) by (rewrite CS6 by inl; rewrite (CS5 9%nat) by inl; rewrite CS4 by inl; exact dR9).
  assert (J18 : getr R6 (reg 18) = Z_to_bv 64 p) by (rewrite CS6 by inl; exact eR18).
  assert (J20 : getr R6 (reg 20) = Z_to_bv 64 (c - 1)) by (rewrite CS6 by inl; rewrite (CS5 20%nat) by inl; rewrite CS4 by inl; exact dR20).
  assert (Z200 : L5.u64_at RSEGS MV6 (sp - 200) 705312) by (apply T36; [lia| lia| exact E200]).
  assert (Z208 : L5.u64_at RSEGS MV6 (sp - 208) (ois + 16)) by (apply T36; [lia| lia| exact E208]).
  assert (Z216 : L5.u64_at RSEGS MV6 (sp - 216) (ois + 24)) by (apply T36; [lia| lia| exact E216]).
  assert (Z224 : L5.u64_at RSEGS MV6 (sp - 224) (ois + 80)) by (apply T36; [lia| lia| exact E224]).
  assert (Z232 : L5.u64_at RSEGS MV6 (sp - 232) 8) by (apply T36; [lia| lia| exact E232]).
  assert (Z240 : L5.u64_at RSEGS MV6 (sp - 240) (ois - 64)) by (apply T36; [lia| lia| exact E240]).
  LeanFeed.pfeed P (PMAISP.aicCl3_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx5 R6 MV6
                (fun j => match j with 2%nat => sp | 33%nat => ois | 40%nat => n | 41%nat => p | 42%nat => c - 1 | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia | (replace (p + n) with (p + n) by lia; assumption)]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FZ7 & MS7 & KS7 & gR1 & gR2 & gR8 & gR9 & gR10 & gR18 & gR19 & gR20 & G0 & G96 & G88 & G80).
  set (W7 := fun a => (ois + 80 <= a < ois + 80 + 24) \/ (p + n + 0 <= a < p + n + 0 + 1)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M6 model6 fx5 fx7 R6 0xd60f0 R7 0xac320 M7v W7 K HH6 AM6 MS7 MG7).
  { intros a Ha N. apply FZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 ois 272 a AOB); lia| lia].
    - split; [apply (L5SAR.block_client L ar LB2 FF 0 0 p c); [left; reflexivity| lia]| lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
  assert (CS7 : forall k, In k PMAISP.KS_aicCl3 -> getr R7 (reg k) = getr R6 (reg k)) by exact KS7.
  assert (EK67 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M6 M7).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M6 M7 W7 FR7). intros a Ha Hc Ho [X|X].
    - apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    - apply (PNC a); [lia| exact Hc]. }
  assert (ASTK7 : L5CA.astk ar M7 sp 20480) by (apply (L5SAR.astk_grows ar M6 M7 sp 20480 ASTK6 MGM7)).
  assert (EK27 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M7) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M6 M7 EK26 EK67)).
  assert (ACC7 : PMSPA.accA M7 ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M2 M7 EK27 WAPP FRB ois 272 AO ACC)).
  assert (ODEF7 : L5.defined M7 ois 272) by (apply (L5.defined_grows M6 M7 _ _ MGM7); exact ODEF6).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH7) as ST7. rewrite (L5A.aly_segs L C LYa) in ST7.
  pose proof (L5A.statics_facts L C M7 LYa ST7) as (GOT7 & CSB7 & CUAR7 & _).
  assert (XV : forall a n0, (ois <= a /\ a + n0 <= ois + 272) \/ (sp - 4096 <= a /\ a + n0 <= sp) \/ (0 <= a /\ a + n0 <= 0x696000) -> L5A.avis H6 a n0).
  { intros a n0 [X|[X|X]]; [eapply L5A.avis_sub; [exact OVIS6| lia| lia]| apply VIS6; lia| apply VIMG6; lia]. }
  assert (X0 : L5.img_clear M7v 1249280 1282048) by (rewrite <- VIS7; apply L5A.img_clear_mrestrict; exact GOT7).
  assert (X1 : L5.u64_at RSEGS M7v 1309752 2147450880) by (rewrite <- VIS7; apply (proj2 (L5A.u64_at_vis H6 M7 1309752 2147450880 (XV 1309752 8 ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB7).
  assert (X2 : L5.u32_at RSEGS M7v 1309760 1) by (rewrite <- VIS7; apply (proj2 (L5A.u32_at_vis H6 M7 1309760 1 (XV 1309760 4 ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR7).
  assert (X3 : L5.writable RSEGS M7v (sp - 4096) 4096).
  { rewrite <- VIS7. apply (proj2 (L5A.writable_vis H6 M7 (sp - 4096) 4096 (XV (sp - 4096) 4096 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M7 sp 20480); [exact ASTK7| lia| lia| lia]. }
  assert (XZ : L5KA.zeros_at M7v (ois / 8 + 2147450880) 34).
  { pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M7 model7 ois 272 HH7 AO O8 ltac:(lia) ltac:(reflexivity) ACC7) as X.
    rewrite HID7, VIS7 in X. exact X. }
  assert (XW : L5.writable RSEGS M7v ois 272).
  { rewrite <- VIS7. apply (proj2 (L5A.writable_vis H6 M7 ois 272 (XV ois 272 ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF7. lia. lia. }
  (* [comment removed for export] *)
  assert (T27 : forall a v, sp - 192 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M7v a v).
  { intros a v Ha Hb X. rewrite <- VIS7. apply (proj2 (L5A.u64_at_vis H6 M7 a v (XV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M2 M7); [|lia|lia|exact X]. intros i Hi.
    rewrite FR7 by (unfold W7; lia). rewrite PRES6'; [| lia| apply L5SAR.stack_client; lia| lia].
    rewrite (proj1 PRES4 i). 2:{ split; [lia|]. split; [apply L5SAR.stack_client; unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| intros rr []]. }
    apply FR3; [lia| unfold W3; lia]. }
  destruct SVI as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  destruct SVB as (T120 & T128 & T136 & T144 & T152 & T160 & T168 & T176 & T184).
  assert (Z8 : L5.u64_at RSEGS M7v (sp - 8) (bv_unsigned (getr R0 (reg 1)))) by (apply T27; [lia| lia| exact S8]).
  assert (Z16 : L5.u64_at RSEGS M7v (sp - 16) (bv_unsigned (getr R0 (reg 8)))) by (apply T27; [lia| lia| exact S16]).
  assert (Z24 : L5.u64_at RSEGS M7v (sp - 24) (bv_unsigned (getr R0 (reg 9)))) by (apply T27; [lia| lia| exact S24]).
  assert (Z32' : L5.u64_at RSEGS M7v (sp - 32) (bv_unsigned (getr R0 (reg 18)))) by (apply T27; [lia| lia| exact S32]).
  assert (Z40 : L5.u64_at RSEGS M7v (sp - 40) (bv_unsigned (getr R0 (reg 19)))) by (apply T27; [lia| lia| exact S40]).
  assert (Z48 : L5.u64_at RSEGS M7v (sp - 48) (bv_unsigned (getr R0 (reg 20)))) by (apply T27; [lia| lia| exact S48]).
  assert (Z56 : L5.u64_at RSEGS M7v (sp - 56) (bv_unsigned (getr R0 (reg 21)))) by (apply T27; [lia| lia| exact S56]).
  assert (Z64 : L5.u64_at RSEGS M7v (sp - 64) (bv_unsigned (getr R0 (reg 22)))) by (apply T27; [lia| lia| exact S64]).
  assert (Z72 : L5.u64_at RSEGS M7v (sp - 72) (bv_unsigned (getr R0 (reg 23)))) by (apply T27; [lia| lia| exact S72]).
  assert (Z80' : L5.u64_at RSEGS M7v (sp - 80) (bv_unsigned (getr R0 (reg 24)))) by (apply T27; [lia| lia| exact S80]).
  assert (Z88 : L5.u64_at RSEGS M7v (sp - 88) (bv_unsigned (getr R0 (reg 25)))) by (apply T27; [lia| lia| exact S88]).
  assert (Z96 : L5.u64_at RSEGS M7v (sp - 96) (bv_unsigned (getr R0 (reg 26)))) by (apply T27; [lia| lia| exact S96]).
  assert (Z104 : L5.u64_at RSEGS M7v (sp - 104) (bv_unsigned (getr R0 (reg 27)))) by (apply T27; [lia| lia| exact S104]).
  assert (Z120 : L5.u64_at RSEGS M7v (sp - 120) 691528) by (apply T27; [lia| lia| exact T120]).
  assert (Z128 : L5.u64_at RSEGS M7v (sp - 128) ois) by (apply T27; [lia| lia| exact T128]).
  assert (Z136 : L5.u64_at RSEGS M7v (sp - 136) (ois + 120)) by (apply T27; [lia| lia| exact T136]).
  assert (Z144 : L5.u64_at RSEGS M7v (sp - 144) 8) by (apply T27; [lia| lia| exact T144]).
  assert (Z152 : L5.u64_at RSEGS M7v (sp - 152) (ois - 64)) by (apply T27; [lia| lia| exact T152]).
  assert (Z160 : L5.u64_at RSEGS M7v (sp - 160) 1266032) by (apply T27; [lia| lia| exact T160]).
  assert (Z168 : L5.u64_at RSEGS M7v (sp - 168) (ois + 16)) by (apply T27; [lia| lia| exact T168]).
  assert (Z176 : L5.u64_at RSEGS M7v (sp - 176) (ois + 120)) by (apply T27; [lia| lia| exact T176]).
  assert (Z184 : L5.u64_at RSEGS M7v (sp - 184) ((ois / 8) + 2147450880)) by (apply T27; [lia| lia| exact T184]).
  assert (U80 : L5.u8_at RSEGS M7v (ois + 80) ((c + 1) mod 256)).
  { replace (c + 1) with (c - 1 + 2) by lia. apply (PMF.u8_of_u64 RSEGS M7v (ois + 80) (c - 1 + 2)); [lia| exact G80]. }
  assert (TB' : Z.testbit ((c + 1) mod 256) 0 = true) by (apply odd_byte; lia).
  assert (B256' : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
  assert (U112 : L5.u32_at RSEGS M7v (ois + 112) 8).
  { rewrite <- VIS3 in E112. apply (proj1 (L5A.u32_at_vis H M3 (ois + 112) 8 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))) in E112.
    rewrite <- VIS7. apply (proj2 (L5A.u32_at_vis H6 M7 (ois + 112) 8 (XV (ois + 112) 4 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M3 M7); [|lia|lia|exact E112]. intros i Hi.
    rewrite FR7 by (unfold W7; lia). rewrite PRES6'; [| lia| apply (L5SAR.obj_client L ar LB FF _ _ ois 272 _ AOB); lia| lia].
    apply (proj1 PRES4). split; [lia|]. split; [apply (L5SAR.obj_client L ar LB FF _ _ ois 272 _ AOB); lia| intros rr []]. }
  assert (R7sp : getr R7 (reg 2) = Z_to_bv 64 (sp - 192)) by exact gR2.
  assert (R7s0 : getr R7 (reg 8) = Z_to_bv 64 (ois + 16)) by exact gR8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as UR1. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as UR8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as UR9. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as UR18.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as UR19. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as UR20.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as UR21. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as UR22.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as UR23. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as UR24.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 25))) as UR25. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 26))) as UR26.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 27))) as UR27. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed P (PMAISP.aicCl4_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx7 R7 M7v
                (fun j => match j with 2%nat => sp | 33%nat => ois | 38%nat => (c + 1) mod 256 | 40%nat => n | 41%nat => p
                          | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9))
                          | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20))
                          | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23))
                          | 52%nat => bv_unsigned (getr R0 (reg 24)) | 53%nat => bv_unsigned (getr R0 (reg 25)) | 54%nat => bv_unsigned (getr R0 (reg 26))
                          | 55%nat => bv_unsigned (getr R0 (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MS8 & KS8 & tR1 & tR2 & tR8 & tR9 & tR10 & tR11 & tR12 & tR13 & tR14 & tR15 & tR16
                 & tR18 & tR19 & tR20 & tR21 & tR22 & tR23 & tR24 & tR25 & tR26 & tR27 & H48 & H40 & H32 & H104).
  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite tR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xa8d80 W_a8964 r F_a8964 eq_refl D_a8964 R8ra ltac:(lia) Hr2) as MS9.
  set (WZ8 := fun a => (sp - 272 <= a < sp - 272 + 80) \/ (ois + 32 <= a < ois + 32 + 24) \/ (ois + 104 <= a < ois + 104 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 M7 model7 fx7 fx8 R7 0xac320 R8 r M8v WZ8 K HH7 AM7).
  { rewrite HID7, VIS7. eapply msteps_trans; [exact MS8| exact MS9]. }
  { rewrite HID7, VIS7. exact MG8. }
  { rewrite HID7, VIS7. intros a Ha N. apply FZ8; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a Ha [Wa|[Wa|Wa]].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 ois 272 a AOB); lia| lia].
    - split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 ois 272 a AOB); lia| lia]. }
  intros MF modelF HHF AMF MRTF HIDF VISF MGMF FRF VVF.
  assert (EK7F : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M7 MF).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M7 MF WZ8 FRF). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (EK0F : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 MF).
  { apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M2 MF EK). apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M7 MF EK27 EK7F). }
  assert (ACCF : PMSPA.accA MF ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M2 MF (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M7 MF EK27 EK7F) WAPP FRB ois 272 AO ACC)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK2 cr2 Aw4 MF modelF ois 272 sp 20480 HHF AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEFF & _).
  (* [comment removed for export] *)
  assert (A2F : forall a, ois <= a < ois + 272 -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 80 <= a < ois + 116) -> MF (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1 N2. rewrite FRF by (unfold WZ8; lia). rewrite FR7 by (unfold W7; lia).
    rewrite PRES6'; [| lia| apply (L5SAR.obj_client L ar LB FF _ _ ois 272 a AOB); lia| lia].
    rewrite (proj1 PRES4 a). 2:{ split; [lia|]. split; [apply (L5SAR.obj_client L ar LB FF _ _ ois 272 a AOB); lia| intros rr []]. }
    apply FR3; [lia| unfold W3; lia]. }
  assert (A7F : forall a, ois <= a < ois + 272 -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 104 <= a < ois + 112) -> MF (Z_to_bv 64 a) = M7v (Z_to_bv 64 a)).
  { intros a Ha N2 N3. rewrite FRF by (unfold WZ8; lia). rewrite <- VIS7. symmetry. apply (AsanAcct.mrestrict_visible H6 M7).
    pose proof (XV a 1 ltac:(lia) 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (A8F : forall a, (ois <= a < ois + 272) -> MF (Z_to_bv 64 a) = M8v (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- VISF. rewrite HID7. symmetry. apply (AsanAcct.mrestrict_visible H6 MF).
    pose proof (XV a 1 ltac:(lia) 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (SHBF : shadow_blk MF p c).
  { assert (SX : forall x, in_shadow_of p c x -> MF (Z_to_bv 64 x) = M4 (Z_to_bv 64 x)).
    { intros x Hx. assert (Hx' := Hx). unfold in_shadow_of, S, SB in Hx'.
      rewrite FRF by (unfold WZ8; destruct OBIG; lia). rewrite FR7 by (unfold W7; destruct OBIG; destruct Q5 as (_ & [Q|Q] & _); lia).
      apply PRES6; [lia| do 6 right; exists (p, c); split; [left; reflexivity| exact Hx]| destruct Q5 as (_ & [Q|Q] & _); lia]. }
    destruct SHBp as [SZp SPp]. split.
    - intros j Hj. unfold byte_at. rewrite SX. apply SZp. exact Hj. unfold in_shadow_of, S.
      pose proof (PMASTR.shadow_idx p c j P8 ltac:(lia) ltac:(lia) ltac:(pose proof (Z.mul_div_le c 8 ltac:(lia)); lia)). lia.
    - intros NZ. exfalso. apply NZ. lia. }
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  destruct HC as (H0 & H24 & H120 & H152 & H156 & H160 & H168 & H176).
  replace (c - 1 + 2) with (c + 1) in G80 by lia.
  unfold PMSPA.cfg in KONT.
  apply (KONT fx8 R8 MF modelF LK2 Aw4 (PM.VLong c n p) (PM.STRM p (n + p) 0) cr2).
  - apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
    assert (CH : forall k, In k PMAISP.KS_aicCl4 -> In k PMAISP.KS_aicCl3 -> In k PMAISP.KS_aicCl2 -> In k PMAIS.CSK -> getr R8 (reg k) = getr R0 (reg k)).
    { intros k' H1 H2 H3 H4'. assert (Hc : In k' L5SAR.cs_all) by (destruct H4' as [<-|[<-|[]]]; inl).
      rewrite (KS8 k' H1), (CS7 k' H2), (CS6 k' Hc), (CS5 k' H3), (CS4 k' Hc), (CS3 k') by (destruct H4' as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      apply MCSK. exact H4'. }
    destruct Hk as [<-|Hk]; [rewrite tR2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; [inl| inl| inl| left; reflexivity]|].
    destruct Hk as [<-|Hk]; [apply CH; [inl| inl| inl| right; left; reflexivity]|].
    destruct Hk as [<-|Hk]; [rewrite tR8; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR9; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR18; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR19; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR20; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR21; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR22; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR23; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR24; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR25; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR26; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR27; apply Z_to_bv_bv_unsigned|].
    destruct Hk.
  - unfold PMAIS.iss_at, PM.iss_at. cbn [PM.vs_data PM.vs_size PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_classic_imp pa_vp_iss_ios PMA.AD ADDR_A] in *.
    split; [a64 A2F H0 M2|].
    split; [apply (L5.defined_sub MF ois 272); [exact ODEFF| lia| lia]|].
    split; [intros x Hx; apply ACCF; lia|].
    split; [a64 A2F V16 M2|].
    split; [a64 A2F H24 M2|].
    split; [a64 A8F H32 M8v|].
    split; [a64 A8F H40 M8v|].
    split; [a64 A8F H48 M8v|].
    split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply A2F; lia| lia| lia|];
            apply (PMCG.u64_of_zeros RSEGS M2 (ois + 64)); [apply (PMCG.zeros_sub M2 (ois + 32) 48); [exact Z32| lia| lia]| lia| lia]|].
    split. { unfold PM.vstr_at. split; [apply (L5.defined_sub MF ois 272); [exact ODEFF| lia| lia]|].
             split; [intros x Hx; apply ACCF; lia|].
             replace (ois + 80 + 8) with (ois + 88) by lia. replace (ois + 80 + 16) with (ois + 96) by lia.
             split; [a64 A7F G80 M7v|]. split; [a64 A7F G88 M7v|]. split; [a64 A7F G96 M7v|].
             split; [lia|]. split; [lia|]. split; [lia|].
             split; [apply (L5.defined_grows M6 MF); [intros x X; apply MGMF, MGM7; exact X| exact DEF6]|].
             apply (PMASTR.aacc_of_block MF p c p c SHBF); [exact P8| lia| lia| lia]. }
    split; [a64 A8F H104 M8v|].
    split; [a32 A7F U112 M7v|].
    split. { unfold PM.iosb_at. cbn [pa_classic_imp PMA.AD ADDR_A].
             replace (ois + 120 + 32) with (ois + 152) by lia. replace (ois + 120 + 36) with (ois + 156) by lia.
             replace (ois + 120 + 40) with (ois + 160) by lia. replace (ois + 120 + 48) with (ois + 168) by lia. replace (ois + 120 + 56) with (ois + 176) by lia.
             split; [a64 A2F H120 M2|]. split; [a32 A2F H152 M2|]. split; [a32 A2F H156 M2|]. split; [a64 A2F H160 M2|].
             split; [a64 A2F H168 M2|].
             split; [apply (PMF.zeros_at_agree M2); [intros i Hi; apply A2F; lia| exact H176]|].
             split; [apply (L5.defined_sub MF ois 272); [exact ODEFF| lia| lia]|].
             split; [intros x Hx; apply ACCF; lia| left; reflexivity]. }
    split; lia.
  - reflexivity.
  - cbn [PM.vs_data PM.sm_g]. reflexivity.
  - reflexivity.
  - apply (PMAIS1.loc_ok_agree M2 MF true); [|exact LOC]. intros a Ha.
    rewrite FRF by (unfold WZ8; lia). rewrite FR7 by (unfold W7; destruct Q1 as [Q|Q]; lia).
    assert (CLa : aclient L ar LB FF 0 0 a).
    { unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
      apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_foot. left. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit PMA.AD ADDR_A app].
      destruct Ha as [X|X]; [exists (0x672532, 0x672c70); split; [right; right; left; reflexivity| cbn [fst snd]; lia]
                                  | exists (0x673398, 0x6733f0); split; [right; right; right; left; reflexivity| cbn [fst snd]; lia]]. }
    rewrite PRES6'; [| lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact CLa| lia]| destruct Q1 as [Q|Q]; lia].
    rewrite (proj1 PRES4 a). 2:{ split; [lia|]. split; [apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact CLa| unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia]| intros rr []]. }
    apply FR3; [lia| unfold W3; lia].
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M0 MF EK0F).
    + pose proof (L5SAR.astk_grows ar M7 MF sp 20480 ASTK7 MGMF) as (_ & _ & _ & _ & SDF & _). exact SDF.
    + apply (L5SAR.dk_trans L ar LB FF sp 20480 M0 M2 MF DK).
      apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M3 MF (L5SAR.dk_grows L ar LB FF sp 20480 M2 M3 MGM3)).
      apply (L5SAR.dk_trans L ar LB FF sp 20480 M3 M4 MF).
      { apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 240) PMSPA.OPNEW_SCR [] M3 M4 PRES4); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia. }
      apply (L5SAR.dk_trans L ar LB FF sp 20480 M4 M6 MF).
      { apply (L5SAR.dk_mem L ar LB FF sp 20480 (sp - 240) 2560 (fun a => p <= a < p + n) M4 M6 PRES6' SDEF6).
        - intros a Ha. destruct (BYTES (a - p) ltac:(lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (p + (a - p)) with a in Bv by lia. rewrite Bv. discriminate.
        - intros a. destruct (L5SAR.rng_dec a p (p + n)) as [X|X]; [left; exact X| right; exact X].
        - lia. - lia. }
      apply (L5SAR.dk_trans L ar LB FF sp 20480 M6 M7 MF (L5SAR.dk_grows L ar LB FF sp 20480 M6 M7 MGM7) (L5SAR.dk_grows L ar LB FF sp 20480 M7 MF MGMF)).
  - unfold PMAIS.cost. cbn [PM.vs_size]. replace (n + 32) with (n + 16 + 16) by lia. exact CRKEEP.
  - apply (L5LZ.model_rt_trans model0 model7 modelF); [|exact MRTF]. apply (L5LZ.model_rt_trans model0 model6 model7); [|exact MRT7].
    apply (L5LZ.model_rt_trans model0 model5 model6); [|exact RT6]. apply (L5LZ.model_rt_trans model0 model4 model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model0 model3 model4); [|exact RT4]. apply (L5LZ.model_rt_trans model0 model2 model3); [exact MRT| exact MRT3].
  - exact INCK.
  - intros x Hx. apply IA4. apply INCA. exact Hx.
  - exact AMF.
  - exact HHF.
Qed.

End Stage.
End PMAIS3L.
