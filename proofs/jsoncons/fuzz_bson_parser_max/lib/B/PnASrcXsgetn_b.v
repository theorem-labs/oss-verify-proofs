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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnASrcKit_b PnARzKit_b PnASrcXsgetnP_b Ba0_code_rd5658_d565c_b.
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

Module PMAXG.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros AC H1 H2 x Hx. apply AC. clear - H1 H2 Hx. lia. Qed.

(* [comment removed for export] *)
Lemma vstr_keepA (M M' : word -> option byte) o s : 0 <= o -> o + 24 <= 2 ^ 64 -> PMFA.agA M M' o 24 ->
  (forall c n p, s = PM.VLong c n p -> L5.defined M' p c /\ PMFA.agsh M M' p c) ->
  PM.vstr_at RSEGS PMSPA.accA M o s -> PM.vstr_at RSEGS PMSPA.accA M' o s.
Proof.
  intros Ho Ho' [AG SH] BLK (D & Cc & Hs). split; [apply (L5C.defined_agree M M' o 24 AG D)|].
  split; [apply (PMFA.accA_agree M M' o 24 SH Cc)|].
  destruct s as [n|c n p].
  - destruct Hs as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact B0].
  - destruct Hs as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (BLK c n p eq_refl) as [DB' SHp].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact W0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact W8]|].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact W16]|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact DB'|]. exact (PMFA.accA_agree M M' p c SHp CB).
Qed.

(* [comment removed for export] *)
Lemma iss_g_updA (M M' : word -> option byte) ois str g eg st g' :
  PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str (PM.STRM g eg st) -> 0 <= ois -> ois + 272 <= 2 ^ 64 ->
  PMFA.agA M M' ois 40 -> PMFA.agA M M' (ois + 48) 224 -> PMFA.agsh M M' (ois + 40) 8 -> L5.defined M' ois 272 ->
  (forall c n p, str = PM.VLong c n p -> L5.defined M' p c /\ PMFA.agsh M M' p c) ->
  L5.u64_at RSEGS M' (ois + 40) g' -> PM.vs_data (ois + 80) str <= g' <= eg ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M' ois str (PM.STRM g' eg st).
Proof.
  intros IA Ho Ho' [AG1 SH1] [AG2 SH2] SH3 DF AGB C40 GR.
  destruct IA as (H0 & D & Cc & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2).
  destruct IOS as (I0 & I32 & I36 & I40 & I48 & IZ & ID & IC & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
  assert (U64 : forall a v, ois <= a -> a + 8 <= ois + 40 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U64b : forall a v, ois + 48 <= a -> a + 8 <= ois + 272 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact X]. }
  assert (SHA : PMFA.agsh M M' ois 272).
  { intros x Hx. destruct (Z_lt_le_dec x (ois + 40)) as [X|X]; [apply SH1; lia|].
    destruct (Z_lt_le_dec x (ois + 48)) as [Y|Y]; [apply SH3; lia| apply SH2; lia]. }
  unfold PM.iss_at, PM.iosb_at. cbn [PM.sm_g PM.sm_eg PM.sm_st].
  split; [apply U64; [lia|lia|exact H0]|]. split; [apply (L5.defined_sub M' ois 272); [exact DF| lia| lia]|].
  split; [apply (PMFA.accA_agree M M' ois 120); [intros x Hx; apply SHA; lia| exact Cc]|].
  split; [apply U64; [lia|lia|exact H16]|]. split; [apply U64; [lia|lia|exact H24]|]. split; [apply U64; [lia|lia|exact H32]|].
  split; [exact C40|]. split; [apply U64b; [lia|lia|exact H48]|]. split; [apply U64b; [lia|lia|exact H64]|].
  split; [apply (vstr_keepA M M' (ois + 80)); [lia|lia| split; [intros i Hi; apply AG2; lia| intros x Hx; apply SHA; lia]| exact AGB| exact VS]|].
  split; [apply U64b; [lia|lia|exact H104]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H112]|].
  split.
  { split; [apply U64b; [lia|lia|exact I0]|]. split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact I32]|].
    split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact I36]|].
    split; [apply U64b; [lia|lia|exact I40]|]. split; [apply U64b; [lia|lia|exact I48]|].
    split; [apply (PMF.zeros_at_agree M M'); [intros i Hi; apply AG2; lia| exact IZ]|].
    split; [apply (L5.defined_sub M' ois 272); [exact DF| lia| lia]|].
    split; [apply (PMFA.accA_agree M M' (ois + 120) 152); [intros x Hx; apply SHA; lia| exact IC]|].
    exact IST. }
  split; [exact E1| lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem xsgetn_ok : PMA.xsgetn_spec L ar HI.
Proof.
  unfold PMA.xsgetn_spec, PMSPA.xsgetn_spec.
  intros fx R M model K LB FF LK Aw cr sp r ois dst str sm HH AM K0 ENT FRM FRS A10 A11 A12 AO O8 ISS BASE OWN DSTB DACC APART KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  change (PMSPA.pm_scr 2) with 16384 in *. unfold PM.CHUNK in *.
  pose proof (PMKA.aobj_of_aobjA FF ois 272 AO O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 sp 16384 HH AOB ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 16384 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & WST).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  destruct sm as [g eg st]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof (PMASK.iss_size_ltA M ois str _ ISS) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  pose proof ISS as (I0 & IDEF & IACC & I16 & I24 & I32 & I40 & I48 & I64 & IVS & I104 & I112 & IIOS & IE1 & IE2).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_strbuf PMA.AD ADDR_A] in *.
  assert (VI64 : forall a v, ois <= a -> a + 8 <= ois + 272 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Xa Xb X. apply (proj2 (L5A.u64_at_vis H M a v (L5A.avis_sub H ois 272 a 8 OVIS Xa Xb) ltac:(lia) ltac:(lia))). exact X. }
  assert (VI32 : forall a v, ois <= a -> a + 4 <= ois + 272 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS MV a v).
  { intros a v Xa Xb X. apply (proj2 (L5A.u32_at_vis H M a v (L5A.avis_sub H ois 272 a 4 OVIS Xa Xb) ltac:(lia) ltac:(lia))). exact X. }
  assert (J16 : L5.u64_at RSEGS MV (ois + 16) 1265728) by (apply VI64; [lia| lia| exact I16]).
  assert (J40 : L5.u64_at RSEGS MV (ois + 16 + 24) g) by (replace (ois + 16 + 24) with (ois + 40) by lia; apply VI64; [lia| lia| exact I40]).
  assert (J48 : L5.u64_at RSEGS MV (ois + 16 + 32) eg) by (replace (ois + 16 + 32) with (ois + 48) by lia; apply VI64; [lia| lia| exact I48]).
  assert (J64 : L5.u64_at RSEGS MV (ois + 16 + 48) 0) by (replace (ois + 16 + 48) with (ois + 64) by lia; apply VI64; [lia| lia| exact I64]).
  assert (J104 : L5.u64_at RSEGS MV (ois + 16 + 88) eg) by (replace (ois + 16 + 88) with (ois + 104) by lia; apply VI64; [lia| lia| exact I104]).
  assert (J112 : L5.u32_at RSEGS MV (ois + 16 + 96) 8) by (replace (ois + 16 + 96) with (ois + 112) by lia; apply VI32; [lia| lia| exact I112]).
  assert (DOB : sp - 80 + 80 <= ois + 16 \/ ois + 16 + 256 <= sp - 80) by lia.
  assert (A8 : (ois + 16) mod 8 = 0) by (replace (ois + 16) with (ois + 2 * 8) by lia; rewrite Z.mod_add by lia; exact O8).
  destruct DSTB as (B & m & DIN & DLO & DHI).
  destruct (BRB (B, m) DIN) as (BQ0 & BQ1). cbn [fst snd] in BQ0, BQ1.
  (* [comment removed for export] *)
  assert (WHERE : (ois + 81 <= g /\ eg <= ois + 104) \/ (exists c n p, str = PM.VLong c n p /\ In (p, c) LB /\ p <= g /\ eg <= p + c)).
  { pose proof (PMASK.iss_unread_whereA M ois str _ ISS) as [(X1 & X2)|(c & n & p & -> & X1 & X2)]; cbn [PM.sm_g PM.sm_eg] in *; [left; lia|].
    right. exists c, n, p. split; [reflexivity|]. split; [apply OWN; left; reflexivity| lia]. }
  assert (G0 : 4096 <= g /\ eg <= 2 ^ 47).
  { destruct WHERE as [(X1 & X2)|(c & n & p & -> & Hin & X1 & X2)]; [lia|]. destruct (BRB (p, c) Hin) as (Y0 & Y1). cbn [fst snd] in Y0, Y1.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (p, c) Hin) as ((Z0 & _) & _). cbn [fst snd] in Z0. lia. }
  destruct G0 as (G0 & GHI).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  change (bv_modulus 64) with (2 ^ 64) in *.
  (* [comment removed for export] *)
  assert (EKF : forall M0 M1 (P : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
            (forall a, P a -> sp - 80 <= a < sp) -> ri_inv HI LB FF LK cr Aw M0 (vml_of model) -> L5SAR.ek L ar LB FF sp 16384 [] M0 M1).
  { intros M0 M1 P FR0 HP HH0. apply (L5SAR.ek_piece L ar LB FF sp 16384 [] M0 M1 P FR0). intros a Ha Hc _ X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M0 _ sp 16384 a HH0 SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; specialize (HP a X); lia|].
    specialize (HP a X). lia. }
  unfold PMSPA.cfg. cbn [pa_xsgetn PMA.AD ADDR_A].
  destruct (Z.eq_dec eg g) as [EQ|NE].
  - (* [comment removed for export] *)
    rewrite EQ in J48, J104.
    LeanFeed.pfeed P (PMAXGP.axgA0_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) ltac:(first [assumption | unfold PMAXGP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & MS1 & KS1 & X10 & _).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xda908 W_d830c r F_d830c eq_refl D_d830c R1ra ltac:(lia) Hr2) as MS2.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xda800 R1 r M1v (fun a => sp - 80 <= a < sp - 80 + 80) K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { exact FR1. }
    { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar LB FF 0 0 a); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1.
    assert (EK1 : L5SAR.ek L ar LB FF sp 16384 [] M M1) by (apply (EKF M M1 _ FR1'); [intros a X; lia| exact HH]).
    apply (KONT fx1 R1 M1 model1 LK Aw 0).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. revert k Hk. apply sub_in. vm_compute. reflexivity.
    + rewrite L5K.rl10. exact X10.
    + lia.
    + replace (g + 0) with g by lia. replace (Z.min 16384 (eg - g)) with 0 by lia.
      apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 16384 [] M M1 EK1 PMKA.wapp_nil FRB BRB _ _ _ AO OWN); [intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact ISS].
    + intros i Hi. lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 16384 _ M M1).
      * intros a (Ha & Hc & _). apply EK1. split; [exact Ha|]. split; [exact Hc| intros rr []].
      * apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
      * apply (L5SAR.dk_grows L ar LB FF sp 16384 M M1 MGM1).
    + exact MRT1.
    + apply incl_refl.
    + apply incl_refl.
    + exact AM1.
    + exact HH1.
  - (* [comment removed for export] *)
    set (len := Z.min 16384 (eg - g)).
    assert (LEN : 1 <= len <= 16384) by (unfold len; lia).
    assert (HEAD : exists fx1 R1 M1v, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xda800) MV (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x77c8c) M1v (seg_rom RSEGS))
              /\ mem_grows MV M1v /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
              /\ (forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
              /\ getr R1 (reg 1) = Z_to_bv 64 895188 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64)
              /\ getr R1 (reg 8) = Z_to_bv 64 0 /\ getr R1 (reg 9) = Z_to_bv 64 16384
              /\ getr R1 (reg 10) = Z_to_bv 64 dst /\ getr R1 (reg 11) = Z_to_bv 64 g /\ getr R1 (reg 12) = Z_to_bv 64 len
              /\ getr R1 (reg 19) = Z_to_bv 64 (ois + 16) /\ getr R1 (reg 20) = Z_to_bv 64 len
              /\ getr R1 (reg 21) = Z_to_bv 64 2147483647 /\ getr R1 (reg 22) = Z_to_bv 64 18446744073709551615
              /\ L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22))) /\ L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21)))
              /\ L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20))) /\ L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19)))
              /\ L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18))) /\ L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9)))
              /\ L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1)))).
    { destruct (Z_le_gt_dec (eg - g) 16384) as [LE|GT].
      - assert (len = eg - g) as -> by (unfold len; lia).
        pose proof (PMAXGP.axgA1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => eg - g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) as P.
        cbn beta iota in P. replace (g + (eg - g)) with eg in P by lia.
        L5SAR.feed P ltac:(first [assumption | unfold PMAXGP.aligned; lia | lia]).
        destruct P as (fx1 & R1 & M1v & MG & _ & FRZ & MS & KS & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & X20 & X21 & X22 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
        exists fx1, R1, M1v. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
        repeat (split; [assumption|]). assumption.
      - assert (len = 16384) as -> by (unfold len; lia).
        pose proof (PMAXGP.axgA2_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => eg - g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) as P.
        cbn beta iota in P. replace (g + (eg - g)) with eg in P by lia.
        L5SAR.feed P ltac:(first [assumption | unfold PMAXGP.aligned; lia | lia]).
        destruct P as (fx1 & R1 & M1v & MG & _ & FRZ & MS & KS & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & X20 & X21 & X22 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
        assert (X12 : getr R1 (reg 12) = Z_to_bv 64 16384) by (rewrite (KS 12%nat) by inl; exact A12).
        exists fx1, R1, M1v. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
        repeat (split; [assumption|]). assumption. }
    destruct HEAD as (fx1 & R1 & M1v & MS1 & MG1 & FRZ1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X19 & X20 & X21 & X22 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xda800 R1 0x77c8c M1v (fun a => sp - 80 <= a < sp - 80 + 80) K HH AM MS1 MG1 FRZ1).
    { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar LB FF 0 0 a); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK1 : L5SAR.ek L ar LB FF sp 16384 [] M M1) by (apply (EKF M M1 _ FR1); [intros a X; lia| exact HH]).
    assert (ASTK1 : L5CA.astk ar M1 sp 16384) by (apply (L5SAR.astk_grows ar M M1 sp 16384 ASTK MGM1)).
    assert (NSH1 : forall x, sp - 80 <= x < sp - 80 + 80 -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
    (* [comment removed for export] *)
    assert (SRC : ((exists q A0, In (q, A0) LB /\ q <= g /\ g + len <= q + A0) \/ (exists o' sz', L5CA.aobj FF o' sz' /\ o' <= g /\ g + len <= o' + sz'))
                  /\ L5.defined M1 g len /\ aacc M1 g len).
    { destruct IVS as (VD & VA & VX).
      destruct WHERE as [(Y1 & Y2)|(c & n & p & Es & Hin & Y1 & Y2)].
      - split; [right; exists ois, 272; split; [exact AOB| unfold len; lia]|]. split.
        + apply (L5.defined_grows M M1 _ _ MGM1). apply (L5.defined_sub M ois 120); [exact IDEF| lia| unfold len; lia].
        + apply (PMFA.accA_agree M M1 g len); [apply (PMARZK.agsh_frame M M1 _ g len FR1 NSH1); lia|].
          apply (aacc_sub M (ois + 80) 24); [exact VA| lia| unfold len; lia].
      - subst str. destruct VX as (_ & _ & _ & _ & _ & _ & DP & ACP).
        split; [left; exists p, c; split; [exact Hin| unfold len; lia]|]. destruct (BRB (p, c) Hin) as (Y0 & Y3). cbn [fst snd] in Y0, Y3. split.
        + apply (L5.defined_grows M M1 _ _ MGM1). apply (L5.defined_sub M p c); [exact DP| lia| unfold len; lia].
        + apply (PMFA.accA_agree M M1 g len); [apply (PMARZK.agsh_frame M M1 _ g len FR1 NSH1); lia|].
          apply (aacc_sub M p c); [exact ACP| lia| unfold len; lia]. }
    destruct SRC as (SCONT & SDEF1 & SACC1).
    assert (DACC1 : aacc M1 dst len).
    { apply (PMFA.accA_agree M M1 dst len); [apply (PMARZK.agsh_frame M M1 _ dst len FR1 NSH1); lia|].
      apply (aacc_sub M dst 16384); [exact DACC| lia| lia]. }
    assert (DDEF1 : L5.defined M1 dst len).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (B, m) DIN) as (_ & DB & _). cbn [fst snd] in DB.
      apply (L5.defined_grows M M1 _ _ MGM1). apply (L5.defined_sub M B m); [exact DB| lia| lia]. }
    assert (R1_4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; exact Rtp).
    (* [comment removed for export] *)
    apply (PMARZK.move_stage_pre L ar C HI LY HIok IL ICok ILY LB FF LK cr Aw M1 model1 fx1 fx1 R1 0x77c8c R1 dst g len (sp - 64) 895188 K
             HH1 AM1 K0 (mst_refl _ _) X1 ltac:(split; [lia| reflexivity]) X2 R1_4 X10 X11 X12 ltac:(lia)).
    { apply (L5SAR.astk_sub ar M1 M1 sp 16384 64 2560 ASTK1 (fun x X => X)); [lia| lia| lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    { exists B, m. split; [exact DIN| unfold len; lia]. }
    { exact DDEF1. }
    { exact DACC1. }
    { exact SCONT. }
    { exact SDEF1. }
    { exact SACC1. }
    { unfold len; lia. }
    intros R2 M2 model2 RP2 R2_10 PRES2 SDEF2 D2 MRT2 AM2 HH2.
    (* [comment removed for export] *)
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 64) 2560 a -> ~ (dst <= a < dst + len) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by exact PRES2.
    assert (DCEIL : dst + 16384 <= ahl_ceil ar).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (B, m) DIN) as ((Z0 & _ & _ & _ & Z4 & _) & _). cbn [fst snd] in Z4. lia. }
    assert (DAPP : dst + 16384 <= 0x7fff7000 \/ 0x10007fff8000 <= dst).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (B, m) DIN) as ((_ & _ & _ & _ & _ & Z5) & _). cbn [fst snd] in Z5.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Z5. lia. }
    assert (STK12 : forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply KEEP2; [lia| apply L5SAR.stack_client; lia| lia]. }
    assert (OBJ12 : forall a, ois <= a < ois + 272 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m ois 272 HH DIN AO) as [Z1|Z1];
        (apply KEEP2; [lia| apply (L5SAR.obj_client L ar LB FF _ _ ois 272 a AOB); lia| lia]). }
    assert (ASTK2 : L5CA.astk ar M2 sp 16384).
    { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M1 M1 M2 _ sp 16384 (sp - 64) 2560 HH1 ASTK1 (fun x X => X)); [| exact SDEF2| lia| lia| lia].
      intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; lia| lia]. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M2 model2 HH2) as (_ & VIS2 & _ & VFS2 & VBLK2 & _).
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M2 model2 ois 272 sp 16384 HH2 AOB ltac:(lia) ltac:(reflexivity))
      as (_ & _ & ODEF2 & OVIS2 & _).
    (* [comment removed for export] *)
    set (W := [(ois + 40, 8); (dst, 16384)] : list L5.range).
    assert (EK12 : L5SAR.ek L ar LB FF sp 16384 W M1 M2).
    { apply (L5SAR.ek_mem L ar LB FF sp 16384 (sp - 64) 2560 (fun a => dst <= a < dst + len) W M1 M2 KEEP2); [lia| lia|].
      intros a _ OW X. apply (OW (dst, 16384)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold len in X; lia]. }
    assert (EK01 : L5SAR.ek L ar LB FF sp 16384 W M M1) by (apply (L5SAR.ek_W L ar LB FF sp 16384 W [] M M1 EK1); intros a _; apply L5C.outside_nil).
    assert (EK02 : L5SAR.ek L ar LB FF sp 16384 W M M2) by exact (L5SAR.ek_trans L ar LB FF sp 16384 W M M1 M2 EK01 EK12).
    assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2).
    { apply (PMASK.base_keep L ar C LY LB FF sp 16384 W M M2 EK02); [| exact BASE].
      pose proof (PMASK.blk_img L ar C HI LY HIok LB FF LK cr Aw M _ B m HH DIN) as BI.
      intros a Ha rr Hr Hin. unfold W in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
    pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 HH2 BASE2) as (Y0 & Y1 & Y2).
    pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 sp 16384 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & WST2).
    set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
    (* [comment removed for export] *)
    assert (OB02 : forall a, ois <= a < ois + 272 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite OBJ12 by exact Ha. apply FR1; [lia| lia]. }
    assert (U2 : forall a v, ois <= a -> a + 8 <= ois + 272 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Xa Xb X. apply (proj2 (L5A.u64_at_vis H2 M2 a v (L5A.avis_sub H2 ois 272 a 8 OVIS2 Xa Xb) ltac:(lia) ltac:(lia))).
      apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply OB02; lia| lia| lia| exact X]. }
    assert (U2b : forall a v, ois <= a -> a + 4 <= ois + 272 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS MV2 a v).
    { intros a v Xa Xb X. apply (proj2 (L5A.u32_at_vis H2 M2 a v (L5A.avis_sub H2 ois 272 a 4 OVIS2 Xa Xb) ltac:(lia) ltac:(lia))).
      apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply OB02; lia| lia| lia| exact X]. }
    assert (K16 : L5.u64_at RSEGS MV2 (ois + 16) 1265728) by (apply U2; [lia| lia| exact I16]).
    assert (K40 : L5.u64_at RSEGS MV2 (ois + 16 + 24) g) by (replace (ois + 16 + 24) with (ois + 40) by lia; apply U2; [lia| lia| exact I40]).
    assert (K48 : L5.u64_at RSEGS MV2 (ois + 16 + 32) eg) by (replace (ois + 16 + 32) with (ois + 48) by lia; apply U2; [lia| lia| exact I48]).
    assert (K64 : L5.u64_at RSEGS MV2 (ois + 16 + 48) 0) by (replace (ois + 16 + 48) with (ois + 64) by lia; apply U2; [lia| lia| exact I64]).
    assert (K104 : L5.u64_at RSEGS MV2 (ois + 16 + 88) eg) by (replace (ois + 16 + 88) with (ois + 104) by lia; apply U2; [lia| lia| exact I104]).
    assert (K112 : L5.u32_at RSEGS MV2 (ois + 16 + 96) 8) by (replace (ois + 16 + 96) with (ois + 112) by lia; apply U2b; [lia| lia| exact I112]).
    assert (KW : L5.writable RSEGS MV2 (ois + 16 + 24) 8).
    { apply (proj2 (L5A.writable_vis H2 M2 (ois + 16 + 24) 8 (L5A.avis_sub H2 ois 272 (ois + 16 + 24) 8 OVIS2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 ois 272); [exact ODEF2| lia| lia]| lia| lia]. }
    assert (SV2 : forall k v, 8 <= k <= 64 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS MV2 (sp - k) v).
    { intros k v Hk X. rewrite <- VIS1 in X.
      assert (Xm1 : L5.u64_at RSEGS M1 (sp - k) v) by exact (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X).
      apply (proj2 (L5A.u64_at_vis H2 M2 (sp - k) v (VIS2 (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply STK12; lia| lia| lia| exact Xm1]. }
    pose proof (SV2 8 _ ltac:(lia) S8) as T8. pose proof (SV2 16 _ ltac:(lia) S16) as T16. pose proof (SV2 24 _ ltac:(lia) S24) as T24.
    pose proof (SV2 32 _ ltac:(lia) S32) as T32. pose proof (SV2 40 _ ltac:(lia) S40) as T40. pose proof (SV2 48 _ ltac:(lia) S48) as T48.
    pose proof (SV2 56 _ ltac:(lia) S56) as T56. pose proof (SV2 64 _ ltac:(lia) S64) as T64.
    assert (C2 : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; exact (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
    assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (C2 2%nat) by inl; exact X2).
    assert (R2_8 : getr R2 (reg 8) = Z_to_bv 64 0) by (rewrite (C2 8%nat) by inl; exact X8).
    assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 16384) by (rewrite (C2 9%nat) by inl; exact X9).
    assert (R2_19 : getr R2 (reg 19) = Z_to_bv 64 (ois + 16)) by (rewrite (C2 19%nat) by inl; exact X19).
    assert (R2_20 : getr R2 (reg 20) = Z_to_bv 64 len) by (rewrite (C2 20%nat) by inl; exact X20).
    assert (R2_21 : getr R2 (reg 21) = Z_to_bv 64 2147483647) by (rewrite (C2 21%nat) by inl; exact X21).
    assert (R2_22 : getr R2 (reg 22) = Z_to_bv 64 18446744073709551615) by (rewrite (C2 22%nat) by inl; exact X22).
    (* [comment removed for export] *)
    assert (TAIL : exists fx3 R3 M3v, msteps RSEGS (@mkst fx1 R2 (Z_to_bv 64 0xda8d4) MV2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xda908) M3v (seg_rom RSEGS))
              /\ mem_grows MV2 M3v
              /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (ois + 16 + 24 <= i < ois + 16 + 24 + 8) -> M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
              /\ (forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
              /\ getr R3 (reg 1) = Z_to_bv 64 (bv_unsigned (getr R (reg 1))) /\ getr R3 (reg 2) = Z_to_bv 64 sp
              /\ getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) /\ getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9)))
              /\ getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) /\ getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19)))
              /\ getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) /\ getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))
              /\ getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22)))
              /\ getr R3 (reg 10) = Z_to_bv 64 len /\ L5.u64_at RSEGS M3v (ois + 16 + 24) (g + len)).
    { destruct (Z.eq_dec len 16384) as [E16|N16].
      - idtac.
        rewrite E16 in R2_20.
        LeanFeed.pfeed P (PMAXGP.axgC1_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => g | 34%nat => eg | 36%nat => ois + 16
                     | 37%nat => bv_unsigned (getr R (reg 1)) | 38%nat => bv_unsigned (getr R (reg 8)) | 39%nat => bv_unsigned (getr R (reg 9))
                     | 40%nat => bv_unsigned (getr R (reg 18)) | 41%nat => bv_unsigned (getr R (reg 19)) | 42%nat => bv_unsigned (getr R (reg 20))
                     | 43%nat => bv_unsigned (getr R (reg 21)) | 44%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [assumption | unfold PMAXGP.aligned; lia | lia]).
        destruct P as (fx3 & R3 & M3v & MG & _ & FRZ & MS & KS & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z18 & Z19 & Z20 & Z21 & Z22 & CG & _).
        exists fx3, R3, M3v. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
        rewrite E16. repeat (split; [assumption|]). assumption.
      - assert (ELEN : eg = g + len) by (unfold len in *; lia).
        pose proof (PMAXGP.axgC2_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => len | 36%nat => ois + 16
                     | 37%nat => bv_unsigned (getr R (reg 1)) | 38%nat => bv_unsigned (getr R (reg 8)) | 39%nat => bv_unsigned (getr R (reg 9))
                     | 40%nat => bv_unsigned (getr R (reg 18)) | 41%nat => bv_unsigned (getr R (reg 19)) | 42%nat => bv_unsigned (getr R (reg 20))
                     | 43%nat => bv_unsigned (getr R (reg 21)) | 44%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
        rewrite <- ELEN in P.
        L5SAR.feed P ltac:(first [assumption | unfold PMAXGP.aligned; lia | lia]).
        destruct P as (fx3 & R3 & M3v & MG & _ & FRZ & MS & KS & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z18 & Z19 & Z20 & Z21 & Z22 & CA & CB & CG & _).
        exists fx3, R3, M3v. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
        rewrite ELEN in CG. repeat (split; [assumption|]). assumption. }
    destruct TAIL as (fx3 & R3 & M3v & MS3 & MG3 & FRZ3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z10 & CG).
    assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite Z1, Z_to_bv_bv_unsigned; exact Rra).
    pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xda908 W_d830c r F_d830c eq_refl D_d830c R3ra ltac:(lia) Hr2) as MS4.
    set (W3 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (ois + 16 + 24 <= a < ois + 16 + 24 + 8)).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx1 fx3 R2 0xda8d4 R3 r M3v W3 K HH2 AM2).
    { eapply msteps_trans; [exact MS3| exact MS4]. }
    { exact MG3. }
    { intros a Ha Nw. apply FRZ3; [exact Ha| intros X; apply Nw; left; exact X| intros X; apply Nw; right; exact X]. }
    { intros a Ha [Wa|Wa]; split.
      - apply (L5SAR.stack_client L ar LB FF 0 0 a); lia.
      - lia.
      - apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia.
      - lia. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (NSH3 : forall x, W3 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
    assert (OB03 : forall a, ois <= a < ois + 272 -> ~ (ois + 40 <= a < ois + 48) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. rewrite FR3; [apply OB02; exact Ha| lia| intros [X|X]; lia]. }
    (* [comment removed for export] *)
    assert (AGSH3 : forall a n0, 0 <= a -> a + n0 <= 2 ^ 47 -> (forall x, a <= x < a + n0 -> aclient L ar LB FF (sp - 64) 2560 (HeapIfaceA.S x)) ->
                      PMFA.agsh M M3 a n0).
    { intros a n0 H0 H1 HC x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
      assert (R0x : 0 <= HeapIfaceA.S x < 2 ^ 64) by (unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia).
      rewrite FR3; [| exact R0x| intros X; apply NSH3 in X; unfold BIGSHADOW_LO, BIGSHADOW_HI in X; lia].
      rewrite KEEP2; [| exact R0x| apply HC; exact Hx| lia].
      apply FR1; [exact R0x| lia]. }
    assert (OSH : forall x, ois <= x < ois + 272 -> aclient L ar LB FF (sp - 64) 2560 (HeapIfaceA.S x)).
    { intros x Hx. destruct AO as (f & Hf & F1 & F2). unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf|].
      unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
    assert (BSH : forall q A0 x, In (q, A0) LB -> q <= x < q + A0 -> aclient L ar LB FF (sp - 64) 2560 (HeapIfaceA.S x)).
    { intros q A0 x Hin Hx. unfold aclient, aclient_g. do 6 right. exists (q, A0). split; [exact Hin|]. cbn [fst snd].
      unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
    assert (ISS3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str (PM.STRM (g + len) eg st)).
    { apply (iss_g_updA M M3 ois str g eg st (g + len) ISS); [lia| lia| | | | | | | ].
      - split; [intros i Hi; apply OB03; lia|]. apply AGSH3; [lia| lia| intros x Hx; apply OSH; lia].
      - split; [intros i Hi; apply OB03; lia|]. apply AGSH3; [lia| lia| intros x Hx; apply OSH; lia].
      - apply AGSH3; [lia| lia| intros x Hx; apply OSH; lia].
      - intros i Hi. apply MGM3. apply ODEF2. exact Hi.
      - intros c n p Es. assert (Hin : In (p, c) LB) by (apply OWN; rewrite Es; left; reflexivity).
        destruct (BRB (p, c) Hin) as (Yb0 & Yb3). cbn [fst snd] in Yb0, Yb3.
        destruct IVS as (_ & _ & VX). rewrite Es in VX. destruct VX as (_ & _ & _ & _ & _ & _ & DP & _).
        split.
        + intros i Hi. apply MGM3. destruct (Z_lt_le_dec (p + i) dst) as [Lo|Hi2]; [| destruct (Z_lt_le_dec (p + i) (dst + len)) as [Lo2|Hi3]].
          * rewrite KEEP2; [apply MGM1; apply DP; exact Hi| lia| apply (L5SAR.block_client L ar LB FF _ _ p c); [exact Hin| lia]| lia].
          * replace (p + i) with (dst + (p + i - dst)) by lia. apply D2. lia.
          * rewrite KEEP2; [apply MGM1; apply DP; exact Hi| lia| apply (L5SAR.block_client L ar LB FF _ _ p c); [exact Hin| lia]| lia].
        + apply AGSH3; [lia| lia| intros x Hx; apply (BSH p c x Hin Hx)].
      - replace (ois + 40) with (ois + 16 + 24) by lia. rewrite <- VIS3 in CG.
        exact (proj1 (L5A.u64_at_vis _ M3 _ _ (L5A.avis_sub _ ois 272 (ois + 16 + 24) 8 OVIS2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CG).
      - clear - IE2 LEN. unfold len in *. lia. }
    assert (MGM23 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 16384 a -> M (Z_to_bv 64 a) <> None -> M3 (Z_to_bv 64 a) <> None).
    { intros a Ha Hc Hd. apply MGM3.
      pose proof (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 16384 a HH SPT Hc) as CAS.
      destruct (Z_lt_le_dec a dst) as [Lo|Hi2]; [| destruct (Z_lt_le_dec a (dst + len)) as [Lo2|Hi3]].
      - rewrite KEEP2; [apply MGM1; exact Hd| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF sp 16384 (sp - 64) 2560 a Hc); lia| lia].
      - replace a with (dst + (a - dst)) by lia. apply D2. lia.
      - rewrite KEEP2; [apply MGM1; exact Hd| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF sp 16384 (sp - 64) 2560 a Hc); lia| lia]. }
    apply (KONT fx3 R3 M3 model3 LK Aw len).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      destruct Hk as [<-|Hk]; [rewrite Z2; symmetry; exact Rsp|].
      destruct Hk as [<-|Hk]; [rewrite (KS3 3%nat) by inl; rewrite (C2 3%nat) by inl; apply KS1; inl|].
      destruct Hk as [<-|Hk]; [rewrite (KS3 4%nat) by inl; rewrite (C2 4%nat) by inl; apply KS1; inl|].
      destruct Hk as [<-|Hk]; [rewrite Z8; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z9; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z18; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z19; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z20; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z21; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite Z22; apply Z_to_bv_bv_unsigned|].
      repeat (destruct Hk as [<-|Hk]; [rewrite (KS3 _) by inl; rewrite (C2 _) by inl; apply KS1; inl|]). destruct Hk.
    + rewrite L5K.rl10. exact Z10.
    + reflexivity.
    + exact ISS3.
    + intros i Hi. apply MGM3. replace (dst + i) with (dst + (dst + i - dst)) by lia. apply D2. lia.
    + change (PMSPA.pm_scr 2) with 16384. apply (L5SAR.ahpres_of L ar LB FF sp 16384 _ M M3).
      * apply (L5SAR.ek_trans L ar LB FF sp 16384 W M M2 M3 EK02).
        apply (L5SAR.ek_piece L ar LB FF sp 16384 W M2 M3 W3 FR3). intros a Ha CA OW [X|X].
        -- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M2 _ sp 16384 a HH2 SPT CA) as [(Yc1 & Yc2)|Yc]; lia.
        -- apply (OW (ois + 40, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 16384 ASTK2 MGM3) as (_ & _ & _ & _ & D3 & _). exact D3.
      * intros a Ha Hc Hd. exact (MGM23 a Ha Hc Hd).
    + exact (L5LZ.model_rt_trans model model2 model3 (L5LZ.model_rt_trans model model1 model2 MRT1 MRT2) MRT3).
    + apply incl_refl.
    + apply incl_refl.
    + exact AM3.
    + exact HH3.
Qed.
End WithHeap.
End PMAXG.
