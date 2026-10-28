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
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAStrP_b Ba0_code_ra7e28_a7e2c_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
(* [comment removed for export] *)
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMASTR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64.
Proof. unfold U. pose proof (bv_unsigned_in_range 64 (getr R (reg k))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aacc_of_block M u m p n : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + n <= u + m -> aacc M p n.
Proof.
  intros [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; Lia.lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. Lia.lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
    split. rewrite E, G. apply SP. exact NZ. Lia.lia.
Qed.
Lemma lor7 n : 0 <= n -> Z.lor n 7 = 8 * (n / 8) + 7.
Proof.
  intros Hn. pose proof (Z.add_lor_land n 7) as A'. change 7 with (Z.ones 3) in A' at 2. rewrite Z.land_ones in A' by Lia.lia. change (2 ^ 3) with 8 in A'. Lia.lia.
Qed.
Lemma count_cases n : 23 <= n < 2 ^ 26 ->
  (n = 23 /\ PMSPA.str_count n = 26) \/ (24 <= n /\ PMSPA.str_count n = 8 * (n / 8) + 8 /\ 24 <= Z.lor n 7 <= 67108871).
Proof.
  intros Hn. unfold PMSPA.str_count. destruct (Z.eqb_spec n 23) as [E|E]; [left; split; [exact E| reflexivity]|].
  right. rewrite lor7 by Lia.lia. split; [Lia.lia|]. split; Lia.lia.
Qed.
Lemma count_range n : 23 <= n < 2 ^ 26 -> let c := PMSPA.str_count n in
  26 <= c <= 67108872 /\ n + 1 <= c /\ c <= n + 16 /\ 3 <= c / 8 /\ c mod 2 = 0 /\ n / 8 < c / 8 /\ (c mod 8 = 0 \/ c = 26).
Proof. intros Hn c. destruct (count_cases n Hn) as [[E1 E2]|(E1 & E2 & E3)]; unfold c; rewrite E2; [subst n; cbn; Lia.lia| Lia.lia]. Qed.
(* [comment removed for export] *)
Lemma zeros_sub1 M b j : L5KA.zeros_at M (b / 8 + 2147450880) 3 -> b mod 8 = 0 -> 0 <= j < 24 -> L5KA.zeros_at M ((b + j) / 8 + 2147450880) 1.
Proof.
  intros Z3 B8 Hj i Hi. replace ((b + j) / 8 + 2147450880 + i) with (b / 8 + 2147450880 + j / 8) by Lia.lia. apply Z3. Lia.lia.
Qed.
Lemma zeros_subp M p c j : L5KA.zeros_at M (p / 8 + 2147450880) (c / 8) -> p mod 8 = 0 -> 0 <= j -> j / 8 < c / 8 -> L5KA.zeros_at M ((j + p) / 8 + 2147450880) 1.
Proof.
  intros Z3 B8 Hj Hjc i Hi. replace ((j + p) / 8 + 2147450880 + i) with (p / 8 + 2147450880 + j / 8) by Lia.lia. apply Z3. Lia.lia.
Qed.
(* [comment removed for export] *)
Lemma shb_bound q m : 0 <= q -> 0 < m -> q + m <= 2 ^ 47 - 8388608 ->
  0 <= q / 8 /\ (q + m - 1) / 8 <= 2 ^ 44 - 2 ^ 20 /\ q / 8 + m / 8 <= 2 ^ 44 - 2 ^ 20.
Proof. intros. Lia.lia. Qed.
Lemma shadow_idx q c j : q mod 8 = 0 -> 0 <= q -> 0 <= j -> 8 * j < c -> q / 8 + j <= (q + c - 1) / 8.
Proof. intros. Lia.lia. Qed.
Lemma shadow_sub q m a n : 0 <= q -> q <= a -> 0 < n -> a + n <= q + m -> q / 8 <= a / 8 /\ (a + n - 1) / 8 <= (q + m - 1) / 8.
Proof. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma credit_facts cr n cap : PMSPA.credit_le (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 16))) cr -> 0 <= n -> 0 <= cap <= n + 16 ->
  acredit_ok L cr cap /\ PMSPA.credit_keep cr (adebit L cr cap) (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 16))) PMSPA.cr0
  /\ PMSPA.credit_keep cr cr (PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (n + 16))) PMSPA.cr0.
Proof.
  intros (C1 & C2) Hn Hc. destruct (PMA.ly_cost L C LY) as (K1 & K2 & K3).
  unfold PMSPA.scA, PM.cost1, PMSPA.HV, LibIfaceAB.heap_view in *. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *.
  unfold acredit_ok, adebit, PMSPA.credit_keep, PMSPA.cr0. cbn [fst snd]. rewrite K1, K2, K3 in *. lia.
Qed.

Theorem str_ctor_ok : PMA.opnew_spec L ar HI -> PMA.str_ctor_spec L ar HI.
Proof.
  intros NEW. unfold PMA.str_ctor_spec, PMSPA.str_ctor_spec.
  intros fx R M model K LB FF LK Aw cr o ptr n sp r HH AM K0 ENT FRM FRS A10 A11 A12 Hn AO O8 OD ACC SRCB SACC CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  change (PMSPA.pm_scr 0) with 12288 in *.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491344 <= sp <= 140737488355328) by lia.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  change (24 / 8) with 3 in OVSH, OCLSH.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model o 24 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (OWv : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (FRO : sp - 64 + 64 <= o \/ o + 24 <= sp - 64) by lia.
  assert (UR1 : U R 1 = r) by (apply (U_of R 1 r Rra); lia).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(o, 24)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  (* [comment removed for export] *)
  assert (EKP : forall M0 M1 (P : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
            (forall a, P a -> sp - 64 <= a < sp \/ o <= a < o + 24) -> L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M0 M1).
  { intros M0 M1 P FRM0 HP. apply (L5SAR.ek_piece L ar LB FF sp 12288 [(o, 24)] M0 M1 P FRM0). intros a Ha Hc Ho X. destruct (HP a X) as [Y|Y].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (o, 24)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Y. }
  unfold PMSPA.cfg. cbn [pa_str_ctor PMA.AD ADDR_A].
  destruct (Z.eq_dec n 0) as [N0|N0].
  { (* [comment removed for export] *)
    subst n.
    assert (OZ1 : L5KA.zeros_at MV ((o + 1) / 8 + 2147450880) 1) by (apply zeros_sub1; [exact OZv| exact O8| lia]).
    LeanFeed.pfeed P (PMASTP.ascZ_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B10 & B11 & C1 & C0).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xa8b34 W_a8720 r F_a8720 eq_refl D_a8720 R1ra ltac:(lia) Hr2) as MS2.
    set (W1 := fun a => sp - 64 <= a < sp - 64 + 64 \/ o + 0 <= a < o + 0 + 2).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xa8a0c R1 r M1v W1 K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 24 a AOB); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M1) by (apply (EKP M M1 W1 FR1); intros a [X|X]; lia).
    apply (KONT fx1 R1 M1 model1 LK Aw (PM.VShort 0) cr).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + split; [apply (L5.defined_grows M M1 _ _ MGM1); exact OD|].
      split; [apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M1 EK WAPP FRB o 24 AO ACC)|].
      split; [lia|]. change (2 * 0) with 0.
      rewrite <- VIS1 in C0. exact (proj1 (L5A.u8_at_vis H M1 o 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia)) C0).
    + reflexivity.
    + intros _. reflexivity.
    + intros X. lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 12288 [(o, 24)] M M1 EK).
      * intros i Hi. apply MGM1. apply SDEF. exact Hi.
      * apply (L5SAR.dk_grows L ar LB FF sp 12288 M M1 MGM1).
    + exact (proj2 (proj2 (credit_facts cr 0 0 CRED ltac:(lia) ltac:(lia)))).
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1. }
  destruct SRCB as [N0'|(bA & bm & INB & BA1 & BA2)]; [exfalso; exact (N0 N0')|].
  pose proof (WB _ INB) as ((BQ0 & BQ1 & BQ2 & BQ3 & BQ4 & BQ5) & BDEF & BSH & _ & BBA & BFA & BFS). cbn [fst snd] in BQ0, BQ1, BQ2, BQ3, BQ4, BQ5, BDEF, BSH, BBA, BFA, BFS.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BQ5. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BQ1.
  assert (SR : 0 <= ptr /\ ptr + n <= 2 ^ 47) by lia.
  assert (US11 : U R 11 = ptr) by (apply (U_of R 11 ptr A11); lia).
  assert (BO : o + 24 <= bA \/ bA + bm <= o).
  { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (BFA g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [ff_addr ff_class fst snd] in X. lia. }
  destruct (PMCG.rdn_some RSEGS M (Z.to_nat n) ptr ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN & _).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. replace (ptr + i) with (bA + (ptr + i - bA)) by lia. apply BDEF. lia. }
  (* [comment removed for export] *)
  pose proof (shb_bound bA bm ltac:(lia) ltac:(lia) ltac:(lia)) as BSB.
  pose proof (shadow_sub bA bm ptr n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BSS.
  assert (SCL : forall a, (ptr <= a < ptr + n \/ S ptr <= a <= S (ptr + n - 1)) -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF 0 0 a /\ a < ahl_ceil ar
                 /\ (ptr <= a < ptr + n \/ 2147450880 <= a <= 2147450880 + 2 ^ 44 - 2 ^ 20)).
  { intros a Hq. destruct Hq as [Ha|Ha].
    - split; [lia|]. split; [apply (L5SAR.block_client L ar LB FF 0 0 bA bm); [exact INB| lia]|]. split; [lia| left; exact Ha].
    - unfold S, SB in Ha. split; [lia|]. split; [|split; [lia| right; lia]].
      do 6 right. exists (bA, bm). split; [exact INB|]. unfold in_shadow_of, S, SB. cbn [fst snd]. lia. }
  destruct (Z_le_gt_dec n 22) as [N22|N23].
  { (* [comment removed for export] *)
    assert (HVN : 1 <= n <= 22) by lia.
    LeanFeed.pfeed P (PMASTP.ascS_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & aR1 & aR2 & aR8 & aR9 & aR10 & aR18 & aR19 & aR21 & aB0 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
    set (W1 := fun a => sp - 64 <= a < sp - 64 + 64 \/ o + 0 <= a < o + 0 + 1).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xa8a0c R1 0x78370 M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 24 a AOB); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof AM1 as (Mh1 & MI1).
    (* [comment removed for export] *)
    pose proof (HAJ.aior_memmove _ _ _ _ _ HIok) as MMV. unfold amemmove_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
    rewrite (L5A.aly_segs L C LYa), (L5A.aly_memmove L C LYa), (L5A.aly_scr_mem L C LYa) in MMV.
    assert (U12 : bv_unsigned (getr R1 2%bv) = sp - 64) by (rewrite L5K.rl2, aR2; apply L5.unsigned_lit; lia).
    assert (AGS1 : forall a, (ptr <= a < ptr + n \/ S ptr <= a <= S (ptr + n - 1)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hq. destruct (SCL a Hq) as (Ha & Hc & Hl & Hr). apply FR1; [exact Ha|]. unfold W1. intros [X|X]; [lia|].
      destruct Hr as [Hr|Hr]; [destruct BO; lia| destruct OBIG; lia]. }
    apply (MMV fx1 R1 M1 model1 LB FF LK cr Aw (o + 1) ptr n bs K); clear MMV.
    { split; [exact HH1|]. split; [exact Mh1|]. split; [exact MI1|].
      split; [rewrite L5K.rl10; exact aR10|]. split; [rewrite L5K.rl12, (KS1 12%nat) by inl; exact A12|]. split; [lia|].
      split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
      split; [rewrite L5K.rl1, aR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
      split. { rewrite U12. apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 64 2560 ASTK MGM1); [lia| lia| lia|].
               replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
      split. { intros b Hb. assert (E1 : M1 (Z_to_bv 64 (S b)) = M (Z_to_bv 64 (S b))).
               { apply FR1. unfold S, SB. split; [pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)); lia| assert (b / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia].
                 unfold W1, S, SB. assert (b / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). intros [X|X]; [lia|].
                 destruct OBIG as [OB|OB]; [|lia]. pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)). lia. }
               unfold byte_at. rewrite E1. exact (ACC b ltac:(lia)). }
      split. { intros i Hi. rewrite U12. apply (L5SAR.obj_client L ar LB FF _ _ o 24 (o + 1 + i) AOB). lia. }
      split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS M1 o 24 ltac:(eapply L5.defined_grows; [exact MGM1 | exact ODEF]) ltac:(lia) ltac:(lia)) as W.
               replace (o + 1 + i) with (o + (1 + i)) by lia. apply W; lia. }
      split. exact K0. apply (L5SAR.app_rng_aobj L ar C HI HIok LB FF LK cr Aw M1 _ o 24 (o + 1) n HH1 AOB); lia. }
    { rewrite L5K.rl11, (KS1 11%nat) by inl. exact A11. }
    { intros b Hb. unfold byte_at. rewrite AGS1 by (right; unfold S; split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia). exact (SACC b Hb). }
    { exact SR. }
    { apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M1 _ bA bm ptr n HH1 INB BA1 BA2). }
    { intros i Hi. right. apply (L5SAR.block_client L ar LB FF _ _ bA bm). exact INB. lia. }
    { rewrite (L5C.rdn_agree RSEGS M M1 (Z.to_nat n) ptr). exact RDN. lia. rewrite Z2Nat.id by lia; lia.
      intros i Hi. rewrite Z2Nat.id in Hi by lia. apply AGS1. left. lia. }
    { intros _. lia. }
    (* [comment removed for export] *)
    intros R2 M2 model2 mR10 RP2 BYTES PRES2 SDEF2 RT2 MI2 HH2. rewrite U12 in PRES2, SDEF2. rewrite L5K.rl1, aR1.
    assert (Mh2 : m_halted model2 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT2); exact Mh1).
    assert (ASTK2 : L5CA.astk ar M2 sp 12288).
    { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M1 M1 M2 _ sp _ (sp - 64) 2560 HH1 ltac:(eapply L5SAR.astk_grows; [exact ASTK | exact MGM1]) (fun x X => X)).
      - intros a Ha Hs Hns. apply PRES2. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
      - exact SDEF2.
      - lia. - lia. - lia. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
    set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M2 model2 o 24 (sp - 64) 2560 HH2 AOB ltac:(lia) ltac:(reflexivity))
      as (_ & _ & ODEF2 & OVIS2 & OVSH2 & OCL2 & OCLSH2).
    change (24 / 8) with 3 in OVSH2, OCLSH2.
    pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
    pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
    assert (EK12 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M1 M2).
    { apply (L5SAR.ek_mem L ar LB FF sp 12288 (sp - 64) 2560 (fun a => o + 1 <= a < o + 1 + n) [(o, 24)] M1 M2 PRES2); [lia| lia|].
      intros a Hc Ho X. apply (Ho (o, 24)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia. }
    assert (EK01 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M1) by (apply (EKP M M1 W1 FR1); intros a [X|X]; lia).
    assert (EK02 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M2) by (apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M1 M2 EK01 EK12)).
    assert (ACC2 : PMSPA.accA M2 o 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M2 EK02 WAPP FRB o 24 AO ACC)).
    (* [comment removed for export] *)
    assert (KV2 : forall a, (sp - 64 <= a < sp \/ (o <= a < o + 24 /\ ~ (o + 1 <= a < o + 1 + n))) -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by lia.
      unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
      2:{ destruct Ra as [Ra|[Ra _]].
          - replace a with ((sp - 64) + (a - (sp - 64))) by lia. apply (VIS2 (sp - 64) 64); lia.
          - replace a with (o + (a - o)) by lia. apply (OVIS2 (a - o)). lia. }
      rewrite PRES2; [| exact Ha | |].
      2:{ destruct Ra as [Ra|[Ra _]]; [apply L5SAR.stack_client; lia| apply (L5SAR.obj_client L ar LB FF _ _ o 24 a AOB); lia]. }
      2:{ destruct Ra as [Ra|[Ra Na]]; [lia| exact Na]. }
      apply VV1.
      destruct Ra as [Ra|[Ra _]].
      - replace a with ((sp - 64) + (a - (sp - 64))) by lia. apply (VIS (sp - 64) 64); lia.
      - replace a with (o + (a - o)) by lia. apply (OVIS (a - o)). lia. }
    assert (SV2 : forall a v0, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
    { intros a v0 Ha Hb X. apply (L5C.u64_at_agree RSEGS M1v MV2); [|lia|lia|exact X]. intros j Hj. apply KV2. left. lia. }
    assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
    assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
    assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
    assert (Y3 : L5.writable RSEGS MV2 (sp - 64) 64).
    { apply (proj2 (L5A.writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
    assert (YZ : L5KA.zeros_at MV2 (o / 8 + 2147450880) 3).
    { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M2 model2 o 24 HH2 AO O8 ltac:(lia) ltac:(reflexivity) ACC2). }
    assert (YZ1 : L5KA.zeros_at MV2 (((o + n) + 1) / 8 + 2147450880) 1).
    { replace ((o + n) + 1) with (o + (n + 1)) by lia. apply zeros_sub1; [exact YZ| exact O8| lia]. }
    assert (YW : L5.writable RSEGS MV2 o 24).
    { apply (proj2 (L5A.writable_vis H2 M2 o 24 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
    assert (CS2 : forall k, In k L5SAR.cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R1 R2 k RP2 Hk)).
    assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite CS2 by inl; exact aR2).
    assert (J8 : getr R2 (reg 8) = Z_to_bv 64 n) by (rewrite CS2 by inl; exact aR8).
    assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (o + 1)) by (rewrite CS2 by inl; exact aR19).
    assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact aR21).
    pose proof (UR R 1) as UR1b. pose proof (UR R 8) as UR8. pose proof (UR R 9) as UR9. pose proof (UR R 18) as UR18.
    pose proof (UR R 19) as UR19. pose proof (UR R 20) as UR20. pose proof (UR R 21) as UR21.
    assert (Y8 : L5.u64_at RSEGS MV2 (sp - 8) (U R 1)) by (apply SV2; [lia| lia| exact C8]).
    assert (Y16 : L5.u64_at RSEGS MV2 (sp - 16) (U R 8)) by (apply SV2; [lia| lia| exact C16]).
    assert (Y24 : L5.u64_at RSEGS MV2 (sp - 24) (U R 9)) by (apply SV2; [lia| lia| exact C24]).
    assert (Y32 : L5.u64_at RSEGS MV2 (sp - 32) (U R 18)) by (apply SV2; [lia| lia| exact C32]).
    assert (Y40 : L5.u64_at RSEGS MV2 (sp - 40) (U R 19)) by (apply SV2; [lia| lia| exact C40]).
    assert (Y48 : L5.u64_at RSEGS MV2 (sp - 48) (U R 20)) by (apply SV2; [lia| lia| exact C48]).
    assert (Y56 : L5.u64_at RSEGS MV2 (sp - 56) (U R 21)) by (apply SV2; [lia| lia| exact C56]).
    LeanFeed.pfeed P (PMASTP.ascTS_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n
                  | 44%nat => U R 1 | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18 | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21
                  | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & tR1 & tR2 & tR8 & tR9 & tR10 & tR11 & tR18 & tR19 & tR20 & tR21 & tB).
    assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite tR1, UR1; reflexivity).
    pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xa8b34 W_a8720 r F_a8720 eq_refl D_a8720 R3ra ltac:(lia) Hr2) as MS4.
    set (W3 := fun a => (o + 1) + 0 <= a < (o + 1) + 0 + 23).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx1 fx3 R2 0xa8af4 R3 r M3v W3 K HH2 (conj Mh2 MI2)).
    { eapply msteps_trans; [exact MS3| exact MS4]. }
    { exact MG3. }
    { intros a Ha N. apply FZ3; [exact Ha| exact N]. }
    { intros a Ha Wa. unfold W3 in Wa. split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 24 a AOB); lia| lia]. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M2 M3) by (apply (EKP M2 M3 W3 FR3); intros a X; unfold W3 in X; lia).
    assert (EK03 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M3) by (apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M2 M3 EK02 EK23)).
    apply (KONT fx3 R3 M3 model3 LK Aw (PM.VShort n) cr).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      assert (CH : forall k, In k PMASTP.KS_ascTS -> In k L5SAR.cs_all -> In k PMASTP.KS_ascS -> getr R3 (reg k) = getr R (reg k)).
      { intros k' H1 H4' H5. rewrite (KS3 k' H1), (CS2 k' H4'). apply KS1. exact H5. }
      destruct Hk as [<-|Hk]; [rewrite tR2, Rsp; reflexivity|].
      destruct Hk as [<-|Hk]; [apply CH; inl|].
      destruct Hk as [<-|Hk]; [apply CH; inl|].
      destruct Hk as [<-|Hk]; [rewrite tR8; symmetry; apply U_to|].
      destruct Hk as [<-|Hk]; [rewrite tR9; symmetry; apply U_to|].
      destruct Hk as [<-|Hk]; [rewrite tR18; symmetry; apply U_to|].
      destruct Hk as [<-|Hk]; [rewrite tR19; symmetry; apply U_to|].
      destruct Hk as [<-|Hk]; [rewrite tR20; symmetry; apply U_to|].
      destruct Hk as [<-|Hk]; [rewrite tR21; symmetry; apply U_to|].
      repeat (destruct Hk as [<-|Hk]; [apply CH; inl|]). destruct Hk.
    + split; [apply (L5.defined_grows M2 M3 _ _ MGM3); exact ODEF2|].
      split; [apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M3 EK03 WAPP FRB o 24 AO ACC)|].
      split; [lia|].
      assert (B2 : L5.u8_at RSEGS MV2 o (2 * n)) by (apply (L5C.u8_at_agree RSEGS M1v MV2); [intros j Hj; apply KV2; right; lia| lia| lia| exact aB0]).
      apply (proj1 (L5A.u8_at_vis H2 M2 o (2 * n) ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))) in B2.
      apply (L5C.u8_at_agree RSEGS M2 M3); [intros j Hj; apply FR3; [lia| unfold W3; lia]| lia| lia| exact B2].
    + reflexivity.
    + intros _. reflexivity.
    + intros X. lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 12288 [(o, 24)] M M3 EK03).
      * intros i Hi. apply MGM3. pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply SD2. exact Hi.
      * apply (L5SAR.dk_trans L ar LB FF sp 12288 M M1 M3 (L5SAR.dk_grows L ar LB FF sp 12288 M M1 MGM1)).
        apply (L5SAR.dk_trans L ar LB FF sp 12288 M1 M2 M3); [|apply (L5SAR.dk_grows L ar LB FF sp 12288 M2 M3 MGM3)].
        apply (L5SAR.dk_mem L ar LB FF sp 12288 (sp - 64) 2560 (fun a => o + 1 <= a < o + 1 + n) M1 M2 PRES2 SDEF2).
        { intros a Ha. destruct (BYTES (a - (o + 1)) ltac:(lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (o + 1 + (a - (o + 1))) with a in Bv by lia. rewrite Bv. discriminate. }
        { intros a. destruct (L5SAR.rng_dec a (o + 1) (o + 1 + n)) as [X|X]; [left; exact X| right; exact X]. }
        lia. lia.
    + exact (proj2 (proj2 (credit_facts cr n 0 CRED ltac:(lia) ltac:(lia)))).
    + apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact RT2].
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM3.
    + exact HH3. }
  (* [comment removed for export] *)
  assert (HVN : 23 <= n <= 67108863) by lia.
  pose proof (count_range n ltac:(lia)) as CAPR. cbv zeta in CAPR.
  pose proof (count_cases n ltac:(lia)) as CAPE.
  set (cap := PMSPA.str_count n) in *.
  destruct (credit_facts cr n cap CRED ltac:(lia) ltac:(lia)) as (CROK & CRKEEP & _).
  assert (HEAD : exists fx1 R1 M1v, mem_grows MV M1v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R 0xa8a0c MV) (st fx1 R1 0x130338 M1v)
      /\ (forall x, In x [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 1) = Z_to_bv 64 690840 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 n
      /\ getr R1 (reg 9) = Z_to_bv 64 ptr /\ getr R1 (reg 10) = Z_to_bv 64 cap /\ getr R1 (reg 18) = Z_to_bv 64 o
      /\ getr R1 (reg 20) = Z_to_bv 64 cap /\ getr R1 (reg 21) = Z_to_bv 64 2147450880
      /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19)
      /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8)
      /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1)).
  { destruct CAPE as [[E23 EC]|(E24 & EC & ELOR)].
    - assert (A12' : getr R (reg 12) = Z_to_bv 64 23) by (rewrite A12, E23; reflexivity).
      LeanFeed.pfeed P (PMASTP.ascH23_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => ptr | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
      exists fx1, R1, M1v. fold cap in EC. rewrite EC, E23.
      split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|].
      split. { intros x Hx. apply KS1. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption.
    - LeanFeed.pfeed P (PMASTP.ascHg_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
      exists fx1, R1, M1v. fold cap in EC. rewrite EC.
      split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|].
      split. { intros x Hx. apply KS1. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption. }
  destruct HEAD as (fx1 & R1 & M1v & MG1 & aFZ & aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  set (W1 := fun a => sp - 64 <= a < sp - 64 + 64).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xa8a0c R1 0x130338 M1v W1 K HH AM aMS MG1).
  { intros a Ha N. apply aFZ; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (ASTK1 : L5CA.astk ar M1 sp 12288) by (apply (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1)).
  unfold PMA.opnew_spec, PMSPA.opnew_spec in NEW. cbn [pa_opnew PMA.AD ADDR_A] in NEW.
  apply (NEW fx1 R1 M1 model1 K LB FF LK Aw cr cap (sp - 64) 0xa8a98 HH1 AM1 K0).
  { rewrite L5K.rl10. exact aR10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact aR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact aR2. }
  { rewrite L5K.rl4, (aKS 4%nat) by inl. exact Rtp. }
  { apply (L5SAR.astk_sub ar M1 M1 sp 12288 64 PMSPA.OPNEW_SCR ASTK1 (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R2 M2 model2 Aw2 p nR10 RP2 (BRp & BAp & FAp & DEFp & SHBp) PRES2 RT2 IA2 AM2 HH2.
  set (LB2 := (p, cap) :: LB) in *. set (cr2 := adebit L cr cap) in *.
  pose proof AM2 as (Mh2 & MI2).
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK cr Aw M1 M1 M2 _ sp _ (sp - 64) PMSPA.OPNEW_SCR [] HH1 ASTK1 (fun x X => X) PRES2);
    unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 o 24 (sp - 64) 2560 HH2 AOB ltac:(lia) ltac:(reflexivity))
    as (_ & _ & ODEF2 & OVIS2 & OVSH2 & OCL2 & OCLSH2).
  pose proof BRp as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1.
  pose proof (shb_bound p cap ltac:(lia) ltac:(lia) ltac:(lia)) as PSH.
  assert (P8 : p mod 8 = 0) by (apply PMFA.mod16_8; exact Q2).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (EK01 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M1) by (apply (EKP M M1 W1 FR1); intros a X; unfold W1 in X; lia).
  assert (EK12 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 12288 (sp - 64) PMSPA.OPNEW_SCR [(o, 24)] [] M1 M2 PRES2); [unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (EK02 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M2) by (apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M1 M2 EK01 EK12)).
  assert (ACC2 : PMSPA.accA M2 o 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M2 EK02 WAPP FRB o 24 AO ACC)).
  assert (YZ2 : L5KA.zeros_at MV2 (o / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 o 24 HH2 AO O8 ltac:(lia) ltac:(reflexivity) ACC2). }
  assert (YW2 : L5.writable RSEGS MV2 o 24).
  { apply (proj2 (L5A.writable_vis H2 M2 o 24 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 64) 64).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  (* [comment removed for export] *)
  assert (STK12 : forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 PRES2). split; [lia|]. split; [|intros rr []]. apply L5SAR.stack_client; [lia| unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia]. }
  assert (CS2 : forall k, In k L5SAR.cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R1 R2 k RP2 Hk)).
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite CS2 by inl; exact aR2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 n) by (rewrite CS2 by inl; exact aR8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 ptr) by (rewrite CS2 by inl; exact aR9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 o) by (rewrite CS2 by inl; exact aR18).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 cap) by (rewrite CS2 by inl; exact aR20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact aR21).
  assert (J10 : getr R2 (reg 10) = Z_to_bv 64 p) by (rewrite <- L5K.rl10; exact nR10).
  assert (PO : p + cap <= o \/ o + 24 <= p).
  { destruct AOB as (g & Hg & X1 & X2 & _). specialize (FAp g ltac:(apply in_or_app; left; exact Hg)). lia. }
  (* [comment removed for export] *)
  LeanFeed.pfeed P (PMASTP.ascN_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | 36%nat => p | 37%nat => cap | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & nFZ & nMS & nKS & nR1 & nR11 & nR12 & nR19 & nR20 & nO8 & nO0 & nO16).
  set (W3 := fun a => o + 0 <= a < o + 0 + 24).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 fx2 fx3 R2 0xa8a98 R3 0x78370 M3v W3 K HH2 AM2 nMS MG3).
  { intros a Ha N. apply nFZ; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W3 in Wa. split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 o 24 a AOB); lia| lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  pose proof AM3 as (Mh3 & MI3).
  assert (ASTK3 : L5CA.astk ar M3 sp 12288) by (apply (L5SAR.astk_grows ar M2 M3 sp 12288 ASTK2 MGM3)).
  (* [comment removed for export] *)
  pose proof (HAJ.aior_memmove _ _ _ _ _ HIok) as MMV. unfold amemmove_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memmove L C LYa), (L5A.aly_scr_mem L C LYa) in MMV.
  assert (U32 : bv_unsigned (getr R3 2%bv) = sp - 64) by (rewrite L5K.rl2, (nKS 2%nat) by inl; rewrite J2; apply L5.unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (SHB3 : shadow_blk M3 p cap).
  { destruct SHBp as [SZp SPp]. split.
    - intros j Hj. unfold byte_at. rewrite FR3. apply SZp. exact Hj. unfold S, SB; lia. unfold W3, S, SB. destruct OBIG as [OB|OB]; lia.
    - intros NZ. unfold byte_at. rewrite FR3. apply SPp. exact NZ. unfold S, SB; lia. unfold W3, S, SB. destruct OBIG as [OB|OB]; lia. }
  assert (AGS3 : forall a, (ptr <= a < ptr + n \/ S ptr <= a <= S (ptr + n - 1)) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Hq. destruct (SCL a Hq) as (Ha & Hc & Hl & Hr).
    assert (NO : ~ (o <= a < o + 24)) by (destruct Hr as [Hr|Hr]; [destruct BO; lia| destruct OBIG; lia]).
    rewrite FR3 by first [exact Ha | unfold W3; lia]. rewrite (proj1 PRES2 a).
    2:{ split; [exact Ha|]. split; [|intros rr []]. apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia]. }
    apply FR1; [exact Ha| unfold W1; lia]. }
  apply (MMV fx3 R3 M3 model3 LB2 FF LK cr2 Aw2 p ptr n bs K); clear MMV.
  { split; [exact HH3|]. split; [exact Mh3|]. split; [exact MI3|].
    split; [rewrite L5K.rl10, (nKS 10%nat) by inl; exact J10|]. split; [rewrite L5K.rl12; exact nR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (nKS 4%nat) by inl; rewrite (CS2 4%nat) by inl; rewrite (aKS 4%nat) by inl; exact Rtp|].
    split; [rewrite L5K.rl1, nR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite U32. apply (L5SAR.astack_ok_of_astk L ar C LYa M3 M3 sp 12288 64 2560 ASTK3 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split. { apply (aacc_of_block M3 p cap p n SHB3); [apply PMFA.mod16_8; exact Q2| lia| lia| lia]. }
    split. { intros i Hi. rewrite U32. apply (L5SAR.block_client L ar LB2 FF _ _ p cap); [left; reflexivity| lia]. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M3 p cap); [apply (L5.defined_grows M2 M3 _ _ MGM3); exact DEFp| lia| lia| lia| lia]. }
    split; [exact K0|]. apply (L5SAR.app_rng_block L ar C HI HIok LB2 FF LK cr2 Aw2 M3 _ p cap p n HH3 ltac:(left; reflexivity)); lia. }
  { rewrite L5K.rl11, nR11. reflexivity. }
  { intros b Hb. unfold byte_at. rewrite AGS3 by (right; unfold S; split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia). exact (SACC b Hb). }
  { exact SR. }
  { apply (L5SAR.app_rng_block L ar C HI HIok LB2 FF LK cr2 Aw2 M3 _ bA bm ptr n HH3 ltac:(right; exact INB) BA1 BA2). }
  { intros i Hi. right. apply (L5SAR.block_client L ar LB2 FF _ _ bA bm); [right; exact INB| lia]. }
  { rewrite (L5C.rdn_agree RSEGS M M3 (Z.to_nat n) ptr). exact RDN. lia. rewrite Z2Nat.id by lia; lia.
    intros i Hi. rewrite Z2Nat.id in Hi by lia. apply AGS3. left. lia. }
  { intros _. pose proof (BAp _ INB) as X. cbn [fst snd] in X. lia. }
  (* [comment removed for export] *)
  intros R4 M4 model4 mR10 RP4 BYTES PRES4 SDEF4 RT4 MI4 HH4. rewrite U32 in PRES4, SDEF4. rewrite L5K.rl1, nR1.
  assert (Mh4 : m_halted model4 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT4); exact Mh3).
  assert (ASTK4 : L5CA.astk ar M4 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw2 M3 M3 M4 _ sp _ (sp - 64) 2560 HH3 ASTK3 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES4. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF4.
    - lia. - lia. - lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  set (H4 := ahid Aw2 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M4 model4 o 24 (sp - 64) 2560 HH4 AOB ltac:(lia) ltac:(reflexivity))
    as (_ & _ & ODEF4 & OVIS4 & OVSH4 & OCL4 & OCLSH4).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as ST4. rewrite (L5A.aly_segs L C LYa) in ST4.
  pose proof (L5A.statics_facts L C M4 LYa ST4) as (GOT4 & CSB4 & CUAR4 & _).
  assert (FAF : fframes_apart p cap FF) by (eapply L5SAR.fframes_apart_incl; [exact FAp| apply incl_appl; apply incl_refl]).
  assert (PNC : forall a, p <= a < p + cap -> ~ aclient L ar LB FF sp 12288 a).
  { intros a Ha. exact (L5SAR.fresh_block_not_client L ar C HI LYa HIok LB FF LK cr Aw M1 _ sp 12288 p cap a HH1 SPT BRp BAp FAF Ha). }
  assert (PRES4' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 64) 2560 a -> ~ (p <= a < p + n) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha Hc Hn'. apply PRES4. exact Ha. apply L5SAR.aclient_consb. exact Hc. exact Hn'. }
  assert (EK23 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M2 M3) by (apply (EKP M2 M3 W3 FR3); intros a X; unfold W3 in X; lia).
  assert (EK34 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M3 M4).
  { apply (L5SAR.ek_mem L ar LB FF sp 12288 (sp - 64) 2560 (fun a => p <= a < p + n) [(o, 24)] M3 M4 PRES4'); [lia| lia|].
    intros a Hc Ho X. apply (PNC a); [lia| exact Hc]. }
  assert (EK04 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M4).
  { apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M3 M4); [|exact EK34].
    apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M2 M3 EK02 EK23). }
  assert (ACC4 : PMSPA.accA M4 o 24) by (apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M4 EK04 WAPP FRB o 24 AO ACC)).
  (* [comment removed for export] *)
  assert (STK4 : forall a, sp - 64 <= a < sp -> MV4 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha. unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4).
    2:{ replace a with ((sp - 64) + (a - (sp - 64))) by lia. apply (VIS4 (sp - 64) 64); lia. }
    rewrite PRES4; [| lia| apply L5SAR.stack_client; lia| lia].
    rewrite FR3 by (unfold W3; lia). rewrite STK12 by lia. apply VV1.
    replace a with ((sp - 64) + (a - (sp - 64))) by lia. apply (VIS (sp - 64) 64); lia. }
  assert (SV4 : forall a v0, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV4 a v0).
  { intros a v0 Ha Hb X. apply (L5C.u64_at_agree RSEGS M1v MV4); [|lia|lia|exact X]. intros j Hj. apply STK4. lia. }
  (* [comment removed for export] *)
  assert (SHB4 : shadow_blk M4 p cap).
  { assert (SHX : forall x, in_shadow_of p cap x -> M4 (Z_to_bv 64 x) = M3 (Z_to_bv 64 x)).
    { intros x Hx. assert (Hx' := Hx). unfold in_shadow_of, S, SB in Hx'. apply PRES4. lia.
      do 6 right. exists (p, cap). split; [left; reflexivity| exact Hx].
      destruct Q5 as (_ & [Q|Q] & _); lia. }
    destruct SHB3 as [SZ3 SP3]. split.
    - intros j Hj. unfold byte_at. rewrite SHX. apply SZ3. exact Hj. unfold in_shadow_of, S.
      pose proof (shadow_idx p cap j P8 ltac:(lia) ltac:(lia) ltac:(pose proof (Z.mul_div_le cap 8 ltac:(lia)); lia)). lia.
    - intros NZ. unfold byte_at. rewrite SHX. apply SP3. exact NZ. unfold in_shadow_of, S.
      pose proof (shadow_idx p cap (cap / 8) P8 ltac:(lia) ltac:(apply Z.div_pos; lia) ltac:(pose proof (Z.mod_pos_bound cap 8 ltac:(lia)); pose proof (Z.div_mod cap 8 ltac:(lia)); lia)).
      assert (0 <= cap / 8) by (apply Z.div_pos; lia). lia. }
  assert (PV4 : L5A.avis H4 p cap) by (apply (VBLK4 p cap); [left; reflexivity| lia| lia]).
  assert (PVS4 : L5A.avis H4 (p / 8 + 2147450880) (cap / 8)).
  { apply (VBSH4 p cap). left; reflexivity. intros i Hi. unfold in_shadow_of, S, SB.
    pose proof (shadow_idx p cap i P8 ltac:(lia) ltac:(lia) ltac:(pose proof (Z.mul_div_le cap 8 ltac:(lia)); lia)). lia. }
  assert (PZ4 : L5KA.zeros_at MV4 (p / 8 + 2147450880) (cap / 8)).
  { apply (proj2 (L5A.zeros_at_vis H4 M4 (p / 8 + 2147450880) (cap / 8) PVS4)).
    intros i Hi. destruct SHB4 as [SZ4 _]. unfold shadow_zero, byte_at, S, SB in SZ4. apply SZ4. exact Hi. }
  assert (DEF4 : L5.defined M4 p cap).
  { intros i Hi. destruct (Z_lt_le_dec i n) as [X|X].
    - destruct (BYTES i ltac:(lia)) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
    - rewrite PRES4; [apply (L5.defined_grows M2 M3 p cap MGM3 DEFp); lia| lia| apply (L5SAR.block_client L ar LB2 FF _ _ p cap); [left; reflexivity| lia]| lia]. }
  assert (PW4 : L5.writable RSEGS MV4 p cap).
  { apply (proj2 (L5A.writable_vis H4 M4 p cap PV4 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact DEF4. lia. lia. }
  assert (PZ1 : L5KA.zeros_at MV4 ((n + p) / 8 + 2147450880) 1) by (apply (zeros_subp MV4 p cap n PZ4); [apply PMFA.mod16_8; exact Q2| lia| lia]).
  assert (PW1 : L5.writable RSEGS MV4 (n + p) 1) by (apply (L5.writable_sub RSEGS MV4 p cap); [exact PW4| lia| lia]).
  assert (Z0 : L5.img_clear MV4 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT4).
  assert (Z1 : L5.u64_at RSEGS MV4 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H4 M4 1309752 2147450880 (VIMG4 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB4).
  assert (Z2 : L5.u32_at RSEGS MV4 1309760 1) by (apply (proj2 (L5A.u32_at_vis H4 M4 1309760 1 (VIMG4 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR4).
  assert (Z3 : L5.writable RSEGS MV4 (sp - 64) 64).
  { apply (proj2 (L5A.writable_vis H4 M4 (sp - 64) 64 (VIS4 (sp - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M4 sp 12288); [exact ASTK4| lia| lia| lia]. }
  assert (ZZ : L5KA.zeros_at MV4 (o / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M4 model4 o 24 HH4 AO O8 ltac:(lia) ltac:(reflexivity) ACC4). }
  assert (ZW : L5.writable RSEGS MV4 o 24).
  { apply (proj2 (L5A.writable_vis H4 M4 o 24 OVIS4 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF4. lia. lia. }
  pose proof (UR R 1) as UR1b. pose proof (UR R 8) as UR8. pose proof (UR R 9) as UR9. pose proof (UR R 18) as UR18.
  pose proof (UR R 19) as UR19. pose proof (UR R 20) as UR20. pose proof (UR R 21) as UR21.
  assert (Y8 : L5.u64_at RSEGS MV4 (sp - 8) (U R 1)) by (apply SV4; [lia| lia| exact C8]).
  assert (Y16 : L5.u64_at RSEGS MV4 (sp - 16) (U R 8)) by (apply SV4; [lia| lia| exact C16]).
  assert (Y24 : L5.u64_at RSEGS MV4 (sp - 24) (U R 9)) by (apply SV4; [lia| lia| exact C24]).
  assert (Y32 : L5.u64_at RSEGS MV4 (sp - 32) (U R 18)) by (apply SV4; [lia| lia| exact C32]).
  assert (Y40 : L5.u64_at RSEGS MV4 (sp - 40) (U R 19)) by (apply SV4; [lia| lia| exact C40]).
  assert (Y48 : L5.u64_at RSEGS MV4 (sp - 48) (U R 20)) by (apply SV4; [lia| lia| exact C48]).
  assert (Y56 : L5.u64_at RSEGS MV4 (sp - 56) (U R 21)) by (apply SV4; [lia| lia| exact C56]).
  assert (L2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; rewrite (nKS 2%nat) by inl; exact J2).
  assert (L8 : getr R4 (reg 8) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; rewrite (nKS 8%nat) by inl; exact J8).
  assert (L19 : getr R4 (reg 19) = Z_to_bv 64 p) by (rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; exact nR19).
  assert (L21 : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R3 R4 21 RP4) by inl; rewrite (nKS 21%nat) by inl; exact J21).
  assert (C8R : 0 <= cap / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (C8U : 3 <= cap / 8 <= 8388609) by (split; [lia| apply Z.div_le_upper_bound; lia]).
  LeanFeed.pfeed P (PMASTP.ascTH_conc fx3 R4 MV4 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 36%nat => p | 37%nat => cap | 38%nat => cap / 8
                | 44%nat => U R 1 | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18 | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21
                | _ => 0 end)) ltac:(first [assumption | unfold PMASTP.aligned; lia | lia]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & MS6 & KS6 & tR1 & tR2 & tR8 & tR9 & tR10 & tR11 & tR18 & tR19 & tR20 & tR21 & tB).
  assert (R6ra : getr R6 (reg 1) = Z_to_bv 64 r) by (rewrite tR1, UR1; reflexivity).
  pose proof (PMK.ret_to RSEGS fx6 R6 M6v 0xa8b34 W_a8720 r F_a8720 eq_refl D_a8720 R6ra ltac:(lia) Hr2) as MS7.
  set (W5 := fun a => (n + p) + 0 <= a < (n + p) + 0 + 1).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M4 model4 fx3 fx6 R4 0xa8af4 R6 r M6v W5 K HH4 (conj Mh4 MI4)).
  { eapply msteps_trans; [exact MS6| exact MS7]. }
  { exact MG6. }
  { intros a Ha N. apply FZ6; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W5 in Wa. split; [apply (L5SAR.block_client L ar LB2 FF 0 0 p cap); [left; reflexivity| lia]| lia]. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
  assert (EK45 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M4 M5).
  { apply (L5SAR.ek_piece L ar LB FF sp 12288 [(o, 24)] M4 M5 W5 FR5). intros a Ha Hc Ho X. apply (PNC a); [unfold W5 in X; lia| exact Hc]. }
  assert (EK05 : L5SAR.ek L ar LB FF sp 12288 [(o, 24)] M M5) by (apply (L5SAR.ek_trans L ar LB FF sp 12288 [(o, 24)] M M4 M5 EK04 EK45)).
  assert (OT : forall a v0, o <= a -> a + 8 <= o + 24 -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS M5 a v0).
  { intros a v0 Ha Hb X. rewrite <- VIS3 in X.
    apply (proj1 (L5A.u64_at_vis H2 M3 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))) in X.
    apply (L5C.u64_at_agree RSEGS M3 M5); [|lia|lia|exact X]. intros j Hj.
    rewrite FR5 by (unfold W5; lia). apply PRES4'; [lia| apply (L5SAR.obj_client L ar LB FF _ _ o 24 j AOB); lia| lia]. }
  assert (SHB5 : shadow_blk M5 p cap).
  { destruct SHB4 as [SZ4 SP4]. split.
    - intros j Hj. unfold byte_at. rewrite FR5. apply SZ4. exact Hj. unfold S, SB; lia. unfold W5, S, SB. destruct Q5 as (_ & [Q|Q] & _); lia.
    - intros NZ. unfold byte_at. rewrite FR5. apply SP4. exact NZ. unfold S, SB; lia. unfold W5, S, SB. destruct Q5 as (_ & [Q|Q] & _); lia. }
  apply (KONT fx6 R6 M5 model5 LK Aw2 (PM.VLong cap n p) cr2).
  + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
    assert (CH : forall k, In k PMASTP.KS_ascTH -> In k L5SAR.cs_all -> In k PMASTP.KS_ascN -> In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg k) = getr R (reg k)).
    { intros k' H1 H4' H5 H6. rewrite (KS6 k' H1), (L5SAR.cs_of_preserved R3 R4 k' RP4 H4'), (nKS k' H5), (CS2 k' H4'). apply aKS. exact H6. }
    destruct Hk as [<-|Hk]; [rewrite tR2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; inl|].
    destruct Hk as [<-|Hk]; [apply CH; inl|].
    destruct Hk as [<-|Hk]; [rewrite tR8; symmetry; apply U_to|].
    destruct Hk as [<-|Hk]; [rewrite tR9; symmetry; apply U_to|].
    destruct Hk as [<-|Hk]; [rewrite tR18; symmetry; apply U_to|].
    destruct Hk as [<-|Hk]; [rewrite tR19; symmetry; apply U_to|].
    destruct Hk as [<-|Hk]; [rewrite tR20; symmetry; apply U_to|].
    destruct Hk as [<-|Hk]; [rewrite tR21; symmetry; apply U_to|].
    repeat (destruct Hk as [<-|Hk]; [apply CH; inl|]). destruct Hk.
  + split; [apply (L5.defined_grows M4 M5 _ _ MGM5); exact ODEF4|].
    split; [apply (PMKA.acc_keepA' L ar LB FF sp 12288 [(o, 24)] M M5 EK05 WAPP FRB o 24 AO ACC)|].
    split; [apply (OT o); [lia| lia| exact nO0]|].
    split; [apply (OT (o + 8)); [lia| lia| exact nO8]|].
    split; [apply (OT (o + 16)); [lia| lia| exact nO16]|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply (L5.defined_grows M4 M5 _ _ MGM5); exact DEF4|].
    apply (aacc_of_block M5 p cap p cap SHB5); [apply PMFA.mod16_8; exact Q2| lia| lia| lia].
  + reflexivity.
  + intros X. lia.
  + intros _. exists p. reflexivity.
  + apply (L5SAR.ahpres_of L ar LB FF sp 12288 [(o, 24)] M M5 EK05).
    * intros i Hi. apply MGM5. pose proof ASTK4 as (_ & _ & _ & _ & SD4 & _). apply SD4. exact Hi.
    * apply (L5SAR.dk_trans L ar LB FF sp 12288 M M1 M5 (L5SAR.dk_grows L ar LB FF sp 12288 M M1 MGM1)).
      apply (L5SAR.dk_trans L ar LB FF sp 12288 M1 M2 M5).
      { apply (L5SAR.dk_callee L ar LB [] FF [] sp 12288 (sp - 64) PMSPA.OPNEW_SCR [] M1 M2 PRES2); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia. }
      apply (L5SAR.dk_trans L ar LB FF sp 12288 M2 M3 M5 (L5SAR.dk_grows L ar LB FF sp 12288 M2 M3 MGM3)).
      apply (L5SAR.dk_trans L ar LB FF sp 12288 M3 M4 M5); [|apply (L5SAR.dk_grows L ar LB FF sp 12288 M4 M5 MGM5)].
      apply (L5SAR.dk_mem L ar LB FF sp 12288 (sp - 64) 2560 (fun a => p <= a < p + n) M3 M4 PRES4' SDEF4).
      { intros a Ha. destruct (BYTES (a - p) ltac:(lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (p + (a - p)) with a in Bv by lia. rewrite Bv. discriminate. }
      { intros a. destruct (L5SAR.rng_dec a p (p + n)) as [X|X]; [left; exact X| right; exact X]. }
      lia. lia.
  + exact CRKEEP.
  + apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model model3 model4); [|exact RT4].
    apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3].
    apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact RT2].
  + intros x Hx. exact Hx.
  + exact IA2.
  + exact AM5.
  + exact HH5.
Qed.
End WithHeap.
End PMASTR.
