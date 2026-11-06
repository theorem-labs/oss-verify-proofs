(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5LazyA SymStepR Pm9PlanKit Pm9L5DefsA PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap CutHeapA CutL5A CutBridgeA CutRtCpsA CutCertA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA IslInterpA IslSoundA IslResumeA IslChainA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import IslCgCB.
Import ListNotations. Import ISLA.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module ISA9.
Abbreviation IC := PMLA.C_cboth.

Definition PC : Z := 0x11b984.
Definition TP : Z := 0x691d90.
Definition GUARD : Z := 0x6b1dd0.
Definition NEED_LOCKS : Z := 0x6b2023.
Definition LOCALE_LOCK : Z := 0x6b2100.
Definition GLOC_GUARD : Z := 0x6907c0.     Definition GLOC_PTR : Z := 0x6907b8.     Definition CLASSIC_IMP : Z := 0x690bd0.
Definition ERRCAT : Z := 0x690388.         Definition CONVCAT : Z := 0x690380.         Definition SYSCAT : Z := 0x6905c0.       Definition ATEXIT_TAB : Z := 0x6b1de0.
Definition ABS_HI : Z := 0x6b4000.
Definition PC_MEMSET : Z := 0x7f228.
Definition PC_MEMCMP : Z := 0x6a920.
Definition SCR : Z := 10240.
Definition MS_SCR : Z := 2560.
Definition MC_SCR : Z := 8192.

Definition WABS : list (Z * Z) := [(0x690388, 0x69038a); (0x6905c0, 0x6905c2); (0x6905d0, 0x6907c8); (0x690878, 0x690cf8); (0x691428, 0x691488); (0x6b2100, 0x6b2104); (0x690380, 0x690382)].
Definition CLEAR : list (Z * Z) := (0x10000, 0x156000) :: WABS.
Definition KN0 : list (Z * abyte) :=
  [(NEED_LOCKS, BL 0); (LOCALE_LOCK, BL 0); (LOCALE_LOCK + 1, BL 0); (LOCALE_LOCK + 2, BL 0); (LOCALE_LOCK + 3, BL 0);
   (GUARD, BS 32 0 0); (GUARD + 1, BS 32 0 1); (GUARD + 2, BS 32 0 2); (GUARD + 3, BS 32 0 3); (GUARD + 4, BS 32 0 4); (GUARD + 5, BS 32 0 5); (GUARD + 6, BS 32 0 6); (GUARD + 7, BS 32 0 7)].
Definition CALLS : list (Z * ckind) := [(PC_MEMSET, KMemset); (PC_MEMCMP, KMemcmp)].
Definition MSOK : list (Z * Z) := [(0x690bf8, 0x690ce8)].
Definition ROOK : list (Z * Z) := [(0x307d8, 0x30808)].
Definition C0 : cfg := CFG [RG 2 (- SCR) 0; RG 10 0 8] ABS_HI WABS CLEAR KN0 [] CALLS MSOK ROOK 2.
Definition F0 (k : nat) : aval := if Nat.eqb k 4 then AL TP else AS k 0.
Definition S0 : ast := ST PC (std_regs F0) (PositiveMap.empty _) [PositiveMap.empty _; PositiveMap.empty _] None.
Definition NSTRETCH : nat := 33.
Definition FUEL : nat := 20000.

Definition CSAVED : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition le_lit (n : nat) (v : Z) : list Z := map bv_unsigned (word_to_le_bytes n (Z_to_bv 64 v)).
Fixpoint zs_eqb (a b : list Z) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && zs_eqb a' b' | _, _ => false end.
Definition cell_is (s : ast) (ad : aaddr) (n : nat) (v : Z) : bool :=
  match cell_lit RSEGS C0 s ad n with Some zs => zs_eqb zs (le_lit n v) | None => false end.

Definition POST_ABS : list (Z * nat * Z) :=
  [(GLOC_GUARD, 1%nat, 1); (GLOC_PTR, 8%nat, CLASSIC_IMP); (ERRCAT, 1%nat, 0); (ERRCAT + 1, 1%nat, 0); (SYSCAT, 1%nat, 0); (SYSCAT + 1, 1%nat, 0);
   (NEED_LOCKS, 1%nat, 0); (LOCALE_LOCK, 4%nat, 0); (CONVCAT, 1%nat, 0); (CONVCAT + 1, 1%nat, 0)].

Definition res_chk (res : cres) : bool :=
  match res with
  | CFin s v imm log =>
      aval_eqb v (AS 1 0) && Z.eqb imm 0 && (match s_resv s with None => true | Some _ => false end) &&
      regs_same CSAVED (s_regs S0) (s_regs s) &&
      forallb (ISLC.ev_chk SCR TP MS_SCR MC_SCR) log &&
      cell_is s (ARg 1 0) 8 CLASSIC_IMP &&
      forallb (fun c => cell_is s (AAbs (fst (fst c))) (snd (fst c)) (snd c)) POST_ABS
  | _ => false
  end.
Definition cert_chk : bool := res_chk (arunC RSEGS C0 NSTRETCH FUEL S0).
Lemma cert : cert_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition guard_rom_chk : bool :=
  forallb (fun i => match seg_rom RSEGS (Z_to_bv 64 (GUARD + i)) with Some _ => true | None => false end) [0; 1; 2; 3; 4; 5; 6; 7].
Lemma guard_rom : guard_rom_chk = true.
Proof. vmc_refl. Qed.

Lemma zs_eqb_eq : forall a b, zs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Lemma le_lit_bytes : forall n v, zbytes (le_lit n v) = word_to_le_bytes n (Z_to_bv 64 v).
Proof.
  intros n v. unfold zbytes, le_lit. rewrite map_map. induction (word_to_le_bytes n (Z_to_bv 64 v)) as [|b t IH]; [reflexivity|].
  cbn [map]. rewrite Z_to_bv_bv_unsigned, IH. reflexivity.
Qed.
Lemma cell_is_rdn : forall E M0 s M ad n v, ISLSA.msim RSEGS C0 E M0 s M -> cell_is s ad n v = true ->
  rdn RSEGS M (ISLSA.aden C0 E ad) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros E M0 s M ad n v Hm H. unfold cell_is in H. destruct (cell_lit RSEGS C0 s ad n) as [zs|] eqn:Hc; [|discriminate].
  apply zs_eqb_eq in H. subst zs. rewrite (ISLSA.cell_lit_sound RSEGS C0 E M0 s M ad n _ Hm Hc). rewrite le_lit_bytes. reflexivity.
Qed.
Lemma res_chk_fin : forall res, res_chk res = true -> exists s' log, res = CFin s' (AS 1 0) 0 log /\ s_resv s' = None /\
  regs_same CSAVED (s_regs S0) (s_regs s') = true /\ forallb (ISLC.ev_chk SCR TP MS_SCR MC_SCR) log = true /\ cell_is s' (ARg 1 0) 8 CLASSIC_IMP = true /\
  forallb (fun c => cell_is s' (AAbs (fst (fst c))) (snd (fst c)) (snd c)) POST_ABS = true.
Proof.
  intros [s' v imm log|s' log|c pc log] Hc; try discriminate Hc. unfold res_chk in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hpost]. apply andb_true_iff in Hc. destruct Hc as [Hc Hobjc]. apply andb_true_iff in Hc. destruct Hc as [Hc Hev].
  apply andb_true_iff in Hc. destruct Hc as [Hc Hsame]. apply andb_true_iff in Hc. destruct Hc as [Hc Hresv].
  apply andb_true_iff in Hc. destruct Hc as [Hv Himm]. apply ISLSA.aval_eqb_eq in Hv. apply Z.eqb_eq in Himm. subst v imm.
  exists s', log. repeat split; try assumption. destruct (s_resv s'); [discriminate|reflexivity].
Qed.

Definition gbyte (M : word -> option byte) (a : Z) : byte :=
  match ISLSA.rb RSEGS M (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Definition gbytes (M : word -> option byte) : list byte :=
  [gbyte M GUARD; gbyte M (GUARD + 1); gbyte M (GUARD + 2); gbyte M (GUARD + 3); gbyte M (GUARD + 4); gbyte M (GUARD + 5); gbyte M (GUARD + 6); gbyte M (GUARD + 7)].
Definition envE (R : bvmap 5 word) (M : word -> option byte) : nat -> word :=
  fun k => if (k <? 32)%nat then getr R (Z_to_bv 5 (Z.of_nat k)) else le_bytes_to_word (gbytes M).
Lemma gbyte_rb : forall M i, In i [0; 1; 2; 3; 4; 5; 6; 7] -> ISLSA.rb RSEGS M (Z_to_bv 64 (GUARD + i)) = Some (gbyte M (GUARD + i)).
Proof.
  intros M i Hi. pose proof guard_rom as Hg. unfold guard_rom_chk in Hg. rewrite forallb_forall in Hg. specialize (Hg i Hi).
  unfold gbyte, ISLSA.rb. destruct (M (Z_to_bv 64 (GUARD + i))); [reflexivity|].
  destruct (seg_rom RSEGS (Z_to_bv 64 (GUARD + i))); [reflexivity|discriminate].
Qed.
Lemma reg_of_nat : forall k (r : reg), bv_unsigned r = Z.of_nat k -> Z_to_bv 5 (Z.of_nat k) = r.
Proof. intros k r H. rewrite <- H. apply Z_to_bv_bv_unsigned. Qed.
Lemma envE_reg : forall R M k (rr : reg), (k < 32)%nat -> bv_unsigned rr = Z.of_nat k -> envE R M k = getr R rr.
Proof. intros R M k rr Hk Hr. unfold envE. destruct (Nat.ltb_spec k 32); [|lia]. rewrite (reg_of_nat k rr Hr). reflexivity. Qed.
Lemma rb_eq : forall (M M' : word -> option byte) x, M' x = M x -> ISLSA.rb RSEGS M' x = ISLSA.rb RSEGS M x.
Proof. intros M M' x H. unfold ISLSA.rb. rewrite H. reflexivity. Qed.
Lemma in_ivs_of_In : forall ivs lo hi a, In (lo, hi) ivs -> lo <= a < hi -> in_ivs ivs a = true.
Proof.
  induction ivs as [|[lo' hi'] t IH]; intros lo hi a Hin Hr; [destruct Hin|]. cbn [in_ivs]. apply orb_true_iff.
  destruct Hin as [Hin|Hin]; [injection Hin as -> ->; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia | right; exact (IH _ _ _ Hin Hr)].
Qed.

Lemma u8_of_le : forall M a v, 0 <= v < 256 -> rdn RSEGS M (Z_to_bv 64 a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 v)) -> L5.u8_at RSEGS M a v.
Proof.
  intros M a v Hv H. unfold L5.u8_at. rewrite H. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite ISLSA.wz_small by lia. reflexivity.
Qed.
Lemma F0_nAU : forall k, nth k (std_regs F0) (AL 0) <> AU.
Proof.
  intros k. destruct (Nat.eq_dec k 0) as [->|H0]; [cbn; discriminate|]. destruct (lt_dec k 32) as [Hlt|Hge].
  - rewrite ISLSA.std_regs_nth by lia. unfold F0. destruct (Nat.eqb k 4); discriminate.
  - rewrite nth_overflow; [discriminate|]. unfold std_regs. cbn [length]. rewrite length_map, length_seq. lia.
Qed.
Lemma regs_pres : forall E (MVb : word -> option byte) s' R R' (M' : word -> option byte) rv',
  (forall rr : reg, getreg S0 rr <> AU -> getr R rr = ISLSA.vden E (getreg S0 rr)) -> ISLSA.sim RSEGS C0 E MVb s' R' M' rv' ->
  regs_same CSAVED (s_regs S0) (s_regs s') = true -> regs_preserved R R'.
Proof.
  intros E MVb s' R R' M' rv' Hreg0 Hsim' Hsame rr Hin.
  assert (HC : In (rnat rr) CSAVED).
  { unfold callee_saved_idx in Hin. unfold rnat, CSAVED. repeat (destruct Hin as [Hin|Hin]; [rewrite <- Hin; cbn; tauto|]). contradiction. }
  assert (EQ : getreg s' rr = getreg S0 rr) by (unfold getreg; symmetry; exact (ISLSA.regs_same_sound CSAVED _ _ Hsame _ HC)).
  assert (NAU : getreg S0 rr <> AU) by (unfold getreg, S0; cbn [s_regs]; apply F0_nAU).
  rewrite (ISLSA.sm_regs _ _ _ _ _ _ _ _ Hsim' rr ltac:(rewrite EQ; exact NAU)), EQ. symmetry. exact (Hreg0 rr NAU).
Qed.

Lemma atexit_agree : forall (M M' : word -> option byte) hs,
  (forall a, ATEXIT_TAB <= a < ATEXIT_TAB + ATEXIT_TAB_BYTES -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  atexit_state_at RSEGS ATEXIT_TAB M hs -> atexit_state_at RSEGS ATEXIT_TAB M' hs.
Proof.
  intros M M' hs AG. unfold ATEXIT_TAB_BYTES in AG.
  assert (C : forall d (n : nat) v, 0 <= d -> d + Z.of_nat n <= 544 -> HeapIfaceA.cell_is RSEGS M (ATEXIT_TAB + d) n v -> HeapIfaceA.cell_is RSEGS M' (ATEXIT_TAB + d) n v).
  { intros d n v Hd Hn Hc. unfold HeapIfaceA.cell_is in *. rewrite (L5C.rdn_agree RSEGS M M' n (ATEXIT_TAB + d)); [exact Hc | unfold ATEXIT_TAB; lia | unfold ATEXIT_TAB; lia |].
    intros i Hi. apply AG. lia. }
  assert (C0' : forall (n : nat) v, Z.of_nat n <= 544 -> HeapIfaceA.cell_is RSEGS M ATEXIT_TAB n v -> HeapIfaceA.cell_is RSEGS M' ATEXIT_TAB n v).
  { intros n v Hn Hc. pose proof (C 0 n v ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact (X Hc). }
  intros (A1 & A2 & A3). split; [apply C0'; [cbn; lia | exact A1] | split; [apply C; [lia | cbn; lia | exact A2] |]].
  destruct hs as [|h hs'].
  - destruct A3 as (B1 & B2). split; [apply C; [lia | cbn; lia | exact B1] |].
    destruct B2 as [B2 | (B2 & B3)]; [left; apply C; [lia | cbn; lia | exact B2] | right; split; apply C; try (cbn; lia); assumption].
  - destruct A3 as (L32 & B1 & B2 & B3 & B4). split; [exact L32 |]. split; [apply C; [lia | cbn; lia | exact B1] |]. split; [apply C; [lia | cbn; lia | exact B2] |].
    split; [apply C; [lia | cbn; lia | exact B3] |].
    intros i f a Hn. destruct (B4 i f a Hn) as (D1 & D2).
    assert (Hi : (i < length (h :: hs'))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
    split.
    + rewrite <- Z.add_assoc in D1 |- *. apply C; [lia | change (Z.of_nat 8) with 8; lia | exact D1].
    + rewrite <- Z.add_assoc in D2 |- *. apply C; [lia | change (Z.of_nat 8) with 8; lia | exact D2].
Qed.

Section Island.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis HTP : hl_tp L = TP.
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis GUARDC : forall a, GUARD <= a < GUARD + 8 -> ~ hl_rt_static L a.
Hypothesis MEMSET_LIBC : CRC.amemset_spec_at L ar HI PC_MEMSET.
Hypothesis MEMCMP_LIBC : CRC.amemcmp_spec_at L ar HI PC_MEMCMP MC_SCR.
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis POI_MS : Forall (fun r : Z * Z => 0x690ce8 <= fst r \/ snd r <= 0x690bf8) (icl_poison IL).
Hypothesis POI_RO : Forall (fun r : Z * Z => 0x30808 <= fst r \/ snd r <= 0x307d8) (icl_poison IL).

Definition W_of (o : Z) : list L5.range := (o, 8) :: map (fun iv => (fst iv, snd iv - fst iv)) WABS.

Lemma wabs_foot : forall lo hi, In (lo, hi) WABS -> In (lo, hi) (PMLA.FOOT IC).
Proof. intros lo hi Hin. cbn in Hin |- *. intuition. Qed.
Lemma wabs_in_foot : forall lo hi a, In (lo, hi) WABS -> lo <= a < hi -> PMLA.in_foot IC a.
Proof. intros lo hi a Hin Hr. exists (lo, hi). split; [exact (wabs_foot _ _ Hin) | exact Hr]. Qed.
Lemma wabs_clear : forall lo hi a, In (lo, hi) WABS -> lo <= a < hi -> ~ PMLA.in_tab IC a /\ a <> PMLA.NEED_LOCKS IC.
Proof. intros lo hi a Hin Hr. unfold PMLA.in_tab, ATEXIT_TAB_BYTES. cbn [PMLA.ATEXIT_TAB PMLA.NEED_LOCKS PMLA.C_cboth]. cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma foot_iv_rng : forall lo hi, In (lo, hi) (PMLA.FOOT IC) -> 0x690380 <= lo /\ hi <= 0x6b2104.
Proof. intros lo hi Hiv. cbn in Hiv. repeat (destruct Hiv as [Hiv|Hiv]; [injection Hiv as <- <-; lia|]). destruct Hiv. Qed.
Lemma foot_rng : forall a, PMLA.in_foot IC a -> 0x690380 <= a < 0x6b2104.
Proof. intros a (iv & Hiv & Hr). cbn in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv. Qed.
Lemma kn0_cases : forall a b, In (a, b) KN0 -> a = NEED_LOCKS \/ (LOCALE_LOCK <= a < LOCALE_LOCK + 4) \/ (GUARD <= a < GUARD + 8).
Proof. intros a b Hin. cbn in Hin. unfold NEED_LOCKS, LOCALE_LOCK, GUARD in Hin |- *. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). destruct Hin. Qed.

Theorem locale_ctor_first_ok : ICG.locale_ctor_first_specA_cg L ar HI IC PC.
Proof.
  intros LB FF LK cr A o sp r. unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hls & Hob & Ho8 & HDo & HSS) Hcont.
  unfold PMSA.a0, PMSA.u8, PMSA.u64, PMSA.acobj, PMSA.stksh, PMLA.stksh, PMSA.ls_ok in *.
  pose proof (L5A.aly_segs L C LAY) as LS.
  pose proof Hls as (HRO & (HAT & HQ1 & HQ2) & HPR). rewrite LS in HAT, HQ1, HQ2.
  change (PMLA.NEED_LOCKS IC) with NEED_LOCKS in HQ1. change (PMLA.LOCALE_LOCK IC) with LOCALE_LOCK in HQ2. change (PMLA.ATEXIT_TAB IC) with ATEXIT_TAB in HAT. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). destruct (CHA.rf_fs _ _ _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & FS4).
  pose proof Hstk as (S1 & S2 & S3 & S4 & S5 & S6). unfold PMSA.ISLAND_SCR, PMSA.MEMCMP_SCR in *.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.acobj_rng L ar LB FF sp o 8 RFx CSP Hob ltac:(lia)) as (O3 & O6 & O5 & O1 & O4).
  assert (OHI : ABS_HI <= o) by (unfold ABS_HI; rewrite ILO, IHI in FS4; unfold FS_BYTES in *; clear - O1 FS4 FS0 CL CSP; lia).
  assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).

  assert (IMGCLR : forall a, 0x10000 <= a < 0x156000 -> ISLC.CLR L ar LB FF sp SCR a).
  { intros a Ha. split; [lia|]. split; [right; right; left; rewrite ILO, IHI; split; [lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); lia]|].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_LO. lia. }
  assert (FOOTWOK : forall a, PMLA.in_foot IC a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp SCR a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Hf. pose proof (foot_rng a Hf) as RG. split; [lia|]. split; [right; right; left; rewrite ILO, IHI; split; [lia | intros [Hs|Hs]; [exact (proj1 (FOOTC2 a Hf) Hs) | exact (proj2 (FOOTC2 a Hf) Hs)]]|].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_LO. lia. }
  assert (FOOTCLR : forall a, PMLA.in_foot IC a -> ISLC.CLR L ar LB FF sp SCR a).
  { intros a Hf. destruct (FOOTWOK a Hf) as (X1 & X2 & X3). split; [exact X1 | split; [exact (aclientw_client _ _ _ _ _ _ _ X2) | exact X3]]. }
  assert (GUARDCLR : forall a, GUARD <= a < GUARD + 8 -> ISLC.CLR L ar LB FF sp SCR a).
  { intros a Ha. unfold GUARD in Ha. split; [lia|]. split; [right; right; left; rewrite ILO, IHI; split; [lia | exact (GUARDC a Ha)]|].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_LO. lia. }
  assert (OWOK : forall a, o <= a < o + 8 -> ISLC.WOK L ar LB FF sp SCR (W_of o) a).
  { intros a Ha. destruct (CL5A.acobj_wok L ar LB FF sp SCR o 8 a RFx CSP Hob Ha) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [|exact X3].
    exists (o, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (VIS_CLR : forall a, ISLC.CLR L ar LB FF sp SCR a -> CCA.vis A model M (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a (X1 & X2 & X3). unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact (CLV _ _ X1 X2 X3). }
  assert (VIS_STK : forall a, sp - SCR <= a < sp -> CCA.vis A model M (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. unfold CCA.vis. apply L5LZ.mrestrict_visible'. apply (CLV 0); [unfold SCR in Ha; lia | right; left; split; [unfold SCR in Ha; lia|lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI, SCR in *. lia. }
  assert (VIS_O : forall a, o <= a < o + 8 -> CCA.vis A model M (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. destruct (OWOK a Ha) as (X1 & X2 & _ & X3). unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact (CLV _ _ X1 (aclientw_client _ _ _ _ _ _ _ X2) X3). }

  set (E := envE R M).
  assert (HE2 : bv_unsigned (E 2%nat) = sp) by (unfold E; rewrite (envE_reg R M 2 2%bv) by (reflexivity || lia); rewrite Hsp; apply ISLSA.wz_small; lia).
  assert (HE10 : bv_unsigned (E 10%nat) = o) by (unfold E; rewrite (envE_reg R M 10 10%bv) by (reflexivity || lia); rewrite Ha0; apply ISLSA.wz_small; lia).
  assert (IO : ISLSA.init_ok C0 E).
  { constructor.
    - cbn [c_abs_hi C0]. unfold ABS_HI. lia.
    - intros j rg Hj. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; unfold ISLSA.rbase; cbn [rg_k rg_lo rg_hi c_abs_hi C0].
      + rewrite HE2. unfold ABS_HI, SCR. split; [lia|]. split; [lia|].
        rewrite (Z.div_mod sp 16) by lia. rewrite S1. replace (16 * (sp / 16) + 0) with ((2 * (sp / 16)) * 8) by lia. apply Z.mod_mul. lia.
      + rewrite HE10. split; [lia|]. split; [lia | exact Ho8].
    - intros j j' rg rg' Hj Hj' Hne. unfold ISLSA.rbase.
      destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-;
      (destruct j' as [|[|j']]; cbn in Hj'; try (destruct j'; discriminate); injection Hj' as <-); try congruence;
      cbn [rg_k rg_lo rg_hi]; rewrite HE2, HE10; unfold SCR; clear - O4 S2; lia. }
  assert (Hreg0 : forall rr : reg, getreg S0 rr <> AU -> getr R rr = ISLSA.vden E (getreg S0 rr)).
  { unfold S0. apply ISLSA.std_regs_ok. intros k Hk. unfold F0. destruct (Nat.eqb_spec k 4) as [->|Hne].
    - rewrite (reg_of_nat 4 4%bv eq_refl). rewrite Htp, HTP. reflexivity.
    - rewrite ISLSA.vden_AS0. unfold E, envE. destruct (Nat.ltb_spec k 32); [reflexivity | lia]. }
  set (MV := CCA.vis A model M).
  assert (RT0 : forall a, 0 < a < c_abs_hi C0 -> ISLSA.rt_at RSEGS C0 E MV a).
  { intros a Ha ab Hab. unfold rdb0 in Hab.
    destruct (kn_find (c_kn0 C0) a) as [b|] eqn:Hkn.
    - injection Hab as <-. apply ISLSA.kn_find_in in Hkn. cbn [c_kn0 C0] in Hkn.
      assert (HG : ISLSA.vden E (AS 32 0) = le_bytes_to_word (gbytes M)) by (rewrite ISLSA.vden_AS0; reflexivity).
      assert (HGB : word_to_le_bytes 8 (ISLSA.vden E (AS 32 0)) = gbytes M) by (rewrite HG; apply ISLSA.le_roundtrip8; reflexivity).
      assert (KV : MV (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { destruct (kn0_cases a b Hkn) as [->|[Hl|Hg]]; apply VIS_CLR; [apply FOOTCLR; exists (0x6b2023, 0x6b2024); split; [clear; cbn; tauto | cbn [fst snd]; unfold NEED_LOCKS; clear; lia]
          | apply FOOTCLR; exists (0x6b2100, 0x6b2104); split; [clear; cbn; tauto | cbn [fst snd]; unfold LOCALE_LOCK in Hl; clear - Hl; lia] | exact (GUARDCLR a Hg)]. }
      rewrite (rb_eq M MV _ KV).
      pose proof (ISLSA.rdn_rb RSEGS M 4 LOCALE_LOCK _ HQ2) as H4. pose proof (ISLSA.rdn_rb RSEGS M 1 NEED_LOCKS _ HQ1) as H1.
      cbn in Hkn. repeat (destruct Hkn as [Hkn|Hkn]; [injection Hkn as <- <-|]); try contradiction;
        try (cbn [ISLSA.bden]; rewrite HGB; first [ rewrite <- (Z.add_0_r GUARD) at 1 | idtac ]; apply gbyte_rb; clear; cbn; tauto).
      + rewrite <- (Z.add_0_r NEED_LOCKS). apply (H1 0%nat). lia.
      + rewrite <- (Z.add_0_r LOCALE_LOCK). apply (H4 0%nat). lia.
      + apply (H4 1%nat). lia.
      + apply (H4 2%nat). lia.
      + apply (H4 3%nat). lia.
    - destruct (in_ivs (c_clear C0) a) eqn:Hcl; [|cbn [c_zero C0 in_ivs] in Hab; discriminate Hab].
      destruct (ISLSA.in_ivs_true _ _ Hcl) as (lo & hi & Hi & Hr). cbn [c_clear C0 CLEAR] in Hi.
      assert (HN : M (Z_to_bv 64 a) = None /\ ISLC.CLR L ar LB FF sp SCR a).
      { destruct Hi as [Hi|Hi].
        + injection Hi as <- <-. split; [apply HRO; cbn; exact Hr | apply IMGCLR; exact Hr].
        + destruct (wabs_clear lo hi a Hi Hr) as [T1 T2]. split; [apply HPR; [exact (wabs_in_foot lo hi a Hi Hr) | exact T1 | exact T2] | apply FOOTCLR; exact (wabs_in_foot lo hi a Hi Hr)]. }
      destruct HN as [HN HC']. unfold ISLSA.rb, MV. rewrite (VIS_CLR a HC'), HN.
      destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [bb|]; [|discriminate Hab]. injection Hab as <-. cbn [ISLSA.bden]. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Hsim0 : ISLSA.sim RSEGS C0 E MV S0 R MV None).
  { apply (ISLSA.sim_init RSEGS C0 E MV); [exact Hreg0 | reflexivity | reflexivity | intros; apply PositiveMap.gempty | | reflexivity | exact RT0 |].
    - intros j t Hj k. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; apply PositiveMap.gempty.
    - intros j rg off Hj Ho. unfold ISLSA.rbase. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; cbn [rg_k rg_lo rg_hi] in Ho |- *.
      + rewrite HE2. unfold MV. rewrite (VIS_STK (sp + off)) by lia. replace (sp + off) with (sp - 10240 + (off + 10240)) by lia. apply S5. unfold SCR in Ho. lia.
      + rewrite HE10. unfold MV. rewrite (VIS_O (o + off)) by lia. apply HDo. lia. }

  set (W := W_of o).
  assert (RAV : E 1%nat = Z_to_bv 64 r) by (unfold E; rewrite (envE_reg R M 1 1%bv) by (reflexivity || lia); exact Hra).
  assert (TPV : TP = hl_tp L) by (symmetry; exact HTP).
  assert (SCRMS : 0 <= hl_scr_mem L <= MS_SCR) by (rewrite (L5A.aly_scr_mem L C LAY); unfold MS_SCR; lia).
  assert (SCRMC : 0 <= MC_SCR) by (unfold MC_SCR; clear; lia).
  assert (WABS_ok : forall a, in_ivs (c_wabs C0) a = true -> ISLC.WOK L ar LB FF sp SCR W a).
  { intros a Ha. cbn [c_wabs C0] in Ha. destruct (ISLSA.in_ivs_true _ _ Ha) as (lo & hi & Hi & Hr).
    destruct (FOOTWOK a (wabs_in_foot lo hi a Hi Hr)) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [|exact X3].
    exists (lo, hi - lo). split; [right; exact (in_map (fun iv : Z * Z => (fst iv, snd iv - fst iv)) WABS (lo, hi) Hi) | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (RTC : forall a, 0 < a < c_abs_hi C0 -> rdb0 RSEGS C0 a <> None -> ISLC.CLR L ar LB FF sp SCR a).
  { intros a Ha Hr. unfold rdb0 in Hr. destruct (kn_find (c_kn0 C0) a) as [b|] eqn:Hkn.
    - apply ISLSA.kn_find_in in Hkn. cbn [c_kn0 C0] in Hkn. destruct (kn0_cases a b Hkn) as [->|[Hl|Hg]];
        [apply FOOTCLR; exists (0x6b2023, 0x6b2024); split; [clear; cbn; tauto | cbn [fst snd]; unfold NEED_LOCKS; clear; lia]
        | apply FOOTCLR; exists (0x6b2100, 0x6b2104); split; [clear; cbn; tauto | cbn [fst snd]; unfold LOCALE_LOCK in Hl; clear - Hl; lia] | exact (GUARDCLR a Hg)].
    - destruct (in_ivs (c_clear C0) a) eqn:Hcl; [|cbn [c_zero C0 in_ivs] in Hr; exfalso; exact (Hr eq_refl)].
      destruct (ISLSA.in_ivs_true _ _ Hcl) as (lo & hi & Hi & Hrg). cbn [c_clear C0 CLEAR] in Hi.
      destruct Hi as [Hi|Hi]; [injection Hi as <- <-; apply IMGCLR; exact Hrg | apply FOOTCLR; exact (wabs_in_foot lo hi a Hi Hrg)]. }
  assert (RGS : forall j rg, nth_error (c_rgs C0) j = Some rg ->
    (rg_k rg = c_spk C0 /\ - SCR <= rg_lo rg /\ rg_hi rg <= 0) \/ (rg_k rg <> c_spk C0 /\ forall off, rg_lo rg <= off < rg_hi rg -> ISLC.WOK L ar LB FF sp SCR W (ISLSA.rbase E rg + off))).
  { intros j rg Hj. destruct j as [|[|j]]; cbn in Hj; try (destruct j; discriminate); injection Hj as <-; cbn [rg_k rg_lo rg_hi c_spk C0].
    - left. lia.
    - right. split; [lia|]. intros off Ho. unfold ISLSA.rbase. cbn [rg_k]. rewrite HE10. apply OWOK. lia. }
  assert (W_app : forall w a, In w W -> L5.in_rng w a -> a + 1 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a).
  { intros w a [<-|Hw] Hin.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - O5 Hin. lia.
    - apply in_map_iff in Hw. destruct Hw as ([lo hi] & <- & Hi). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      pose proof (foot_rng a (wabs_in_foot lo hi a Hi ltac:(lia))). unfold BIGSHADOW_LO. lia. }
  assert (IMGACC : forall LK' A' (M' : mem) model' lo hi, ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
            0x10000 <= lo -> hi <= 0x6b4000 -> lo < hi -> Forall (fun r : Z * Z => hi <= fst r \/ snd r <= lo) (icl_poison IL) -> aacc M' lo (hi - lo)).
  { intros LK' A' M' model' lo hi HH' Hlo Hhi Hlt HP a Ha. left.
    destruct (ISH _ _ _ _ _ _ _ HH' lo (hi - lo) ltac:(rewrite ILO; lia) ltac:(rewrite IHI; lia) ltac:(lia)) as [BZ _].
    - eapply Forall_impl; [|exact HP]. intros [x y] Hxy. cbn [fst snd] in *. clear - Hxy. lia.
    - apply BZ. unfold in_shadow_of, S. clear - Ha. split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia]. }
  assert (MS_acc : forall LK' A' (M' : mem) model' lo hi, ri_inv HI LB FF LK' cr A' M' (vml_of model') -> In (lo, hi) (c_msok C0) -> aacc M' lo (hi - lo)).
  { intros LK' A' M' model' lo hi HH' [Hin|[]]. injection Hin as <- <-. apply (IMGACC LK' A' M' model' _ _ HH'); [clear; lia|clear; lia|clear; lia| exact POI_MS]. }
  assert (RO_acc : forall LK' A' (M' : mem) model' lo hi, ri_inv HI LB FF LK' cr A' M' (vml_of model') -> In (lo, hi) (c_rook C0) -> aacc M' lo (hi - lo)).
  { intros LK' A' M' model' lo hi HH' [Hin|[]]. injection Hin as <- <-. apply (IMGACC LK' A' M' model' _ _ HH'); [clear; lia|clear; lia|clear; lia| exact POI_RO]. }
  assert (ABSHI : c_abs_hi C0 <= hl_img_hi L) by (rewrite IHI; cbn [c_abs_hi C0]; unfold ABS_HI; lia).
  assert (RO_rng : forall lo hi, In (lo, hi) (c_rook C0) -> hl_img_lo L <= lo /\ hi <= hl_img_hi L) by (intros lo hi [Hin|[]]; injection Hin as <- <-; rewrite ILO, IHI; lia).
  assert (RO_clr : forall lo hi a, In (lo, hi) (c_rook C0) -> lo <= a < hi -> ISLC.CLR L ar LB FF sp SCR a) by (intros lo hi a [Hin|[]] Hr; injection Hin as <- <-; apply IMGCLR; lia).
  assert (MEMSET : forall pc, In (pc, KMemset) (c_calls C0) -> CRC.amemset_spec_at L ar HI pc).
  { intros pc Hin. cbn [c_calls C0 CALLS] in Hin. destruct Hin as [Hin|[Hin|[]]]; [injection Hin as <-; exact MEMSET_LIBC | discriminate Hin]. }
  assert (MEMCMP : forall pc, In (pc, KMemcmp) (c_calls C0) -> CRC.amemcmp_spec_at L ar HI pc MC_SCR).
  { intros pc Hin. cbn [c_calls C0 CALLS] in Hin. destruct Hin as [Hin|[Hin|[]]]; [discriminate Hin | injection Hin as <-; exact MEMCMP_LIBC]. }
  assert (INV0 : ISLC.INV L ar HI PMSA.fp_ok C0 E LB FF LK cr A M model sp SCR W S0 fx R M model A LK).
  { split; [|unfold MV in Hsim0; rewrite LS; exact Hsim0].
    split; [exact Hmo|]. split; [apply L5LZ.sbm_model_rt; apply same_but_materialized_refl|]. split; [apply incl_refl|]. split; [apply incl_refl|].
    split; [exact HH|]. split; [exact Hroom|]. split; [exact Hfp|]. split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]. }
  pose proof (ISLC.chain_sound L ar C HI HIok LYI LYR LYB LYN PMSA.fp_ok C0 E IO FUEL LB FF LK cr A M model sp SCR W K r TP MS_SCR MC_SCR) as CS.
  rewrite LS in CS.
  specialize (CS Hstk ltac:(unfold SCR; clear; lia) ltac:(reflexivity) Hffrs HKnil HE2 RAV Hraok TPV SCRMS SCRMC WABS_ok RTC RGS W_app HSS MS_acc ABSHI RO_acc RO_rng RO_clr MEMSET MEMCMP).
  destruct (res_chk_fin _ cert) as (s' & log & Hrun & Hresv & Hsame & Hev & Hobjc & Hpost).
  unfold PMSA.cfg. rewrite LS. unfold PMSA.cfg in Hcont. rewrite LS in Hcont. change (Z_to_bv 64 PC) with (Z_to_bv 64 (s_pc S0)).
  apply (CS NSTRETCH S0 fx R M model A LK s' log INV0 Hrun Hresv Hev). clear CS Hrun.
  intros fx' R' M' model' A' LK' [HC' Hsim']. rewrite LS in Hsim'.
  pose proof HC' as (Hmo' & Hrt' & HA' & HLK' & HH' & _ & Hfp' & HKP' & HGR').
  pose proof (ISLSA.sm_mem _ _ _ _ _ _ _ _ Hsim') as Hm'.
  assert (VIS'_CLR : forall a, ISLC.CLR L ar LB FF sp SCR a -> CCA.vis A' model' M' (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a (X1 & X2 & X3). unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model' sp SCR a HH' X1 X2 X3). }

  assert (RB : forall a (n : nat) v lo hi, cell_is s' (AAbs a) n v = true -> In (lo, hi) (PMLA.FOOT IC) -> lo <= a -> a + Z.of_nat n <= hi ->
               rdn RSEGS M' (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v))).
  { intros a n v lo hi Hc Hlh Ha Hn. assert (Hf : forall i, a <= i < a + Z.of_nat n -> PMLA.in_foot IC i) by (intros i Hi; exists (lo, hi); split; [exact Hlh | cbn [fst snd]; clear - Hi Ha Hn; lia]).
    pose proof (foot_iv_rng lo hi Hlh) as RG.
    rewrite <- (cell_is_rdn E _ s' _ (AAbs a) n v Hm' Hc). cbn [ISLSA.aden]. symmetry.
    apply (L5C.rdn_agree RSEGS M' (CCA.vis A' model' M') n a ltac:(clear - RG Ha; lia) ltac:(clear - RG Hn; lia)). intros i Hi. apply VIS'_CLR. apply FOOTCLR. exact (Hf i Hi). }
  unfold POST_ABS in Hpost. cbn [forallb fst snd] in Hpost.
  apply andb_true_iff in Hpost. destruct Hpost as [P1 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P2 Hpost].
  apply andb_true_iff in Hpost. destruct Hpost as [P3 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P4 Hpost].
  apply andb_true_iff in Hpost. destruct Hpost as [P5 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P6 Hpost].
  apply andb_true_iff in Hpost. destruct Hpost as [P7 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P8 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P9 Hpost]. apply andb_true_iff in Hpost. destruct Hpost as [P10 _].
  pose proof (RB _ _ _ 0x6905d0 0x6907c8 P1 ltac:(clear; cbn; tauto) ltac:(unfold GLOC_GUARD; clear; lia) ltac:(unfold GLOC_GUARD; clear; cbn; lia)) as Q1.
  pose proof (RB _ _ _ 0x6905d0 0x6907c8 P2 ltac:(clear; cbn; tauto) ltac:(unfold GLOC_PTR; clear; lia) ltac:(unfold GLOC_PTR; clear; cbn; lia)) as Q2.
  pose proof (RB _ _ _ 0x690388 0x69038a P3 ltac:(clear; cbn; tauto) ltac:(unfold ERRCAT; clear; lia) ltac:(unfold ERRCAT; clear; cbn; lia)) as Q3.
  pose proof (RB _ _ _ 0x690388 0x69038a P4 ltac:(clear; cbn; tauto) ltac:(unfold ERRCAT; clear; lia) ltac:(unfold ERRCAT; clear; cbn; lia)) as Q4.
  pose proof (RB _ _ _ 0x6905c0 0x6905c2 P5 ltac:(clear; cbn; tauto) ltac:(unfold SYSCAT; clear; lia) ltac:(unfold SYSCAT; clear; cbn; lia)) as Q5.
  pose proof (RB _ _ _ 0x6905c0 0x6905c2 P6 ltac:(clear; cbn; tauto) ltac:(unfold SYSCAT; clear; lia) ltac:(unfold SYSCAT; clear; cbn; lia)) as Q6.
  pose proof (RB _ _ _ 0x6b2023 0x6b2024 P7 ltac:(clear; cbn; tauto) ltac:(unfold NEED_LOCKS; clear; lia) ltac:(unfold NEED_LOCKS; clear; cbn; lia)) as Q7.
  pose proof (RB _ _ _ 0x6b2100 0x6b2104 P8 ltac:(clear; cbn; tauto) ltac:(unfold LOCALE_LOCK; clear; lia) ltac:(unfold LOCALE_LOCK; clear; cbn; lia)) as Q8.
  pose proof (RB _ _ _ 0x690380 0x690382 P9 ltac:(clear; cbn; tauto) ltac:(unfold CONVCAT; clear; lia) ltac:(unfold CONVCAT; clear; cbn; lia)) as Q9.
  pose proof (RB _ _ _ 0x690380 0x690382 P10 ltac:(clear; cbn; tauto) ltac:(unfold CONVCAT; clear; lia) ltac:(unfold CONVCAT; clear; cbn; lia)) as Q10.
  clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10.

  pose proof (cell_is_rdn E _ s' _ (ARg 1 0) 8 CLASSIC_IMP Hm' Hobjc) as QO. cbn [ISLSA.aden nth_error c_rgs C0] in QO. unfold ISLSA.rbase in QO. cbn [rg_k] in QO. rewrite HE10, Z.add_0_r in QO.
  assert (QO' : rdn RSEGS M' (Z_to_bv 64 o) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CLASSIC_IMP))).
  { rewrite <- QO. symmetry. apply (L5C.rdn_agree RSEGS M' (CCA.vis A' model' M') 8 o ltac:(clear - O3; lia) ltac:(clear - O6; cbn; lia)). intros i Hi. cbn in Hi.
    destruct (OWOK i ltac:(lia)) as (X1 & X2 & _ & X3). unfold CCA.vis. apply L5LZ.mrestrict_visible'.
    exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model' sp SCR i HH' X1 (aclientw_client _ _ _ _ _ _ _ X2) X3). }
  clear QO.

  assert (OUTW : forall a, a < 0x690380 \/ 0x6b1de0 <= a < 0x6b2023 -> L5.outside W a).
  { intros a Ha w [<-|Hw] Hin.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold ABS_HI in OHI. clear - Ha Hin OHI. lia.
    - apply in_map_iff in Hw. destruct Hw as ([lo hi] & <- & Hi). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. cbn in Hi. clear - Ha Hi Hin.
      repeat (destruct Hi as [Hi|Hi]; [injection Hi as <- <-; lia|]). destruct Hi. }
  assert (TABEQ : forall a, ATEXIT_TAB <= a < ATEXIT_TAB + ATEXIT_TAB_BYTES -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. unfold ATEXIT_TAB, ATEXIT_TAB_BYTES in Ha. apply HKP'.
    destruct (FOOTCLR a ltac:(exists (0x6b1de0, 0x6b2000); split; [clear; cbn; tauto | cbn [fst snd]; clear - Ha; lia])) as (X1 & X2 & _).
    split; [exact X1|]. split; [exact X2|]. apply OUTW. clear - Ha. lia. }
  assert (IMGEQ : forall a, 0x10000 <= a < 0x156000 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply HKP'. destruct (IMGCLR a Ha) as (X1 & X2 & _). split; [exact X1|]. split; [exact X2|]. apply OUTW. clear - Ha. lia. }
  apply (Hcont fx' R' M' model' LB cr LB ((o, 8) :: PMSA.foot_ranges IC) LK' A' Hfp').
  -
    split; [exact QO'|]. split; [apply u8_of_le; [lia | exact Q1]|]. split; [exact Q2|].
    split; [unfold PMLA.errcat_guard, PMLA.u8; cbn [PMLA.ERRCAT_GUARD PMLA.C_cboth]; split; (apply u8_of_le; [lia|]); [exact Q3 | exact Q4]|].
    split; [unfold PMLA.convcat_guard, PMLA.u8; cbn [PMLA.CONVCAT_GUARD PMLA.C_cboth]; split; (apply u8_of_le; [lia|]); [exact Q9 | exact Q10]|].
    split; [unfold PMLA.atexit_ok, PMLA.libc_quiet; split; [apply (atexit_agree M M' _ TABEQ); exact HAT | split; [exact Q7 | exact Q8]]|].
    split; [intros i Hi; rewrite (IMGEQ i Hi); exact (HRO i Hi)|].
    split; [apply u8_of_le; [lia | exact Q5]|]. split; [apply u8_of_le; [lia | exact Q6]|].
    repeat split; reflexivity.
  - exact (regs_pres E _ s' R R' _ None Hreg0 Hsim' Hsame).
  -
    split; [|split].
    + intros a (Ha & Hc & Ho). apply HKP'. split; [exact Ha|]. split; [exact Hc|]. intros w Hw Hin. apply (Ho w); [|exact Hin].
      destruct Hw as [<-|Hw]; [left; reflexivity | right]. apply in_map_iff in Hw. destruct Hw as ([lo hi] & <- & Hi).
      unfold PMSA.foot_ranges. apply in_map_iff. exists (lo, hi). split; [reflexivity | exact (wabs_foot lo hi Hi)].
    + intros i Hi. clear - HGR' Hi CL S2 S3 S4 S5. apply HGR'; [lia | right; left; split; lia | apply S5; lia].
    + intros a Ha Hc Hd. apply HGR'; [exact Ha | | exact Hd]. eapply CHA.aclient_scr; [exact Hc | intros x Hx; clear - Hx; lia].
  - exact Hrt'.
  - exact HA'.
  - exact Hmo'.
  - exact HLK'.
  - exact HH'.
Qed.
End Island.
End ISA9.
