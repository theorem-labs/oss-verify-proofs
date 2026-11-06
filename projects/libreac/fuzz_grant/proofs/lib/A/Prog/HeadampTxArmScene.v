(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_arm_scene on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_headamp_tx_arm_scene (0x84f1c) on fuzz_grant's ASan build: for a base below 48
   and a width other than 0 the call stores the base and the clamped width in the
   table's scene fields (bytes 436 and 437), zeroes the nine bytes 440..448 with
   __asan_memset, stores the base and the width again (449, 450) and clears the
   4-byte counter at 456; for any other base or width it writes nothing. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaStep PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC1g HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel reac_headamp_tx_arm_scene_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac arm_dec :=
  repeat match goal with
  | |- context [ ((?k <=? ?n)%nat && (?n <? ?m)%nat)%bool ] =>
      first [ replace ((k <=? n)%nat && (n <? m)%nat)%bool with true by
                (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia)
            | replace ((k <=? n)%nat && (n <? m)%nat)%bool with false by
                (symmetry; apply andb_false_iff;
                 first [left; apply Nat.leb_gt; lia | right; apply Nat.ltb_ge; lia]) ]
  end.

Ltac arm_len :=
  repeat first [ rewrite Mem.length_le1 | rewrite Mem.length_le4
               | rewrite Mem.upd_bytes_length by arm_len ]; lia.

Lemma arm_bow0 : forall k, YP09.byte_of_word (Z_to_bv 64 0) k = Z_to_bv 8 0.
Proof. intros k. unfold YP09.byte_of_word. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma arm_inFP : forall tx a,
  (tx + 436 <= a < tx + 438) \/ (tx + 440 <= a < tx + 451) \/ (tx + 456 <= a < tx + 460) ->
  inFP [(tx + 436, tx + 438); (tx + 440, tx + 451); (tx + 456, tx + 460)] a.
Proof.
  intros tx a [H | [H | H]];
  [exists (tx + 436, tx + 438) | exists (tx + 440, tx + 451) | exists (tx + 456, tx + 460)];
  cbn [In fst snd]; split; [tauto | lia | tauto | lia | tauto | lia].
Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition TARM_STK : Z := 48 + ESTACK.
Definition A_tx_arm_sceneP : Z := BASE + AF_reac_headamp_tx_arm_scene.
Definition arm_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0); (32%nat, mkAF SBz SBz 0) ] [] [].
Definition arm_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 32 ].
Definition ss_arm : sstate := mkSS AF_reac_headamp_tx_arm_scene sr_atoms arm_regions None arm_facts.
Definition arm_SH : list shent := [ mkSHE 10 0 460 ].
Definition EAS (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SBz]).
Definition W436 : YP09.region := YP09.mkRegion (Some 10%nat) 436 438 436 438 [].
Definition W449 : YP09.region := YP09.mkRegion (Some 10%nat) 449 451 449 451 [].
Definition W456 : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [].

Lemma arm_mbyte_of_frame : forall (H : word -> bool) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict H m) (mrestrict H m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H E' rs m m' a HF Hn Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma arm_mbyte_some : forall H (m : word -> option byte) a z,
  aview SEGS H m a = Some z -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 z).
Proof.
  intros H m a z E. unfold aview in E. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb;
  cbn in E; [|discriminate]. injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma arm_written : forall (Ex : env) m (tx sb sw : Z) (T : list byte) (WSV : sv) (c1 c2 c3 : list YP09.chunk),
  0 <= sb < 48 -> length T = 460%nat ->
  bv_unsigned (ew Ex 10) = tx ->
  sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb ->
  sv_denot Ex WSV = Z_to_bv 64 (reac_headamp_tx_arm_scene_c.arm_w sb sw) ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 436 438 436 438 c1) ->
  In (YP09.mkChunk 436 (CVal 1 (SOff 11 0))) c1 -> In (YP09.mkChunk 437 (CVal 1 WSV)) c1 ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 449 451 449 451 c2) ->
  In (YP09.mkChunk 449 (CVal 1 (SOff 11 0))) c2 -> In (YP09.mkChunk 450 (CVal 1 WSV)) c2 ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 456 460 456 460 c3) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) c3 ->
  (forall i, 440 <= i < 449 -> mbyte SEGS m (tx + i) = Some (Z_to_bv 8 0)) ->
  (forall i, tx_fbyte i = true -> ~ (436 <= i < 438) -> ~ (440 <= i < 451) -> ~ (456 <= i < 460) ->
     mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  obj_at SEGS m tx LAY_TX (tx_vals (reac_headamp_tx_arm_scene_c.arm_T T sb sw)).
Proof.
  intros Ex m tx sb sw T WSV c1 c2 c3 Hsb HTl E10 E11 EW HR1 I436 I437 HR2 I449 I450 HR3 I456 Hz Hkeep.
  apply (proj2 (tx_obj_bytes SEGS m tx _)).
  intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  unfold reac_headamp_tx_arm_scene_c.arm_T.
  rewrite !SegSetModel.nth_upd_bytes by arm_len.
  rewrite ?Mem.length_le1, ?Mem.length_le4.
  destruct (Z_lt_le_dec i 436) as [L|L].
  { arm_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia]. }
  destruct (Z_lt_le_dec i 437) as [L1|L1].
  { assert (i = 436) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 436 - 436)%nat with 0%nat. rewrite le1_byte_of_word. rewrite <- E11.
    replace (tx + 436) with (bv_unsigned (ew Ex 10) + 436 + 0) by lia.
    exact (byte_of_region SEGS Ex m 10%nat _ _ 436 438 436 438 436 1 (SOff 11 0) 0 HR1 eq_refl I436 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 438) as [L2|L2].
  { assert (i = 437) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 437 - 437)%nat with 0%nat. rewrite le1_byte_of_word. rewrite <- EW.
    replace (tx + 437) with (bv_unsigned (ew Ex 10) + 437 + 0) by lia.
    exact (byte_of_region SEGS Ex m 10%nat _ _ 436 438 436 438 437 1 WSV 0 HR1 eq_refl I437 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 440) as [L3|L3].
  { exfalso. assert (i = 438 \/ i = 439) as [-> | ->] by lia; vm_compute in Hi; discriminate. }
  destruct (Z_lt_le_dec i 449) as [L4|L4].
  { rewrite (Hz i ltac:(lia)). f_equal.
    destruct (Z_lt_le_dec i 444) as [L5|L5].
    { arm_dec. cbv beta iota. rewrite le4_byte_of_word by lia. symmetry. apply arm_bow0. }
    destruct (Z_lt_le_dec i 448) as [L6|L6].
    { arm_dec. cbv beta iota. rewrite le4_byte_of_word by lia. symmetry. apply arm_bow0. }
    assert (i = 448) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 448 - 448)%nat with 0%nat. rewrite le1_byte_of_word. symmetry. apply arm_bow0. }
  destruct (Z_lt_le_dec i 450) as [L7|L7].
  { assert (i = 449) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 449 - 449)%nat with 0%nat. rewrite le1_byte_of_word. rewrite <- E11.
    replace (tx + 449) with (bv_unsigned (ew Ex 10) + 449 + 0) by lia.
    exact (byte_of_region SEGS Ex m 10%nat _ _ 449 451 449 451 449 1 (SOff 11 0) 0 HR2 eq_refl I449 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 451) as [L8|L8].
  { assert (i = 450) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 450 - 450)%nat with 0%nat. rewrite le1_byte_of_word. rewrite <- EW.
    replace (tx + 450) with (bv_unsigned (ew Ex 10) + 450 + 0) by lia.
    exact (byte_of_region SEGS Ex m 10%nat _ _ 449 451 449 451 450 1 WSV 0 HR2 eq_refl I450 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 456) as [L9|L9].
  { arm_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia]. }
  arm_dec. cbv beta iota.
  rewrite (le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 456) ltac:(lia)).
  replace (Z.of_nat (Z.to_nat i - 456)) with (i - 456) by lia.
  replace (tx + i) with (bv_unsigned (ew Ex 10) + 456 + (i - 456)) by lia.
  rewrite (byte_of_region SEGS Ex m 10%nat _ _ 456 460 456 460 456 4 (SLit 0) (i - 456) HR3 eq_refl I456 ltac:(cbn; lia)).
  reflexivity.
Qed.

Section H.
Variable B : asyms.
Definition theadamp_tx_arm_scene_spec : Prop :=
 forall ly S W (regs : bvmap 5 word) mem md ch0 (tx sb sw : Z) (T : list byte),
 afn_pre SEGS B TARM_STK ly S W regs mem md ch0 ->
 getr regs 10 = w64 tx -> getr regs 11 = w64 sb -> getr regs 12 = w64 sw ->
 0 <= sb < 256 -> 0 <= sw < 256 ->
 In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
 obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
 SRr SEGS W (cfg_at SEGS A_tx_arm_sceneP regs mem md)
  (apost_base SEGS B TARM_STK [(tx + 436, tx + 438); (tx + 440, tx + 451); (tx + 456, tx + 460)]
     regs ly S W mem md 0
   (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
      obj_at SEGS (mrestrict (w_H W) mem') tx LAY_TX
        (tx_vals (if (sw =? 0) || (48 <=? sb) then T
                  else reac_headamp_tx_arm_scene_c.arm_T T sb sw)))).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma arm_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx sb sw : Z),
  afn_pre SEGS B TARM_STK ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 sb -> getr regs 12 = w64 sw ->
  0 <= sb < 256 -> 0 <= sw < 256 ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (EAS regs) ss_arm
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_tx_arm_sceneP) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx arm_SH (EAS regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx sb sw HPRE H10 H11 H12 Hsb Hsw Htx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : TARM_STK = 4144) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size TX_SIZE) with 460 in *.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite restrict_mkst_fx.
  set (E := EAS regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBz]) n)
    by (intros n Hn; subst E; unfold EAS; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 sb) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 sw) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (change 242%nat with (A_OBJ 1); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E 273%nat = Z_to_bv 64 (VAL (A_OBJ 32)))
    by (change 273%nat with (A_OBJ 32); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_arm, A_tx_arm_sceneP. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold arm_regions, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
        [cbn [sv_denot]; change (A_OBJ 32) with 273%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 CBx SBz);
        [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold arm_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
      repeat split; lia.
    + split; [|split; exact I].
      cbn [arm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E12, E32, !unsigned_lit_small by (unfold SBz; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil Hsb Hsw.
      clear. unfold SBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, arm_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_block SEGS B LAWS ly S W mem md E CBx 10 tx TX_SIZE 0 460 HAR Htx).
    + unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SBz; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

(* the writes of a run land only in writable regions: name every byte outside them *)
Ltac arm_nwr Uspv Eu10v :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
      rewrite ?Uspv, ?Eu10v in Hr; lia |]);
  destruct Hin.

Ltac arm_awr Uspv Eu10v Htxv txv :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply awr_ok_cons_stack;
      [ reflexivity
      | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Uspv
      | azlit_tac | azlit_tac |]
  | eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat txv TX_SIZE);
      [ reflexivity
      | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10v
      | exact Htxv | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (req_size TX_SIZE) with 460; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply arm_inFP; lia |] ].

Ltac arm_disj Eu10v Egotv Ecellv Uspv :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  try unfold W436; try unfold W449; try unfold W456;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?Eu10v, ?Egotv, ?Ecellv;
  rewrite ?unsigned_lit_small by
    (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 32)); lia);
  rewrite ?Uspv;
  try unfold off_img in *;
  repeat match goal with |- _ /\ _ => split end;
  first [exact I | lia].

Ltac arm_addregion HS R Hpresv Eu10v Egotv Ecellv Uspv txv :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let HR := fresh "HR" in let HS2 := fresh "HS" in
    assert (HR : region_ok SEGS Ex (ms_mem (restrict Hh msx)) R)
      by (cbn [restrict ms_mem]; unfold R, region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite Eu10v;
          split; [lia|]; split; [lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hpresv (txv + o) ltac:(lia)))
          | apply Forall_nil ]);
    pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) R HS
                  ltac:(vm_compute; reflexivity) HR ltac:(arm_disj Eu10v Egotv Ecellv Uspv)) as HS2;
    clear HS HR; rename HS2 into HS
  end.

(* the return: the post's frame, journal and callee-saved registers *)
Ltac arm_ret HS HJ HAE E1 Hra W ly S regs :=
  let R1 := fresh "R1" in
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat9 := fresh "mat" in intros mat9; cbn [ms_regs ms_mem]; rewrite R1, ?E1, Hra;
  unfold apost_base; cbv beta;
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
    split; [reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs [Z_to_bv 64 SBz] HS);
            [ eapply env_agree_trans; [exact HAE | split; [intros n Hn;
                rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
            | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]
  end.

(* a path that writes nothing: every byte of the table is the one it was *)
Ltac arm_refused HTo Uspv Eu10v :=
  let i := fresh "i" in let Hi := fresh "Hi" in let Hir := fresh "Hir" in
  apply (proj2 (tx_obj_bytes SEGS _ _ _)); intros i Hi; pose proof (tx_fbyte_range i Hi) as Hir;
  rewrite <- (proj1 (tx_obj_bytes SEGS _ _ _) HTo i Hi);
  repeat match goal with
  | Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ ?mB) |- mbyte _ (mrestrict _ ?mB) ?a = _ =>
      rewrite (arm_mbyte_of_frame _ _ _ _ _ a Hf ltac:(arm_nwr Uspv Eu10v) ltac:(lia)); clear Hf
  end;
  reflexivity.

Theorem pb_headamp_tx_arm_scene : theadamp_tx_arm_scene_spec.
Proof.
unfold theadamp_tx_arm_scene_spec.
intros ly S W regs mem md ch0 tx sb sw T HPRE H10 H11 H12 Hsb Hsw Htx HTl HTo.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (arm_entry ly S W regs mem md ch0 tx sb sw HPRE H10 H11 H12 Hsb Hsw Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B TARM_STK [(tx + 436, tx + 438); (tx + 440, tx + 451); (tx + 456, tx + 460)]
              ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TARM_STK = 4144) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size TX_SIZE) with 460 in *.
pose proof (blk_off_imgP B ly S W mem md tx TX_SIZE HAR Htx) as Htximg.
change (req_size TX_SIZE) with 460 in Htximg.
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
remember (EAS regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EAS; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBz]) n)
  by (intros n Hn; subst E; unfold EAS; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 sb) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 sw) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (change 242%nat with (A_OBJ 1); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 273%nat = Z_to_bv 64 (VAL (A_OBJ 32)))
  by (change 273%nat with (A_OBJ 32); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SBz]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ugot : bv_unsigned (ew E 242%nat) = VAL (A_OBJ 1))
  by (rewrite Egot; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (Ucell : bv_unsigned (ew E 273%nat) = VAL (A_OBJ 32))
  by (rewrite Ecell; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 32)); lia).
assert (Hes : ESTACK = 4096) by reflexivity.
clear HEdef EL.
unfold cfg_at. change (w64 A_tx_arm_sceneP) with (Z_to_bv 64 A_tx_arm_sceneP).
paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
psrr_branch_tok RUN BR HS SHOK EFFspan.
- (* 47 < sb : nothing is written *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 sb E11) in Hc by (unfold M64; lia).
  apply Z.ltb_lt in Hc.
  assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = true) by (apply orb_true_iff; right; apply Z.leb_le; lia).
  paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
  arm_ret HS HJ HAE E1 Hra W ly S regs.
  rewrite HIF. arm_refused HTo Usp Eu10.
- (* sb <= 47 *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 sb E11) in Hc by (unfold M64; lia).
  apply Z.ltb_ge in Hc. rename Hc into Hsb47.
  paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
  psrr_branch_tok RUN BR HS SHOK EFFspan.
  + (* sw = 0 : nothing is written *)
    rewrite branch_eq_U, (U_atom E 12 sw E12), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_eq in Hc.
    assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = true) by (apply orb_true_iff; left; apply Z.eqb_eq; lia).
    paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
    arm_ret HS HJ HAE E1 Hra W ly S regs.
    rewrite HIF. arm_refused HTo Usp Eu10.
  + (* sw <> 0 : the scene is armed *)
    rewrite branch_eq_U, (U_atom E 12 sw E12), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_neq in Hc. rename Hc into Hsw0.
    assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = false)
      by (apply orb_false_iff; split; [apply Z.eqb_neq; lia | apply Z.leb_gt; lia]).
    lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      destruct (al_blocks _ _ LAWS ly S W (ms_mem msx) _ tx TX_SIZE (proj1 HJ) Htx)
        as (_ & _ & _ & _ & Hpres' & _);
      change (req_size TX_SIZE) with 460 in Hpres'
    end.
    arm_addregion HS W436 Hpres' Eu10 Egot Ecell Usp tx.
    arm_addregion HS W449 Hpres' Eu10 Egot Ecell Usp tx.
    arm_addregion HS W456 Hpres' Eu10 Egot Ecell Usp tx.
    clear Hpres'.
    paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
    psrr_branch_tok RUN BR HS SHOK EFFspan.
    * (* sb + sw <= 48 : the width is kept *)
      rewrite branch_geu_U, U_SLit, U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom E 11 sb E11), (U_atom E 12 sw E12) in Hc by lia.
      rewrite (zcanon_id 48), (zcanon_id (sb + sw)) in Hc by (unfold M64; lia).
      apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc. rename Hc into Hclamp.
      assert (EW0 : forall Ex : env, ew Ex 11 = ew E 11 -> ew Ex 12 = ew E 12 ->
                sv_denot Ex (SOff 12 0) = Z_to_bv 64 (reac_headamp_tx_arm_scene_c.arm_w sb sw)).
      { intros Ex H11' H12'. cbn [sv_denot]. rewrite H12', E12, unsigned_lit_small, Z.add_0_r by lia.
        unfold reac_headamp_tx_arm_scene_c.arm_w. replace (48 <? sb + sw) with false by (symmetry; apply Z.ltb_ge; lia).
        reflexivity. }
      (* the call of __asan_memset (tx + 440, 0, 9) *)
      paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
      pmkst HS.
      prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
      prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
      prreg HS (3%bv : bv 5) Rgp2. prreg HS (4%bv : bv 5) Rtp2.
      rewrite Eu10 in Ra0.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
        assert (HspT : spZ rT = spZ regs - 48)
          by (unfold spZ at 1; rewrite Rsp2, Usp; rewrite unsigned_lit_small by lia; lia) end.
      eapply SRr_bind.
      { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
          eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W rT mT
                    _ _ _ _ _ _ _ _ _ _ _ dT _ (tx + 440) 0 9 (-48) _ HJ) end.
        - rewrite Ra0. reflexivity.
        - rewrite Ra1. reflexivity.
        - rewrite Ra2. reflexivity.
        - lia.
        - lia.
        - lia.
        - rewrite HspT. lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite Rgp2, E3. exact Hgp.
        - rewrite Rtp2, E4. exact Htp.
        - exact Rra.
        - apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
        - intros a Ha. split; [|lia].
          right; left; split; [apply arm_inFP; lia
                              | exists tx, TX_SIZE; split; [exact Htx | change (req_size TX_SIZE) with 460; lia]].
        - eapply (amem_range_of_block SEGS B LAWS); [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia].
        - eapply (range_addressable_of_block SEGS B LAWS); [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia].
        - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS);
            [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia | lia].
        - exact I. }
      cbv beta. intros W2 c2 _ Hpost.
      destruct Hpost as (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Ha0' & Heff & Hfrc & Hpres2).
      subst W2. subst c2.
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2' & _ & _ & _).
      destruct (al_blocks _ _ LAWS ly S W mem2 md2 tx TX_SIZE (proj1 HJ2) Htx) as (_ & _ & _ & _ & Htxpres2 & _).
      change (req_size TX_SIZE) with 460 in Htxpres2.
      jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HSX.
      lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
      { repeat (apply Forall_cons;
          [ split;
            [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
              rewrite ?Usp, ?Eu10, ?Ugot, ?Ucell in Ha;
              apply (mbyte_of_aview SEGS); apply Hfrc; unfold off_img in Htximg; lia
            | intros a Ha _; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
              rewrite ?Usp, ?Eu10, ?Ugot, ?Ucell in Ha;
              first [ lia
                    | apply (apresent_writable SEGS);
                      first [ apply (proj1 (Htxpres2 a ltac:(lia))) | apply Hpres2'; lia ] ] ]
          | ]).
        apply Forall_nil. }
      specialize (HSX HRKX). rewrite <- restrict_mkst_fx in HSX. clear HRKX HS.
      assert (HEIX : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB)))
        by (apply img_env_havoc; [exact HEI | cbv; lia]).
      assert (SHOKX : sh_ok SEGS CBx arm_SH (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)).
      { unfold sh_ok, arm_SH. apply Forall_cons; [|apply Forall_nil].
        apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 _ CBx 10 tx TX_SIZE 0 460 (proj1 HJ2) Htx).
        + unfold U, CBx. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
          rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SBz; lia). reflexivity.
        + unfold U. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
          rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
        + lia.
        + change (req_size TX_SIZE) with 460. lia. }
      clear SHOK.
      (* the three stores after the call, and the return *)
      paj_run_tok RUN HSX HJ2 SHOKX EFFspan; [arm_awr Usp Eu10 Htx tx |].
      lazymatch type of HSX with
      | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) W436) in
        let r1 := eval vm_compute in (nth 1 (ss_mem ssx) W436) in
        let r2 := eval vm_compute in (nth 2 (ss_mem ssx) W436) in
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0%nat r0 HSX ltac:(vm_compute; reflexivity)) as HQ0;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1%nat r1 HSX ltac:(vm_compute; reflexivity)) as HQ1;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 2%nat r2 HSX ltac:(vm_compute; reflexivity)) as HQ2;
        cbn [restrict ms_mem] in HQ0, HQ1, HQ2;
        assert (EU10f : bv_unsigned (ew Ex 10) = tx)
          by (cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10);
        assert (E11f : sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb)
          by (cbn [sv_denot extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia);
              rewrite E11, unsigned_lit_small, Z.add_0_r by lia; reflexivity);
        assert (EWf := EW0 Ex ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity)
                           ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity))
      end.
      lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?mF) |- _ =>
        assert (HZ : forall i, 440 <= i < 449 -> mbyte SEGS (mrestrict (w_H W) mF) (tx + i) = Some (Z_to_bv 8 0));
        [ intros i Hi;
          rewrite (arm_mbyte_of_frame _ _ _ _ _ (tx + i) Hf ltac:(arm_nwr Usp Eu10) ltac:(lia));
          apply arm_mbyte_some; replace (tx + i) with (tx + 440 + (i - 440)) by lia;
          rewrite (Heff (i - 440) ltac:(lia)); reflexivity
        | ] end.
      arm_ret HSX HJ2 HAE E1 Hra W ly S regs.
      rewrite HIF.
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
      apply (arm_written _ _ tx sb sw T _ _ _ _ ltac:(lia) HTl EU10f E11f EWf HQ2
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ1
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ0
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HZ).
      intros i Hi N1 N2 N3. pose proof (tx_fbyte_range i Hi) as Hir.
      rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
      apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
      apply (F2 tx TX_SIZE i Htx Htx ltac:(change (req_size TX_SIZE) with 460; lia)).
      intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
    * (* 48 < sb + sw : the width is clamped to 48 - sb *)
      rewrite branch_geu_U, U_SLit, U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom E 11 sb E11), (U_atom E 12 sw E12) in Hc by lia.
      rewrite (zcanon_id 48), (zcanon_id (sb + sw)) in Hc by (unfold M64; lia).
      apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc. rename Hc into Hclamp.
      assert (EW0 : forall Ex : env, ew Ex 11 = ew E 11 -> ew Ex 12 = ew E 12 ->
                sv_denot Ex (SAlu ALU_SUB (SLit 0) (SOff 11 (-48))) =
                Z_to_bv 64 (reac_headamp_tx_arm_scene_c.arm_w sb sw)).
      { intros Ex H11' H12'.
        unfold reac_headamp_tx_arm_scene_c.arm_w. replace (48 <? sb + sw) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite denot_lit_U. f_equal.
        rewrite U_SAlu, U_SLit, U_SOff. cbn [zalu_raw]. rewrite H11', E11, unsigned_lit_small by lia.
        unfold zcanon, M64. rewrite Zmod_0_l.
        rewrite <- (Z.mod_unique (sb + -48) (2 ^ 64) (-1) (sb + -48 + 2 ^ 64)) by lia.
        replace (0 - (sb + -48 + 2 ^ 64)) with ((48 - sb) + (-1) * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      (* the call of __asan_memset (tx + 440, 0, 9) *)
      paj_run_tok RUN HS HJ SHOK EFFspan; [arm_awr Usp Eu10 Htx tx |].
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
      pmkst HS.
      prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
      prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
      prreg HS (3%bv : bv 5) Rgp2. prreg HS (4%bv : bv 5) Rtp2.
      rewrite Eu10 in Ra0.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
        assert (HspT : spZ rT = spZ regs - 48)
          by (unfold spZ at 1; rewrite Rsp2, Usp; rewrite unsigned_lit_small by lia; lia) end.
      eapply SRr_bind.
      { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
          eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W rT mT
                    _ _ _ _ _ _ _ _ _ _ _ dT _ (tx + 440) 0 9 (-48) _ HJ) end.
        - rewrite Ra0. reflexivity.
        - rewrite Ra1. reflexivity.
        - rewrite Ra2. reflexivity.
        - lia.
        - lia.
        - lia.
        - rewrite HspT. lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite Rgp2, E3. exact Hgp.
        - rewrite Rtp2, E4. exact Htp.
        - exact Rra.
        - apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
        - intros a Ha. split; [|lia].
          right; left; split; [apply arm_inFP; lia
                              | exists tx, TX_SIZE; split; [exact Htx | change (req_size TX_SIZE) with 460; lia]].
        - eapply (amem_range_of_block SEGS B LAWS); [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia].
        - eapply (range_addressable_of_block SEGS B LAWS); [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia].
        - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS);
            [exact (proj1 HJ) | exact Htx | lia | change (req_size TX_SIZE) with 460; lia | lia].
        - exact I. }
      cbv beta. intros W2 c2 _ Hpost.
      destruct Hpost as (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Ha0' & Heff & Hfrc & Hpres2).
      subst W2. subst c2.
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2' & _ & _ & _).
      destruct (al_blocks _ _ LAWS ly S W mem2 md2 tx TX_SIZE (proj1 HJ2) Htx) as (_ & _ & _ & _ & Htxpres2 & _).
      change (req_size TX_SIZE) with 460 in Htxpres2.
      jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HSX.
      lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
      { repeat (apply Forall_cons;
          [ split;
            [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
              rewrite ?Usp, ?Eu10, ?Ugot, ?Ucell in Ha;
              apply (mbyte_of_aview SEGS); apply Hfrc; unfold off_img in Htximg; lia
            | intros a Ha _; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
              rewrite ?Usp, ?Eu10, ?Ugot, ?Ucell in Ha;
              first [ lia
                    | apply (apresent_writable SEGS);
                      first [ apply (proj1 (Htxpres2 a ltac:(lia))) | apply Hpres2'; lia ] ] ]
          | ]).
        apply Forall_nil. }
      specialize (HSX HRKX). rewrite <- restrict_mkst_fx in HSX. clear HRKX HS.
      assert (HEIX : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB)))
        by (apply img_env_havoc; [exact HEI | cbv; lia]).
      assert (SHOKX : sh_ok SEGS CBx arm_SH (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)).
      { unfold sh_ok, arm_SH. apply Forall_cons; [|apply Forall_nil].
        apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 _ CBx 10 tx TX_SIZE 0 460 (proj1 HJ2) Htx).
        + unfold U, CBx. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
          rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SBz; lia). reflexivity.
        + unfold U. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
          rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
        + lia.
        + change (req_size TX_SIZE) with 460. lia. }
      clear SHOK.
      (* the three stores after the call, and the return *)
      paj_run_tok RUN HSX HJ2 SHOKX EFFspan; [arm_awr Usp Eu10 Htx tx |].
      lazymatch type of HSX with
      | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) W436) in
        let r1 := eval vm_compute in (nth 1 (ss_mem ssx) W436) in
        let r2 := eval vm_compute in (nth 2 (ss_mem ssx) W436) in
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0%nat r0 HSX ltac:(vm_compute; reflexivity)) as HQ0;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1%nat r1 HSX ltac:(vm_compute; reflexivity)) as HQ1;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 2%nat r2 HSX ltac:(vm_compute; reflexivity)) as HQ2;
        cbn [restrict ms_mem] in HQ0, HQ1, HQ2;
        assert (EU10f : bv_unsigned (ew Ex 10) = tx)
          by (cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10);
        assert (E11f : sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb)
          by (cbn [sv_denot extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia);
              rewrite E11, unsigned_lit_small, Z.add_0_r by lia; reflexivity);
        assert (EWf := EW0 Ex ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity)
                           ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity))
      end.
      lazymatch goal with Hf : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?mF) |- _ =>
        assert (HZ : forall i, 440 <= i < 449 -> mbyte SEGS (mrestrict (w_H W) mF) (tx + i) = Some (Z_to_bv 8 0));
        [ intros i Hi;
          rewrite (arm_mbyte_of_frame _ _ _ _ _ (tx + i) Hf ltac:(arm_nwr Usp Eu10) ltac:(lia));
          apply arm_mbyte_some; replace (tx + i) with (tx + 440 + (i - 440)) by lia;
          rewrite (Heff (i - 440) ltac:(lia)); reflexivity
        | ] end.
      arm_ret HSX HJ2 HAE E1 Hra W ly S regs.
      rewrite HIF.
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
      apply (arm_written _ _ tx sb sw T _ _ _ _ ltac:(lia) HTl EU10f E11f EWf HQ2
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ1
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ0
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HZ).
      intros i Hi N1 N2 N3. pose proof (tx_fbyte_range i Hi) as Hir.
      rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
      apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
      apply (F2 tx TX_SIZE i Htx Htx ltac:(change (req_size TX_SIZE) with 460; lia)).
      intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.

End H.
End F.
End D.
