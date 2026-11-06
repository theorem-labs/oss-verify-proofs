(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the head-amp table layout and the contract and walk of reac_headamp_tx_effective on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxEffective.v at a working branch 5651bf66924 (blob 388b000b518, the blob the walk was ported from), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; B's contract allows tx = 0 (the test at 0x85c18 then answers the default value) and B adds four UBSan pointer-overflow guards and one alignment guard into the trap at 0x85cc4, refuted with PaNot.U_not_ltb from tx = 0 mod 4 and tx + 287 < 2^64. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxEffective.v (source cited in the line above): the walk
   of reac_headamp_tx_effective over image B's listing and walk layer
   (lib/B/Prog), against the contract GrantBContracts.v states (walk_reac_headamp_tx_effective).
   reac_headamp_tx_effective (image B 0x85c00, 228 bytes, 57 instructions; image A 0x84e64, 184 bytes):
   for p > 2 it returns 0; for tx = 0 or ch > 47 it returns dflt p; else it returns the value byte at
   tx + 3ch + p when the set byte at tx + 144 + 3ch + p is not 0, else dflt p.
   What image B adds over image A, and where this file differs from the donor:
   - the contract allows tx = 0 (the test at 0x85c18 is C's `t &&`, not a UBSan guard). Atom 10's facts admit
     0 (lo 0, still 16-aligned), so the walk splits 0x85c18 by hand; the tx = 0 leaf reads no table byte and the
     post asks for the table only when tx <> 0 (eff_ret takes the contract's disjunction);
   - the UBSan alignment guard 0x85c28 (`andi a3,a0,3; bnez a3`) is decided inside the run from atom 10's
     16-alignment;
   - the four UBSan pointer-overflow guards `not t, x; bltu t, k` into the trap 0x85cc4 (`unimp`):
     0x85c3c (x = tx + 144, k = 3ch), 0x85c50 (x = tx + 144 + 3ch, k = p), 0x85c80 (x = tx, k = 3ch) and
     0x85c8c (x = tx + 3ch, k = p). The symbolic engine has no interval for `x XOR -1`, so the walk splits each
     and refutes the taken side (refute_povf: PaNot.U_not_ltb, then x + k < 2^64 from tx + 460 <= the
     allocation ceiling < 2^47);
   - the shadow-base cell is object 35 (image A: 32), so bcell_regionP, the GOT chunk and Ecell are re-keyed;
     image B's bounds are IMG_LO_B / IMG_TOP_B (blk_off_imgB, not the shared off_img);
   - the entry offset is AF_reac_headamp_tx_effective = 0x51c4 of image B's listing.
   The two report branches 0x85cd4 and 0x85ce0 (`__asan_report_load1`; the second is the last slot of the function
   and falls into reac_headamp_tx_arm_scene 0x85ce4) are refuted inside the run from eff_SH2: both bytes read lie in
   whole granules of the live block, so neither shadow check enters its slow block.
   The head-amp table layout is lib/Prog/HeadampLayout.v (address-free; GrantBContracts.v states every head-amp
   contract over it through ATx). This file re-exports it, with the image-free lemmas over it that image A's file
   carries (tb_range .. tx_fbyte_range, ported from lib/A/Prog/HeadampTxEffective.v:55-204, :267-277), so the image-B
   walks of the four table functions take them from here and keep image A's modules out of their Require closure. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib PaNot GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Export HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The image-free lemmas over the head-amp table layout (tb_range, tb_nth, le_from_range, le_byte_le_from,
   le4_byte_of_word, le1_byte_of_word, obj_at_fields, fields_bytes_lay, tx_obj_bytes, tx_cell_val,
   byte_of_region, lay_inside_TX, tx_fbyte_range) come from lib/Prog/HeadampLayout.v, Required Export above;
   this file carried its own copies only while that module briefly lacked them. *)

(* The value of a linear symbolic value (the sums the code builds), from its linear normal form. *)
Lemma U_lin : forall E v l c, lin_nf v = Some (l, c) -> 0 <= lin_denot E l + c < 2 ^ 64 ->
  U E v = lin_denot E l + c.
Proof. intros E v l c Hl Hr. rewrite (lin_nf_sound E v l c Hl). apply Z.mod_small. unfold M64. lia. Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head stays a section variable, as in GrantBContracts.v: no sink_head instance is in lib/B's Require
   closure. *)
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition SBz : Z := 0x7fff8000.
Definition CBx : sv := SOff 32 0.
Definition EFFspan : Z * Z := (SBz, SBz + 2 ^ 44 - 1).
(* t + ch + (ch << 1) + p: its linear form t + 3ch + p is the one the code's sums tx + 144 + 3ch + p and
   tx + 3ch + p normalise to, so both resolve to atom 33 (the cell's address) through this alias. *)
Definition XE : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SAlu ALU_SLL (SOff 11 0) (SLit 1))) (SOff 12 0).
(* atom 10 is tx: 0 (NULL) or a live block, 16-aligned either way. *)
Definition eff_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 140737479966720 4);
            (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0);
            (32%nat, mkAF SBz SBz 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ]
          [] [ (XE, SOff 33 0) ].
Definition eff_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32 ].
Definition ss_eff : sstate := mkSS AF_reac_headamp_tx_effective sr_atoms eff_regions None eff_facts.
Definition eff_SH : list shent := [].
Definition RX : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 145 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0)); YP09.mkChunk 144 (CVal 1 (SOff 34 0))].
Definition eff_SH2 : list shent := [ mkSHE 33 0 152 ].
Definition eff_extra (tx ch p : Z) (T : list byte) : list word :=
  map (Z_to_bv 64) [SBz; tx + 3 * ch + p; tb T (144 + 3 * ch + p); tb T (3 * ch + p)].
Definition EE (regs : bvmap 5 word) (tx ch p : Z) (T : list byte) : env :=
  Eimg (Ereg regs (eff_extra tx ch p T)).

Lemma denot_XE : forall E t c pv,
  ew E 10 = Z_to_bv 64 t -> ew E 11 = Z_to_bv 64 c -> ew E 12 = Z_to_bv 64 pv ->
  0 <= t -> 0 <= c < 256 -> 0 <= pv < 256 -> t + 3 * c + pv < 2 ^ 64 ->
  sv_denot E XE = Z_to_bv 64 (t + 3 * c + pv).
Proof.
  intros E t c pv Ht Hc Hpv Ht0 Hcr Hpr Hlt.
  rewrite denot_lit_U. f_equal. unfold XE.
  rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 10 t Ht ltac:(lia)), (U_atom E 11 c Hc ltac:(lia)), (U_atom E 12 pv Hpv ltac:(lia)).
  rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
  change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (t + c)) by (unfold M64; lia).
  rewrite (zcanon_id (c * 2)) by (unfold M64; lia).
  rewrite (zcanon_id (t + c + c * 2)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma eff_dflt_val : forall E (p : Z), 0 <= p < 256 -> ew E 12 = Z_to_bv 64 p ->
  sv_denot E (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 12 (-2)) (SLit 1)) (SLit 5)) = w64 (dflt p).
Proof.
  intros E p Hp E12.
  assert (HI : U E (SAlu ALU_SLTU (SOff 12 (-2)) (SLit 1))
               = Z.b2z ((p + -2) mod 18446744073709551616 <? 1)).
  { rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SOff, E12, unsigned_lit_small by lia.
    rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
    unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
    destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z]; apply Z.mod_small; lia. }
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite HI.
  rewrite U_SLit, (zcanon_id 5) by (unfold M64; lia).
  change (Z.land 5 63) with 5.
  rewrite <- (dflt_code_all p ltac:(lia)).
  unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. apply Z.mod_small.
  destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z];
    rewrite Z.shiftl_mul_pow2 by lia; lia.
Qed.

Section H.
Variable B : asyms.
Section P.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma eff_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p : Z) (T : list byte),
  afn_pre SEGS B STK_reac_headamp_tx_effective ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p ->
  0 <= ch < 256 -> 0 <= p < 256 ->
  tx mod 16 = 0 -> 0 <= tx <= 140737479966720 ->
  st_ok_pi SEGS VAL (EE regs tx ch p T) ss_eff
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx eff_SH (EE regs tx ch p T) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp Htx16 Htxr.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : STK_reac_headamp_tx_effective = 4112) by reflexivity.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
  rewrite restrict_mkst_fx.
  set (E := EE regs tx ch p T).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (eff_extra tx ch p T)) n)
    by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (tb T (144 + 3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T (3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (change 242%nat with (A_OBJ 1); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
    by (change 276%nat with (A_OBJ 35); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  pose proof (tb_range T (144 + 3 * ch + p)) as Rset. pose proof (tb_range T (3 * ch + p)) as Rval.
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_eff. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold eff_regions, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
        [cbn [sv_denot]; change (A_OBJ 35) with 276%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 CBx SBz);
        [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold eff_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
      repeat split; lia.
    + split; [|split; [exact I | ]].
      * cbn [eff_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, E10, E11, E12, E32, E34, E35, !unsigned_lit_small by (unfold SBz; lia).
        change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htxr Rset Rval Hch Hp.
        clear. unfold SBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [eff_facts f_alias alias_ok]. split; [|exact I].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply (denot_XE E tx ch p E10 E11 E12); try lia.
  - unfold sh_ok, eff_SH. apply Forall_nil.
Qed.

(* The shadow entry the walk uses once the arguments are in range: the 152 bytes from cell (ch, p) on cover both
   shadow-byte checks the code makes (set byte at +144, value byte at +0). *)
Lemma shent_of_block_at : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex CBx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS CBx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

Lemma eff_keep : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md memF mdF (tx : Z) (T : list byte),
  ajournal SEGS B STK_reac_headamp_tx_effective (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) memF) tx LAY_TX (tx_vals T).
Proof.
  intros ly S W regs mem md memF mdF tx T HJ Hin HO.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (proj2 (tx_obj_bytes SEGS (mrestrict (w_H W) memF) tx T)).
  intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HO i Hi).
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem memF (tx + i)).
  exact (F2 tx TX_SIZE i Hin Hin ltac:(change (req_size TX_SIZE) with 460; lia)
           ltac:(intros X; exact (inFP_nil _ X))).
Qed.

(* Every leaf: the contract's post from the journal, the kept registers and a0. The table is asked for only when
   tx <> 0, and then the contract's premise gives it as a live block holding T. *)
Lemma eff_ret : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
                       (regsF : bvmap 5 word) memF mdF (tx ch p : Z) (T : list byte),
  ajournal SEGS B STK_reac_headamp_tx_effective (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  (tx = 0 \/ (In (tx, TX_SIZE) (ablocks B ly S) /\ obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T))) ->
  aregs_preserved regs regsF ->
  getr regsF 10 = w64 (eff T tx ch p) ->
  tb_reac_headamp_tx_effective_post B regs ly S W mem md tx ch p T W
    (mkCfg (mkst regsF (getr regs 1) memF (seg_rom SEGS)) mdF).
Proof.
  intros ly S W regs mem md regsF memF mdF tx ch p T HJ HTX HP Hv.
  unfold tb_reac_headamp_tx_effective_post, apost_base. exists ly, S, regsF, memF, mdF.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hv|].
  intros Hnz. destruct HTX as [H0 | [Hin HO]]; [contradiction|].
  exact (eff_keep ly S W regs mem md memF mdF tx T HJ Hin HO).
Qed.

Ltac eff_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac eff_leaf_core HS HJx RETt Wt lyt St regst memt mdt txt cht pt Tt HTXt HAEt Hrat E1t Et v pf gl :=
  let R1 := fresh "R1" in let R10 := fresh "R10" in let mat := fresh "mat" in
  eff_reg HS (1%bv : bv 5) (getr regst 1)
    ltac:(cbn [sv_denot]; rewrite E1t, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) R1;
  eff_reg HS (10%bv : bv 5) v pf R10;
  eapply (RETt Wt _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat; cbn [ms_regs ms_mem]; rewrite R1, Hrat;
  eapply (eff_ret lyt St Wt regst memt mdt _ _ _ txt cht pt Tt);
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx
  | exact HTXt
  | eapply (aregs_preserved_of_st_ok SEGS _ Et _ _ regst (eff_extra txt cht pt Tt) HS);
    [exact HAEt | vm_compute; reflexivity]
  | rewrite R10; f_equal; gl ].

(* U E v for a linear v over atoms 10, 11, 12 (E10 E11 E12 : ew E n = Z_to_bv 64 _), as a sum of tx, ch, p. *)
Ltac lin_U E E10 E11 E12 v H :=
  let r := eval vm_compute in (lin_nf v) in
  lazymatch r with
  | Some (?l, ?c) =>
    assert (H : U E v = lin_denot E l + c);
    [ apply U_lin;
      [ vm_compute; reflexivity
      | cbn [lin_denot]; rewrite ?E10, ?E11, ?E12, ?unsigned_lit_small by lia; lia ]
    | cbn [lin_denot] in H; rewrite ?E10, ?E11, ?E12, ?unsigned_lit_small in H by lia ]
  end.

(* The taken side of a UBSan pointer-overflow guard `not t, x; bltu t, k` (into the trap 0x85cc4): it is taken
   iff x + k passes 2^64 - 1 (PaNot.U_not_ltb), which is false for x = tx + (at most 287) and tx + 460 below the
   allocation ceiling. *)
Ltac refute_povf Hc E E10 E11 E12 :=
  exfalso; rewrite branch_ltu_U, U_not_ltb in Hc; apply Z.ltb_lt in Hc;
  lazymatch type of Hc with
  | _ < U _ ?v + U _ ?k =>
    let Hv := fresh "Hv" in let Hk := fresh "Hk" in
    lin_U E E10 E11 E12 v Hv; lin_U E E10 E11 E12 k Hk; rewrite Hv, Hk in Hc; lia
  end.

Theorem eff_walk : tb_reac_headamp_tx_effective_spec B.
Proof.
unfold tb_reac_headamp_tx_effective_spec.
intros ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp HTl HTX.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_headamp_tx_effective = 4112) by reflexivity.
assert (Htxa : tx mod 16 = 0 /\ 0 <= tx <= 140737479966720).
{ destruct HTX as [-> | [Htx _]]; [split; [reflexivity | lia]|].
  destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & _).
  change (req_size TX_SIZE) with 460 in Htxceil. split; [exact Htx16 | lia]. }
destruct Htxa as [Htx16 Htxr].
destruct (eff_entry ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp Htx16 Htxr) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_headamp_tx_effective [] ly S W regs mem md ch0 HPRE) as HJ.
pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
pose proof (tb_range T (144 + 3 * ch + p)) as Rset. pose proof (tb_range T (3 * ch + p)) as Rval.
remember (EE regs tx ch p T) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (eff_extra tx ch p T)) n)
  by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (tb T (144 + 3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (tb T (3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (change 242%nat with (A_OBJ 1); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
  by (change 276%nat with (A_OBJ 35); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs (eff_extra tx ch p T)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HUB : U E CBx = SHADOW_OFF)
  by (unfold CBx; rewrite (U_atom E 32 SBz E32) by (unfold SBz; lia); reflexivity).
assert (HU33 : forall c, 0 <= tx + 3 * ch + p + c < 2 ^ 64 -> U E (SOff 33 c) = tx + 3 * ch + p + c).
{ intros c Hc. rewrite U_SOff, E33, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_reac_headamp_tx_effective)) with (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)).
(* The frame, the save of ra, and the test 0x85c0c of p against 2. *)
paj_run_tok RUN HS HJ SHOK EFFspan;
  [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
psrr_branch_tok RUN BR HS SHOK EFFspan.
- (* 2 >= p *)
  rewrite branch_geu_U, U_SLit, (zcanon_id 2), (U_atom E 12 p E12) in Hc by (unfold M64; lia).
  apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc. rename Hc into Hp2.
  paj_run_tok RUN HS HJ SHOK EFFspan;
    [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  (* 0x85c18 `beqz a0`: C's `t &&` *)
  psrr_branch_tok RUN BR HS SHOK EFFspan.
  + (* tx = 0 : the default, no table byte read *)
    rewrite branch_eq_U, (U_atom E 10 tx E10), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into Htx0.
    paj_run_tok RUN HS HJ SHOK EFFspan;
      [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
    eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T HTX HAE Hra E1 E (w64 (dflt p))
      ltac:(exact (eff_dflt_val E p ltac:(lia) E12))
      ltac:(symmetry; rewrite Htx0; apply (eff_t0 T ch p); lia).
  + (* tx <> 0 : the live block *)
    rewrite branch_eq_U, (U_atom E 10 tx E10), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc. rename Hc into Htxnz.
    pose proof HTX as HTX'. destruct HTX' as [Htx0 | [Htx HTo]]; [contradiction|].
    destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & Htxpres & _).
    change (req_size TX_SIZE) with 460 in Htxceil.
    pose proof (blk_off_imgB B ly S W mem md tx TX_SIZE HAR Htx) as Htximg.
    change (req_size TX_SIZE) with 460 in Htximg.
    rewrite IMG_LO_B_val, IMG_TOP_B_val in Htximg.
    paj_run_tok RUN HS HJ SHOK EFFspan;
      [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
    psrr_branch_tok RUN BR HS SHOK EFFspan.
    * (* 47 < ch : the default *)
      rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
      apply Z.ltb_lt in Hc. rename Hc into Hch47.
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T HTX HAE Hra E1 E (w64 (dflt p))
        ltac:(exact (eff_dflt_val E p ltac:(lia) E12))
        ltac:(symmetry; apply (eff_ch T tx ch p ltac:(lia) ltac:(lia))).
    * (* ch <= 47 : the cell *)
      rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
      apply Z.ltb_ge in Hc. rename Hc into Hch47.
      (* the address of the cell is inside the block *)
      assert (HF33 : afact_ok E 33 (mkAF 4096 140737479966720 0)).
      { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
        rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
      apply (st_ok_pi_add_fact E _ _ 33 _ HS) in HF33. clear HS. rename HF33 into HS.
      lazymatch type of HS with
      | st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
        assert (HO : obj_at SEGS (mrestrict (w_H W) (ms_mem msx)) tx LAY_TX (tx_vals T))
          by (exact (eff_keep ly S W regs mem md (ms_mem msx) _ tx T HJ Htx HTo));
        assert (HR : region_ok SEGS E (ms_mem (restrict Hh msx)) RX);
        [ cbn [restrict ms_mem];
          unfold RX, region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite E33, unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          apply Forall_cons;
          [ apply (chunk_ok_val SEGS E _ (tx + 3 * ch + p) 0 1 (SOff 35 0) (tb T (3 * ch + p)));
            [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
            replace (tx + 3 * ch + p + 0) with (tx + (3 * ch + p)) by lia;
            exact (tx_cell_val SEGS _ tx T (3 * ch + p) ltac:(lia) HO)
          | apply Forall_cons;
            [ apply (chunk_ok_val SEGS E _ (tx + 3 * ch + p) 144 1 (SOff 34 0) (tb T (144 + 3 * ch + p)));
              [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
              replace (tx + 3 * ch + p + 144) with (tx + (144 + 3 * ch + p)) by lia;
              exact (tx_cell_val SEGS _ tx T (144 + 3 * ch + p) ltac:(lia) HO)
            | apply Forall_nil ] ]
        | pose proof (st_ok_pi_add_region E ssx (restrict Hh msx) RX HS
                        ltac:(vm_compute; reflexivity) HR
                        ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
                                let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
                              cbn [all_disjoint]; unfold extent_disjoint, RX;
                              cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
                              rewrite ?E33, ?Egot, ?Ecell, ?E2;
                              rewrite !unsigned_lit_small by
                                (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 35)); lia);
                              change (bv_unsigned (getr regs 2)) with (spZ regs);
                              revert Hslo Hceil Htxceil Htx4096 Htximg HcellR HgotR Hch47 Hp2 Hch Hp C1 C3 WS;
                              clear; intros;
                              repeat match goal with |- _ /\ _ => split end;
                              first [exact I | lia])) as HS2;
          clear HS HO HR; rename HS2 into HS ]
      end.
      lazymatch type of HS with
      | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        assert (SHOK2 : sh_ok SEGS CBx eff_SH2 E (mrestrict (w_H W) (ms_mem msx)));
        [ unfold sh_ok, eff_SH2; apply Forall_cons;
          [ eapply (shent_of_block_at ly S W (ms_mem msx) _ E 33 (tx + 3 * ch + p) tx TX_SIZE 0 152
                      (proj1 HJ) Htx HUB);
            [rewrite (HU33 0) by lia; lia | lia | lia | change (req_size TX_SIZE) with 460; lia]
          | apply Forall_nil ]
        | ] end.
      clear SHOK. rename SHOK2 into SHOK.
      (* the alignment guard 0x85c28 (decided), up to the guard 0x85c3c: tx + 144 + 3ch *)
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      psrr_branch_tok RUN BR HS SHOK EFFspan; [refute_povf Hc E E10 E11 E12 | clear Hc].
      (* the guard 0x85c50: tx + 144 + 3ch + p *)
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      psrr_branch_tok RUN BR HS SHOK EFFspan; [refute_povf Hc E E10 E11 E12 | clear Hc].
      (* the shadow check of the set byte (whole granule), its load, and the test 0x85c78 *)
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      psrr_branch_tok RUN BR HS SHOK EFFspan.
      -- (* the cell was never set : the default *)
        rewrite branch_eq_U, (U_atom E 34 (tb T (144 + 3 * ch + p)) E34), U_lit in Hc by lia.
        apply Z.eqb_eq in Hc. rename Hc into Hset.
        paj_run_tok RUN HS HJ SHOK EFFspan;
          [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
        eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T HTX HAE Hra E1 E (w64 (dflt p))
          ltac:(exact (eff_dflt_val E p ltac:(lia) E12))
          ltac:(rewrite (eff_cell T tx ch p ltac:(lia) ltac:(lia) ltac:(lia));
                rewrite (proj2 (Z.eqb_eq (tb T (144 + 3 * ch + p)) 0) Hset); reflexivity).
      -- (* the cell was set : its value *)
        rewrite branch_eq_U, (U_atom E 34 (tb T (144 + 3 * ch + p)) E34), U_lit in Hc by lia.
        apply Z.eqb_neq in Hc. rename Hc into Hset.
        (* the guard 0x85c80: tx + 3ch *)
        paj_run_tok RUN HS HJ SHOK EFFspan;
          [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
        psrr_branch_tok RUN BR HS SHOK EFFspan; [refute_povf Hc E E10 E11 E12 | clear Hc].
        (* the guard 0x85c8c: tx + 3ch + p *)
        paj_run_tok RUN HS HJ SHOK EFFspan;
          [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
        psrr_branch_tok RUN BR HS SHOK EFFspan; [refute_povf Hc E E10 E11 E12 | clear Hc].
        (* the shadow check of the value byte (whole granule), its load, and the return *)
        paj_run_tok RUN HS HJ SHOK EFFspan;
          [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
        eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T HTX HAE Hra E1 E (w64 (tb T (3 * ch + p)))
          ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(rewrite (eff_cell T tx ch p ltac:(lia) ltac:(lia) ltac:(lia));
                rewrite (proj2 (Z.eqb_neq (tb T (144 + 3 * ch + p)) 0) Hset); reflexivity).
- (* p > 2 : zero *)
  rewrite branch_geu_U, U_SLit, (zcanon_id 2), (U_atom E 12 p E12) in Hc by (unfold M64; lia).
  apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc. rename Hc into Hp2.
  paj_run_tok RUN HS HJ SHOK EFFspan;
    [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T HTX HAE Hra E1 E (w64 0) ltac:(cbn [sv_denot]; reflexivity)
    ltac:(symmetry; apply (eff_p3 T tx ch p ltac:(lia))).
Qed.

End P.

Theorem pb_reac_headamp_tx_effective : walk_reac_headamp_tx_effective B.
Proof.
unfold walk_reac_headamp_tx_effective, hyps_reac_headamp_tx_effective, RT_LAWS, RT_PALIB.
intros (LAWS & TL). exact (eff_walk LAWS TL).
Qed.

End H.
End F.
End D.
