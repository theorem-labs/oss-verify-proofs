(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxSet.v at a working branch 5651bf66924 (blob 4381d874223; the walk was ported from blob 706b07923f6, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; B adds eight UBSan guards into the trap at 0x85bac (null 0x85ad0, alignment 0x85ad8, six pointer-overflow), refuted for a live 4-aligned block with tx + 431 < 2^64. *)
(* reac_headamp_tx_set (image B 0x85a90, 88 instructions) on the build with the memory and undefined-behaviour
   checks: the walk of its machine code against the contract tb_reac_headamp_tx_set_spec of GrantBContracts.v.
   The branch tree is image A's (refusals ch > 47, p >= 3, p = 2 and v >= 56, p < 2 and v >= 2; acceptances
   p < 2 and v <= 1, p = 2 and v <= 55). Image B adds, on the acceptance paths only, eight guards into the trap at
   0x85bac: tx = 0 (0x85ad0), tx mod 4 <> 0 (0x85ad8) and six checks that a pointer sum does not pass 2^64
   (0x85ae8 ~tx < 3ch, 0x85afc ~(tx+3ch) < p, 0x85b20 ~(tx+144) < 3ch, 0x85b2c ~(tx+144+3ch) < p,
   0x85b54 ~(tx+288) < 3ch, 0x85b60 ~(tx+288+3ch) < p). Each is false for the live 460-byte block at tx
   (4096 <= tx, tx mod 16 = 0, tx + 460 < 2^47). The four checked stores (0x85b1c, 0x85b50, 0x85b80 one byte;
   0x85b98 four bytes) lie in whole granules of the block, so the shadow token engine absorbs the branches into
   the error-path calls 0x85bbc / 0x85bcc / 0x85bdc (store1) and 0x85bec (store4). The acceptance code from the
   null check on is the same on both acceptance paths; the tactic set_accept_tail states it once. *)
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
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC1g PaNot.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
(* The address-free layout of the 460-byte table (TX_SIZE, LAY_TX, tx_vals): lib/Prog/HeadampLayout.v, the file the
   contract names it through (alias ATx there, HL here). Required, never imported. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel reac_headamp_tx_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module HL := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.

Ltac tx_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac tx_dec :=
  repeat match goal with
  | |- context [ ((?k <=? ?n)%nat && (?n <? ?m)%nat)%bool ] =>
      first [ replace ((k <=? n)%nat && (n <? m)%nat)%bool with true by
                (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia)
            | replace ((k <=? n)%nat && (n <? m)%nat)%bool with false by
                (symmetry; apply Bool.not_true_iff_false; let Hb := fresh "Hb" in intros Hb;
                 apply andb_true_iff in Hb; destruct Hb as [Hb1 Hb2];
                 apply Nat.leb_le in Hb1; apply Nat.ltb_lt in Hb2; lia) ]
  end.

(* The value U of a symbolic sum, product or shift whose parts do not wrap, in the hypothesis Hc: every U is
   unfolded to its parts, the atoms are replaced by their values (the Eu equations in the context), and each
   zcanon is dropped from the innermost one out, once lia shows its argument is below 2^64. *)
Ltac uev_in Hc :=
  repeat first [ rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SLit in Hc | rewrite U_SOff in Hc ];
  cbn [zalu_raw zmd_raw] in Hc;
  repeat match goal with Eu : bv_unsigned (ew _ _) = _ |- _ => rewrite Eu in Hc end;
  repeat first
    [ match type of Hc with
      | context [zcanon ?x] =>
          lazymatch x with
          | context [zcanon _] => fail
          | _ => rewrite (zcanon_id x) in Hc by (unfold M64; lia)
          end
      end
    | progress change (Z.land 1 63) with 1 in Hc
    | rewrite Z.shiftl_mul_pow2 in Hc by lia
    | progress change (2 ^ 1) with 2 in Hc
    | progress change (zcanon (-1)) with (2 ^ 64 - 1) in Hc
    | rewrite lxor_allones in Hc by lia ].

(* A taken branch into the trap at 0x85bac, refuted. The six pointer-overflow guards `not t, x; bltu t, k` are
   taken iff x + k passes 2^64 - 1 (PaNot.U_not_ltb); x and k are sums of tx, 3 * ch, p and 144 / 288, far below
   2^64. The null guard (beqz a0) needs 4096 <= tx; the alignment guard (andi a4, a0, 3; bnez a4) tx mod 16 = 0. *)
Ltac refute_trap :=
  lazymatch goal with
  | Hc : branch_taken BC_LTU _ _ = true |- _ =>
      rewrite branch_ltu_U in Hc;
      first [ rewrite U_not_ltb in Hc; apply Z.ltb_lt in Hc; uev_in Hc; lia
            | apply Z.ltb_lt in Hc; uev_in Hc; lia ]
  | Hc : branch_taken BC_EQ _ _ = true |- _ =>
      rewrite branch_eq_U in Hc; apply Z.eqb_eq in Hc; uev_in Hc; lia
  | Hc : branch_taken BC_NE _ _ = true |- _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc; uev_in Hc;
      first [ lia
            | change 3 with (Z.ones 2) in Hc; rewrite Z.land_ones in Hc by lia; lia ]
  end.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition SBz : Z := 0x7fff8000.
(* The shadow base: atom 32 of the environment, the value the code loads from the cell (object 35). *)
Definition CBx : sv := SOff 32 0.
Definition SETspan : Z * Z := (SBz, SBz + 2 ^ 44 - 1).
(* tx + ch + (ch << 1) + p, the address image A's code builds for cell (ch, p); the alias names it atom 33. Image B
   builds (tx + ((ch << 1) + ch)) + p, the same linear form. *)
Definition XE : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SAlu ALU_SLL (SOff 11 0) (SLit 1))) (SOff 12 0).
Definition set_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0); (13%nat, mkAF 0 255 0);
            (32%nat, mkAF SBz SBz 0) ] [] [ (XE, SOff 33 0) ].
Definition set_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32 ].
Definition ss_set : sstate := mkSS AF_reac_headamp_tx_set sr_atoms set_regions None set_facts.
Definition SR0 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition SR144 : YP09.region := YP09.mkRegion (Some 33%nat) 144 145 144 145 [].
Definition SR288 : YP09.region := YP09.mkRegion (Some 33%nat) 288 289 288 289 [].
Definition SR432 : YP09.region := YP09.mkRegion (Some 10%nat) 432 436 432 436 [].
Definition set_SH : list shent := [ mkSHE 33 0 296; mkSHE 10 0 460 ].
Definition EST (regs : bvmap 5 word) (tx ch p : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p])).

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

Section H.
Variable B : asyms.

(* The bytes a call keeps: every byte of the block outside its footprint. *)
Lemma tx_keep_fp : forall STK FP ly S (W : world SEGS) (regs : bvmap 5 word) mem md memF mdF tx T,
  ajournal SEGS B STK (spZ regs) FP ly S W mem md [] ly S W memF mdF 0 ->
  In (tx, HL.TX_SIZE) (ablocks B ly S) ->
  obj_at SEGS (mrestrict (w_H W) mem) tx HL.LAY_TX (HL.tx_vals T) ->
  (forall i, 0 <= i < 460 -> ~ inFP FP (tx + i)) ->
  obj_at SEGS (mrestrict (w_H W) memF) tx HL.LAY_TX (HL.tx_vals T).
Proof.
  intros STK FP ly S W regs mem md memF mdF tx T HJ Hin HO Hfp.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (proj2 (HL.tx_obj_bytes SEGS (mrestrict (w_H W) memF) tx T)).
  intros i Hi. pose proof (HL.tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (HL.tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HO i Hi).
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem memF (tx + i)).
  apply (F2 tx HL.TX_SIZE i Hin Hin ltac:(change (req_size HL.TX_SIZE) with 460; lia)).
  apply Hfp. lia.
Qed.

Definition SR0f : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 13 0))].
Definition SR144f : YP09.region := YP09.mkRegion (Some 33%nat) 144 145 144 145 [YP09.mkChunk 144 (CVal 1 (SLit 1))].
Definition SR288f : YP09.region := YP09.mkRegion (Some 33%nat) 288 289 288 289 [YP09.mkChunk 288 (CVal 1 (SLit 1))].
Definition SR432f : YP09.region := YP09.mkRegion (Some 10%nat) 432 436 432 436 [YP09.mkChunk 432 (CVal 4 (SLit 1))].

Lemma set_written : forall (Ex : env) m (tx ch p v : Z) (T : list byte),
  0 <= ch < 48 -> 0 <= p < 3 -> 0 <= v < 256 -> length T = 460%nat ->
  bv_unsigned (ew Ex 33) = tx + 3 * ch + p ->
  bv_unsigned (ew Ex 10) = tx ->
  sv_denot Ex (SOff 13 0) = Z_to_bv 64 v ->
  region_ok SEGS Ex m SR0f -> region_ok SEGS Ex m SR144f ->
  region_ok SEGS Ex m SR288f -> region_ok SEGS Ex m SR432f ->
  (forall i, HL.tx_fbyte i = true -> i <> 3 * ch + p -> i <> 144 + 3 * ch + p -> i <> 288 + 3 * ch + p ->
     ~ (432 <= i < 436) -> mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  obj_at SEGS m tx HL.LAY_TX (HL.tx_vals (reac_headamp_tx_set_c.set_T T ch p v)).
Proof.
  intros Ex m tx ch p v T Hch Hp Hv HTl E33 E10 E13 HR0 HR144 HR288 HR432 Hkeep.
  assert (L1 : length (Mem.upd_bytes T (Z.to_nat (3 * ch + p)) (Mem.le1 (Z_to_bv 64 v))) = 460%nat)
    by (rewrite Mem.upd_bytes_length; [exact HTl | rewrite Mem.length_le1; lia]).
  assert (L2 : length (Mem.upd_bytes (Mem.upd_bytes T (Z.to_nat (3 * ch + p)) (Mem.le1 (Z_to_bv 64 v)))
                         (Z.to_nat (144 + 3 * ch + p)) (Mem.le1 (Z_to_bv 64 1))) = 460%nat)
    by (rewrite Mem.upd_bytes_length; [exact L1 | rewrite Mem.length_le1; lia]).
  assert (L3 : length (Mem.upd_bytes (Mem.upd_bytes (Mem.upd_bytes T (Z.to_nat (3 * ch + p)) (Mem.le1 (Z_to_bv 64 v)))
                         (Z.to_nat (144 + 3 * ch + p)) (Mem.le1 (Z_to_bv 64 1)))
                         (Z.to_nat (288 + 3 * ch + p)) (Mem.le1 (Z_to_bv 64 1))) = 460%nat)
    by (rewrite Mem.upd_bytes_length; [exact L2 | rewrite Mem.length_le1; lia]).
  apply (proj2 (HL.tx_obj_bytes SEGS m tx _)).
  intros i Hi. pose proof (HL.tx_fbyte_range i Hi) as Hir.
  unfold reac_headamp_tx_set_c.set_T.
  rewrite (SegSetModel.nth_upd_bytes _ _ 432 (Z.to_nat i)) by (rewrite Mem.length_le4, L3; lia).
  rewrite Mem.length_le4.
  rewrite (SegSetModel.nth_upd_bytes _ _ (Z.to_nat (288 + 3 * ch + p)) (Z.to_nat i)) by (rewrite Mem.length_le1, L2; lia).
  rewrite Mem.length_le1.
  rewrite (SegSetModel.nth_upd_bytes _ _ (Z.to_nat (144 + 3 * ch + p)) (Z.to_nat i)) by (rewrite Mem.length_le1, L1; lia).
  rewrite Mem.length_le1.
  rewrite (SegSetModel.nth_upd_bytes _ _ (Z.to_nat (3 * ch + p)) (Z.to_nat i)) by (rewrite Mem.length_le1, HTl; lia).
  rewrite Mem.length_le1.
  destruct (Z.eq_dec i (3 * ch + p)) as [Heq | N1].
  { subst i. tx_dec. cbv beta iota. rewrite Nat.sub_diag.
    rewrite HL.le1_byte_of_word. rewrite <- E13.
    replace (tx + (3 * ch + p)) with (bv_unsigned (ew Ex 33) + 0 + 0) by lia.
    apply (HL.byte_of_region SEGS Ex m 33%nat _ _ 0 1 0 1 0 1 (SOff 13 0) 0 HR0 eq_refl);
      [left; reflexivity | cbn; lia]. }
  destruct (Z.eq_dec i (144 + 3 * ch + p)) as [Heq | N2].
  { subst i. tx_dec. cbv beta iota. rewrite Nat.sub_diag.
    rewrite HL.le1_byte_of_word.
    replace (tx + (144 + 3 * ch + p)) with (bv_unsigned (ew Ex 33) + 144 + 0) by lia.
    rewrite (HL.byte_of_region SEGS Ex m 33%nat _ _ 144 145 144 145 144 1 (SLit 1) 0 HR144 eq_refl
               ltac:(left; reflexivity) ltac:(cbn; lia)).
    try (f_equal; cbn [sv_denot]; reflexivity). }
  destruct (Z.eq_dec i (288 + 3 * ch + p)) as [Heq | N3].
  { subst i. tx_dec. cbv beta iota. rewrite Nat.sub_diag.
    rewrite HL.le1_byte_of_word.
    replace (tx + (288 + 3 * ch + p)) with (bv_unsigned (ew Ex 33) + 288 + 0) by lia.
    rewrite (HL.byte_of_region SEGS Ex m 33%nat _ _ 288 289 288 289 288 1 (SLit 1) 0 HR288 eq_refl
               ltac:(left; reflexivity) ltac:(cbn; lia)).
    try (f_equal; cbn [sv_denot]; reflexivity). }
  destruct (Z_le_dec 432 i) as [Hge | Hlt].
  { destruct (Z_lt_dec i 436) as [Hlt4 | Hge4].
    - tx_dec. cbv beta iota.
      rewrite (HL.le4_byte_of_word (Z_to_bv 64 1) (Z.to_nat i - 432) ltac:(lia)).
      replace (Z.of_nat (Z.to_nat i - 432)) with (i - 432) by lia.
      replace (tx + i) with (bv_unsigned (ew Ex 10) + 432 + (i - 432)) by lia.
      rewrite (HL.byte_of_region SEGS Ex m 10%nat _ _ 432 436 432 436 432 4 (SLit 1) (i - 432) HR432 eq_refl
                 ltac:(left; reflexivity) ltac:(cbn; lia)).
      try (f_equal; cbn [sv_denot]; reflexivity).
    - tx_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia]. }
  tx_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia].
Qed.

Section L.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma tx_shent : forall ly S (W : world SEGS) mem md (Ex : env) (tx : Z) (n : nat) (q lo hi : Z),
  AR SEGS B ly S W mem md -> In (tx, HL.TX_SIZE) (ablocks B ly S) ->
  U Ex CBx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  tx <= q + lo -> lo <= hi -> q + hi <= tx + req_size HL.TX_SIZE ->
  shent_ok SEGS CBx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex tx n q lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md tx HL.TX_SIZE HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md tx HL.TX_SIZE (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

Lemma set_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p v : Z),
  afn_pre SEGS B STK_reac_headamp_tx_set ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p -> getr regs 13 = w64 v ->
  0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  In (tx, HL.TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (EST regs tx ch p) ss_set
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_set)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx (@nil shent) (EST regs tx ch p) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx ch p v HPRE H10 H11 H12 H13 Hch Hp Hv Htx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : STK_reac_headamp_tx_set = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx HL.TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size HL.TX_SIZE) with 460 in *.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
  rewrite restrict_mkst_fx.
  set (E := EST regs tx ch p).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p])) n)
    by (intros n Hn; subst E; unfold EST; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; unfold EST; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35)))
    by (subst E; unfold EST; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some n) = z).
  { intros n z Hn Hz. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hz. }
  split.
  - unfold ss_set. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold set_regions, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
        [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SBz);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold set_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
      repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [set_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, E10, E11, E12, E13, E32, !unsigned_lit_small by (unfold SBz; lia).
        change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil Hch Hp Hv.
        clear. unfold SBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [set_facts f_alias alias_ok]. split; [|exact I].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply (denot_XE E tx ch p E10 E11 E12); try lia.
  - apply Forall_nil.
Qed.

Ltac tx_disj E33v E10v Egotv Ecellv Uspv :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  try unfold SR0; try unfold SR144; try unfold SR288; try unfold SR432;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?E33v, ?E10v, ?Egotv, ?Ecellv;
  rewrite ?unsigned_lit_small by
    (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 35)); lia);
  rewrite ?Uspv;
  repeat match goal with |- _ /\ _ => split end;
  first [exact I | lia].

Ltac tx_addregion HS R E33v E10v Hpresv Egotv Ecellv Uspv txv chv pv :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let HR := fresh "HR" in let HS2 := fresh "HS" in
    assert (HR : region_ok SEGS Ex (ms_mem (restrict Hh msx)) R)
      by (cbn [restrict ms_mem]; unfold R, region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite ?E33v, ?E10v; rewrite ?unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS);
            first [ apply (proj1 (Hpresv (txv + 3 * chv + pv + o) ltac:(lia)))
                  | apply (proj1 (Hpresv (txv + o) ltac:(lia)))
                  | match goal with |- ?g => idtac "REGFAIL" g end ]
          | apply Forall_nil ]);
    pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) R HS
                  ltac:(vm_compute; reflexivity) HR ltac:(tx_disj E33v E10v Egotv Ecellv Uspv)) as HS2;
    clear HS HR; rename HS2 into HS
  end.

Ltac tx_awr_plain Uspv :=
  awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Uspv.

Ltac tx_awr_accept Uspv Htxv E33v E10v HFPv txv chv pv :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  unfold thd_set_fp; rewrite HFPv;
  eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat txv HL.TX_SIZE);
    [reflexivity | exact E10v | exact Htxv | cbn [YP09.r_wlo]; lia
     | cbn [YP09.r_whi]; change (req_size HL.TX_SIZE) with 460; lia
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exists (txv + 432, txv + 436);
       split; [right; right; right; left; reflexivity | cbn [fst snd]; lia]
     | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (txv + 3 * chv + pv));
    [reflexivity | exact E33v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
       [ exists (txv + 288 + 3 * chv + pv, txv + 289 + 3 * chv + pv);
         split; [right; right; left; reflexivity | cbn [fst snd]; lia]
       | exists txv, HL.TX_SIZE; split; [exact Htxv | change (req_size HL.TX_SIZE) with 460; lia] ]
     | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (txv + 3 * chv + pv));
    [reflexivity | exact E33v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
       [ exists (txv + 144 + 3 * chv + pv, txv + 145 + 3 * chv + pv);
         split; [right; left; reflexivity | cbn [fst snd]; lia]
       | exists txv, HL.TX_SIZE; split; [exact Htxv | change (req_size HL.TX_SIZE) with 460; lia] ]
     | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (txv + 3 * chv + pv));
    [reflexivity | exact E33v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
       [ exists (txv + 3 * chv + pv, txv + 3 * chv + pv + 1);
         split; [left; reflexivity | cbn [fst snd]; lia]
       | exists txv, HL.TX_SIZE; split; [exact Htxv | change (req_size HL.TX_SIZE) with 460; lia] ]
     | ];
  eapply awr_ok_cons_stack; [reflexivity | exact Uspv | azlit_tac | azlit_tac |];
  apply awr_ok_cons_ro; [azlit_tac|];
  apply awr_ok_cons_ro; [azlit_tac|];
  apply awr_ok_nil.

(* A refusal leaf: a0 = -1, nothing of the table written. *)
Ltac set_refuse_leaf HS HJ E HAE HFP E1 Hra Htx HTo regs ly S W mem md tx ch p v T :=
  let R1 := fresh "R1" in let R10 := fresh "R10" in
  tx_reg HS (1%bv : bv 5) (getr regs 1)
    ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) R1;
  tx_reg HS (10%bv : bv 5) (w64 (-1)) ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; vm_compute; reflexivity) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros ?; cbn [ms_regs ms_mem]; rewrite R1, Hra;
  unfold tb_reac_headamp_tx_set_post, apost_base; cbv beta;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
    split; [reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p]) HS);
            [exact HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    split; [rewrite HFP; exact R10 | unfold thd_set_T; rewrite HFP]
  end;
  apply (tx_keep_fp STK_reac_headamp_tx_set (thd_set_fp tx ch p v) ly S W regs mem md _ _ tx T HJ Htx HTo);
  let i := fresh "i" in let Hi := fresh "Hi" in let r := fresh "r" in let Hin := fresh "Hin" in
  let Hr := fresh "Hr" in
  intros i Hi; unfold thd_set_fp; rewrite HFP; intros (r & Hin & Hr); destruct Hin.

(* An acceptance: from the null check at 0x85ad0 to the return. The cell's atom 33 and the four regions the stores
   fill are added; each run stops at one of the six pointer-overflow guards, whose taken side (the trap) is
   refuted; the last run returns 0 with the three cell bytes and the active flag stored. *)
Ltac set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p :=
  paj_run_tok RUN HS HJ SHOK SETspan; [ tx_awr_accept Usp Htx Eu33 Eu10 HFP tx ch p | ].
Ltac set_guard HS SHOK := psrr_branch_tok RUN BR HS SHOK SETspan; [ refute_trap | ].
Ltac set_accept_tail E HS HJ SHOK ly S W mem md regs tx ch p v T Htx HTo HTl HFP HUB HAE
                      E1 E10 E13 E33 Eu10 Eu33 Egot Ecell Usp Hra :=
  let HF33 := fresh "HF33" in let Hpres := fresh "Hpres" in let SHOK2 := fresh "SHOK" in
  let HQ432 := fresh "HQ432" in let HQ288 := fresh "HQ288" in let HQ144 := fresh "HQ144" in
  let HQ0 := fresh "HQ0" in let R1 := fresh "R1" in let R10 := fresh "R10" in let F2 := fresh "F2" in
  assert (HF33 : afact_ok E 33 (mkAF 4096 140737479966720 0))
    by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
        rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia);
  apply (st_ok_pi_add_fact E _ _ 33 _ HS) in HF33; clear HS; rename HF33 into HS;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    destruct (al_blocks _ _ LAWS ly S W (ms_mem msx) _ tx HL.TX_SIZE (proj1 HJ) Htx)
      as (_ & _ & _ & _ & Hpres & _);
    change (req_size HL.TX_SIZE) with 460 in Hpres
  end;
  tx_addregion HS SR0 E33 E10 Hpres Egot Ecell Usp tx ch p;
  tx_addregion HS SR144 E33 E10 Hpres Egot Ecell Usp tx ch p;
  tx_addregion HS SR288 E33 E10 Hpres Egot Ecell Usp tx ch p;
  tx_addregion HS SR432 E33 E10 Hpres Egot Ecell Usp tx ch p;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOK2 : sh_ok SEGS CBx set_SH E (mrestrict (w_H W) (ms_mem msx)));
    [ unfold sh_ok, set_SH; apply Forall_cons;
      [ apply (tx_shent ly S W (ms_mem msx) _ E tx 33%nat (tx + 3 * ch + p) 0 296 (proj1 HJ) Htx HUB
                 ltac:(rewrite U_SOff, E33, unsigned_lit_small by lia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia)
                 ltac:(lia) ltac:(lia) ltac:(change (req_size HL.TX_SIZE) with 460; lia))
      | apply Forall_cons;
        [ apply (tx_shent ly S W (ms_mem msx) _ E tx 10%nat tx 0 460 (proj1 HJ) Htx HUB
                   ltac:(rewrite U_SOff, E10, unsigned_lit_small by lia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia)
                   ltac:(lia) ltac:(lia) ltac:(change (req_size HL.TX_SIZE) with 460; lia))
        | apply Forall_nil ] ]
    | ] end;
  clear SHOK; rename SHOK2 into SHOK;
  set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  set_guard HS SHOK; set_run_accept HS HJ SHOK Usp Htx Eu33 Eu10 HFP tx ch p;
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0%nat SR432f HS
                  ltac:(vm_compute; reflexivity)) as HQ432;
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 1%nat SR288f HS
                  ltac:(vm_compute; reflexivity)) as HQ288;
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 2%nat SR144f HS
                  ltac:(vm_compute; reflexivity)) as HQ144;
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3%nat SR0f HS
                  ltac:(vm_compute; reflexivity)) as HQ0
  end;
  cbn [restrict ms_mem] in HQ432, HQ288, HQ144, HQ0;
  tx_reg HS (1%bv : bv 5) (getr regs 1)
    ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) R1;
  tx_reg HS (10%bv : bv 5) (w64 0) ltac:(cbn [sv_denot]; reflexivity) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros ?; cbn [ms_regs ms_mem]; rewrite R1, Hra;
  unfold tb_reac_headamp_tx_set_post, apost_base; cbv beta;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
    split; [reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p]) HS);
            [exact HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    split; [rewrite HFP; exact R10 | unfold thd_set_T; rewrite HFP]
  end;
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
  apply (set_written E _ tx ch p v T ltac:(lia) ltac:(lia) ltac:(lia) HTl
           ltac:(rewrite E33; apply unsigned_lit_small; lia)
           ltac:(rewrite E10; apply unsigned_lit_small; lia)
           ltac:(cbn [sv_denot]; rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
           HQ0 HQ144 HQ288 HQ432);
  let i := fresh "i" in let Hi := fresh "Hi" in let Hir := fresh "Hir" in
  intros i Hi ? ? ? ?; pose proof (HL.tx_fbyte_range i Hi) as Hir;
  rewrite <- (proj1 (HL.tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi);
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i));
  apply (F2 tx HL.TX_SIZE i Htx Htx ltac:(change (req_size HL.TX_SIZE) with 460; lia));
  unfold thd_set_fp; rewrite HFP;
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  cbn [In] in Hin; destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr; lia.

Theorem pb_core : tb_reac_headamp_tx_set_spec B.
Proof.
unfold tb_reac_headamp_tx_set_spec.
intros ly S W regs mem md ch0 tx ch p v T HPRE H10 H11 H12 H13 Hch Hp Hv Htx HTl HTo.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (set_entry ly S W regs mem md ch0 tx ch p v HPRE H10 H11 H12 H13 Hch Hp Hv Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_headamp_tx_set (thd_set_fp tx ch p v) ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_headamp_tx_set = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx HL.TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size HL.TX_SIZE) with 460 in *.
pose proof (blk_off_imgB B ly S W mem md tx HL.TX_SIZE HAR Htx) as Htximg.
change (req_size HL.TX_SIZE) with 460 in Htximg. rewrite IMG_LO_B_val, IMG_TOP_B_val in Htximg.
pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
remember (EST regs tx ch p) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EST; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p])) n)
  by (intros n Hn; subst E; unfold EST; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (change 242%nat with (A_OBJ 1); subst E; unfold EST; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
  by (change 276%nat with (A_OBJ 35); subst E; unfold EST; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SBz; tx + 3 * ch + p])) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Eu11 : bv_unsigned (ew E 11) = ch) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Eu12 : bv_unsigned (ew E 12) = p) by (rewrite E12; apply unsigned_lit_small; lia).
assert (Eu33 : bv_unsigned (ew E 33) = tx + 3 * ch + p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HUB : U E CBx = SHADOW_OFF)
  by (unfold CBx; rewrite (U_atom E 32 SBz E32) by (unfold SBz; lia); reflexivity).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_reac_headamp_tx_set)) with (Z_to_bv 64 (BASE + AF_reac_headamp_tx_set)).
paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
psrr_branch_tok RUN BR HS SHOK SETspan.
- (* 47 < ch : refused *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
  apply Z.ltb_lt in Hc.
  assert (HFP : ((ch <? 48) && legalb p v)%bool = false)
    by (apply andb_false_iff; left; apply Z.ltb_ge; lia).
  paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
  set_refuse_leaf HS HJ E HAE HFP E1 Hra Htx HTo regs ly S W mem md tx ch p v T.
- (* ch <= 47 *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
  apply Z.ltb_ge in Hc. rename Hc into Hch47.
  paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
  psrr_branch_tok RUN BR HS SHOK SETspan.
  + (* 2 <= p *)
    rewrite branch_geu_U, (U_atom E 12 p E12), U_SLit, (zcanon_id 2) in Hc by (unfold M64; lia).
    apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc. rename Hc into Hp2.
    paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
    psrr_branch_tok RUN BR HS SHOK SETspan.
    * (* p <> 2 : refused *)
      rewrite branch_ne_U, (U_atom E 12 p E12), U_SLit, (zcanon_id 2) in Hc by (unfold M64; lia).
      apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc.
      assert (HFP : ((ch <? 48) && legalb p v)%bool = false)
        by (apply andb_false_iff; right; unfold legalb; apply orb_false_iff; split;
            apply andb_false_iff; [left; apply Z.ltb_ge; lia | left; apply Z.eqb_neq; lia]).
      paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
      set_refuse_leaf HS HJ E HAE HFP E1 Hra Htx HTo regs ly S W mem md tx ch p v T.
    * (* p = 2 *)
      rewrite branch_ne_U, (U_atom E 12 p E12), U_SLit, (zcanon_id 2) in Hc by (unfold M64; lia).
      apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc. rename Hc into Hpeq.
      paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
      psrr_branch_tok RUN BR HS SHOK SETspan.
      -- (* 56 <= v : refused *)
         rewrite branch_geu_U, (U_atom E 13 v E13), U_SLit, (zcanon_id 56) in Hc by (unfold M64; lia).
         apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
         assert (HFP : ((ch <? 48) && legalb p v)%bool = false)
           by (apply andb_false_iff; right; unfold legalb; apply orb_false_iff; split;
               apply andb_false_iff; [left; apply Z.ltb_ge; lia | right; apply Z.leb_gt; lia]).
         paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
         set_refuse_leaf HS HJ E HAE HFP E1 Hra Htx HTo regs ly S W mem md tx ch p v T.
      -- (* v <= 55 : accepted *)
         rewrite branch_geu_U, (U_atom E 13 v E13), U_SLit, (zcanon_id 56) in Hc by (unfold M64; lia).
         apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
         assert (HFP : ((ch <? 48) && legalb p v)%bool = true)
           by (apply andb_true_iff; split; [apply Z.ltb_lt; lia | unfold legalb; apply orb_true_iff;
               right; apply andb_true_iff; split; [apply Z.eqb_eq; lia | apply Z.leb_le; lia]]).
         set_accept_tail E HS HJ SHOK ly S W mem md regs tx ch p v T Htx HTo HTl HFP HUB HAE
           E1 E10 E13 E33 Eu10 Eu33 Egot Ecell Usp Hra.
  + (* p < 2 *)
    rewrite branch_geu_U, (U_atom E 12 p E12), U_SLit, (zcanon_id 2) in Hc by (unfold M64; lia).
    apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc. rename Hc into Hp2.
    paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
    psrr_branch_tok RUN BR HS SHOK SETspan.
    * (* v <= 1 : accepted *)
      rewrite branch_geu_U, U_SLit, (zcanon_id 1), (U_atom E 13 v E13) in Hc by (unfold M64; lia).
      apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
      assert (HFP : ((ch <? 48) && legalb p v)%bool = true)
        by (apply andb_true_iff; split; [apply Z.ltb_lt; lia | unfold legalb; apply orb_true_iff;
            left; apply andb_true_iff; split; [apply Z.ltb_lt; lia | apply Z.leb_le; lia]]).
      set_accept_tail E HS HJ SHOK ly S W mem md regs tx ch p v T Htx HTo HTl HFP HUB HAE
        E1 E10 E13 E33 Eu10 Eu33 Egot Ecell Usp Hra.
    * (* v > 1 : refused *)
      rewrite branch_geu_U, U_SLit, (zcanon_id 1), (U_atom E 13 v E13) in Hc by (unfold M64; lia).
      apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
      assert (HFP : ((ch <? 48) && legalb p v)%bool = false)
        by (apply andb_false_iff; right; unfold legalb; apply orb_false_iff; split;
            apply andb_false_iff; [right; apply Z.leb_gt; lia | left; apply Z.eqb_neq; lia]).
      paj_run_tok RUN HS HJ SHOK SETspan; [tx_awr_plain Usp |].
      set_refuse_leaf HS HJ E HAE HFP E1 Hra Htx HTo regs ly S W mem md tx ch p v T.
Qed.

End L.

(* The walk: image B's runtime laws and image facts (hyps_reac_headamp_tx_set) give the contract. The function
   calls no program function, so no callee contract is assumed. *)
Theorem pb_reac_headamp_tx_set : walk_reac_headamp_tx_set B.
Proof.
  unfold walk_reac_headamp_tx_set, hyps_reac_headamp_tx_set, RT_LAWS, RT_PALIB.
  intros [LAWS TL]. exact (pb_core LAWS TL).
Qed.

End H.
End F.
End D.
