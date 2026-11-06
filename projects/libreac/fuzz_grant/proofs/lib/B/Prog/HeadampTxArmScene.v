(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_arm_scene on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxArmScene.v at a working branch 5651bf66924 (blob 8f3765f0519, the blob the walk was ported from), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; B inlines image A's __asan_memset(tx + 440, 0, 9) as three stores at 440 / 444 / 448, so A's memset call segment and its hypothesis are gone, the frame is 16 bytes (A: 48), and the 4-byte store at tx + 456 lies in the block's last partial granule (shadow 4). *)
(* reac_headamp_tx_arm_scene (image B 0x85ce4, 404 bytes, 101 instructions): for a base below 48 and a width
   other than 0 the call stores the base and the clamped width in the table's replay and scene fields
   (bytes 436, 437, 449, 450), zeroes the bytes 440..448 and clears the 4-byte counter at 456; for any other
   base or width it writes nothing.
   What differs from image A (0x84f1c):
   - the frame is 16 bytes (image A's is 48, which also saves s0..s4), so the stack need is 16 + ESTACK;
   - image A's call of __asan_memset (tx + 440, 0, 9) is three inline stores here (4-byte 0 at 440 and 444,
     1-byte 0 at 448), each with its own shadow check, so this walk takes NO callee contract and has no call:
     image A's AMEMSET hypothesis and the whole call segment of each armed leaf are gone, and image A's
     region W449 (449..451) becomes W440 (440..451), whose chunks give the bytes 440..448 that image A took
     from the memset post;
   - two UBSan guards into the unimp at 0x85dec (0x85cf8 tx = 0, 0x85d00 tx mod 4) are new; both are decided by
     the token engine from the entry fact of atom 10 (4096 <= tx, tx mod 16 = 0), which AR's block law gives.
   The eight shadow checks before the stores are discharged from the block's shadow entry (mkSHE 10 0 460): the
   three whole granules 54..56 (bytes 432..455) and the last, partial granule 57 (shadow 4), whose slow block 0x85e68 is entered on
   every armed call and returns to the store at 0x85ddc, so no __asan_report_store{1,4} call is ever reached. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05 YN3g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel reac_headamp_tx_arm_scene_c NextModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The address-free layout of the 460-byte head-amp table and the byte lemmas over it (lib/Prog/HeadampLayout.v,
   the same module GrantBContracts.v names ATx, so the contract's LAY_TX / tx_vals are these), the table image B's
   code leaves, and the signed 4-byte read of byte 440 the table invariant names. Required, not imported. *)
Module BTx := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.
Module BArm := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.reac_headamp_tx_arm_scene_c.
Module BNx := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.NextModel.

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

(* The four bytes of replay_idx the inline stores leave: 0. *)
Lemma arm_tbz : forall T sb sw i, length T = 460%nat -> 440 <= i < 444 ->
  tb (BArm.arm_T T sb sw) i = 0.
Proof.
  intros T sb sw i HT Hi. unfold tb, BArm.arm_T.
  rewrite !SegSetModel.nth_upd_bytes by arm_len.
  rewrite ?Mem.length_le1, ?Mem.length_le4.
  arm_dec. cbv beta iota.
  rewrite (BTx.le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 440) ltac:(lia)).
  rewrite arm_bow0. vm_compute. reflexivity.
Qed.

(* The table invariant reac_headamp_tx_next needs: the armed table's replay_idx is 0, so not negative. *)
Lemma arm_replay_ok : forall T sb sw, length T = 460%nat -> thd_replay_ok (BArm.arm_T T sb sw).
Proof.
  intros T sb sw HT. unfold thd_replay_ok. intros _.
  assert (H0 : tb (BArm.arm_T T sb sw) 440 = 0) by (apply arm_tbz; [exact HT | lia]).
  assert (H1 : tb (BArm.arm_T T sb sw) (440 + 1) = 0) by (apply arm_tbz; [exact HT | lia]).
  assert (H2 : tb (BArm.arm_T T sb sw) (440 + 2) = 0) by (apply arm_tbz; [exact HT | lia]).
  assert (H3 : tb (BArm.arm_T T sb sw) (440 + 3) = 0) by (apply arm_tbz; [exact HT | lia]).
  unfold BNx.s32, BNx.u32. rewrite H0, H1, H2, H3. apply Z.leb_le. reflexivity.
Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition A_tx_arm_sceneB : Z := BASE + AF_reac_headamp_tx_arm_scene.
Definition ASBz : Z := 0x7fff8000.
Definition ACBx : sv := SOff 32 0.
Definition ARMspan : Z * Z := (ASBz, ASBz + 2 ^ 44 - 1).
Definition arm_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0); (32%nat, mkAF ASBz ASBz 0) ] [] [].
(* image B's frame is 16 bytes, image A's 48 *)
Definition arm_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32 ].
Definition ss_arm : sstate := mkSS AF_reac_headamp_tx_arm_scene sr_atoms arm_regions None arm_facts.
Definition arm_SH : list shent := [ mkSHE 10 0 460 ].
Definition EAS (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 ASBz]).
Definition W436 : YP09.region := YP09.mkRegion (Some 10%nat) 436 438 436 438 [].
(* image A's W449 (449..451) widened to the bytes the inline stores write *)
Definition W440 : YP09.region := YP09.mkRegion (Some 10%nat) 440 451 440 451 [].
Definition W456 : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [].

Lemma arm_mbyte_of_frame : forall (H : word -> bool) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict H m) (mrestrict H m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H E' rs m m' a HF Hn Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* The table after an armed call: every byte the eight stores leave, from the three write regions, and every
   other byte of the layout from Hkeep. Image A takes 440..448 from the memset post; image B's bytes come from
   the chunks of W440. *)
Lemma arm_written : forall (Ex : env) m (tx sb sw : Z) (T : list byte) (WSV : sv) (c1 c2 c3 : list YP09.chunk),
  0 <= sb < 48 -> length T = 460%nat ->
  bv_unsigned (ew Ex 10) = tx ->
  sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb ->
  sv_denot Ex WSV = Z_to_bv 64 (BArm.arm_w sb sw) ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 436 438 436 438 c1) ->
  In (YP09.mkChunk 436 (CVal 1 (SOff 11 0))) c1 -> In (YP09.mkChunk 437 (CVal 1 WSV)) c1 ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 440 451 440 451 c2) ->
  In (YP09.mkChunk 440 (CVal 4 (SLit 0))) c2 -> In (YP09.mkChunk 444 (CVal 4 (SLit 0))) c2 ->
  In (YP09.mkChunk 448 (CVal 1 (SLit 0))) c2 ->
  In (YP09.mkChunk 449 (CVal 1 (SOff 11 0))) c2 -> In (YP09.mkChunk 450 (CVal 1 WSV)) c2 ->
  region_ok SEGS Ex m (YP09.mkRegion (Some 10%nat) 456 460 456 460 c3) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) c3 ->
  (forall i, BTx.tx_fbyte i = true -> ~ (436 <= i < 438) -> ~ (440 <= i < 451) -> ~ (456 <= i < 460) ->
     mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  obj_at SEGS m tx BTx.LAY_TX (BTx.tx_vals (BArm.arm_T T sb sw)).
Proof.
  intros Ex m tx sb sw T WSV c1 c2 c3 Hsb HTl E10 E11 EW
         HR1 I436 I437 HR2 I440 I444 I448 I449 I450 HR3 I456 Hkeep.
  apply (proj2 (BTx.tx_obj_bytes SEGS m tx _)).
  intros i Hi. pose proof (BTx.tx_fbyte_range i Hi) as Hir.
  unfold BArm.arm_T.
  rewrite !SegSetModel.nth_upd_bytes by arm_len.
  rewrite ?Mem.length_le1, ?Mem.length_le4.
  destruct (Z_lt_le_dec i 436) as [L|L].
  { arm_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia]. }
  destruct (Z_lt_le_dec i 437) as [L1|L1].
  { assert (i = 436) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 436 - 436)%nat with 0%nat. rewrite BTx.le1_byte_of_word. rewrite <- E11.
    replace (tx + 436) with (bv_unsigned (ew Ex 10) + 436 + 0) by lia.
    exact (BTx.byte_of_region SEGS Ex m 10%nat _ _ 436 438 436 438 436 1 (SOff 11 0) 0 HR1 eq_refl I436 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 438) as [L2|L2].
  { assert (i = 437) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 437 - 437)%nat with 0%nat. rewrite BTx.le1_byte_of_word. rewrite <- EW.
    replace (tx + 437) with (bv_unsigned (ew Ex 10) + 437 + 0) by lia.
    exact (BTx.byte_of_region SEGS Ex m 10%nat _ _ 436 438 436 438 437 1 WSV 0 HR1 eq_refl I437 ltac:(cbn; lia)). }
  destruct (Z_lt_le_dec i 440) as [L3|L3].
  { exfalso. assert (i = 438 \/ i = 439) as [-> | ->] by lia; vm_compute in Hi; discriminate. }
  destruct (Z_lt_le_dec i 444) as [L4|L4].
  { arm_dec. cbv beta iota.
    rewrite (BTx.le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 440) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 440)) with (i - 440) by lia.
    replace (tx + i) with (bv_unsigned (ew Ex 10) + 440 + (i - 440)) by lia.
    rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 440 451 440 451 440 4 (SLit 0) (i - 440) HR2 eq_refl I440 ltac:(cbn; lia)).
    reflexivity. }
  destruct (Z_lt_le_dec i 448) as [L5|L5].
  { arm_dec. cbv beta iota.
    rewrite (BTx.le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 444) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 444)) with (i - 444) by lia.
    replace (tx + i) with (bv_unsigned (ew Ex 10) + 444 + (i - 444)) by lia.
    rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 440 451 440 451 444 4 (SLit 0) (i - 444) HR2 eq_refl I444 ltac:(cbn; lia)).
    reflexivity. }
  destruct (Z_lt_le_dec i 449) as [L6|L6].
  { assert (i = 448) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 448 - 448)%nat with 0%nat. rewrite BTx.le1_byte_of_word.
    replace (tx + 448) with (bv_unsigned (ew Ex 10) + 448 + 0) by lia.
    rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 440 451 440 451 448 1 (SLit 0) 0 HR2 eq_refl I448 ltac:(cbn; lia)).
    reflexivity. }
  destruct (Z_lt_le_dec i 450) as [L7|L7].
  { assert (i = 449) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 449 - 449)%nat with 0%nat. rewrite BTx.le1_byte_of_word. rewrite <- E11.
    replace (tx + 449) with (bv_unsigned (ew Ex 10) + 449 + 0) by lia.
    rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 440 451 440 451 449 1 (SOff 11 0) 0 HR2 eq_refl I449 ltac:(cbn; lia)).
    reflexivity. }
  destruct (Z_lt_le_dec i 451) as [L8|L8].
  { assert (i = 450) by lia. subst i. arm_dec. cbv beta iota.
    change (Z.to_nat 450 - 450)%nat with 0%nat. rewrite BTx.le1_byte_of_word. rewrite <- EW.
    replace (tx + 450) with (bv_unsigned (ew Ex 10) + 450 + 0) by lia.
    rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 440 451 440 451 450 1 WSV 0 HR2 eq_refl I450 ltac:(cbn; lia)).
    reflexivity. }
  destruct (Z_lt_le_dec i 456) as [L9|L9].
  { arm_dec. cbv beta iota. apply Hkeep; solve [exact Hi | lia]. }
  arm_dec. cbv beta iota.
  rewrite (BTx.le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 456) ltac:(lia)).
  replace (Z.of_nat (Z.to_nat i - 456)) with (i - 456) by lia.
  replace (tx + i) with (bv_unsigned (ew Ex 10) + 456 + (i - 456)) by lia.
  rewrite (BTx.byte_of_region SEGS Ex m 10%nat _ _ 456 460 456 460 456 4 (SLit 0) (i - 456) HR3 eq_refl I456 ltac:(cbn; lia)).
  reflexivity.
Qed.

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma arm_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx sb sw : Z),
  afn_pre SEGS B STK_reac_headamp_tx_arm_scene ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 sb -> getr regs 12 = w64 sw ->
  0 <= sb < 256 -> 0 <= sw < 256 ->
  In (tx, BTx.TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (EAS regs) ss_arm
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_tx_arm_sceneB) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ACBx arm_SH (EAS regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx sb sw HPRE H10 H11 H12 Hsb Hsw Htx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : STK_reac_headamp_tx_arm_scene = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx BTx.TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size BTx.TX_SIZE) with 460 in *.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  (* image B's range is the opaque IMG_LO_B / IMG_TOP_B of GrantTop.v: to numerals, else lia cannot
     place the GOT and shadow-base cells. *)
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
  rewrite restrict_mkst_fx.
  set (E := EAS regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 ASBz]) n)
    by (intros n Hn; subst E; unfold EAS; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 sb) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 sw) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 ASBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (change 242%nat with (A_OBJ 1); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
    by (change 276%nat with (A_OBJ 35); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_arm, A_tx_arm_sceneB. apply pa_entry_st_ok_full.
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
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
        [cbn [sv_denot]; change (A_OBJ 35) with 276%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 ACBx ASBz);
        [cbn [sv_denot ACBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold ASBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold arm_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
      repeat split; lia.
    + split; [|split; exact I].
      cbn [arm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E12, E32, !unsigned_lit_small by (unfold ASBz; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil Hsb Hsw.
      clear. unfold ASBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, arm_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_block SEGS B LAWS ly S W mem md E ACBx 10 tx BTx.TX_SIZE 0 460 HAR Htx).
    + unfold U, ACBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold ASBz; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + change (req_size BTx.TX_SIZE) with 460. lia.
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
  | eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat txv BTx.TX_SIZE);
      [ reflexivity
      | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10v
      | exact Htxv | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (req_size BTx.TX_SIZE) with 460; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply arm_inFP; lia |] ].

Ltac arm_disj Eu10v Egotv Ecellv Uspv :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  try unfold W436; try unfold W440; try unfold W456;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?Eu10v, ?Egotv, ?Ecellv;
  rewrite ?unsigned_lit_small by
    (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 35)); lia);
  rewrite ?Uspv;
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
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs [Z_to_bv 64 ASBz] HS);
            [ eapply env_agree_trans; [exact HAE | split; [intros n Hn;
                rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
            | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]
  end.

(* a path that writes nothing: every byte of the table is the one it was *)
Ltac arm_refused HTo Uspv Eu10v :=
  let i := fresh "i" in let Hi := fresh "Hi" in let Hir := fresh "Hir" in
  apply (proj2 (BTx.tx_obj_bytes SEGS _ _ _)); intros i Hi; pose proof (BTx.tx_fbyte_range i Hi) as Hir;
  rewrite <- (proj1 (BTx.tx_obj_bytes SEGS _ _ _) HTo i Hi);
  repeat match goal with
  | Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ ?mB) |- mbyte _ (mrestrict _ ?mB) ?a = _ =>
      rewrite (arm_mbyte_of_frame _ _ _ _ _ a Hf ltac:(arm_nwr Uspv Eu10v) ltac:(lia)); clear Hf
  end;
  reflexivity.

Lemma pb_arm_core : tb_reac_headamp_tx_arm_scene_spec B.
Proof.
unfold tb_reac_headamp_tx_arm_scene_spec.
(* The contract states no premise for the 4-byte store at tx + 456: its shadow check (granule 57, partial,
   shadow 4) takes the slow block 0x85e68 and returns to the store from the block's own shadow entry
   mkSHE 10 0 460, so no report call is reached (header, :19-21). *)
intros ly S W regs mem md ch0 tx sb sw T HPRE H10 H11 H12 Hsb Hsw Htx HTl HTo.
unfold tb_reac_headamp_tx_arm_scene_post.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (arm_entry ly S W regs mem md ch0 tx sb sw HPRE H10 H11 H12 Hsb Hsw Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_headamp_tx_arm_scene
              [(tx + 436, tx + 438); (tx + 440, tx + 451); (tx + 456, tx + 460)]
              ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_headamp_tx_arm_scene = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx BTx.TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size BTx.TX_SIZE) with 460 in *.
pose proof (blk_off_imgB B ly S W mem md tx BTx.TX_SIZE HAR Htx) as Htximg.
change (req_size BTx.TX_SIZE) with 460 in Htximg.
(* Htximg is image B's range, opaque: to numerals, so that arm_disj's lia can place the block against the
   GOT and shadow-base cells (on the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the
   walk does not depend on which). *)
rewrite IMG_LO_B_val, IMG_TOP_B_val in Htximg.
pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
remember (EAS regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EAS; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 ASBz]) n)
  by (intros n Hn; subst E; unfold EAS; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 sb) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 sw) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 ASBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (change 242%nat with (A_OBJ 1); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
  by (change 276%nat with (A_OBJ 35); subst E; unfold EAS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 ASBz]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ugot : bv_unsigned (ew E 242%nat) = VAL (A_OBJ 1))
  by (rewrite Egot; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (Ucell : bv_unsigned (ew E 276%nat) = VAL (A_OBJ 35))
  by (rewrite Ecell; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 35)); lia).
assert (Hes : ESTACK = 4096) by reflexivity.
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_reac_headamp_tx_arm_scene)) with (Z_to_bv 64 A_tx_arm_sceneB).
(* the frame, the save of ra and the compare of the base with 47 *)
paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
psrr_branch_tok RUN BR HS SHOK ARMspan.
- (* 47 < sb : nothing is written *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 sb E11) in Hc by (unfold M64; lia).
  apply Z.ltb_lt in Hc.
  assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = true) by (apply orb_true_iff; right; apply Z.leb_le; lia).
  paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
  arm_ret HS HJ HAE E1 Hra W ly S regs.
  unfold thd_arm_T. rewrite HIF.
  split; [arm_refused HTo Usp Eu10 | intros HR; exact HR].
- (* sb <= 47: the next slot is the test of the width *)
  rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 sb E11) in Hc by (unfold M64; lia).
  apply Z.ltb_ge in Hc. rename Hc into Hsb47.
  (* the split leaves the state at the branch 0x85cf0, now decided by its condition: step it *)
  paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
  psrr_branch_tok RUN BR HS SHOK ARMspan.
  + (* sw = 0 : nothing is written *)
    rewrite branch_eq_U, (U_atom E 12 sw E12), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_eq in Hc.
    assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = true) by (apply orb_true_iff; left; apply Z.eqb_eq; lia).
    paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
    arm_ret HS HJ HAE E1 Hra W ly S regs.
    unfold thd_arm_T. rewrite HIF.
    split; [arm_refused HTo Usp Eu10 | intros HR; exact HR].
  + (* sw <> 0 : the scene is armed. The two trap guards (tx = 0 at 0x85cf8, tx mod 4 at 0x85d00) are decided
       from the entry facts of atom 10 (4096 <= tx, tx mod 16 = 0), so the run goes on to the clamp test. *)
    rewrite branch_eq_U, (U_atom E 12 sw E12), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_neq in Hc. rename Hc into Hsw0.
    assert (HIF : ((sw =? 0) || (48 <=? sb))%bool = false)
      by (apply orb_false_iff; split; [apply Z.eqb_neq; lia | apply Z.leb_gt; lia]).
    lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      destruct (al_blocks _ _ LAWS ly S W (ms_mem msx) _ tx BTx.TX_SIZE (proj1 HJ) Htx)
        as (_ & _ & _ & _ & Hpres' & _);
      change (req_size BTx.TX_SIZE) with 460 in Hpres'
    end.
    arm_addregion HS W436 Hpres' Eu10 Egot Ecell Usp tx.
    arm_addregion HS W440 Hpres' Eu10 Egot Ecell Usp tx.
    arm_addregion HS W456 Hpres' Eu10 Egot Ecell Usp tx.
    clear Hpres'.
    paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
    psrr_branch_tok RUN BR HS SHOK ARMspan.
    * (* sb + sw <= 48 : the width is kept *)
      rewrite branch_geu_U, U_SLit, U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom E 11 sb E11), (U_atom E 12 sw E12) in Hc by lia.
      rewrite (zcanon_id 48), (zcanon_id (sb + sw)) in Hc by (unfold M64; lia).
      apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc. rename Hc into Hclamp.
      assert (EW0 : forall Ex : env, ew Ex 11 = ew E 11 -> ew Ex 12 = ew E 12 ->
                sv_denot Ex (SOff 12 0) = Z_to_bv 64 (BArm.arm_w sb sw)).
      { intros Ex H11' H12'. cbn [sv_denot]. rewrite H12', E12, unsigned_lit_small, Z.add_0_r by lia.
        unfold BArm.arm_w. replace (48 <? sb + sw) with false by (symmetry; apply Z.ltb_ge; lia).
        reflexivity. }
      (* the eight stores, each after its shadow check, and the return *)
      paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) W436) in
        let r1 := eval vm_compute in (nth 1 (ss_mem ssx) W436) in
        let r2 := eval vm_compute in (nth 2 (ss_mem ssx) W436) in
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HQ0;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1%nat r1 HS ltac:(vm_compute; reflexivity)) as HQ1;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 2%nat r2 HS ltac:(vm_compute; reflexivity)) as HQ2;
        cbn [restrict ms_mem] in HQ0, HQ1, HQ2;
        assert (EU10f : bv_unsigned (ew Ex 10) = tx)
          by (cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10);
        assert (E11f : sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb)
          by (cbn [sv_denot extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia);
              rewrite E11, unsigned_lit_small, Z.add_0_r by lia; reflexivity);
        assert (EWf := EW0 Ex ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity)
                           ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity))
      end.
      arm_ret HS HJ HAE E1 Hra W ly S regs.
      unfold thd_arm_T. rewrite HIF.
      split; [| intros _; exact (arm_replay_ok T sb sw HTl)].
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
      apply (arm_written _ _ tx sb sw T _ _ _ _ ltac:(lia) HTl EU10f E11f EWf HQ2
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ1
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ0
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
      intros i Hi N1 N2 N3. pose proof (BTx.tx_fbyte_range i Hi) as Hir.
      rewrite <- (proj1 (BTx.tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
      apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
      apply (F2 tx BTx.TX_SIZE i Htx Htx ltac:(change (req_size BTx.TX_SIZE) with 460; lia)).
      intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
    * (* 48 < sb + sw : the width is clamped to 48 - sb *)
      rewrite branch_geu_U, U_SLit, U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom E 11 sb E11), (U_atom E 12 sw E12) in Hc by lia.
      rewrite (zcanon_id 48), (zcanon_id (sb + sw)) in Hc by (unfold M64; lia).
      apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc. rename Hc into Hclamp.
      assert (EW0 : forall Ex : env, ew Ex 11 = ew E 11 -> ew Ex 12 = ew E 12 ->
                sv_denot Ex (SAlu ALU_SUB (SLit 0) (SOff 11 (-48))) =
                Z_to_bv 64 (BArm.arm_w sb sw)).
      { intros Ex H11' H12'.
        unfold BArm.arm_w. replace (48 <? sb + sw) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite denot_lit_U. f_equal.
        rewrite U_SAlu, U_SLit, U_SOff. cbn [zalu_raw]. rewrite H11', E11, unsigned_lit_small by lia.
        unfold zcanon, M64. rewrite Zmod_0_l.
        rewrite <- (Z.mod_unique (sb + -48) (2 ^ 64) (-1) (sb + -48 + 2 ^ 64)) by lia.
        replace (0 - (sb + -48 + 2 ^ 64)) with ((48 - sb) + (-1) * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      (* the eight stores, each after its shadow check, and the return *)
      paj_run_tok RUN HS HJ SHOK ARMspan; [arm_awr Usp Eu10 Htx tx |].
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) W436) in
        let r1 := eval vm_compute in (nth 1 (ss_mem ssx) W436) in
        let r2 := eval vm_compute in (nth 2 (ss_mem ssx) W436) in
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HQ0;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1%nat r1 HS ltac:(vm_compute; reflexivity)) as HQ1;
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 2%nat r2 HS ltac:(vm_compute; reflexivity)) as HQ2;
        cbn [restrict ms_mem] in HQ0, HQ1, HQ2;
        assert (EU10f : bv_unsigned (ew Ex 10) = tx)
          by (cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Eu10);
        assert (E11f : sv_denot Ex (SOff 11 0) = Z_to_bv 64 sb)
          by (cbn [sv_denot extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia);
              rewrite E11, unsigned_lit_small, Z.add_0_r by lia; reflexivity);
        assert (EWf := EW0 Ex ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity)
                           ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); reflexivity))
      end.
      arm_ret HS HJ HAE E1 Hra W ly S regs.
      unfold thd_arm_T. rewrite HIF.
      split; [| intros _; exact (arm_replay_ok T sb sw HTl)].
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
      apply (arm_written _ _ tx sb sw T _ _ _ _ ltac:(lia) HTl EU10f E11f EWf HQ2
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ1
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
               HQ0
               ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
      intros i Hi N1 N2 N3. pose proof (BTx.tx_fbyte_range i Hi) as Hir.
      rewrite <- (proj1 (BTx.tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
      apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
      apply (F2 tx BTx.TX_SIZE i Htx Htx ltac:(change (req_size BTx.TX_SIZE) with 460; lia)).
      intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.

End H.

Section W.
Variable B : asyms.
Theorem pb_reac_headamp_tx_arm_scene : walk_reac_headamp_tx_arm_scene B.
Proof.
  unfold walk_reac_headamp_tx_arm_scene, hyps_reac_headamp_tx_arm_scene, RT_LAWS, RT_PALIB.
  intros (HL & HT). exact (pb_arm_core B HL HT).
Qed.
End W.
End F.
End D.
