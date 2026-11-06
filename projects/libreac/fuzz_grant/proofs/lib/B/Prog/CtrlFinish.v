(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_finish on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) walk of ctrl_finish. B's ctrl_finish is 244 bytes, 188 shorter than A's 432, because it calls the two checksum stamps out of line; the entry state, the row's shadow entry and the final tcj_kept follow lib/A/Prog/CtrlFinish.v, and the caller-journal lemmas (tcj_kept composition, garr8 / region transport) follow lib/A/Prog/CtrlStampHeadamp.v, both of a working branch 5aae1e8a0ce (AB01 1e6f4323d1e; the whole lib Require closure of the two files is 187 files with 0 Admitted / admit / Axiom / Parameter); every address, slot and constant is read from image B's listing (lib/B/Prog/GrantList.v). *)
(* ctrl_finish on image B (fuzz_grant.asan-ubsan, bin sha256 fde52226dc48, symbols 5a5ee7c02b4e), 0x83fdc =
   BASE + AF_ctrl_finish (AF_ctrl_finish = 0x35a0, listing base 0x80a3c): the walk of lib/B/Prog/
   GrantBContracts.v's walk_ctrl_finish.

   Image A inlines the two checksum stamps (lib/A/Prog/CtrlFinish.v of a working branch 5aae1e8a0ce); image B calls
   them out of line, so this walk takes one contract per program callee and has no summation loop of its own:
     0x84074  jal  reac_ctrl_record_cksum_stamp (a0 = p + 34, a1 = 6)   writes the record's byte at p + 39
     0x84094  j    reac_ctrl_block_cksum_stamp  (a0 = p + 18)           writes the block's byte at p + 49,
                                                                        and returns to ctrl_finish's caller.
   The 32 bytes of the caller's control block are then RcFin.fin 2 16 6 Bk = stamp32 (rstamp Bk 16 6).
   The trap guards of `unimp` 0x840a8 are decided by the entry facts (0x83fec row alignment from IMG_CTRL_ROW;
   0x84028 / 0x84078 p <> 0, 0x84030 / 0x84080 p + 18 below 2 ^ 64, from the contract's p bounds), except
   0x84054 (`not a0,a4; bltu a0,a3`), which the engine leaves open; the walk refutes its taken arm with
   cf_lxor_m1 (~ (p + 18) = 2 ^ 64 - 1 - (p + 18), which is not below 16).

   A-vs-B contract deltas (tb_ctrl_finish_spec of GrantBContracts.v against A's tctrl_finish_spec): B ADDS the
   premise `p <> 0` (A has `0 <= p` only; B's trap guards 0x84028 / 0x84078 test it, and the entry fact of
   atom 10 is `1 <= p`); B RECASTS A's per-byte `forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x` as
   `p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18` (the form the two stamps' contracts take, passed to them
   unchanged); the stack-clearance premise `spZ regs <= p + 18 \/ p + 50 <= spZ regs - STK` is A's, at B's
   STK_ctrl_finish = 16 + 16 + ESTACK (A: TCF_STK = 16 + ESTACK); and walk_ctrl_finish takes the contracts of
   reac_ctrl_record_cksum_stamp and reac_ctrl_block_cksum_stamp, which A has not got. B's contract has no
   premise A lacks beyond `p <> 0`.
   The image facts A takes as Section hypotheses (HGOTimg, HCELimg, HROWimg, HROWsep) are B's hyps_ctrl_finish
   (IMG_CTRL_ROW, IMG_CTRL_ROW_IMG) over B_ROW = VAL (A_OBJ 18) + 240 and the cell object 35.

   OBL_finish_report_dead. ctrl_finish's three report branches are
     0x84010 bnez a3 -> 0x840ac -> (0x840b0 blt not taken) -> 0x840b4 __asan_report_load1
     0x84044 bnez a3 -> 0x840b8 -> (0x840bc blt not taken) -> 0x840c0 __asan_report_load1
     0x84068 bnez a1 -> 0x840c4 -> (0x840c8 blt not taken) -> 0x840cc __asan_report_load1
   and 0x840cc is ctrl_finish's last word, so a returning report falls through into reac_box_model_block 0x840d0.
   Each of the three is the instrumented check of one byte of the control-frame row (B_ROW + 20, + 18, + 19). The
   walk refutes all three through ONE shadow entry, `cf_SH = [mkSHE 11 18 21]`, which cf_entry discharges with
   YCbq.v's `shent_ok_of_range` from the contract's own premise
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (B_ROW + 18) 3.
   With that entry in scope PaShadow.v's `tok_load` / `tok_branch_pi` decide each check's shadow load and its
   branch, so the symbolic run never leaves the fast path and never reaches 0x840ac / 0x840b8 / 0x840c4, let alone
   a report slot. hyps_ctrl_finish holds no contract for any __asan_report_* entry and none for
   GS_reac_box_model_block, and this file takes none. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcFin RcRec RcModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The write-rights goal every run of this walk leaves: the 16-byte frame on the machine stack, then the
   three read-only regions (the GOT word, the shadow-base cell and the row). *)
Ltac cf_usp Usp :=
  cbn [ew ewset extK havoc Eimg Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add];
  rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); rewrite Usp; lia.
Ltac cf_awr sp0v spv uspt :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sq ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sq fp b0 bc lyq ownq) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
  [ reflexivity | uspt | cbn; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac cf_norm :=
  cbn [ew ewset extK havoc Eimg Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add];
  rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia).
Ltac cf_eq Hx := cf_norm; exact Hx.
Ltac cf_usp2 Uspv :=
  rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite Uspv; lia.
Ltac cf_val Eq := cf_norm; rewrite ?Eq; rewrite ?unsigned_lit_small by lia; try reflexivity.
(* Only this call's 16-byte machine-stack frame is written by a run of the engine. *)
Ltac cf_hm Usp :=
  let xx := fresh "xx" in let HB := fresh "HB" in
  intros xx HB;
  repeat match goal with
  | Hf : frame_of ?Ew ?rsw (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mrestrict ?Hq ?mB xx = _ =>
    rewrite (Hf xx ltac:(let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [ subst r;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset extK havoc Eimg
               Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
          rewrite ?Usp in Hr; lia |]);
      destruct Hin)); clear Hf
  end; reflexivity.
(* `not a0,a4` at 0x84050 is `xori a0,a4,-1`, which the engine leaves as Z.lxor with the canonical -1. *)
Lemma cf_lxor_m1 : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx.
assert (Hlog : Z.log2 x < 64).
{ destruct (Z.eq_dec x 0) as [-> | Hnz]; [rewrite Z.log2_nonpos by lia; lia|].
  apply Z.log2_lt_pow2; [lia | change (2 ^ 64) with 18446744073709551616; lia]. }
replace 18446744073709551615 with (Z.ones 64) by (vm_compute; reflexivity).
assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
{ apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    rewrite (Z.bits_above_log2 x n ltac:(lia) ltac:(lia)). reflexivity. }
rewrite E, Z.land_ones by lia.
replace (Z.lnot x) with (- x - 1) by (unfold Z.lnot; lia).
replace (Z.ones 64) with 18446744073709551615 by (vm_compute; reflexivity).
change (2 ^ 64) with 18446744073709551616.
replace (- x - 1) with (18446744073709551615 - x + (-1) * 18446744073709551616) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* ---- the address-free arithmetic: the record the inner stamp sums, and the block the outer one stamps ---- *)
(* The record is Bk[16 .. 22); reac_ctrl_record_cksum_stamp sums its first five bytes and writes the sixth. *)
Definition cf_RS (Bk : list byte) : list byte := firstn 5 (skipn 16 Bk).
Lemma cf_nth_skipn : forall (l : list byte) (n j : nat) (d : byte), nth j (skipn n l) d = nth (n + j) l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; cbn [skipn nth Nat.add]; [destruct j; reflexivity | apply IH].
Qed.
Lemma cf_nth_firstn : forall (l : list byte) (k j : nat) (d : byte), (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j d Hj; [lia|].
destruct l as [|x l]; cbn [firstn nth]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity | apply IH; lia].
Qed.
Lemma cf_RS_len : forall Bk, length Bk = 32%nat -> length (cf_RS Bk) = 5%nat.
Proof.
intros Bk HL. unfold cf_RS. rewrite firstn_length_le; [reflexivity|].
rewrite length_skipn, HL. lia.
Qed.
Lemma cf_stampck : forall Bk, length Bk = 32%nat ->
  RcRec.stampck (cf_RS Bk) = (- RcFin.rsum Bk 16 5) mod 128.
Proof.
intros Bk HL. unfold RcRec.stampck, RcFin.rsum.
rewrite (cf_RS_len Bk HL). change (Z.to_nat 16) with 16%nat. change (Z.to_nat 5) with 5%nat.
f_equal. f_equal. unfold cf_RS. cbn [RcModel.psum].
rewrite !(cf_nth_firstn (skipn 16 Bk) 5) by lia. reflexivity.
Qed.
(* The block the outer stamp sees: Bk with its record checksum written at index 21. *)
Definition cf_B1 (Bk : list byte) : list byte := RcFin.rstamp Bk 16 6.
Lemma cf_B1_eq : forall Bk, cf_B1 Bk = Mem.upd_bytes Bk 21 [Z_to_bv 8 ((- RcFin.rsum Bk 16 5) mod 128)].
Proof. intros Bk. unfold cf_B1, RcFin.rstamp. reflexivity. Qed.
Lemma cf_B1_len : forall Bk, length Bk = 32%nat -> length (cf_B1 Bk) = 32%nat.
Proof.
intros Bk HL. rewrite cf_B1_eq. rewrite Mem.upd_bytes_length by (cbn [length]; lia). exact HL.
Qed.
Lemma cf_fin_eq : forall Bk, RcFin.fin 2 16 6 Bk = RcFin.stamp32 (cf_B1 Bk).
Proof. intros Bk. reflexivity. Qed.
Lemma cf_nth_upd1 : forall (l : list byte) (kk : nat) (b d : byte) (j : nat),
(kk < length l)%nat -> (j < length l)%nat ->
nth j (Mem.upd_bytes l kk [b]) d = if (j =? kk)%nat then b else nth j l d.
Proof.
intros l kk b d j Hk Hj. unfold Mem.upd_bytes.
assert (Hfl : length (firstn kk l) = kk) by (apply firstn_length_le; lia).
destruct (Nat.eqb_spec j kk) as [->|Hne].
- rewrite app_nth2 by lia. rewrite Hfl, Nat.sub_diag. reflexivity.
- destruct (Nat.lt_ge_cases j kk) as [Hlt|Hge].
  + rewrite app_nth1 by lia.
    rewrite <- (firstn_skipn kk l) at 2. rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite Hfl. cbn [app].
    destruct (j - kk)%nat as [|q] eqn:Hq; [lia|]. cbn [nth].
    rewrite <- (firstn_skipn (kk + 1)%nat l) at 2.
    rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
    rewrite firstn_length_le by lia. f_equal. lia.
Qed.
Lemma cf_B1_nth : forall Bk j, length Bk = 32%nat -> (j < 32)%nat ->
  nth j (map bv_unsigned (cf_B1 Bk)) 0 =
  if (j =? 21)%nat then (- RcFin.rsum Bk 16 5) mod 128 else nth j (map bv_unsigned Bk) 0.
Proof.
intros Bk j HL Hj.
assert (HB : length (cf_B1 Bk) = 32%nat) by (apply cf_B1_len; exact HL).
rewrite (nth_indep (map bv_unsigned (cf_B1 Bk)) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, HB; lia).
rewrite (map_nth bv_unsigned (cf_B1 Bk) (Z_to_bv 8 0) j).
rewrite cf_B1_eq, (cf_nth_upd1 Bk 21 _ (Z_to_bv 8 0) j) by lia.
destruct (Nat.eqb_spec j 21) as [->|Hne].
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  pose proof (Z.mod_pos_bound (- RcFin.rsum Bk 16 5) 128 ltac:(lia)). apply Z.mod_small. lia.
- rewrite (nth_indep (map bv_unsigned Bk) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, HL; lia).
  rewrite (map_nth bv_unsigned Bk (Z_to_bv 8 0) j). reflexivity.
Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* image B's own read range, as GrantTop.v computes it from grantsegsB0's PT_LOADs. *)
Definition CF_LO : Z := Eval vm_compute in IMG_LO.
Definition CF_HI : Z := Eval vm_compute in IMG_HI.
Lemma cf_lo_eq : CF_LO = IMG_LO. Proof. vm_compute. reflexivity. Qed.
Lemma cf_hi_eq : CF_HI = IMG_HI. Proof. vm_compute. reflexivity. Qed.
Lemma cf_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.
Definition cf_Bx : sv := SOff 32 0.
Definition cf_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The three bytes of the row the call reads: +18 rec_off 16, +19 rec_len 6, +20 cksum kind 2. *)
Definition cf_row : YP09.region :=
  YP09.mkRegion (Some 11%nat) 18 21 0 0
    [YP09.mkChunk 18 (CVal 1 (SLit 16)); YP09.mkChunk 19 (CVal 1 (SLit 6)); YP09.mkChunk 20 (CVal 1 (SLit 2))].
Definition cf_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; cf_row ].
Definition cf_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 58) 0);
            (32%nat, mkAF SB SB 0); (11%nat, mkAF CF_LO CF_HI 3) ] [] [].
Definition ss_cf : sstate := mkSS AF_ctrl_finish sr_atoms cf_regions None cf_facts.
(* The one shadow entry that kills the three report branches. *)
Definition cf_SH : list shent := [ mkSHE 11 18 21 ].
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
(* IMG_CTRL_ROW, spelled out (the walk uses five of its eight conjuncts) and IMG_CTRL_ROW_IMG. *)
Hypothesis HRal : B_ROW mod 8 = 0.
Hypothesis HRlo : IMG_LO + 64 <= B_ROW.
Hypothesis HRhi : B_ROW + 24 + 64 <= IMG_HI.
Hypothesis HRg1 : ls_apart B_ROW 24 (VAL (A_OBJ 1)) 8.
Hypothesis HRc35 : ls_apart B_ROW 24 (VAL (A_OBJ 35)) 8.
Hypothesis HRimg : forall a, B_ROW <= a < B_ROW + 24 -> in_img SEGS a.
(* the two program callees, by their contracts, in the order walk_ctrl_finish lists them *)
Hypothesis HREC : tb_reac_ctrl_record_cksum_stamp_spec B.
Hypothesis HBLK : tb_reac_ctrl_block_cksum_stamp_spec B.

(* ---- the caller-journal bookkeeping (image B restatement of the shapes lib/A/Prog/CtrlStampHeadamp.v
   of a working branch 5aae1e8a0ce states for image A's walks) --------------------------------------------- *)
(* A step that changes no byte but this call's own machine-stack window keeps everything tcj_kept names:
   every block, frame, frame shadow and image byte lies below alloc_ceiling, hence below the window. *)
Lemma cf_tcj_of_keep : forall STK lyc Sc W memc mdc m2 sp (E : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W) m2 a) ->
(forall a, sp - STK <= a < sp -> apresent (w_H W) m2 a) ->
tcj_kept B STK lyc Sc W memc W m2 sp E.
Proof.
intros STK lyc Sc W memc mdc m2 sp E HAR Hce H64 Hav Hpr Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
unfold tcj_kept. split; [intros a Ha Hn _; apply Hav; lia|].
split.
{ intros b m i Hb Hi _. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4 & Hcb & _).
  apply Hav; lia. }
split.
{ intros a Hi _ _. pose proof (Hsegs a Hi) as Hlo. apply Hav; unfold kLowMemEnd in *; lia. }
split.
{ intros cid pos a Hf Hz _.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (F4 & Fc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hs1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  assert (Hr : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr in Hz. cbn [fst snd] in Hz. destruct Hz as [Hz | Hz]; lia. }
  apply Hav; lia. }
split; [intros a Ha Hn Hp; apply Hpr; [lia | exact Hn | exact Hp] | exact Hw].
Qed.
Lemma cf_tcj_mono : forall STK lyc Sc W memc W2 mem2 sp (E E' : Z -> Prop),
tcj_kept B STK lyc Sc W memc W2 mem2 sp E -> (forall a, E a -> E' a) ->
tcj_kept B STK lyc Sc W memc W2 mem2 sp E'.
Proof.
intros STK lyc Sc W memc W2 mem2 sp E E' (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw He; apply K1; [exact Ha | exact Hw | intros H; exact (He (HE a H))]|].
split; [intros b m i Hb Hi He; apply (K2 b m i Hb Hi); intros H; exact (He (HE _ H))|].
split; [exact K3|].
split; [intros cid pos a Hf Hz He; apply (K4 cid pos a Hf Hz); intros H; exact (He (HE _ H))|].
split; [exact K5 | exact K6].
Qed.
Lemma cf_tcj_compose : forall STK STK' lyc Sc W memc W1 m1 W2 m2 sp sp' (E E' : Z -> Prop),
tcj_kept B STK lyc Sc W memc W1 m1 sp E ->
tcj_kept B STK' lyc Sc W1 m1 W2 m2 sp' E' ->
sp - STK <= sp' - STK' -> sp' <= sp -> alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 ->
(forall a, E' a -> E a) ->
tcj_kept B STK lyc Sc W memc W2 m2 sp E.
Proof.
intros STK STK' lyc Sc W memc W1 m1 W2 m2 sp sp' E E'
(T1 & T2 & T3 & T4 & T5 & T6) (U1 & U2 & U3 & U4 & U5 & U6) H1 H2 H3 H4 HE.
split.
{ intros a Ha Hw He. rewrite (U1 a Ha); [exact (T1 a Ha Hw He) | lia | intros H; exact (He (HE a H))]. }
split.
{ intros b m i Hin Hi He. rewrite (U2 b m i Hin Hi); [exact (T2 b m i Hin Hi He) | intros H; exact (He (HE _ H))]. }
split.
{ intros a Hi Ho Her. rewrite (U3 a Hi Ho Her). exact (T3 a Hi Ho Her). }
split.
{ intros cid pos a Hin Hz He. rewrite (U4 cid pos a Hin Hz); [exact (T4 cid pos a Hin Hz He)
  | intros H; exact (He (HE a H))]. }
split.
{ intros a Ha Hw Hp. apply (U5 a Ha); [lia | exact (T5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_le_gt_dec (sp' - STK') a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a sp') as [Hh|Hh]|].
- exact (U6 a (conj Hl Hh)).
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
Qed.
Lemma cf_aj_pres : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W2) mem2 a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.
Lemma cf_region_kept : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma cf_garr8_aview : forall H H2 (m m2 : word -> option byte) base l,
garr8 SEGS (mrestrict H m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview SEGS H2 m2 a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H2 m2) base l.
Proof.
intros H H2 m m2 base l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hkk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
rewrite (mbyte_of_aview SEGS H H2 m m2 (base + Z.of_nat j + Z.of_nat 0)
  ltac:(apply Hk; cbn [Z.of_nat]; lia)).
exact (Hv 0%nat ltac:(lia)).
Qed.
(* The right to write [q, q + n) in whatever state the caller's journal has reached. *)
Lemma cf_twr : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k2 sp q n,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k2 ->
(forall a, q <= a < q + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
(forall a, q <= a < q + n -> ~ (sp - ESTACK <= a < sp)) ->
twr_ok B STK sp0 FP ly S lyc Sc own W2 mem2 sp q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k2 sp q n HJ Hwr Hsp a Ha.
destruct (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k2 a HJ (Hwr a Ha))
  as [Hpres Hown].
split; [exact (Hwr a Ha)|]. split; [exact Hpres|]. split; [exact Hown | exact (Hsp a Ha)].
Qed.
(* A byte the caller let this call write is a byte of its machine-stack window, of one of its blocks, or of
   one of its side-stack frames (awr_byte_cases); in each case a callee's tcj_kept keeps it unless the callee
   wrote it. *)
Lemma cf_keep_byte : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 m2 md2 k2 STK' sp' (E : Z -> Prop) a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 md2 k2 ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
tcj_kept B STK' lyc Sc W m1 W m2 sp' E ->
~ (sp' - STK' <= a < sp') -> ~ E a ->
aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 m2 md2 k2 STK' sp' E a HJ Hwr (K1 & K2 & K3 & K4 & K5 & K6) Hsp HE.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases _ _ LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 md2 k2 a HJ Hwr)
  as (_ & [ (Hac & Hst) | [ (Happ & b & m & Hin & Hr & _) | (cid & pos & Hin & Hc) ] ]).
- apply K1; [lia | exact Hsp | exact HE].
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin ltac:(lia)).
  replace (b + (a - b)) with a by lia. exact HE.
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  apply (K4 cid pos a Hin'); [ destruct Hc as [(_ & Hz) | (_ & Hz)]; [left | right]; exact Hz | exact HE ].
Qed.
(* The shadow of such a byte, for the second callee's premise after the first callee ran: re-derived from the
   current state for the stack and for a block, and kept by tcj_kept's frame-shadow clause for a frame. *)
Lemma cf_ra_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 m2 md2 k2 STK' sp' (E : Z -> Prop) q n,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 md2 k2 ->
(forall a, q <= a < q + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
tcj_kept B STK' lyc Sc W m1 W m2 sp' E ->
(forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
amem_range q n ->
range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF q n ->
range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 m2 md2 k2 STK' sp' E q n HJ Hwr TK HEsh Ham HRA x Hx.
pose proof TK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases _ _ LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 md2 k2 x HJ (Hwr x Hx))
  as (_ & [ (Hac & Hst) | [ (Happ & b & m & Hin & Hr & _) | (cid & pos & Hin & Hc) ] ]).
- (* the caller's machine-stack window: its shadow is the stack's, zero in every state the journal reaches *)
  pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & _) & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2 ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz. rewrite Elo, Ehi in Hz. rewrite Elo in Hpal. rewrite Ehi in Hpah. unfold page_aligned in Hpal, Hpah.
  set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
  pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl. rewrite Hpal, Z.add_0_r in Dl.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite Hpah, Z.add_0_r in Dh.
  assert (Hl8 : lo mod 8 = 0) by (rewrite Dl; replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia; apply Z_mod_mult).
  assert (Hn8 : (hi - lo) mod 8 = 0) by (rewrite Dl, Dh; replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096 - lo / 4096)) * 8) by lia; apply Z_mod_mult).
  apply (zero_shadow_range _ _ lo (hi - lo) Hl8 Hn8 Hz). lia.
- exact (range_addressable_of_block _ _ LAWS lyc Sc W m2 md2 b m x 1 HAR Hin ltac:(lia) ltac:(lia) x ltac:(lia)).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct Hc as [(Happ & Hz) | (Hsh & _)];
    [| exfalso; unfold amem_range in Ham; lia].
  destruct (frame_al64 _ _ lyc Sc W m2 md2 cid pos HAR Hin') as (Hfa & Hfb & Hf64).
  destruct (frames_bounds _ _ LAWS lyc Sc W m2 md2 cid pos HAR Hin') as (F4 & Fc & _).
  unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
  set (f := frame_addr lyc cid pos) in *. set (fb := fs_frame_bytes cid) in *.
  assert (Hs : shadow_addr f <= shadow_addr x < shadow_addr f + fb / 8).
  { pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod fb 64 ltac:(lia)) as Db.
    rewrite Hfa, Z.add_0_r in Df. rewrite Hfb, Z.add_0_r in Db.
    assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Df at 1; replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (E8b : fb / 8 = 8 * (fb / 64)) by (rewrite Db at 1; replace (64 * (fb / 64)) with (8 * (fb / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold shadow_addr. split.
    - pose proof (Z.div_le_mono f x 8 ltac:(lia) ltac:(lia)). lia.
    - assert (x / 8 < f / 8 + fb / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx.
  assert (HRx : range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF x 1).
  { eapply range_addressable_agree; [| exact (range_addressable_sub _ _ q n x 1 HRA ltac:(lia) ltac:(lia))].
    intros y Hy. assert (Hyx : y = x) by lia. subst y. unfold shadow_of_addr.
    change (SHADOW_OFF + x / 8) with (shadow_addr x).
    apply (K4 cid pos (shadow_addr x) Hin');
      [ right; unfold in_zr; cbn [fst snd]; exact Hs | exact (HEsh _ Hsx) ]. }
  apply HRx. lia.
Qed.

Lemma cf_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 p -> getr regs 11 = w64 B_ROW ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_ctrl_finish -> spZ regs <= sp0 ->
garr8 SEGS (mrestrict (w_H W) memc) (B_ROW + 18) [16; 6; 2] ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (B_ROW + 18) 3 ->
0 < p -> p + 50 <= 2 ^ 47 - 8 ->
st_ok_pi SEGS VAL (EC regs) ss_cf
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ctrl_finish)) memc (seg_rom SEGS)))
/\ sh_ok SEGS cf_Bx cf_SH (EC regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p
HJ H10 H11 Hal16 Hwlo Hwhi HROW HRAR Hp0 Hphi.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_ctrl_finish = 4128) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 35%nat ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR.
pose proof pa_B_ok as HBASE.
pose proof cf_lo_eq as Hclo. pose proof cf_hi_eq as Hchi.
pose proof IMG_LO_B_val as HLOv. pose proof IMG_TOP_B_val as HHIv.
assert (HIl : IMG_LO = IMG_LO_B) by reflexivity.
assert (HIh : IMG_HI = IMG_TOP_B) by reflexivity.
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 B_ROW) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 SB] 0)).
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E35g : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HrowR : IMG_LO_B <= B_ROW /\ B_ROW + 24 <= IMG_TOP_B) by (rewrite <- HIl, <- HIh; lia).
destruct (HROW 0%nat ltac:(cbn; lia)) as [Mr0 _]. destruct (HROW 1%nat ltac:(cbn; lia)) as [Mr1 _].
destruct (HROW 2%nat ltac:(cbn; lia)) as [Mr2 _]. cbn [nth] in Mr0, Mr1, Mr2.
change (Z.of_nat 0) with 0 in Mr0. change (Z.of_nat 1) with 1 in Mr1. change (Z.of_nat 2) with 2 in Mr2.
rewrite Z.add_0_r in Mr0.
replace (B_ROW + 18 + 1) with (B_ROW + 19) in Mr1 by lia.
replace (B_ROW + 18 + 2) with (B_ROW + 20) in Mr2 by lia.
unfold ls_apart in HRg1, HRc35.
split.
- unfold ss_cf. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cf_regions, cf_row, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
      [cbn [sv_denot]; rewrite E35g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E35g) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 cf_Bx SB);
      [cbn [sv_denot cf_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 11%nat B_ROW E11) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ B_ROW 18 1 (SLit 16) 16); [reflexivity | zside | zside | exact Mr0].
      -- apply (chunk_ok_val SEGS E _ B_ROW 19 1 (SLit 6) 6); [reflexivity | zside | zside | exact Mr1].
      -- apply (chunk_ok_val SEGS E _ B_ROW 20 1 (SLit 2) 2); [reflexivity | zside | zside | exact Mr2].
  + apply pairwise_disjoint_of_extents.
    unfold cf_regions, cf_row, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 11%nat B_ROW E11) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E35g) by (pose proof (pa_val_range (A_OBJ 35)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hsp46 HcellR HgcD HgotR HrowR HRg1 HRc35 C1 C3 WS Hstk0 HLOv HHIv HIl HIh. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold cf_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    rewrite Hclo, Hchi.
    revert Hsp46 Hal16 Hp0 Hphi HRal HRlo HRhi HLOv HHIv HIl HIh. clear. unfold SB. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cf_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E cf_Bx 11%nat (B_ROW + 18) 3 B_ROW 18 21 HRAR).
  + unfold U, cf_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 18 21) with 18 in Hx. change (Z.max 18 21) with 21 in Hx.
    unfold SHADOW_OFF. lia.
Qed.

(* tb_ctrl_finish_spec under this section's hypotheses: the walk. *)
Theorem cf_walk : tb_ctrl_finish_spec B.
Proof.
unfold tb_ctrl_finish_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p Bk
HJ HROD Hra Hra4 Hgp Htp H10 H11 Hal16 Hwlo Hwhi HROW HRAR HLB HGB Hp0 Hphi Hpne Hamem Hoff HWR HPSP HRA HHULL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct pa_B_ok as (HB0 & HB1 & HB2).
assert (WS : STK_ctrl_finish = 4128) by reflexivity.
destruct (cf_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p
HJ H10 H11 Hal16 Hwlo Hwhi HROW HRAR ltac:(lia) Hphi) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hwce : alloc_ceiling <= spZ regs - STK_ctrl_finish) by lia.
assert (Hsp64 : spZ regs <= 2 ^ 64) by lia.
remember (EC regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; unfold EC; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_ctrl_finish)) with (Z_to_bv 64 (BASE + AF_ctrl_finish)).
paj_run_tok RUN HS HJ SHOK cf_span;
[ cf_awr sp0 (spZ regs) ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia) |].
(* 0x84054 `not a0,a4; bltu a0,a3`: a0 = ~ (p + 18), a3 = 16, so the trap arm needs ~ (p + 18) <u 16. *)
psrr_branch_tok RUN BR HS SHOK cf_span.
- exfalso.
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    assert (EX10 : ew Ex 10 = Z_to_bv 64 p)
      by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E10);
    rewrite branch_ltu_U, U_SAlu,
      (U_atom_off Ex 10%nat p 18 EX10 ltac:(lia) ltac:(lia)), U_SLit, (U_lit Ex 16 ltac:(lia)) in Hc end.
  cbn [zalu_raw] in Hc.
  replace (zcanon (-1)) with 18446744073709551615 in Hc by (vm_compute; reflexivity).
  rewrite (cf_lxor_m1 (p + 18) ltac:(lia)) in Hc.
  rewrite zcanon_id in Hc by (unfold M64; lia).
  apply Z.ltb_lt in Hc. lia.
- (* --- entry .. 0x84074, the call of reac_ctrl_record_cksum_stamp (a0 = p + 34, a1 = 6) --- *)
  paj_run_tok RUN HS HJ SHOK cf_span; [ cf_awr sp0 (spZ regs) ltac:(cf_usp Usp) |].
  lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    pose (m1 := ms_mem msc);
    assert (HM1 : forall xx : word, ~ (spZ regs - 16 <= bv_unsigned xx < spZ regs) ->
      mrestrict (w_H W) m1 xx = mrestrict (w_H W) memc xx) by (unfold m1; cf_hm Usp) end.
  assert (HAV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) m1 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply cf_aview_eq; apply HM1; rewrite unsigned_lit_small by lia; lia).
  (* the record's five source bytes and their shadow, at the memory the call sees *)
  assert (HLRS : Z.of_nat (length (cf_RS Bk)) = 6 - 1) by (rewrite (cf_RS_len Bk HLB); reflexivity).
  assert (HRSm : garr8 SEGS (mrestrict (w_H W) memc) (p + 34) (map bv_unsigned (cf_RS Bk))).
  { intros j Hj. rewrite length_map, (cf_RS_len Bk HLB) in Hj.
    assert (Hq : nth j (map bv_unsigned (cf_RS Bk)) 0 = nth (16 + j) (map bv_unsigned Bk) 0).
    { rewrite (nth_indep (map bv_unsigned (cf_RS Bk)) 0 (bv_unsigned (Z_to_bv 8 0)))
        by (rewrite length_map, (cf_RS_len Bk HLB); lia).
      rewrite (map_nth bv_unsigned (cf_RS Bk) (Z_to_bv 8 0) j).
      rewrite (nth_indep (map bv_unsigned Bk) 0 (bv_unsigned (Z_to_bv 8 0)))
        by (rewrite length_map, HLB; lia).
      rewrite (map_nth bv_unsigned Bk (Z_to_bv 8 0) (16 + j)).
      unfold cf_RS. rewrite (cf_nth_firstn (skipn 16 Bk) 5) by lia.
      rewrite cf_nth_skipn. reflexivity. }
    rewrite Hq. destruct (HGB (16 + j)%nat ltac:(rewrite length_map, HLB; lia)) as [Hv Hr].
    split; [replace (p + 34 + Z.of_nat j) with (p + 18 + Z.of_nat (16 + j)) by lia; exact Hv | exact Hr]. }
  assert (HRS1 : garr8 SEGS (mrestrict (w_H W) m1) (p + 34) (map bv_unsigned (cf_RS Bk))).
  { apply (cf_garr8_aview (w_H W) (w_H W) memc m1). exact HRSm.
    intros a Ha. rewrite length_map, (cf_RS_len Bk HLB) in Ha. apply HAV1; unfold amem_range in Hamem; lia. }
  assert (HRA1 : range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF (p + 34) 6).
  { assert (Hsub : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 34) 6)
      by (eapply range_addressable_sub; [exact HRA | lia | lia]).
    eapply range_addressable_agree; [| exact Hsub].
    intros a Ha. unfold shadow_of_addr.
    assert (Hd1 : 0 <= a / 8) by (apply Z.div_pos; lia).
    assert (Hd2 : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
    apply HAV1; unfold SHADOW_OFF; lia. }
  (* the registers at the call *)
  lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    prreg HSc (1%bv : bv 5) Rd1; prreg HSc (2%bv : bv 5) Rd2; prreg HSc (3%bv : bv 5) Rd3;
    prreg HSc (4%bv : bv 5) Rd4; prreg HSc (10%bv : bv 5) Rd10; prreg HSc (11%bv : bv 5) Rd11;
    assert (Esp : spZ (ms_regs msc) = spZ regs - 16)
      by (unfold spZ at 1; rewrite Rd2; cf_norm; rewrite Usp; rewrite unsigned_lit_small by lia; lia);
    pmkst HSc end.
  rewrite pa_sigma_reac_ctrl_record_cksum_stamp.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      pose proof (HREC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mm mdx k rg (p + 34) 6 (cf_RS Bk) HJ) as CALL end.
    unfold cfg_at in CALL.
    change (w64 (BASE + AF_reac_ctrl_record_cksum_stamp))
      with (Z_to_bv 64 (BASE + AF_reac_ctrl_record_cksum_stamp)) in CALL.
    apply CALL; clear CALL.
    - rewrite Rd1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite Rd1. rewrite unsigned_lit_small by lia. lia.
    - rewrite Rd3. cf_eq E3.
    - rewrite Rd4. cf_eq E4.
    - rewrite Rd10. cf_val E10.
    - rewrite Rd11. reflexivity.
    - rewrite Esp. replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hal16.
    - rewrite Esp. unfold STK_reac_ctrl_record_cksum_stamp, STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Esp. lia.
    - lia.
    - exact HLRS.
    - exact HRS1.
    - lia.
    - unfold amem_range in *. lia.
    - unfold STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Esp. unfold STK_reac_ctrl_record_cksum_stamp, STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Esp. eapply cf_twr; [exact HJ | |];
      intros a Ha; [ exact (proj1 (HWR a ltac:(lia))) | unfold STK_ctrl_finish, ESTACK in *; lia ].
    - exact HRA1. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HFIN1 & TK1).
  rewrite Esp in TK1. rewrite Rd1. pose proof HJ2 as HJm2.
  (* the block, with the record's checksum in place *)
  assert (HGB1 : garr8 SEGS (mrestrict (w_H W) m1) (p + 18) (map bv_unsigned Bk)).
  { apply (cf_garr8_aview (w_H W) (w_H W) memc m1). exact HGB.
    intros a Ha. rewrite length_map, HLB in Ha. apply HAV1;
    unfold STK_ctrl_finish, ESTACK in *; lia. }
  assert (HBk1 : garr8 SEGS (mrestrict (w_H W) mem2) (p + 18) (map bv_unsigned (cf_B1 Bk))).
  { intros j Hj. rewrite length_map, (cf_B1_len Bk HLB) in Hj.
    rewrite (cf_B1_nth Bk j HLB ltac:(lia)).
    destruct (Nat.eqb_spec j 21) as [->|Hne].
    - assert (Hx : nth 5 (map bv_unsigned (cf_RS Bk ++ [Z_to_bv 8 (RcRec.stampck (cf_RS Bk))])) 0
                 = (- RcFin.rsum Bk 16 5) mod 128).
      { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0)))
          by (rewrite length_map, length_app, (cf_RS_len Bk HLB); cbn [length]; lia).
        rewrite (map_nth bv_unsigned _ (Z_to_bv 8 0) 5).
        rewrite app_nth2 by (rewrite (cf_RS_len Bk HLB); lia).
        rewrite (cf_RS_len Bk HLB). cbn [Nat.sub nth].
        rewrite (cf_stampck Bk HLB), Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        pose proof (Z.mod_pos_bound (- RcFin.rsum Bk 16 5) 128 ltac:(lia)). apply Z.mod_small. lia. }
      destruct (HFIN1 5%nat ltac:(rewrite length_map, length_app, (cf_RS_len Bk HLB); cbn [length]; lia)) as [Hv Hr].
      rewrite Hx in Hv, Hr. split; [replace (p + 18 + Z.of_nat 21) with (p + 34 + Z.of_nat 5) by (cbn; lia); exact Hv
                                   | exact Hr].
    - destruct (HGB1 j ltac:(rewrite length_map, HLB; lia)) as [Hv Hr]. split; [|exact Hr].
      intros kk Hkk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
      assert (Hkeep : aview SEGS (w_H W) mem2 (p + 18 + Z.of_nat j + Z.of_nat 0)
                    = aview SEGS (w_H W) m1 (p + 18 + Z.of_nat j + Z.of_nat 0)).
      { eapply (cf_keep_byte STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 mem2 md2 k
                  STK_reac_ctrl_record_cksum_stamp (spZ regs - 16) (fun a => a = p + 34 + 6 - 1));
        [ exact HJ2
        | exact (proj1 (HWR (p + 18 + Z.of_nat j + Z.of_nat 0) ltac:(cbn [Z.of_nat]; lia)))
        | exact TK1
        | unfold STK_reac_ctrl_record_cksum_stamp, STK_ctrl_finish, ESTACK in *; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia ]. }
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m1 mem2 (p + 18 + Z.of_nat j + Z.of_nat 0) Hkeep).
      exact (Hv 0%nat ltac:(lia)). }
  (* --- 0x84078 .. 0x84094, the tail jump to reac_ctrl_block_cksum_stamp (a0 = p + 18) --- *)
  assert (HGall : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m1)).
  { repeat match goal with
    | Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mC) =>
      first [ exact Hg | eapply mem_grows_trans; [exact Hg |] ]
    end; apply mem_grows_refl. }
  assert (TKA : tcj_kept B STK_ctrl_finish lyc Sc W memc W m1 (spZ regs) (fun a => p + 18 <= a < p + 50)).
  { apply (cf_tcj_of_keep STK_ctrl_finish lyc Sc W memc mdc m1 (spZ regs)
             (fun a => p + 18 <= a < p + 50) HAR Hwce Hsp64).
    - intros a Ha Hn. apply HAV1; unfold STK_ctrl_finish, ESTACK in *; lia.
    - intros a _ _ Hp. exact (apresent_grows (w_H W) memc m1 a HGall Hp).
    - intros a Ha. apply (cf_aj_pres STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 _ k HJ). lia. }
  lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    jafter_call_keep_pi HSc 64%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2 end.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    lazymatch goal with |- region_kept _ ?Ez _ _ _ =>
      apply (cf_region_kept Ez (w_H W) (w_H W) m1 mem2 2%nat (spZ regs) (-16) 0 (-16) 0) end.
    - cf_norm. exact Usp.
    - intros a Ha. apply (proj1 TK1);
      [ unfold STK_ctrl_finish, ESTACK in *; lia
      | unfold STK_reac_ctrl_record_cksum_stamp; lia
      | cbv beta; unfold STK_ctrl_finish, ESTACK in *; lia ].
    - intros a Ha. apply (cf_aj_pres STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k HJ2).
      unfold STK_ctrl_finish, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss3 _ =>
    let v := eval vm_compute in ss3 in change ss3 with v in HS;
    assert (HEIb : img_env VAL A_LIM Ev) by (apply img_env_havoc; [assumption | cbv; lia]);
    assert (Uspb : bv_unsigned (ew Ev 2) = spZ regs) by (cf_norm; exact Usp);
    assert (E1b : ew Ev 1 = getr regs 1) by (cf_norm; exact E1);
    assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ev)
      by (split; [intros nn Hnn; rewrite ew_havoc_old by lia;
                  rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia
                 | cbn [ed ewset havoc extK Eimg]; apply (proj2 HAE)]);
    assert (SHOKb : sh_ok SEGS cf_Bx (@nil shent) Ev (mrestrict (w_H W) mem2)) by constructor
  end.
  paj_run_tok RUN HS HJ2 SHOKb cf_span; [ cf_awr sp0 (spZ regs) ltac:(cf_usp2 Usp) |].
  lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    pose (m3 := ms_mem msc);
    assert (HM3 : forall xx : word, ~ (spZ regs - 16 <= bv_unsigned xx < spZ regs) ->
      mrestrict (w_H W) m3 xx = mrestrict (w_H W) mem2 xx) by (unfold m3; cf_hm Uspb) end.
  assert (HAV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_ctrl_finish <= a < spZ regs) ->
    aview SEGS (w_H W) m3 a = aview SEGS (w_H W) mem2 a)
  by (intros a Ha Hn; apply cf_aview_eq; apply HM3;
      rewrite unsigned_lit_small by lia; unfold STK_ctrl_finish, ESTACK in *; lia).
  assert (HG3 : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) m3)).
  { repeat match goal with
    | Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mC) =>
      first [ exact Hg | eapply mem_grows_trans; [exact Hg |] ]
    end; apply mem_grows_refl. }
  assert (TKB : tcj_kept B STK_ctrl_finish lyc Sc W mem2 W m3 (spZ regs) (fun a => p + 18 <= a < p + 50)).
  { apply (cf_tcj_of_keep STK_ctrl_finish lyc Sc W mem2 md2 m3 (spZ regs)
             (fun a => p + 18 <= a < p + 50) (proj1 HJm2) Hwce Hsp64).
    - exact HAV3.
    - intros a _ _ Hp. exact (apresent_grows (w_H W) mem2 m3 a HG3 Hp).
    - intros a Ha. apply (cf_aj_pres STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m3 _ k HJ2). lia. }
  (* the block's bytes and their shadow at the tail jump *)
  assert (HBk3 : garr8 SEGS (mrestrict (w_H W) m3) (p + 18) (map bv_unsigned (cf_B1 Bk))).
  { apply (cf_garr8_aview (w_H W) (w_H W) mem2 m3). exact HBk1.
    intros a Ha. rewrite length_map, (cf_B1_len Bk HLB) in Ha. apply HAV3;
    unfold STK_ctrl_finish, ESTACK in *; lia. }
  assert (HRA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF (p + 18) 32).
  { eapply (cf_ra_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 mem2 md2 k
              STK_reac_ctrl_record_cksum_stamp (spZ regs - 16) (fun a => a = p + 34 + 6 - 1) (p + 18) 32 HJm2);
    [ intros a Ha; exact (proj1 (HWR a ltac:(lia)))
    | exact TK1
    | intros a Ha; cbv beta; unfold amem_range in Hamem; lia
    | exact Hamem
    | eapply range_addressable_agree; [| exact HRA];
      intros a Ha; unfold shadow_of_addr;
      assert (Hd1 : 0 <= a / 8) by (apply Z.div_pos; lia);
      assert (Hd2 : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia);
      apply HAV1; unfold SHADOW_OFF; lia ]. }
  assert (HRA3 : range_addressable (aview SEGS (w_H W) m3) SHADOW_OFF (p + 18) 32).
  { eapply range_addressable_agree; [| exact HRA2].
    intros a Ha. unfold shadow_of_addr.
    assert (Hd1 : 0 <= a / 8) by (apply Z.div_pos; lia).
    assert (Hd2 : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
    apply HAV3; unfold SHADOW_OFF, STK_ctrl_finish, ESTACK in *; lia. }
  (* the registers at the tail jump *)
  lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    prreg HSc (1%bv : bv 5) Rt1; prreg HSc (2%bv : bv 5) Rt2; prreg HSc (3%bv : bv 5) Rt3;
    prreg HSc (4%bv : bv 5) Rt4; prreg HSc (10%bv : bv 5) Rt10;
    assert (Etsp : spZ (ms_regs msc) = spZ regs)
      by (unfold spZ at 1; rewrite Rt2; cf_norm; exact Usp);
    assert (Etra : getr (ms_regs msc) 1 = getr regs 1) by (rewrite Rt1; cf_norm; exact E1);
    assert (HPT : aregs_preserved regs (ms_regs msc))
      by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SB] HSc);
          [exact HAEb | vm_compute; reflexivity]);
    pmkst HSc end.
  rewrite pa_sigma_reac_ctrl_block_cksum_stamp.
  eapply SRr_mono.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      pose proof (HBLK STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mm mdx k rg (p + 18) (cf_B1 Bk) HJ2) as CALL end.
    unfold cfg_at in CALL.
    change (w64 (BASE + AF_reac_ctrl_block_cksum_stamp))
      with (Z_to_bv 64 (BASE + AF_reac_ctrl_block_cksum_stamp)) in CALL.
    apply CALL; clear CALL.
    - rewrite Etra. exact Hra.
    - unfold raZ. rewrite Etra. exact Hra4.
    - rewrite Rt3. cf_eq E3.
    - rewrite Rt4. cf_eq E4.
    - rewrite Rt10. cf_val E10.
    - rewrite Etsp. exact Hal16.
    - rewrite Etsp. unfold STK_reac_ctrl_block_cksum_stamp, STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Etsp. lia.
    - exact (cf_B1_len Bk HLB).
    - exact HBk3.
    - lia.
    - unfold amem_range in *. lia.
    - unfold STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Etsp. unfold STK_reac_ctrl_block_cksum_stamp, STK_ctrl_finish, ESTACK in *. lia.
    - rewrite Etsp. eapply cf_twr; [exact HJ2 | |];
      intros a Ha; [ exact (proj1 (HWR a ltac:(lia))) | unfold STK_ctrl_finish, ESTACK in *; lia ].
    - exact HRA3. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HFIN2 & TK2).
  rewrite Etsp in TK2.
  split; [reflexivity|]. exists regs4, mem4, md4.
  split; [rewrite Etra; reflexivity|].
  split; [exact HJ4|].
  split; [intros r Hr; rewrite (HP4 r Hr); exact (HPT r Hr)|].
  split; [rewrite cf_fin_eq; exact HFIN2|].
  (* the whole call keeps everything outside its stack window and the caller's 32 bytes *)
  eapply (cf_tcj_compose STK_ctrl_finish STK_reac_ctrl_block_cksum_stamp lyc Sc W memc W m3 W mem4
            (spZ regs) (spZ regs) (fun a => p + 18 <= a < p + 50) (fun a => a = p + 18 + 31));
  [ | exact TK2
  | unfold STK_reac_ctrl_block_cksum_stamp, STK_ctrl_finish, ESTACK in *; lia
  | lia | exact Hwce | exact Hsp64 | intros a Ha; cbv beta in Ha; lia ].
  eapply (cf_tcj_compose STK_ctrl_finish STK_ctrl_finish lyc Sc W memc W mem2 W m3
            (spZ regs) (spZ regs) (fun a => p + 18 <= a < p + 50) (fun a => p + 18 <= a < p + 50));
  [ | exact TKB | lia | lia | exact Hwce | exact Hsp64 | intros a Ha; exact Ha ].
  eapply (cf_tcj_compose STK_ctrl_finish STK_reac_ctrl_record_cksum_stamp lyc Sc W memc W m1 W mem2
            (spZ regs) (spZ regs - 16) (fun a => p + 18 <= a < p + 50) (fun a => a = p + 34 + 6 - 1));
  [ exact TKA | exact TK1
  | unfold STK_reac_ctrl_record_cksum_stamp, STK_ctrl_finish, ESTACK in *; lia
  | lia | exact Hwce | exact Hsp64 | intros a Ha; cbv beta in Ha; lia ].
Qed.
End H.

(* walk_ctrl_finish as lib/B/Prog/GrantBContracts.v states it: hyps_ctrl_finish (RT_LAWS, RT_PALIB, IMG_CTRL_ROW,
   IMG_CTRL_ROW_IMG), then the contracts of reac_ctrl_record_cksum_stamp and reac_ctrl_block_cksum_stamp. No
   contract of an __asan_report_* entry or of reac_box_model_block is taken: this is OBL_finish_report_dead. *)
Theorem pb_ctrl_finish (B : asyms) : walk_ctrl_finish B.
Proof.
unfold walk_ctrl_finish, hyps_ctrl_finish, RT_LAWS, RT_PALIB, IMG_CTRL_ROW, IMG_CTRL_ROW_IMG.
intros (HL & HPL & (HRal & HRlo & HRhi & _ & _ & HRg1 & HRc35 & _) & HRimg) HREC HBLK.
eapply cf_walk; eassumption.
Qed.
Theorem pb_OBL_finish_report_dead (B : asyms) : OBL_finish_report_dead B.
Proof. exact (pb_ctrl_finish B). Qed.
End F.
End D.
