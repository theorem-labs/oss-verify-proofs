(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the leaf walk: the seed at
   the entry, the run, the return) and lib/A/AC8b.v (loops by fuel induction) at c8557374ad2e: the walk of
   syntax_reply_matches on fuzz_command.asan. This file: the prologue (0x8857c to the item loop at 0x885e8), the entry
   facts the statement's premises give, and the theorem. The segments are in syntax_reply_matches_s1.v .. _s7.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/syntax_reply_matches.v, with its module paths and module names changed; 645 of its 702 lines of code are new or changed and 209 lines of the source are left out. *)
(* reac_boxreg_find (fuzz_boxreg.asan 0x816a0, 64 instructions): the contract of the ASan build's code.
   The function takes a 48-byte frame on the machine stack (addi sp,sp,-48). It reads the 6 MAC bytes mac[0..5] one at
   a time, each after the ASan check of its shadow byte (mac_is_zero is inlined in this build); the all-zero MAC
   returns -1. Else it loads n = r->n at r + 280 after the check of that word's shadow byte and, for i = 0 .. n - 1,
   calls bcmp (r + 56 i, mac, 6) through BS___interceptor_trampoline_bcmp (0x41404, the same address as __wrap_bcmp
   in the unstripped image's symbol table); it returns the first i whose result is 0, else -1. It writes nothing
   outside its own frame and the bcmp wrapper's stack window.
   Stack: the own 48-byte frame and 2 * ESTACK below it for the bcmp wrapper (abcmp_realizes asks for 2 * ESTACK of
   present stack below the caller's sp, CONVENTIONS section 4); there is no program callee.
   Read footprint, each byte covered by a premise: the 288-byte registry struct at r, a heap block of the caller
   (In (r, REG_SIZE) (ablocks ..) and its bytes bs; the code reads r + 280 .. r + 283 and the MACs r + 56 i ..
   r + 56 i + 5 for i < n); the 6 MAC bytes M at p (afobj and their bytes); the shadow bytes of both (the
   __asan_report_load1 / __asan_report_load4 branches are refuted by the block's shadow in AR and by afobj's
   range_addressable). The only image reads are the GOT word of the shadow base and the shadow cell, both fixed by
   AR (AR_const_law, lib/Reusable/YG0d.v); the bcmp wrapper's own reads are inside abcmp_realizes.
   Where the MAC lives: every caller passes the harness's local uint8_t mac[6] of LLVMFuzzerTestOneInput
   (fuzz/fuzz_boxreg.c:206), directly (:312, :336, :365) or as reac_boxreg_add's own argument (src/reac_boxreg.c:95).
   It is at offset 0x20 of the harness's 416-byte ASan frame block (0x80190 .. 0x80198: ld a0,0x28(s1);
   addi a0,a0,0x20; sd a0,0x70(s1)), whose shadow byte 4 the harness sets to 6 at its loop top (0x8021c .. 0x80220),
   so the 6 bytes are addressable at every call. That frame block is the __asan_stack_malloc_3 side-stack frame
   (0x7ffbc), a frame in frames S: AR fixes the use-after-return flag cell to 1 (AR_const_law), so the harness takes
   the fake-stack path and the MAC is not on the caller's machine stack. Hence the premise afobj SEGS B ly S W mem p 6,
   the form of grant's caller frame objects (fuzz_grant lib/A/Prog/CtrlChecksumVerify.v).
   Hazards: the struct is 288 bytes (rows 0..280, n at +280, fabric at +284; box i's MAC at 56 i); n <= 5 (Pau's
   boxreg_B1) keeps every bcmp range inside the block (box 5 would be r + 280 .. r + 285); the bcmp entry is the
   trampoline at 0x41404 (__wrap_bcmp is an alias of the same address), stated with abcmp_realizes, not
   amemcmp_realizes; no f* or csr instruction occurs in the 64 instructions (capstone scan), so the fixed {fx} is
   sound. The old walk's runtime cells (asan_cells, REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254/255, app_mem (p + 7))
   leave the statement: they are premises of the runtime hypothesis, not of this function.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReacBoxregFind.v) calls mac_is_zero as a function, has an
   80-byte frame and adds UBSan traps on r (null, alignment), on the box index (i = 5) and on pointer overflow; the
   result is the same.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_find_c.v find_result, lib/Prog/Boxreg.v boxreg_B1),
   used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
(* REG_SIZE, the size of struct reac_boxreg, is ReacBoxregInit's. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_find_c.
(* The walk layer (a Theorem Labs lane, 96ab2dc6c23): the engine's tactics and the frame / call lemmas the walk uses. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep BoxPaLib YC1g YC1h YC4b YC45 YC81 YC85 BoxFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 48-byte frame and 2 * ESTACK below it for
   the bcmp wrapper. *)
Definition A_reac_boxreg_findP : Z := BASE + AF_reac_boxreg_find.
Definition REAC_BOXREG_FIND_STK : Z := 48 + 2 * ESTACK.
Section h.
Variable B : asyms.
Definition treac_boxreg_find_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r p : Z) (bs M : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_FIND_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) /\
(forall i, 0 <= i < 6 ->
  aview SEGS (w_H W') mem' (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) /\
exists z, getr regs' 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z).
Definition treac_boxreg_find_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte),
afn_pre SEGS B REAC_BOXREG_FIND_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p ->
In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
(forall i, 0 <= i < 6 ->
  aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (cfg_at SEGS A_reac_boxreg_findP regs mem md) (treac_boxreg_find_post regs ly S W mem md r p bs M).
(* ---- The walk (a Theorem Labs lane, rule 24: a re-walk; the old walk is 67b70ae1ec3:lib/A/Prog/reac_boxreg_find.v). ----
   Stops of the code (WALK-PLANS.md section 2): the six iterations of the inlined mac_is_zero (0x816dc .. 0x81718),
   each with the shadow check of its MAC byte (the harness's 0x06 shadow byte: the slow path 0x8170c .. 0x81710
   returns to the load; the engine's shadow tokens take it from fnd_SH); then the check of n's shadow at r + 280
   (0 for the whole block) and the scan 0x81740 .. 0x81764, one bcmp call per box i < n. The walk runs the code
   symbolically up to the n test (blez at 0x81738), forgets the registers the MAC loop leaves (the merge step of
   pb_reac_boxreg_find: fnd_ss_scan is the same state on all six paths), and walks the scan once per value
   n = 0 .. 5 (Pau's boxreg_B1), one bcmp contract per call (fnd_bcmp). *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* Model facts about the registry bytes bs and the MAC bytes M. *)
Lemma fnd_bsub_nth : forall (bs : list byte) (k n : Z) (j : nat), 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  (j < Z.to_nat n)%nat -> nth j (Boxreg.bsub bs k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) bs (Z_to_bv 8 0).
Proof.
intros bs k n j Hk Hn Hkn Hj. unfold Boxreg.bsub. rewrite nth_firstn.
replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
apply nth_skipn.
Qed.
Lemma fnd_n_bytes : forall bs, length bs = 288%nat -> Boxreg.boxreg_B1 bs ->
  forall k, (k < 4)%nat -> YG0f.le_byte (Boxreg.bx_n bs) 4 k = bv_unsigned (nth (280 + k) bs (Z_to_bv 8 0)).
Proof.
intros bs HL HB k Hk.
assert (Hk4 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%nat) by lia.
assert (E : Boxreg.bsub bs 280 4 = [nth 280 bs (Z_to_bv 8 0); nth 281 bs (Z_to_bv 8 0); nth 282 bs (Z_to_bv 8 0);
  nth 283 bs (Z_to_bv 8 0)]).
{ apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  - rewrite Boxreg.bsub_length by lia. reflexivity.
  - intros j Hj. rewrite Boxreg.bsub_length in Hj by lia. change (Z.to_nat 4) with 4%nat in Hj.
    rewrite (fnd_bsub_nth bs 280 4 j) by lia. change (Z.to_nat 280) with 280%nat.
    destruct j as [|[|[|[|j]]]]; [reflexivity..|lia]. }
unfold Boxreg.boxreg_B1, Boxreg.bx_n, Boxreg.rd4 in *. rewrite E in *.
rewrite Bytes.bytes_le_to_Z_le_val in *. cbn [map Bytes.le_val] in *.
pose proof (bv_unsigned_in_range 8 (nth 280 bs (Z_to_bv 8 0))) as R0.
pose proof (bv_unsigned_in_range 8 (nth 281 bs (Z_to_bv 8 0))) as R1.
pose proof (bv_unsigned_in_range 8 (nth 282 bs (Z_to_bv 8 0))) as R2.
pose proof (bv_unsigned_in_range 8 (nth 283 bs (Z_to_bv 8 0))) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
assert (Hg : bv_unsigned (nth (280 + k) bs (Z_to_bv 8 0)) =
  match k with O => bv_unsigned (nth 280 bs (Z_to_bv 8 0)) | 1%nat => bv_unsigned (nth 281 bs (Z_to_bv 8 0))
  | 2%nat => bv_unsigned (nth 282 bs (Z_to_bv 8 0)) | _ => bv_unsigned (nth 283 bs (Z_to_bv 8 0)) end)
  by (destruct Hk4 as [-> | [-> | [-> | ->]]]; reflexivity).
rewrite Hg. clear Hg.
revert HB R0 R1 R2 R3.
generalize (bv_unsigned (nth 280 bs (Z_to_bv 8 0))) as b0.
generalize (bv_unsigned (nth 281 bs (Z_to_bv 8 0))) as b1.
generalize (bv_unsigned (nth 282 bs (Z_to_bv 8 0))) as b2.
generalize (bv_unsigned (nth 283 bs (Z_to_bv 8 0))) as b3.
intros b3 b2 b1 b0 HB R0 R1 R2 R3.
assert (Hs : bv_swrap 32 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) = b0 /\ b1 = 0 /\ b2 = 0 /\ b3 = 0).
{ revert HB. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648. intros HB. Z.div_mod_to_equations. lia. }
destruct Hs as (Hs & -> & -> & ->). rewrite Hs. unfold YG0f.le_byte.
rewrite (Z.mod_small b0) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct Hk4 as [-> | [-> | [-> | ->]]]; cbn [Z.of_nat Z.mul Nat.add].
- change (2 ^ 0) with 1. rewrite Z.div_1_r. apply Z.mod_small. lia.
- rewrite Z.div_small by lia. reflexivity.
- rewrite Z.div_small by lia. reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma fnd_mac_iff : forall bs M i, length bs = 288%nat -> length M = 6%nat -> 0 <= i <= 4 ->
  (Boxreg.bx_mac bs i = M <->
   forall j, 0 <= j < 6 -> nth (Z.to_nat (56 * i + j)) bs (Z_to_bv 8 0) = nth (Z.to_nat j) M (Z_to_bv 8 0)).
Proof.
intros bs M i HL HM Hi. unfold Boxreg.bx_mac. split.
- intros <- j Hj. rewrite (fnd_bsub_nth bs (56 * i) 6 (Z.to_nat j)) by lia. f_equal. lia.
- intros H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  + rewrite Boxreg.bsub_length by lia. rewrite HM. reflexivity.
  + intros j Hj. rewrite Boxreg.bsub_length in Hj by lia.
    rewrite (fnd_bsub_nth bs (56 * i) 6 j) by lia.
    replace (Z.to_nat (56 * i) + j)%nat with (Z.to_nat (56 * i + Z.of_nat j)) by lia.
    rewrite (H (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma fnd_zero6 : forall M, length M = 6%nat ->
  (forall j, (j < 6)%nat -> bv_unsigned (nth j M (Z_to_bv 8 0)) = 0) -> M = Boxreg.zero6.
Proof.
intros M HL H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
- rewrite HL. reflexivity.
- intros j Hj. rewrite HL in Hj. unfold Boxreg.zero6. rewrite nth_repeat. apply bv_eq. rewrite (H j Hj). reflexivity.
Qed.
Lemma fnd_nzero6 : forall M j, bv_unsigned (nth j M (Z_to_bv 8 0)) <> 0 -> M <> Boxreg.zero6.
Proof. intros M j H E. subst M. unfold Boxreg.zero6 in H. rewrite nth_repeat in H. apply H. reflexivity. Qed.
Lemma fnd_vm1 : forall H (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Ha. destruct (aview_byte SEGS H mem a v Ha) as (b & Hb & -> & _).
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, Hb. f_equal.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
assert (HL : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x).
{ intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small x (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia. }
apply bv_eq. rewrite Z_to_bv_unsigned. rewrite HL by lia. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity.
Qed.
(* The symbolic state at the first slot. Atoms: 32 the shadow base, 33 n (the word r + 280), 34 .. 39 the MAC bytes. *)
Definition fnd_SB : Z := 0x7fff8000.
Definition fnd_Bx : sv := SOff 32 0.
Definition fnd_Bspan : Z * Z := (fnd_SB, fnd_SB + 2 ^ 44 - 1).
Definition fnd_mchunk (j : nat) : YP09.chunk := YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (34 + j) 0)).
Definition fnd_rregion : YP09.region := YP09.mkRegion (Some 10%nat) 0 288 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition fnd_mregion : YP09.region := YP09.mkRegion (Some 11%nat) 0 6 0 0 (map fnd_mchunk (seq 0 6)).
Definition fnd_regions : smem := [stack_region 48; got_regionP; bcell_regionP 32; fnd_rregion; fnd_mregion].
Definition fnd_facts : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (10%nat, mkAF 4096 140737479966720 4) ::
    (11%nat, mkAF 4096 140737479966720 3) :: (32%nat, mkAF fnd_SB fnd_SB 0) :: (33%nat, mkAF 0 5 0) ::
    map (fun j => ((34 + j)%nat, mkAF 0 255 0)) (seq 0 6)) [] [].
Definition ss_fnd : sstate := mkSS AF_reac_boxreg_find sr_atoms fnd_regions None fnd_facts.
Definition fnd_SH : list shent := [mkSHE 10 0 288; mkSHE 11 0 6].
Definition fnd_mb (M : list byte) (j : nat) : Z := bv_unsigned (nth j M (Z_to_bv 8 0)).
Definition fnd_extra (bs M : list byte) : list word :=
  map (Z_to_bv 64) (fnd_SB :: Boxreg.bx_n bs :: map (fnd_mb M) (seq 0 6)).
Definition fnd_E (regs : bvmap 5 word) (bs M : list byte) : env := Eimg (Ereg regs (fnd_extra bs M)).
Lemma fnd_ew : forall regs bs M,
  ew (fnd_E regs bs M) 32 = Z_to_bv 64 fnd_SB /\ ew (fnd_E regs bs M) 33 = Z_to_bv 64 (Boxreg.bx_n bs) /\
  (forall j, (j < 6)%nat -> ew (fnd_E regs bs M) (34 + j) = Z_to_bv 64 (fnd_mb M j)).
Proof.
intros regs bs M. split; [reflexivity|]. split; [reflexivity|].
intros j Hj. destruct j as [|[|[|[|[|[|j]]]]]]; [reflexivity..|lia].
Qed.
Lemma fnd_mb_range : forall M j, 0 <= fnd_mb M j < 256.
Proof. intros M j. unfold fnd_mb. pose proof (bv_unsigned_in_range 8 (nth j M (Z_to_bv 8 0))) as R. exact R. Qed.
Lemma fnd_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte),
  afn_pre SEGS B REAC_BOXREG_FIND_STK ly S W regs mem md ch ->
  getr regs 10 = w64 r -> getr regs 11 = w64 p ->
  In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < REG_SIZE ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs ->
  afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
  (forall i, 0 <= i < 6 ->
    aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
  st_ok_pi SEGS VAL (fnd_E regs bs M) ss_fnd
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_reac_boxreg_findP) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS fnd_Bx fnd_SH (fnd_E regs bs M) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r p bs M HPRE H10 H11 Hin HL Hbs HB1 HFO HLM HM.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_FIND_STK = 8240) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Hrimg.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md r REG_SIZE cid pos HAR Hin Hfin) as Hsep.
change (req_size REG_SIZE) with 288 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hpm.
assert (HN : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
rewrite restrict_mkst_fx.
destruct (fnd_ew regs bs M) as (E32 & E33 & EM).
set (E := fnd_E regs bs M) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fnd_extra bs M)) n)
  by (intros n Hn; subst E; unfold fnd_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold fnd_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold fnd_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HUB : U E fnd_Bx = SHADOW_OFF) by (unfold fnd_Bx; rewrite (U_atom E 32 fnd_SB E32) by (unfold fnd_SB; lia); reflexivity).
pose proof (pa_val_range (A_OBJ 1)) as Rg1. pose proof (pa_val_range (A_OBJ 12)) as Rg12.
split.
- unfold ss_fnd, A_reac_boxreg_findP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold fnd_regions, stack_region, got_regionP, bcell_regionP, fnd_rregion, fnd_mregion.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 fnd_Bx fnd_SB);
      [cbn [sv_denot fnd_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold fnd_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (Boxreg.bx_n bs));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      apply val_mem_of_rd32. intros k Hk. rewrite (fnd_n_bytes bs HL HB1 k Hk).
      replace (r + 280 + Z.of_nat k) with (r + (280 + Z.of_nat k)) by lia. rewrite Hbs by (unfold REG_SIZE; lia).
      do 3 f_equal. lia.
    * rewrite (VB 11%nat p E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      unfold fnd_mchunk.
      apply (chunk_ok_val SEGS E _ p (Z.of_nat j) 1 (SOff (34 + j) 0) (fnd_mb M j)).
      -- cbn [sv_denot]. rewrite (EM j) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- pose proof (fnd_mb_range M j). zside.
      -- zside.
      -- apply fnd_vm1. rewrite HM by lia. unfold fnd_mb. rewrite Nat2Z.id. reflexivity.
  + apply pairwise_disjoint_of_extents.
    unfold fnd_regions, stack_region, got_regionP, bcell_regionP, fnd_rregion, fnd_mregion, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
    rewrite (VB 10%nat r E10) by lia. rewrite (VB 11%nat p E11) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    revert Hslo Hshi H47 Hceil Hf4096 Hfceil Hflo Hfhi Hfimg Hrimg Hsep Hr4096 Hrceil C1 C3 WS Hstk0 HcellR HgcD HgotR.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [fnd_facts f_atoms atoms_ok map seq app Nat.add].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
      revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 4) with 16;
      revert Hr16 Hr4096 Hrceil C1; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E11, unsigned_lit_small by lia; change (2 ^ 3) with 8;
      revert Hp8 Hf4096 Hfceil Hflo Hfhi C1; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold fnd_SB; lia);
      rewrite Z.pow_0_r, Z.mod_1_r; unfold fnd_SB; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
      rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    repeat match goal with
    | |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2];
        let j := eval vm_compute in (n - 34)%nat in
        let Ej := fresh "Ej" in pose proof (EM j ltac:(lia)) as Ej; cbn [Nat.add] in Ej;
        rewrite Ej; rewrite unsigned_lit_small by (pose proof (fnd_mb_range M j); lia);
        rewrite Z.pow_0_r, Z.mod_1_r; pose proof (fnd_mb_range M j); lia|]
    end.
    exact I.
- unfold sh_ok, fnd_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E fnd_Bx 10 r 288 r 0 288).
    * apply (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZE r 288 HAR Hin); change (req_size REG_SIZE) with 288; lia.
    * exact HUB.
    * rewrite (U_atom E 10 r E10) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. revert Hria Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E fnd_Bx 11 p 6 p 0 6 HRA).
    * exact HUB.
    * rewrite (U_atom E 11 p E11) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
(* The post-condition from the journal at the return: the registry bytes and the MAC bytes are kept (FP = [], the
   function writes only its own frame and the bcmp window). *)
Lemma fnd_ret : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte)
  (regsF : bvmap 5 word) memF mdF (z : Z),
  afn_pre SEGS B REAC_BOXREG_FIND_STK ly S W regs mem md ch ->
  In (r, REG_SIZE) (ablocks B ly S) ->
  (forall i, 0 <= i < REG_SIZE ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  afobj SEGS B ly S W mem p 6 ->
  (forall i, 0 <= i < 6 ->
    aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
  ajournal SEGS B REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  aregs_preserved regs regsF -> getr regsF 10 = w64 z -> reac_boxreg_find_c.find_result bs M z ->
  treac_boxreg_find_post regs ly S W mem md r p bs M W
    (mkCfg (YK11.mkst regsF (getr regs 1) memF (YK11.seg_rom SEGS)) mdF).
Proof.
intros ly S W regs mem md ch r p bs M regsF memF mdF z HPRE Hin Hbs HFO HM HJ HP H10 HR.
pose proof HFO as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & F4 & _).
unfold treac_boxreg_find_post, apost_base. exists ly, S, regsF, memF, mdF.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ intros i Hi. rewrite <- (Hbs i Hi). apply (F2 r REG_SIZE i Hin Hin).
  - change (req_size REG_SIZE) with 288. unfold REG_SIZE in Hi. lia.
  - intros X. exact (inFP_nil _ X). }
split.
{ intros i Hi. rewrite <- (HM i Hi). apply (F4 cid pos (p + i) Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - intros X. exact (inFP_nil _ X). }
exists z. split; [exact H10 | exact HR].
Qed.
(* One call bcmp (r + 56 i, p, 6) through the trampoline (abcmp_realizes, CONVENTIONS section 4): both ranges are
   readable, addressable and outside the wrapper's 2 * ESTACK window below sp - 48; the result is 0 iff box i's MAC
   is M (lib/Prog/Boxreg.v bx_mac). *)
Lemma fnd_bcmp : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte)
  (regsT : bvmap 5 word) memT mdT (i : Z) (raw : word),
  afn_pre SEGS B REAC_BOXREG_FIND_STK ly S W regs mem md ch ->
  In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall k, 0 <= k < REG_SIZE ->
    aview SEGS (w_H W) mem (r + k) = Some (bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0)))) ->
  afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
  (forall k, 0 <= k < 6 ->
    aview SEGS (w_H W) mem (p + k) = Some (bv_unsigned (nth (Z.to_nat k) M (Z_to_bv 8 0)))) ->
  ajournal SEGS B REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
  0 <= i <= 4 ->
  spZ regsT = spZ regs - 48 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 (r + 56 * i) -> getr regsT 11 = w64 p -> getr regsT 12 = w64 6 ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) memT (YK11.seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
    c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = v /\ (v = w64 0 <-> Boxreg.bx_mac bs i = M) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - 2 * ESTACK <= a < spZ regs - 48) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros ly S W regs mem md ch r p bs M regsT memT mdT i raw HPRE Hin HL Hbs HFO HLM HM HJT Hi
  Qsp Qgp Qtp Q10 Q11 Q12 Qra Hraw.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
pose proof HJT as (HART & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & F4 & _).
assert (WS : REAC_BOXREG_FIND_STK = 8240) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.
assert (KR : forall k, 0 <= k < 288 ->
  aview SEGS (w_H W) memT (r + k) = Some (bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0)))).
{ intros k Hk. rewrite <- (Hbs k ltac:(unfold REG_SIZE; lia)). apply (F2 r REG_SIZE k Hin Hin).
  - change (req_size REG_SIZE) with 288. lia.
  - intros X. exact (inFP_nil _ X). }
assert (KM : forall k, 0 <= k < 6 ->
  aview SEGS (w_H W) memT (p + k) = Some (bv_unsigned (nth (Z.to_nat k) M (Z_to_bv 8 0)))).
{ intros k Hk. rewrite <- (HM k Hk). apply (F4 cid pos (p + k) Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - intros X. exact (inFP_nil _ X). }
assert (Usp : spZ regsT = spZ regs + -48) by lia.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W regsT memT
    REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md [] ly S mdT 0 (r + 56 * i) p 6 (-48) raw HJT).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite Hes, WS. lia.
  - exact Qgp.
  - exact Qtp.
  - exact Qra.
  - exact Hraw.
  - intros a Ha. split.
    + replace a with (r + (a - r)) by lia. rewrite (KR (a - r)) by lia. discriminate.
    + rewrite Qsp, Hes. lia.
  - intros a Ha. split.
    + replace a with (p + (a - p)) by lia. rewrite (KM (a - p)) by lia. discriminate.
    + rewrite Qsp, Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - apply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE _ _ HART Hin);
      change (req_size REG_SIZE) with 288; lia.
  - apply amem_range_high; [lia | | lia].
    revert Happ Hflo Hfhi. clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE _ _ HART Hin);
      change (req_size REG_SIZE) with 288; lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE _ _ HART Hin);
      change (req_size REG_SIZE) with 288; lia.
  - apply (range_addressable_entry_frame SEGS B LAWS REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md []
      ly S W memT mdT 0 cid pos p 6 HJT Hfin Hcid); [lia | lia | exact Hfal | | exact HAR | exact HRA].
    intros x X. exfalso. exact (inFP_nil _ X).
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W memT mdT cid pos p 6 HART Hfin); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
split.
{ rewrite Hcmp, (fnd_mac_iff bs M i HL HLM Hi). split.
  - intros X j Hj. pose proof (X j Hj) as Xj.
    replace (r + 56 * i + j) with (r + (56 * i + j)) in Xj by lia.
    rewrite (KR (56 * i + j)) in Xj by lia. rewrite (KM j Hj) in Xj.
    injection Xj as Xj. apply bv_eq. exact Xj.
  - intros X j Hj. replace (r + 56 * i + j) with (r + (56 * i + j)) by lia.
    rewrite (KR (56 * i + j)) by lia. rewrite (KM j Hj). rewrite (X j Hj). reflexivity. }
split; [|exact Hpr2].
intros a Ha Hna. apply Hfr; [exact Ha|]. lia.
Qed.
(* The scan's test of the bcmp result after a call that left the caller-saved registers in atoms k .. k + 15
   (ss_after_call): a0 is atom k + 4. *)
Lemma fnd_br_a0 : forall E (k : nat) (regs2 : bvmap 5 word) b,
  branch_taken BC_EQ (sv_denot (havoc E k (map (getr regs2) CLOB)) (SOff (k + 4) 0))
    (sv_denot (havoc E k (map (getr regs2) CLOB)) (SLit 0)) = b ->
  (b = true <-> getr regs2 10 = w64 0).
Proof.
intros E k regs2 b Hb. rewrite branch_eq_U in Hb. rewrite U_lit in Hb by lia. rewrite U_SOff in Hb.
assert (Hw : ew (havoc E k (map (getr regs2) CLOB)) (k + 4) = getr regs2 10).
{ unfold havoc. cbn [ew]. replace (k + 4 <? k)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + 4 - k)%nat with 4%nat by lia. reflexivity. }
rewrite Hw, Z.add_0_r in Hb. pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as R.
change (bv_modulus 64) with (2 ^ 64) in R. rewrite zcanon_id in Hb by (unfold M64; lia).
subst b. split.
- intros X. apply Z.eqb_eq in X. apply bv_eq. rewrite X. reflexivity.
- intros X. rewrite X. reflexivity.
Qed.
(* The state at the n test (blez s3, 0x81738) after the MAC loop, with the six registers the loop leaves (a0 .. a5)
   in atoms 600 .. 605: s0 = p, s1 = r, s2 = -1, s3 = n (atom 33), the six saved registers in the frame. *)
Definition fnd_scan_stack : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0
    [YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition fnd_scan_regs : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-48); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 11 0; SOff 10 0;
   SOff 600 0; SOff 601 0; SOff 602 0; SOff 603 0; SOff 604 0; SOff 605 0; SOff 16 0; SOff 17 0;
   SLit 18446744073709551615; SOff 33 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0;
   SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition fnd_scan_fa : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
   (11%nat, mkAF 4096 140737479966720 3); (33%nat, mkAF 0 5 0)].
Definition fnd_ss_scan : sstate := mkSS (AF_reac_boxreg_find + 0x98) fnd_scan_regs [fnd_scan_stack] None (mkFacts fnd_scan_fa [] []).
Local Ltac fnd_envok HAE :=
  split; [intros nn Hnn; repeat first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia];
          exact (proj1 HAE nn Hnn)
         | cbn [havoc ewset ed]; exact (proj2 HAE)].
Local Ltac fnd_awr Usp :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | repeat (rewrite ew_havoc_old by lia); rewrite Usp; lia
  | cbn [YP09.r_wlo]; cbv [REAC_BOXREG_FIND_STK ESTACK]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ].
(* A return of the scan: the post-condition from the journal (fnd_ret), the callee-saved registers from the
   symbolic state, a0 = z. *)
Local Ltac fnd_leaf z Hz :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H ?W) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HAE : env_agree 32 (Ereg ?regs ?extra) _, Hra : YK0s.ret_ok (getr ?regs 1), E1 : ew _ 1 = getr ?regs 1 |- _ =>
  let R1 := fresh "R1" in let R10 := fresh "R10" in
  prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat; cbn [ms_regs ms_mem];
  rewrite R1, E1, Hra;
  eapply (fnd_ret _ _ W regs _ _ _ _ _ _ _ _ _ _ z ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
    ltac:(eassumption) ltac:(eassumption));
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs extra HS); [fnd_envok HAE | vm_compute; reflexivity]
  | rewrite R10; apply bv_eq; reflexivity
  | Hz ]
  end.
Local Ltac fnd_ne_cases j :=
  let Hjj := fresh "Hjj" in assert (Hjj : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia;
  destruct Hjj as [-> | [-> | [-> | [-> | ->]]]]; first [assumption | lia].
(* The scan of the boxes 0 .. n - 1 (n = 0 .. 5): one call of bcmp per box. *)
Lemma fnd_scan : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte) E ms mdc extra,
  afn_pre SEGS B REAC_BOXREG_FIND_STK ly S W regs mem md ch ->
  In (r, REG_SIZE) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < REG_SIZE ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs ->
  afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
  (forall i, 0 <= i < 6 ->
    aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
  M <> Boxreg.zero6 ->
  img_env VAL A_LIM E -> env_agree 32 (Ereg regs extra) E ->
  ew E 10 = Z_to_bv 64 r -> ew E 11 = Z_to_bv 64 p -> ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs) ->
  st_ok_pi SEGS VAL E fnd_ss_scan (restrict (w_H W) ms) ->
  ajournal SEGS B REAC_BOXREG_FIND_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) mdc 0 ->
  SRr SEGS W (mkCfg ms mdc) (treac_boxreg_find_post regs ly S W mem md r p bs M).
Proof.
intros ly S W regs mem md ch r p bs M E ms mdc extra HPRE Hin HL Hbs HB1 HFO HLM HM HNZ HEI HAE E10 E11 E33 HS HJ.
pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_FIND_STK = 8240) by reflexivity.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as R. change (bv_modulus 5) with 32 in R.
  rewrite (proj1 HAE n ltac:(lia)). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
change (req_size REG_SIZE) with 288 in *.
pose proof HB1 as HN. unfold Boxreg.boxreg_B1 in HN.
remember (Boxreg.bx_n bs) as n eqn:Hn.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) by lia.
clear HB1.
destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]];
lazymatch type of E33 with ew _ _ = Z_to_bv 64 ?c =>
  pose proof (st_ok_pi_add_fact E _ _ 33 (mkAF c c 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS0
end; clear HS; rename HS0 into HS.
all: let rec loop i k :=
  paj_run_shc RUNP RUNC HS HJ; [fnd_awr Usp|];
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ssx _ |- _ =>
    let why := eval vm_compute in (sym_step_pi pl_tpi ssx) in
    lazymatch why with
    | PStop (SR_branch _ _ _) =>
      psrr_branch_pi RUNP BR HS;
      [ exfalso; rewrite branch_ne_U, U_SOff, U_lit in Hc by lia; repeat (rewrite ew_havoc_old in Hc by lia);
        rewrite E33, unsigned_lit_small in Hc by lia; vm_compute in Hc; discriminate Hc
      | clear Hc; loop i k ]
    | _ =>
      fnd_leaf (-1) ltac:(right; right; split; [exact HNZ | split; [reflexivity |
        intros j Hj; rewrite <- Hn in Hj; fnd_ne_cases j]])
    end
  | HS : st_ok _ ?Ex _ (restrict (w_H _) ?msx) |- _ =>
    let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
    let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
    prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
    prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
    pmkst HS;
    eapply SRr_bind;
    [ eapply (fnd_bcmp ly S W regs mem md ch r p bs M (ms_regs msx) (ms_mem msx) _ i _ HPRE Hin HL Hbs HFO HLM HM HJ);
      [ lia
      | unfold spZ at 1; rewrite Rsp, Usp; rewrite unsigned_lit_small; lia
      | rewrite Rgp; exact E3
      | rewrite Rtp; exact E4
      | rewrite Ra0, E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia
      | rewrite Ra1, E11; reflexivity
      | rewrite Ra2; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity] ]
    | let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in let v := fresh "v" in
      let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in
      let Hfr2 := fresh "Hfr" in let Hpres2 := fresh "Hpres" in
      cbv beta; intros ? ? _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2);
      clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp;
      let HS2 := fresh "HS2" in
      jafter_call_keep_hi HS k regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
      match type of HS2 with ?Q -> _ =>
        let HQ := fresh "HQ" in
        assert (HQ : Q);
        [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
          eapply (region_kept_aview Ex (w_H W) _ mem2 2%nat (spZ regs));
          [ repeat (rewrite ew_havoc_old by lia); exact Usp
          | intros aa Haa; apply Hfr2; cbv [ESTACK]; lia
          | exact Hpres2 ]
        | specialize (HS2 HQ); clear HQ ] end;
      clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
      let HEI2 := fresh "HEI" in
      pose proof (img_env_havoc_hi Ex k (map (getr regs2) CLOB) ltac:(eassumption) ltac:(cbv; lia)) as HEI2;
      clear HJ; rename HJ2 into HJ;
      paj_run_shc RUNP RUNC HS HJ; [fnd_awr Usp|];
      psrr_branch_pi RUNP BR HS;
      [ let Hz := fresh "Hz" in
        assert (Hz : Boxreg.bx_mac bs i = M)
          by (apply Hcmp; rewrite <- Hv; apply (fnd_br_a0 _ k regs2 _ Hc); reflexivity);
        paj_run_shc RUNP RUNC HS HJ; [fnd_awr Usp|];
        fnd_leaf i ltac:(right; left; split; [exact HNZ | split; [rewrite <- Hn; lia |
          split; [exact Hz | intros j Hj; fnd_ne_cases j]]])
      | let Hz := fresh "HNE" in
        assert (Hz : Boxreg.bx_mac bs i <> M)
          by (intros X; apply (proj2 Hcmp) in X; rewrite <- Hv in X; apply (fnd_br_a0 _ k regs2 _ Hc) in X;
              discriminate);
        clear Hc Hv Hcmp;
        let i' := eval vm_compute in (i + 1) in let k' := eval vm_compute in (k + 16)%nat in
        loop i' k' ] ]
  end in loop 0 512%nat.
Qed.
(* A MAC byte test (bnez a4, 0x816f0): the branch condition as a fact about the byte. *)
Local Ltac fnd_macfact :=
  lazymatch goal with Hc : branch_taken BC_NE (sv_denot ?Ex (SOff ?n 0)) (sv_denot ?Ex (SLit 0)) = _,
    EM : forall j, (j < 6)%nat -> ew _ (34 + j) = Z_to_bv 64 (fnd_mb ?M j) |- _ =>
  let j := eval vm_compute in (n - 34)%nat in
  let Ej := fresh "Ej" in
  assert (Ej : ew Ex n = Z_to_bv 64 (fnd_mb M j))
    by (repeat (rewrite ew_ewset_other by lia); exact (EM j ltac:(lia)));
  rewrite branch_ne_U, (U_atom Ex n _ Ej ltac:(pose proof (fnd_mb_range M j); lia)), U_lit in Hc by lia;
  clear Ej;
  let H := fresh "HMb" in
  first [ apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc ]; rename Hc into H
  end.
Theorem pb_reac_boxreg_find : treac_boxreg_find_spec.
Proof.
unfold treac_boxreg_find_spec.
intros ly S W regs mem md ch r p bs M HPRE H10 H11 Hin HL Hbs HB1 HFO HLM HM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (fnd_entry ly S W regs mem md ch r p bs M HPRE H10 H11 Hin HL Hbs HB1 HFO HLM HM) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_FIND_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (fnd_ew regs bs M) as (E32 & E33 & EM).
remember (fnd_E regs bs M) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fnd_extra bs M)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fnd_extra bs M)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 A_reac_boxreg_findP) with (Z_to_bv 64 A_reac_boxreg_findP).
let zero_leaf := idtac;
  fnd_leaf (-1) ltac:(left; split; [|reflexivity]; apply fnd_zero6; [exact HLM|];
    intros j Hj; destruct j as [|[|[|[|[|[|j]]]]]]; [..|lia]; unfold fnd_mb in *; assumption) in
let merge := idtac;
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H _) ?msx),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  pmkst HS;
  let HS2 := fresh "HS2" in
  jafter_stretch_keep_hi HS 600%nat (ms_regs msx) (mrestrict (w_H W) (ms_mem msx))
    [(10%bv : bv 5); (11%bv : bv 5); (12%bv : bv 5); (13%bv : bv 5); (14%bv : bv 5); (15%bv : bv 5)]
    6124 [0%nat] HS2;
  specialize (HS2 (fun _ _ => eq_refl));
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q);
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      eapply (region_kept_aview Ex (w_H W) _ _ 2%nat (spZ regs));
      [ repeat (rewrite ew_ewset_other by lia); exact Usp | intros; reflexivity | intros aa Haa; exact Haa ]
    | specialize (HS2 HQ); clear HQ ] end;
  rewrite <- restrict_mkst_fx in HS2;
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pi_facts_incl3 _ _ _ fnd_scan_fa [] [] HS2
    ltac:(intros x Hx; vm_compute in Hx |- *; tauto) ltac:(intros x Hx; destruct Hx)
    ltac:(intros x Hx; destruct Hx)) as HS3;
  clear HS2;
  lazymatch type of HS3 with st_ok_pi _ _ ?E2 _ _ =>
  eapply (fnd_scan ly S W regs mem md ch r p bs M E2 _ _ (fnd_extra bs M) HPRE Hin HL Hbs HB1 HFO HLM HM);
  [ lazymatch goal with H : fnd_mb M ?j <> 0 |- _ => exact (fnd_nzero6 M j H) end
  | apply img_env_havoc_hi; [eassumption | cbv; lia]
  | split; [intros nn Hnn; rewrite ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia);
            exact (proj1 HAE nn Hnn) | cbn [havoc ewset ed]; exact (proj2 HAE)]
  | rewrite ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); exact E10
  | rewrite ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); exact E11
  | rewrite ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); exact E33
  | refine (eq_ind _ (fun s => st_ok_pi SEGS VAL _ s _) HS3 fnd_ss_scan _); vm_compute; reflexivity
  | exact HJ ]
  end end in
let rec go := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK fnd_Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM fnd_Bx fnd_SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) =>
      psym_why_tok tpi tw K fnd_Bx fnd_Bspan fnd_SH (start K fnd_Bx fnd_Bspan fnd_SH ss) end in
    lazymatch why with
    | SR_jalr _ => zero_leaf
    | SR_branch BC_GE _ _ => merge
    | SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' fnd_Bspan; [fnd_macfact; go | fnd_macfact; go]
    | _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
    end
  end end in
go.
Qed.
End h.
End f.
End d.
