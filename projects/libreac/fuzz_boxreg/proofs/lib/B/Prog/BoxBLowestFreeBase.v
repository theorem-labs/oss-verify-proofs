(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's ASan build (lib/A). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_of.v, with its module paths, module names and numbers changed; 682 of its 761 lines of code are new or changed and 759 lines of the source are left out. *)
(* lowest_free_base (fuzz_boxreg.asan-ubsan 0x81e94, 53 instructions): the contract of the ASan+UBSan build's code.
   The function takes a 64-byte frame on the machine stack (addi sp,sp,-64; it saves ra and s0..s5 there) and checks
   r (a0) for 4-byte alignment for UBSan. Then, for each candidate base b = 0, 1, ..., it reads fabric (r + 284) of
   the 288-byte registry struct at r, a heap block of the caller, after the check of its shadow byte; while
   b + k <= fabric (k in a1) it calls range_taken (r, b, k) (lib/B/Prog/BoxBRangeTaken.v, whose contract the proof
   takes as a Section hypothesis at BASE + AF_range_taken) and returns the first b that range_taken reports free; it
   returns -1 when b + k passes the fabric. The result is Pau's lowest_free of lib/Prog/lowest_free_base_c.v, used as
   it is with the model of lib/Prog/Boxreg.v. It writes nothing outside its own frame and range_taken's.
   Stack: its own 64 bytes and range_taken's RANGE_TAKEN_STKB below them.
   Hazards: the struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284). Every UBSan check
   branches to the UBSan trap (the unimp at 0x81f64): the alignment check on r is refuted by the allocator's block
   law (r a multiple of 16); the overflow checks on b + 1 (addiw) and b + 1 + k (addw against the 64-bit sum) by
   b + k <= fabric <= 40 at each step. The branch to __asan_report_load4 is refuted by the block's shadow. k is the
   sign-extended int nch, 1 <= k < 2^31. range_taken's premises (boxreg_B1, fabric <= 40, the row bounds, 0 <= b,
   0 <= k, b + k <= fabric) follow from boxreg_B1..B3 and the loop guard at each call; its read premise is this
   function's, as the memory and the blocks are the same at the call.
   Image difference: the asan build (lib/A/Prog/LowestFreeBase.v) inlines range_taken, takes a 32-byte frame and
   has no UBSan checks; the result is the same. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBRangeTaken.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg lowest_free_base_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 64-byte frame and range_taken's stack
   (its 16-byte frame and ESTACK) below it. *)
Definition AB_lowest_free_baseP : Z := BASE + AF_lowest_free_base.
Definition LOWEST_FREE_BASE_STKB : Z := 64 + RANGE_TAKEN_STKB.
Section h.
Variable B : asyms.
Definition tblowest_free_base_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (k : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B LOWEST_FREE_BASE_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
exists z, getr regs' 10 = w64 z /\ lowest_free_base_c.lowest_free bs k z).
Definition tblowest_free_base_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
afn_pre SEGS B LOWEST_FREE_BASE_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> 1 <= k < 2 ^ 31 ->
In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
SRr SEGS W (cfg_at SEGS AB_lowest_free_baseP regs mem md) (tblowest_free_base_post regs ly S W mem md k bs).
(* The walk.  Image values: the shadow base 0x7fff8000 (the .bss cell of PALib's object 12, read through the GOT
   word of object 1); the loop head 0x81ee8 is AF_lowest_free_base + 0x54.  The walk runs the entry block to the
   loop head; each iteration (lfb_iter) restarts the symbolic state at the loop head from the loop invariant
   lfb_li, so the loop needs no generalisation of a symbolic state.  Every UBSan trap and the branch to
   __asan_report_load4 are refuted: the alignment check of r (0x81ebc) and the b + 1 overflow check (0x81f14) by
   the engine from the facts (r a multiple of 16 by the allocator's block law, 0 <= b <= 40), the shadow check of
   r + 284 (0x81eec) by the shadow entry of the block (lfb_shent), and the b + 1 + k overflow check (0x81f24) in
   lfb_iter from b + k <= fabric <= 40. *)
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RT : tbrange_taken_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
Definition LFB_SB : Z := 0x7fff8000.
Definition LFB_Bx : sv := SOff 32 0.
Definition LFB_span : Z * Z := (LFB_SB, LFB_SB + 2 ^ 44 - 1).
Definition LFB_PCH : Z := AF_lowest_free_base + 0x54.
(* The entry state (ss_lfb0, atoms 0..31 the call's registers, 32 the shadow base, 33 the fabric word) and the
   loop-head state (ss_lfbL, atoms 0..31 the registers at the loop head, 32 the shadow base, 33 the fabric word,
   34..40 the call's ra, s0..s5 that the frame holds). *)
Definition lfb_fabric_region (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 288 0 0 [YP09.mkChunk 284 (CVal 4 (SOff 33 0))].
Definition lfb_regions0 : smem := [stack_region 64; got_regionP; bcell_regionP 32; lfb_fabric_region 10].
Definition lfb_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
  (11%nat, mkAF 1 (2 ^ 31 - 1) 0); (32%nat, mkAF LFB_SB LFB_SB 0); (33%nat, mkAF 1 40 0)] [] [].
Definition ss_lfb0 : sstate := mkSS AF_lowest_free_base sr_atoms lfb_regions0 None lfb_facts0.
Definition lfb_SH0 : list shent := [mkSHE 10 0 288].
Definition lfb_ex0 (F : Z) : list word := map (Z_to_bv 64) [LFB_SB; F].
Definition lfb_fr_chunks : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 40 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
   YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0));
   YP09.mkChunk 56 (CVal 8 (SOff 34 0))].
Definition lfb_regionsL : smem := [YP09.mkRegion (Some 2%nat) 0 64 0 0 lfb_fr_chunks; lfb_fabric_region 8].
Definition lfb_factsL : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 140737479966720 4);
  (9%nat, mkAF 1 (2 ^ 31 - 1) 0); (18%nat, mkAF 0 40 0); (32%nat, mkAF LFB_SB LFB_SB 0); (33%nat, mkAF 1 40 0)] [] [].
Definition lfb_regsL : list sv :=
  sr_set (sr_set sr_atoms 19%bv (SOff 8 284)) 20%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 284) (SLit 3)) (SOff 32 0)).
Definition ss_lfbL : sstate := mkSS LFB_PCH lfb_regsL lfb_regionsL None lfb_factsL.
Definition lfb_SHL : list shent := [mkSHE 8 0 288].
Definition lfb_svregs : list (bv 5) := [1%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv].
Definition lfb_exL (regs0 : bvmap 5 word) (F : Z) : list word :=
  map (Z_to_bv 64) [LFB_SB; F] ++ map (getr regs0) lfb_svregs.
(* The frame words (offset from the call's sp, register) that the entry block saves. *)
Definition lfb_saved : list (Z * bv 5) :=
  [(-56, 21%bv); (-48, 20%bv); (-40, 19%bv); (-32, 18%bv); (-24, 9%bv); (-16, 8%bv); (-8, 1%bv)].
Definition lfb_frame (regs0 : bvmap 5 word) (m : word -> option byte) : Prop :=
  forall o (rr : bv 5), In (o, rr) lfb_saved -> val_mem SEGS m (spZ regs0 + o) 8 (bv_unsigned (getr regs0 rr)).
Definition lfb_keep (regs0 regsL : bvmap 5 word) : Prop :=
  getr regsL 3 = getr regs0 3 /\ getr regsL 4 = getr regs0 4 /\ getr regsL 22 = getr regs0 22 /\
  getr regsL 23 = getr regs0 23 /\ getr regsL 24 = getr regs0 24 /\ getr regsL 25 = getr regs0 25 /\
  getr regsL 26 = getr regs0 26 /\ getr regsL 27 = getr regs0 27.
(* The loop invariant at 0x81ee8 for the candidate b, over the machine registers, memory and model there. *)
Definition lfb_li (regs0 : bvmap 5 word) ly S (W : world SEGS) mem md (r k : Z) (bs : list byte) (b : Z)
  (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  ajournal SEGS B LOWEST_FREE_BASE_STKB (spZ regs0) [] ly S W mem md [] ly S W memL mdL 0 /\
  getr regsL 2 = w64 (spZ regs0 - 64) /\ getr regsL 8 = w64 r /\ getr regsL 9 = w64 k /\
  getr regsL 18 = w64 b /\ getr regsL 19 = w64 (r + 284) /\ getr regsL 20 = w64 (LFB_SB + (r + 284) / 8) /\
  lfb_keep regs0 regsL /\
  lfb_frame regs0 (mrestrict (w_H W) memL) /\
  0 <= b <= Boxreg.bx_fabric bs /\ (b = 0 \/ b + k <= Boxreg.bx_fabric bs + 1) /\
  (forall c, 0 <= c < b -> lowest_free_base_c.slice_meets bs c k).
(* The fabric word at r + 284, as the 4 bytes the struct premise gives. *)
Lemma lfb_fabric_val : forall (H : word -> bool) (memX : word -> option byte) (r : Z) (bs : list byte),
  length bs = 288%nat -> Boxreg.boxreg_B2 bs ->
  (forall i, 0 <= i < 288 -> aview SEGS H memX (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  val_mem SEGS (mrestrict H memX) (r + 284) 4 (Boxreg.bx_fabric bs).
Proof.
intros H memX r bs HL HB2 HV. unfold Boxreg.boxreg_B2 in HB2.
assert (HS : length (skipn 284 bs) = 4%nat) by (rewrite length_skipn; lia).
assert (HN : forall j, (j < 4)%nat -> nth (284 + j) bs (Z_to_bv 8 0) = nth j (skipn 284 bs) (Z_to_bv 8 0))
  by (intros j Hj; rewrite nth_skipn; reflexivity).
unfold Boxreg.bx_fabric, Boxreg.rd4, Boxreg.bsub in *.
change (Z.to_nat 284) with 284%nat in *. change (Z.to_nat 4) with 4%nat in *.
destruct (skipn 284 bs) as [|x0 [|x1 [|x2 [|x3 [|x4 l]]]]] eqn:Hsk; cbn [length] in HS; try lia.
cbn [firstn] in *.
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val in *.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val] in *.
pose proof (bv_unsigned_in_range 8 x0) as T0. pose proof (bv_unsigned_in_range 8 x1) as T1.
pose proof (bv_unsigned_in_range 8 x2) as T2. pose proof (bv_unsigned_in_range 8 x3) as T3.
change (bv_modulus 8) with 256 in T0, T1, T2, T3.
set (u := bv_unsigned x0 + 256 * (bv_unsigned x1 + 256 * (bv_unsigned x2 + 256 * (bv_unsigned x3 + 256 * 0)))) in *.
assert (Hu : bv_swrap 32 u = u).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in *. change (2 ^ 32 / 2) with (2 ^ 31) in *.
  Z.div_mod_to_equations. lia. }
rewrite Hu in *.
intros kk Hk.
destruct (aview_byte SEGS H memX (r + (284 + Z.of_nat kk)) _ (HV (284 + Z.of_nat kk) ltac:(lia))) as (b0 & Hb0 & Hv0 & _).
replace (r + 284 + Z.of_nat kk) with (r + (284 + Z.of_nat kk)) by lia. rewrite Hb0. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hv0.
replace (Z.to_nat (284 + Z.of_nat kk)) with (284 + kk)%nat by lia. rewrite (HN kk Hk).
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
assert (Hkk : kk = 0%nat \/ kk = 1%nat \/ kk = 2%nat \/ kk = 3%nat) by lia.
rewrite Z.shiftr_div_pow2 by lia.
subst u. destruct Hkk as [-> | [-> | [-> | ->]]]; cbn [nth];
[ change (2 ^ (8 * Z.of_nat 0)) with 1
| change (2 ^ (8 * Z.of_nat 1)) with 256
| change (2 ^ (8 * Z.of_nat 2)) with 65536
| change (2 ^ (8 * Z.of_nat 3)) with 16777216 ];
change (2 ^ 32) with 4294967296; Z.div_mod_to_equations; lia.
Qed.
(* The shadow entry of the 288-byte block: every granule addressable, and apart from the shadow region. *)
Lemma lfb_shent : forall ly S (W : world SEGS) mem md Ex (n : nat) (q : Z),
  AR SEGS B ly S W mem md -> In (q, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) ->
  U Ex LFB_Bx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  shent_ok SEGS LFB_Bx Ex (mrestrict (w_H W) mem) (mkSHE n 0 288).
Proof.
intros ly S W mem md Ex n q HAR Hin HB Hq.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md q _ HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in *.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
rewrite <- (aview_rd_of SEGS). split.
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md q _ (q + 0) (288 - 0) HAR Hin);
  change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288; lia.
- intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
  revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  revert Hbia Hb4096 Hbceil C1 C3 C5. clear. intros. lia.
Qed.
(* The loop-head symbolic state from the loop invariant. *)
Lemma lfb_loop_entry : forall ly S (W : world SEGS) (regs0 : bvmap 5 word) mem md ch (r k : Z) (bs : list byte)
  b regsL memL mdL,
  afn_pre SEGS B LOWEST_FREE_BASE_STKB ly S W regs0 mem md ch -> 1 <= k < 2 ^ 31 ->
  In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B2 bs ->
  lfb_li regs0 ly S W mem md r k bs b regsL memL mdL ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsL (lfb_exL regs0 (Boxreg.bx_fabric bs)))) ss_lfbL
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + LFB_PCH)) memL (seg_rom SEGS)))
  /\ sh_ok SEGS LFB_Bx lfb_SHL (Eimg (Ereg regsL (lfb_exL regs0 (Boxreg.bx_fabric bs)))) (mrestrict (w_H W) memL).
Proof.
intros ly S W regs0 mem md ch r k bs b regsL memL mdL HPRE Hk Hin HL HV HB2 HLI.
destruct HLI as (HJ & R2 & R8 & R9 & R18 & R19 & R20 & Rkeep & HFR & Hb & Hbk & HINV).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STKB = 4176) by reflexivity.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W memL mdL r _ HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in *.
pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
assert (HVL : forall i, 0 <= i < 288 ->
  aview SEGS (w_H W) memL (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
{ intros i Hi. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 r BoxBReacBoxregInit.REG_SIZEB i Hin Hin
    ltac:(change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288; lia) (inFP_nil _)).
  apply HV. unfold BoxBReacBoxregInit.REG_SIZEB. lia. }
pose proof (lfb_fabric_val (w_H W) memL r bs HL HB2 HVL) as HFV.
set (F := Boxreg.bx_fabric bs) in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsL (lfb_exL regs0 F))).
assert (EL : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regsL rr).
{ intros n rr Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regsL _ n rr Hr). }
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (lfb_exL regs0 F) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsL _ j). }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 64)) by (rewrite (EL 2%nat 2%bv) by (lia || reflexivity); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 r) by (rewrite (EL 8%nat 8%bv) by (lia || reflexivity); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 k) by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 b) by (rewrite (EL 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 LFB_SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (Esv : forall j (rr : bv 5), (j < 7)%nat -> nth j lfb_svregs (0%bv : bv 5) = rr ->
  ew E (34 + j) = getr regs0 rr).
{ intros j rr Hj Hrr. replace (34 + j)%nat with (32 + (2 + j))%nat by lia. rewrite (EX (2 + j)%nat) by lia.
  subst rr. do 7 (destruct j as [|j]; [reflexivity|]). lia. }
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hsp : 2 ^ 46 <= spZ regs0 - 64 /\ spZ regs0 <= 2 ^ 47) by (unfold ASTACK in *; lia).
assert (Hr47 : r + 288 <= spZ regs0 - 64) by lia.
split.
- unfold ss_lfbL. apply pa_entry_st_ok_full.
  + intros rr. unfold lfb_regsL.
    destruct (decide (rr = 20%bv)) as [->|N20].
    { rewrite sr_get_set_same by reflexivity. rewrite (denot_shx E 8 32 284 r LFB_SB E8 E32) by (unfold LFB_SB; lia).
      exact R20. }
    rewrite sr_get_set_other by exact N20.
    destruct (decide (rr = 19%bv)) as [->|N19].
    { rewrite sr_get_set_same by reflexivity. cbn [sv_denot]. rewrite E8, unsigned_lit_small by lia. exact R19. }
    rewrite sr_get_set_other by exact N19. exact (regs_ok_Eimg_Ereg regsL _ rr).
  + vm_compute. reflexivity.
  + unfold lfb_regionsL, lfb_fabric_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 2%nat (spZ regs0 - 64) E2) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold lfb_fr_chunks.
      do 7 (lazymatch goal with
      | |- Forall _ (YP09.mkChunk ?od (CVal 8 (SOff ?x 0)) :: _) =>
        apply Forall_cons;
        [ let j := eval cbv in (x - 34)%nat in
          let rr := constr:(nth j lfb_svregs (0%bv : bv 5)) in
          let Hx := fresh "Hx" in
          assert (Hx : ew E x = getr regs0 rr) by exact (Esv j rr ltac:(lia) eq_refl);
          apply (chunk_ok_val SEGS E _ (spZ regs0 - 64) od 8 (SOff x 0) (bv_unsigned (getr regs0 rr)));
          [ cbn [sv_denot]; rewrite Hx, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs0 rr)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu;
            change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | zside
          | replace (spZ regs0 - 64 + od) with (spZ regs0 + (od - 64)) by lia;
            apply HFR; cbn; tauto ]
        | ]
      end).
      apply Forall_nil.
    * rewrite (VB 8%nat r E8) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ r 284 4 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
      | zside | exact HFV].
  + apply pairwise_disjoint_of_extents.
    unfold lfb_regionsL, lfb_fabric_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 2%nat (spZ regs0 - 64) E2) by lia. rewrite (VB 8%nat r E8) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
  + split; [|split; exact I].
    cbn [lfb_factsL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E9, E18, E32, E33, !unsigned_lit_small by (unfold LFB_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hsp16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
    unfold LFB_SB. repeat split; lia.
- unfold sh_ok, lfb_SHL. apply Forall_cons; [|apply Forall_nil].
  apply (lfb_shent ly S W memL mdL E 8 r HAR Hin).
  + unfold LFB_Bx. rewrite (U_atom E 32 LFB_SB E32) by (unfold LFB_SB; lia). reflexivity.
  + exact (U_atom E 8 r E8 ltac:(lia)).
Qed.
(* The entry symbolic state from the pre-condition. *)
Lemma lfb_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
  afn_pre SEGS B LOWEST_FREE_BASE_STKB ly S W regs mem md ch ->
  getr regs 10 = w64 r -> getr regs 11 = w64 k -> 1 <= k < 2 ^ 31 ->
  In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B2 bs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (lfb_ex0 (Boxreg.bx_fabric bs)))) ss_lfb0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_lowest_free_baseP) mem (seg_rom SEGS)))
  /\ sh_ok SEGS LFB_Bx lfb_SH0 (Eimg (Ereg regs (lfb_ex0 (Boxreg.bx_fabric bs)))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hin HL HV HB2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STKB = 4176) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r _ HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in *.
pose proof (blk_off_imgP B ly S W mem md r _ HAR Hin) as Hrimg.
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
pose proof (lfb_fabric_val (w_H W) mem r bs HL HB2
  (fun i Hi => HV i ltac:(unfold BoxBReacBoxregInit.REG_SIZEB; lia))) as HFV.
set (F := Boxreg.bx_fabric bs) in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lfb_ex0 F))).
assert (EL : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n rr Hr). }
assert (E2 : ew E 2 = getr regs 2) by (apply EL; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EL 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite (EL 11%nat 11%bv) by (lia || reflexivity); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 LFB_SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 F)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_lfb0, AB_lowest_free_baseP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold lfb_regions0, stack_region, got_regionP, bcell_regionP, lfb_fabric_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 LFB_Bx LFB_SB);
      [cbn [sv_denot LFB_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold LFB_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ r 284 4 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
      | zside | exact HFV].
  + apply pairwise_disjoint_of_extents.
    unfold lfb_regions0, stack_region, got_regionP, bcell_regionP, lfb_fabric_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hrimg Hrceil Hr4096.
    clear. intros. repeat split; lia.
  + split; [|split; exact I].
    cbn [lfb_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33, !unsigned_lit_small by (unfold LFB_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold LFB_SB. repeat split; lia.
- unfold sh_ok, lfb_SH0. apply Forall_cons; [|apply Forall_nil].
  apply (lfb_shent ly S W mem md E 10 r HAR Hin).
  + unfold LFB_Bx. rewrite (U_atom E 32 LFB_SB E32) by (unfold LFB_SB; lia). reflexivity.
  + exact (U_atom E 10 r E10 ltac:(lia)).
Qed.
Lemma lfb_addw : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 31 -> sv_denot E (SAluw ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. cbn [sv_denot]. rewrite Ha, Hb.
rewrite (aluw_addsub_of_lit ALU_ADD _ _ (x + y) (or_introl eq_refl) (alu64_add_lit x y)).
f_equal. unfold zalu32, zcanon, zu32, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [zalu_raw].
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
unfold M32. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648. change (2 ^ 64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.
Lemma lfb_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. rewrite Z.add_0_r. reflexivity. Qed.
Lemma lfb_add64 : forall E a c x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E c = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD a c) = Z_to_bv 64 (x + y).
Proof. intros E a c x y Ha Hc. cbn [sv_denot]. rewrite Ha, Hc. apply alu64_add_lit. Qed.
Lemma lfb_frame_intro : forall (regs0 : bvmap 5 word) m,
  val_mem SEGS m (spZ regs0 - 56) 8 (bv_unsigned (getr regs0 21)) ->
  val_mem SEGS m (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)) ->
  val_mem SEGS m (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) ->
  val_mem SEGS m (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) ->
  val_mem SEGS m (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem SEGS m (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem SEGS m (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
  lfb_frame regs0 m.
Proof.
intros regs0 m V21 V20 V19 V18 V9 V8 V1 o rr Hin. cbn [lfb_saved In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
  first [ exact V21 | exact V20 | exact V19 | exact V18 | exact V9 | exact V8 | exact V1 ] |]).
destruct Hin.
Qed.
Lemma lfb_aregs : forall (regs0 regsF : bvmap 5 word),
  getr regsF 2 = getr regs0 2 -> getr regsF 3 = getr regs0 3 -> getr regsF 4 = getr regs0 4 ->
  getr regsF 8 = getr regs0 8 -> getr regsF 9 = getr regs0 9 ->
  getr regsF 18 = getr regs0 18 -> getr regsF 19 = getr regs0 19 -> getr regsF 20 = getr regs0 20 ->
  getr regsF 21 = getr regs0 21 -> getr regsF 22 = getr regs0 22 -> getr regsF 23 = getr regs0 23 ->
  getr regsF 24 = getr regs0 24 -> getr regsF 25 = getr regs0 25 -> getr regsF 26 = getr regs0 26 ->
  getr regsF 27 = getr regs0 27 ->
  aregs_preserved regs0 regsF.
Proof.
intros regs0 regsF H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 n Hn. unfold acallee_saved in Hn.
assert (Hc : n = 2 \/ n = 3 \/ n = 4 \/ n = 8 \/ n = 9 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/
  n = 24 \/ n = 25 \/ n = 26 \/ n = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
assumption.
Qed.
(* What the call of range_taken (r, b, k) leaves (tbrange_taken_post's own part). *)
Definition lfb_rtK (bs : list byte) (b k : Z) ly S (W : world SEGS)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
  ((lowest_free_base_c.slice_meets bs b k /\ getr regs' 10 = w64 1) \/
   (~ lowest_free_base_c.slice_meets bs b k /\ getr regs' 10 = w64 0)).
Local Ltac lfb_ewq :=
  cbn [ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
  repeat (rewrite ew_havoc_old; [|cbv; lia]); repeat (rewrite ew_ewset_other; [|lia]); assumption.
Local Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Local Ltac lfb_rng v := pose proof (bv_unsigned_in_range 64 v); change (bv_modulus 64) with (2 ^ 64) in *;
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
(* One frame word, read from the stack region HR of base atom 2 at base: chunk offset od, atom x. *)
Local Ltac lfb_fv HR Hbase base od x :=
  lazymatch goal with |- val_mem _ ?m ?a 8 (bv_unsigned ?v) =>
    replace a with (base + od) by lia;
    apply (field_of_region _ m 2%nat base _ _ _ _ _ od 8 (SOff x 0) (bv_unsigned v) HR Hbase);
    [ cbn; tauto
    | lazymatch goal with |- sv_denot ?Ey _ = _ =>
        let Hx := fresh "Hx" in assert (Hx : ew Ey x = v) by lfb_ewq;
        cbn [sv_denot]; rewrite Hx, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity end
    | lfb_rng v
    | lia ]
  end.
(* The return at 0x81f60 (ret), from the restored registers. *)
Lemma lfb_ret_ok : forall ly S (W : world SEGS) (regs0 : bvmap 5 word) mem md (k : Z) (bs : list byte)
  Ex ssx msx mdx (z : Z),
  st_ok_pi SEGS VAL Ex ssx (restrict (w_H W) msx) -> ss_resv ssx = None ->
  plookup pl_tpi (ss_pc ssx) = Some (PW RET_WORD_r) ->
  ajournal SEGS B LOWEST_FREE_BASE_STKB (spZ regs0) [] ly S W mem md [] ly S W (ms_mem msx) mdx 0 ->
  YK0s.ret_ok (getr regs0 1) ->
  getr (ms_regs msx) 1 = getr regs0 1 -> aregs_preserved regs0 (ms_regs msx) ->
  getr (ms_regs msx) 10 = w64 z -> lowest_free_base_c.lowest_free bs k z ->
  SRr SEGS W (mkCfg msx mdx) (tblowest_free_base_post regs0 ly S W mem md k bs).
Proof.
intros ly S W regs0 mem md k bs Ex ssx msx mdx z HS Hrv Hpl HJ Hra H1 HP H10 HZ.
eapply (RET W _ _ _ _ _ HS Hrv Hpl). intros mat.
unfold tblowest_free_base_post, apost_base.
exists ly, S, (ms_regs msx), (ms_mem msx), (with_vm_backing (m_vm_lazy mdx) mat mdx).
split; [rewrite H1, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists z. split; [exact H10 | exact HZ].
Qed.
Local Ltac lfb_rq HS :=
  lazymatch goal with |- getr (ms_regs ?m) ?rr = _ =>
    let Q := fresh "Q" in prreg HS rr Q; rewrite Q; clear Q end.
(* One iteration from the loop head: return -1 (0x81ef8 taken), return b (range_taken reports b free), or the
   loop head again with b + 1. *)
Lemma lfb_iter : forall ly S (W : world SEGS) (regs0 : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
  afn_pre SEGS B LOWEST_FREE_BASE_STKB ly S W regs0 mem md ch -> 1 <= k < 2 ^ 31 ->
  In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
  forall b regsL memL mdL,
  (forall b' regs' mem' md', 0 <= Boxreg.bx_fabric bs + 1 - b' < Boxreg.bx_fabric bs + 1 - b ->
    lfb_li regs0 ly S W mem md r k bs b' regs' mem' md' ->
    SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + LFB_PCH)) mem' (seg_rom SEGS)) md')
      (tblowest_free_base_post regs0 ly S W mem md k bs)) ->
  lfb_li regs0 ly S W mem md r k bs b regsL memL mdL ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + LFB_PCH)) memL (seg_rom SEGS)) mdL)
    (tblowest_free_base_post regs0 ly S W mem md k bs).
Proof.
intros ly S W regs0 mem md ch r k bs HPRE Hk Hin HL HV HB1 HB2 HB3 b regsL memL mdL IH HLI.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (lfb_loop_entry ly S W regs0 mem md ch r k bs b regsL memL mdL HPRE Hk Hin HL HV HB2 HLI) as [HS SHOK].
destruct HLI as (HJ & R2 & R8 & R9 & R18 & R19 & R20 & Rkeep & HFR & Hb & Hbk & HINV).
destruct Rkeep as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STKB = 4176) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memL mdL r _ (proj1 HJ) Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in *.
pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
assert (HB1' : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
set (F := Boxreg.bx_fabric bs) in *.
remember (Eimg (Ereg regsL (lfb_exL regs0 F))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regsL rr).
{ intros n rr Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regsL _ n rr Hr). }
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (lfb_exL regs0 F) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsL _ j). }
clear HEdef.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 64)) by (rewrite (EL 2%nat 2%bv) by (lia || reflexivity); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 r) by (rewrite (EL 8%nat 8%bv) by (lia || reflexivity); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 k) by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 b) by (rewrite (EL 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (EL 3%nat 3%bv) by (lia || reflexivity); exact K3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (EL 4%nat 4%bv) by (lia || reflexivity); exact K4).
assert (E22 : ew E 22 = getr regs0 22) by (rewrite (EL 22%nat 22%bv) by (lia || reflexivity); exact K22).
assert (E23 : ew E 23 = getr regs0 23) by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); exact K23).
assert (E24 : ew E 24 = getr regs0 24) by (rewrite (EL 24%nat 24%bv) by (lia || reflexivity); exact K24).
assert (E25 : ew E 25 = getr regs0 25) by (rewrite (EL 25%nat 25%bv) by (lia || reflexivity); exact K25).
assert (E26 : ew E 26 = getr regs0 26) by (rewrite (EL 26%nat 26%bv) by (lia || reflexivity); exact K26).
assert (E27 : ew E 27 = getr regs0 27) by (rewrite (EL 27%nat 27%bv) by (lia || reflexivity); exact K27).
assert (E32 : ew E 32 = Z_to_bv 64 LFB_SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs0 1) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs0 8) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs0 9) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs0 18) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs0 19) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr regs0 20) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = getr regs0 21) by exact (EX 8%nat ltac:(lia)).
clear EX.
assert (Hsp : 2 ^ 46 <= spZ regs0 - 64 /\ spZ regs0 <= 2 ^ 47) by (unfold ASTACK in *; lia).
assert (Hsp2 : getr regs0 2 = Z_to_bv 64 (spZ regs0)) by (unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
(* the struct bytes, now and after any run that keeps the journal *)
assert (HVJ : forall memX mdX, ajournal SEGS B LOWEST_FREE_BASE_STKB (spZ regs0) [] ly S W mem md [] ly S W memX mdX 0 ->
  forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
  aview SEGS (w_H W) memX (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
{ intros memX mdX HJX i Hi. pose proof HJX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 r BoxBReacBoxregInit.REG_SIZEB i Hin Hin
    ltac:(change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288; unfold BoxBReacBoxregInit.REG_SIZEB in Hi; lia)
    (inFP_nil _)).
  apply HV. exact Hi. }
unfold LFB_PCH in *.
paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
psrr_branch_tok RUN BR HS SHOK LFB_span.
- (* fabric < b + k: no base from b on fits; return -1 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let D9 := fresh "D" in let D18 := fresh "D" in let D33 := fresh "D" in
    assert (D9 : sv_denot Ex (SOff 9 0) = Z_to_bv 64 k) by (apply lfb_atom0; [lfb_ewq | lia]);
    assert (D18 : sv_denot Ex (SOff 18 0) = Z_to_bv 64 b) by (apply lfb_atom0; [lfb_ewq | lia]);
    assert (D33 : sv_denot Ex (SOff 33 0) = Z_to_bv 64 F) by (apply lfb_atom0; [lfb_ewq | lia]);
    rewrite (lfb_addw Ex _ _ k b D9 D18) in Hc by lia; rewrite D33 in Hc end.
  cbn [branch_taken] in Hc. rewrite Boxreg.lts_lit in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
  eapply (lfb_ret_ok ly S W regs0 mem md k bs _ _ _ _ (-1) HS eq_refl ltac:(vm_compute; reflexivity) HJ Hra).
  + lfb_rq HS. exact E34.
  + apply lfb_aregs; try (lfb_rq HS; assumption).
    lfb_rq HS. rewrite E2, unsigned_lit_small by lia. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. exact (eq_sym Hsp2).
  + lfb_rq HS. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  + left. split; [reflexivity|]. intros c Hc0 Hck. apply HINV. lia.
- (* b + k <= fabric: call range_taken (r, b, k) *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let D9 := fresh "D" in let D18 := fresh "D" in let D33 := fresh "D" in
    assert (D9 : sv_denot Ex (SOff 9 0) = Z_to_bv 64 k) by (apply lfb_atom0; [lfb_ewq | lia]);
    assert (D18 : sv_denot Ex (SOff 18 0) = Z_to_bv 64 b) by (apply lfb_atom0; [lfb_ewq | lia]);
    assert (D33 : sv_denot Ex (SOff 33 0) = Z_to_bv 64 F) by (apply lfb_atom0; [lfb_ewq | lia]);
    rewrite (lfb_addw Ex _ _ k b D9 D18) in Hc by lia; rewrite D33 in Hc end.
  cbn [branch_taken] in Hc. rewrite Boxreg.lts_lit in Hc by lia. apply Z.ltb_ge in Hc.
  rename Hc into Hfit.
  paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
  (* at the call of range_taken (0x81f08) *)
  pmkst HS. rewrite pa_sigma_range_taken.
  prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
  prreg HS (8%bv : bv 5) CR8. prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11. prreg HS (12%bv : bv 5) CR12.
  rewrite E2 in CR2. rewrite E3 in CR3. rewrite E4 in CR4. rewrite E8 in CR8. rewrite E8 in CR10. rewrite E18 in CR11.
  rewrite E9 in CR12.
  match goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
    assert (HVc : forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
      aview SEGS (w_H W) mm (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) by exact (HVJ _ _ HJ) end.
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W _ _ _ LOWEST_FREE_BASE_STKB (spZ regs0) [] ly S W mem md [] ly S _ 0 RANGE_TAKEN_STKB []
      0 (-64) _ [] (lfb_rtK bs b k ly S W) HJ).
    - unfold spZ at 1. rewrite CR2, unsigned_lit_small by lia. lia.
    - reflexivity.
    - lia.
    - unfold RANGE_TAKEN_STKB, ESTACK. lia.
    - unfold RANGE_TAKEN_STKB, ESTACK. lia.
    - rewrite CR3. exact Hgp.
    - rewrite CR4. exact Htp.
    - reflexivity.
    - rewrite CR1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite CR1. pose proof pa_base_lo. pose proof pa_B_ok. rewrite unsigned_lit_small by lia. lia.
    - left. split; [|reflexivity]. left. unfold s0Z. rewrite CR8, unsigned_lit_small by lia. lia.
    - intros Hpre. unfold lfb_rtK.
      assert (HRB : forall i, 0 <= i < Boxreg.bx_n bs -> 0 <= Boxreg.bx_base bs i /\ 0 <= Boxreg.bx_nch bs i /\
        Boxreg.bx_base bs i + Boxreg.bx_nch bs i <= Boxreg.bx_fabric bs)
        by (intros i Hi; destruct (HB3 i Hi) as (_ & ? & _ & ? & ?); lia).
      exact (RT ly S W _ _ _ [] r b k bs Hpre CR10 CR11 CR12 Hin HL HVc HB1 ltac:(lia) HRB ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
  destruct HK as (-> & -> & -> & HRES).
  rewrite CR1.
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP [0%nat] HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS2 HQ); clear HQ ] end.
  { apply Forall_cons; [|apply Forall_nil].
    lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      assert (HE2 : ew Ex 2 = Z_to_bv 64 (spZ regs0 - 64)) by lfb_ewq end.
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ms_mem restrict]; rewrite HE2;
    rewrite unsigned_lit_small by lia; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS).
    apply (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc). lia. }
  rewrite <- restrict_mkst_fx in HS2.
  cbn [app] in HJ2. replace (0 + 0) with 0 in HJ2 by reflexivity.
  clear HS HJ SHOK. rename HS2 into HS, HJ2 into HJ.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex 512 ?ws) _ (restrict _ ?msx) =>
    lazymatch goal with HEx : img_env _ _ Ex |- _ =>
      pose proof (img_env_havoc_hi Ex 512%nat ws HEx ltac:(cbv; lia)) as HEIc end;
    assert (SHOK : sh_ok SEGS LFB_Bx [] (havoc Ex 512 ws) (mrestrict (w_H W) (ms_mem msx))) by apply Forall_nil
  end.
  paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
  psrr_branch_tok RUN BR HS SHOK LFB_span.
  + (* range_taken returned 0: b is free *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (A10 : sv_denot Ex (SOff 516 0) = getr regs2 10)
        by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) end.
    rewrite A10 in Hc. cbn [sv_denot] in Hc.
    destruct HRES as [(HSM & HA0) | (HNSM & HA0)]; rewrite HA0 in Hc; [vm_compute in Hc; discriminate Hc|].
    paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
    eapply (lfb_ret_ok ly S W regs0 mem md k bs _ _ _ _ b HS eq_refl ltac:(vm_compute; reflexivity) HJ Hra).
    * lfb_rq HS. exact E34.
    * apply lfb_aregs; try (lfb_rq HS; assumption).
      lfb_rq HS. rewrite E2, unsigned_lit_small by lia. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. exact (eq_sym Hsp2).
    * lfb_rq HS. exact E18.
    * right. split; [lia|]. split; [lia|]. split; [exact HNSM | exact HINV].
  + (* range_taken returned 1: b is taken; next candidate b + 1 *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (A10 : sv_denot Ex (SOff 516 0) = getr regs2 10)
        by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) end.
    rewrite A10 in Hc. cbn [sv_denot] in Hc.
    destruct HRES as [(HSM & HA0) | (HNSM & HA0)]; rewrite HA0 in Hc; [|vm_compute in Hc; discriminate Hc].
    clear Hc.
    paj_run_tok RUN HS HJ SHOK LFB_span; [awr_ok_tac|].
    psrr_branch_tok RUN BR HS SHOK LFB_span.
    * (* no overflow of b + 1 + k: back to the loop head *)
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK LFB_span (AF_lowest_free_base + 0x54); [awr_ok_tac|].
      pmkst HS.
      apply (IH (b + 1)); [lia|].
      split; [exact HJ|].
      split; [lfb_rq HS; exact E2|].
      split; [lfb_rq HS; exact E8|].
      split; [lfb_rq HS; exact E9|].
      split; [lfb_rq HS; rewrite E18, unsigned_lit_small by lia; reflexivity|].
      split; [lfb_rq HS; rewrite E8, unsigned_lit_small by lia; reflexivity|].
      split.
      { prreg_raw HS (20%bv : bv 5) Q20. rewrite Q20.
        lazymatch goal with |- sv_denot ?Ey _ = _ =>
          apply (denot_shx Ey 8 32 284 r LFB_SB); [lfb_ewq | lfb_ewq | lia | lia | lia | unfold LFB_SB; lia] end. }
      split.
      { unfold lfb_keep. repeat split; lfb_rq HS; assumption. }
      split.
      { lazymatch type of HS with st_ok_pi _ _ ?Ey _ (restrict _ ?msx) =>
          pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
          let Hy2 := fresh "Hy2" in assert (Hy2 : ew Ey 2 = Z_to_bv 64 (spZ regs0 - 64)) by lfb_ewq;
          assert (Hbase : bv_unsigned (ew Ey 2) = spZ regs0 - 64) by (rewrite Hy2; apply unsigned_lit_small; lia) end.
        apply lfb_frame_intro;
        [ lfb_fv HR Hbase (spZ regs0 - 64) 8 40%nat | lfb_fv HR Hbase (spZ regs0 - 64) 16 39%nat
        | lfb_fv HR Hbase (spZ regs0 - 64) 24 38%nat | lfb_fv HR Hbase (spZ regs0 - 64) 32 37%nat
        | lfb_fv HR Hbase (spZ regs0 - 64) 40 36%nat | lfb_fv HR Hbase (spZ regs0 - 64) 48 35%nat
        | lfb_fv HR Hbase (spZ regs0 - 64) 56 34%nat ]. }
      split; [lia|]. split; [right; lia|].
      intros c Hcb. destruct (Z.eq_dec c b) as [->|Hne]; [exact HSM | apply HINV; lia].
    * (* the overflow trap: b + 1 + k fits in 32 bits *)
      exfalso.
      lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ => set (Ez := Ex) in Hc end.
      assert (HzB : ew Ez 18 = Z_to_bv 64 b) by (unfold Ez; lfb_ewq).
      assert (HzK : ew Ez 9 = Z_to_bv 64 k) by (unfold Ez; lfb_ewq).
      assert (DB1 : sv_denot Ez (SOff 18 1) = Z_to_bv 64 (b + 1))
        by (cbn [sv_denot]; rewrite HzB, unsigned_lit_small by lia; reflexivity).
      assert (DK0 : sv_denot Ez (SOff 9 0) = Z_to_bv 64 k) by (apply lfb_atom0; [exact HzK | lia]).
      assert (DK1 : sv_denot Ez (SOff 9 1) = Z_to_bv 64 (k + 1))
        by (cbn [sv_denot]; rewrite HzK, unsigned_lit_small by lia; reflexivity).
      assert (DB0 : sv_denot Ez (SOff 18 0) = Z_to_bv 64 b) by (apply lfb_atom0; [exact HzB | lia]).
      rewrite (lfb_addw Ez _ _ (b + 1) k DB1 DK0) in Hc by lia.
      rewrite (lfb_add64 Ez _ _ (k + 1) b DK1 DB0) in Hc.
      replace (k + 1 + b) with (b + 1 + k) in Hc by lia.
      cbn [branch_taken] in Hc. rewrite Boxreg.eqb_lit, Z.eqb_refl in Hc by lia. discriminate Hc.
Qed.
Lemma lfb_loop : forall ly S (W : world SEGS) (regs0 : bvmap 5 word) mem md ch (r k : Z) (bs : list byte),
  afn_pre SEGS B LOWEST_FREE_BASE_STKB ly S W regs0 mem md ch -> 1 <= k < 2 ^ 31 ->
  In (r, BoxBReacBoxregInit.REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
  (forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
    aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
  forall (n : nat) b regsL memL mdL, (Z.to_nat (Boxreg.bx_fabric bs + 1 - b) <= n)%nat ->
  lfb_li regs0 ly S W mem md r k bs b regsL memL mdL ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + LFB_PCH)) memL (seg_rom SEGS)) mdL)
    (tblowest_free_base_post regs0 ly S W mem md k bs).
Proof.
intros ly S W regs0 mem md ch r k bs HPRE Hk Hin HL HV HB1 HB2 HB3 n.
induction n as [|n IHn]; intros b regsL memL mdL Hn HLI.
- exfalso. destruct HLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _). lia.
- apply (lfb_iter ly S W regs0 mem md ch r k bs HPRE Hk Hin HL HV HB1 HB2 HB3 b regsL memL mdL); [|exact HLI].
  intros b' regs' mem' md' Hb' HLI'. apply (IHn b' regs' mem' md'); [lia | exact HLI'].
Qed.
Theorem pbb_lowest_free_base : tblowest_free_base_spec.
Proof.
unfold tblowest_free_base_spec.
intros ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hin HL HV HB1 HB2 HB3.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (lfb_entry ly S W regs mem md ch r k bs HPRE H10 H11 Hk Hin HL HV HB2) as [HS SHOK].
pose proof (ajournal_init SEGS B LOWEST_FREE_BASE_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_BASE_STKB = 4176) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r _ HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size BoxBReacBoxregInit.REG_SIZEB) with 288 in *.
pose proof HB2 as HB2'. unfold Boxreg.boxreg_B2 in HB2'.
set (F := Boxreg.bx_fabric bs) in *.
remember (Eimg (Ereg regs (lfb_ex0 F))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n rr Hr). }
assert (E32 : ew E 32 = Z_to_bv 64 LFB_SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HEdef.
assert (E1 : ew E 1 = getr regs 1) by (apply EL; [lia | reflexivity]).
assert (E2 : ew E 2 = getr regs 2) by (apply EL; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs 3) by (apply EL; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (apply EL; [lia | reflexivity]).
assert (E8 : ew E 8 = getr regs 8) by (apply EL; [lia | reflexivity]).
assert (E9 : ew E 9 = getr regs 9) by (apply EL; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EL 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite (EL 11%nat 11%bv) by (lia || reflexivity); exact H11).
assert (E18 : ew E 18 = getr regs 18) by (apply EL; [lia | reflexivity]).
assert (E19 : ew E 19 = getr regs 19) by (apply EL; [lia | reflexivity]).
assert (E20 : ew E 20 = getr regs 20) by (apply EL; [lia | reflexivity]).
assert (E21 : ew E 21 = getr regs 21) by (apply EL; [lia | reflexivity]).
assert (E22 : ew E 22 = getr regs 22) by (apply EL; [lia | reflexivity]).
assert (E23 : ew E 23 = getr regs 23) by (apply EL; [lia | reflexivity]).
assert (E24 : ew E 24 = getr regs 24) by (apply EL; [lia | reflexivity]).
assert (E25 : ew E 25 = getr regs 25) by (apply EL; [lia | reflexivity]).
assert (E26 : ew E 26 = getr regs 26) by (apply EL; [lia | reflexivity]).
assert (E27 : ew E 27 = getr regs 27) by (apply EL; [lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. change (w64 AB_lowest_free_baseP) with (Z_to_bv 64 AB_lowest_free_baseP).
paj_run_to_tok RUNTO HS HJ SHOK LFB_span (AF_lowest_free_base + 0x54);
  [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
pmkst HS.
apply (lfb_loop ly S W regs mem md ch r k bs HPRE Hk Hin HL HV HB1 HB2 HB3 (Z.to_nat (F + 1)) 0); [lia|].
split; [exact HJ|].
split; [lfb_rq HS; rewrite Usp; reflexivity|].
split; [lfb_rq HS; exact E10|].
split; [lfb_rq HS; exact E11|].
split; [lfb_rq HS; reflexivity|].
split; [lfb_rq HS; rewrite E10, unsigned_lit_small by lia; reflexivity|].
split.
{ prreg_raw HS (20%bv : bv 5) Q20. rewrite Q20.
  lazymatch goal with |- sv_denot ?Ey _ = _ =>
    apply (denot_shx Ey 10 32 284 r LFB_SB); [lfb_ewq | lfb_ewq | lia | lia | lia | unfold LFB_SB; lia] end. }
split.
{ unfold lfb_keep. repeat split; lfb_rq HS; assumption. }
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ey _ (restrict _ ?msx) =>
    pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
    let Hy2 := fresh "Hy2" in assert (Hy2 : ew Ey 2 = getr regs 2) by lfb_ewq;
    assert (Hbase : bv_unsigned (ew Ey 2) = spZ regs) by (rewrite Hy2; reflexivity) end.
  apply lfb_frame_intro;
  [ lfb_fv HR Hbase (spZ regs) (-56) 21%nat | lfb_fv HR Hbase (spZ regs) (-48) 20%nat
  | lfb_fv HR Hbase (spZ regs) (-40) 19%nat | lfb_fv HR Hbase (spZ regs) (-32) 18%nat
  | lfb_fv HR Hbase (spZ regs) (-24) 9%nat | lfb_fv HR Hbase (spZ regs) (-16) 8%nat
  | lfb_fv HR Hbase (spZ regs) (-8) 1%nat ]. }
split; [lia|]. split; [left; reflexivity|].
intros c Hc. lia.
Qed.
End h.
End f.
End d.
