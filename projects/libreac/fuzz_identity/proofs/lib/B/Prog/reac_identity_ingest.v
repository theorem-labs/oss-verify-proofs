(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* reac_identity_ingest (fuzz_identity.asan-ubsan 0x83aa8, 0x5c4 bytes; listing offset AF_reac_identity_ingest = 0x3334,
   IdentBList.v lines 3307..3675): its ASan+UBSan-build contract treac_identity_ingest_spec.
   Form: cgif's caller-journal form (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v tlzw_kept / tlzw_pR_ok / tlzw_post /
   tlzw_spec, CONVENTIONS.md §2). LLVMFuzzerTestOneInput calls it four times: 0x80a34 (all arguments 0, set at
   0x80a24..0x80a30), 0x80a54 (a0 = ld 0xb8(s1), a1 = a2 = 0, a3 = 4, set at 0x80a44..0x80a50), and the two record
   calls a6+352 (0x80cf8) and a6+112 (0x80d94). The caller-journal form is needed for the two record calls, because
   they write up to 38 bytes of a record in the caller's frame: a6 is its class-4 side-stack frame
   (__asan_stack_malloc_4(768) at 0x807e8) or, when there is no fake frame, the realigned machine stack
   (0x80804..0x8081c). A callee whose apost_base FP covers a byte of its caller's frame cannot be composed by the
   caller (Reusable/YCbq.v:724-729 ajournal_sub and :1859-1860 accept only callee FP bytes that are in the
   caller's FP and in a block, or in a temporary block).
   The UBSan checks of this build are 20 branches to the trap word at 0x83f04 (IdentBList.v:3586) and no
   __ubsan_* call; each trap branch is discharged from the premises below (id mod 8 = 0, p <> 0 on a call that is
   not refused, the payload inside a live heap block, the record inside a frame or the machine stack), as the
   __asan_report_* error path is.
   The functional result is the released plain model, used as it is: lib/Prog/RcIdentModel.v (ING) and
   lib/Prog/reac_identity_ingest_c.v (ingest_refused, ingest_ret). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_reac_identity_ingest : Z := BASE + AF_reac_identity_ingest.
(* The stack the call needs, measured from the listing: the 32-byte frame (0x83aa8 addi sp,sp,-32; ra, s0, s1
   saved at sp+24, sp+16, sp+8), no realignment of sp, no side-stack frame, and no call on any path that
   returns (the only calls are the 23 __asan_report_* calls of the error path); plus ESTACK, CONVENTIONS §3. *)
Definition INGEST_STK : Z := 32 + ESTACK.
(* Allocator events and live heap bytes of one call: none. The plain model changes no byte outside the
   38-byte record (lib/Prog/reac_identity_ingest_c.v: munch [(id, id + 38)]) and the ASan+UBSan listing calls
   neither the allocator nor the side-stack allocator. *)
Definition EV_INGEST : Z := 0.
Definition LIVE_INGEST : Z := 0.
Section h.
Variable B : asyms.
(* The caller's 38-byte identity record at id, as tlzw_pR_ok and tlzw_spec's pR premises state pR: it lies
   in one live side-stack frame of the caller's current state or in the machine stack, it does not meet the
   callee's stack window, the caller may write each byte and each byte is present, the shadow says each byte
   is addressable (the shadow checks of the ASan stores read it), and it holds idb. *)
Definition ting_rec_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp id : Z) (idb : list byte)
  : Prop :=
  id mod 8 = 0 /\
  ((exists cid pos, In (cid, pos) (frames Sc) /\
      forall a, id <= a < id + 38 -> in_zr a (frame_rng lyc (cid, pos))) \/
   (ly_stk_lo lyc <= id /\ id + 38 <= ly_stk_hi lyc)) /\
  (sp <= id \/ id + 38 <= sp - INGEST_STK) /\
  (forall a, id <= a < id + 38 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 /\
  length idb = RcIdentModel.ID_SIZE /\
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb.
(* The payload p .. p + len: inside one live heap block of the caller's current state, and it holds pb. *)
Definition ting_pay_ok (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (p len : Z) (pb : list byte) : Prop :=
  (0 < len -> exists bi Li, In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + len <= bi + Li) /\
  mbytes_at SEGS (mrestrict (w_H W) memc) p pb.
(* What the call keeps is IdentBCJ.v's shared shape `tcj_kept B INGEST_STK` (cgif lib/YC20.v:311-330
   tlzw_kept): everything but its own stack window and the bytes E it may write. The call allocates
   nothing and writes no heap byte. *)
(* The bytes the call may write: the record, and only when the call is not refused. On a refused call it
   writes nothing outside its own window, so the caller keeps every byte of its frames and blocks. *)
Definition ting_E (id p len : Z) : Z -> Prop :=
  fun a => reac_identity_ingest_c.ingest_refused id p len = false /\ id <= a < id + 38.
(* The post-condition: the caller's journal extended to the return state (same layout, allocator state and
   world: the call allocates nothing), callee-saved registers kept, a0 = the plain model's result, the bytes
   outside the record and the callee's window kept, and the record = the plain model's new record. *)
Definition treac_identity_ingest_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (id ad p len : Z) (idb pb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 (k + EV_INGEST) /\
    aregs_preserved regs regs2 /\
    getr regs2 10 = w64 (reac_identity_ingest_c.ingest_ret id ad p len idb pb) /\
    tcj_kept B INGEST_STK lyc Sc W memc W mem2 (spZ regs) (ting_E id p len) /\
    (reac_identity_ingest_c.ingest_refused id p len = false ->
       mbytes_at SEGS (mrestrict (w_H W) mem2) id (snd (RcIdentModel.ING idb ad pb))).
Definition treac_identity_ingest_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\
     ting_pay_ok lyc Sc W memc p len pb) ->
  st_nev Sc + EV_INGEST <= EV_MAX -> blocks_bytes Sc + LIVE_INGEST <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
(* The walk's Section hypotheses (cgif lib/A/AChd.v:73-76, without its AMEMCMP): the allocator laws and the listing
   facts (the shadow GOT slot, object 1 at 0x9c690, and the shadow cell, object 31 at 0xa52b8, that
   0x83ac0..0x83ac8 read). No runtime entry and no callee contract: no call is reached on a path that returns. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).

(* The walk's symbolic state. Atoms: 0..31 the registers at the call, 32 the shadow base, 33..70 the 38 bytes
   of the record, 71..87 the first 17 bytes of the payload. *)
Definition SBi : Z := 0x7fff8000.
Definition IBx : sv := SOff 32 0.
Definition Ispan : Z * Z := (SBi, SBi + 2 ^ 44 - 1).
Definition rbyte (l : list byte) (j : nat) : Z := bv_unsigned (nth j l (Z_to_bv 8 0)).
Definition ing_extra (idb pb : list byte) : list word :=
  Z_to_bv 64 SBi :: map (fun j => Z_to_bv 64 (rbyte idb j)) (seq 0 38) ++ map (fun i => Z_to_bv 64 (rbyte pb i)) (seq 0 17).
Definition EI (regs : bvmap 5 word) (idb pb : list byte) : env := Eimg (Ereg regs (ing_extra idb pb)).
Definition REC : YP09.region := YP09.mkRegion (Some 10%nat) 0 38 0 38
  (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0))) (seq 0 38)).
Definition PAY (n : nat) : YP09.region := YP09.mkRegion (Some 12%nat) 0 (Z.of_nat n) 0 0
  (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (71 + i) 0))) (seq 0 n)).
Definition byte_atoms : list (nat * afact) := map (fun j => (j, mkAF 0 255 0)) (seq 33 55).
Definition regsC (n : nat) : smem := [stack_region 32; got_regionP; bcell_regionP 32; REC; PAY n].
Definition regs0 : smem := [stack_region 32; got_regionP; bcell_regionP 32].
Definition SHC (n : nat) : list shent := [mkSHE 10 0 38; mkSHE 12 0 (Z.of_nat n)].

Lemma rbyte_range : forall l j, 0 <= rbyte l j < 256.
Proof.
  intros l j. unfold rbyte. pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma EI_low : forall regs idb pb n, (n < A_TEXT)%nat -> ew (EI regs idb pb) n = ew (Ereg regs (ing_extra idb pb)) n.
Proof. intros regs idb pb n Hn. unfold EI. apply Eimg_low. exact Hn. Qed.

Lemma EI_reg : forall regs idb pb n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (EI regs idb pb) n = getr regs r.
Proof.
  intros regs idb pb n r Hn Hr. rewrite EI_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr).
Qed.

Lemma EI_sb : forall regs idb pb, ew (EI regs idb pb) 32 = Z_to_bv 64 SBi.
Proof. intros. rewrite EI_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

Lemma nth_map_seq0 : forall {X} (f : nat -> X) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros X f n j d Hj. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma EI_rec : forall regs idb pb j, (j < 38)%nat -> ew (EI regs idb pb) (33 + j) = Z_to_bv 64 (rbyte idb j).
Proof.
  intros regs idb pb j Hj. rewrite EI_low by (unfold A_TEXT; lia).
  replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold ing_extra.
  cbn [nth]. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
  exact (nth_map_seq0 (fun j => Z_to_bv 64 (rbyte idb j)) 38 j _ Hj).
Qed.

Lemma EI_pay : forall regs idb pb i, (i < 17)%nat -> ew (EI regs idb pb) (71 + i) = Z_to_bv 64 (rbyte pb i).
Proof.
  intros regs idb pb i Hi. rewrite EI_low by (unfold A_TEXT; lia).
  replace (71 + i)%nat with (32 + S (38 + i))%nat by lia. rewrite ew_Ereg_extra. unfold ing_extra.
  cbn [nth]. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. replace (38 + i - 38)%nat with i by lia.
  exact (nth_map_seq0 (fun i => Z_to_bv 64 (rbyte pb i)) 17 i _ Hi).
Qed.

Lemma EI_obj : forall regs idb pb i, (i < 32)%nat -> ew (EI regs idb pb) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs idb pb i Hi. unfold EI. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma val1_of_mbyte : forall m a b, mbyte SEGS m a = Some b -> val_mem SEGS m a 1 (bv_unsigned b).
Proof.
  intros m a b H k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, H. f_equal.
  rewrite le_byte_small by (pose proof (bv_unsigned_in_range 8 b) as R; change (bv_modulus 8) with 256 in R; cbn; lia).
  rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The numbers the walk needs, from the caller's journal and the premises of a call that is not refused. *)
Lemma ing_sp_bounds : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  alloc_ceiling + INGEST_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  (forall a, spZ regs - INGEST_STK <= a < spZ regs -> apresent (w_H W) memc a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H1 H2.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  split; [lia|]. split; [lia|]. intros a Ha. apply Hpres. lia.
Qed.

Lemma ing_rec_bounds : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) id idb,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  4096 <= id /\ id + 38 <= 2 ^ 47 /\ id mod 8 = 0 /\ (id + 38 <= IMG_LO \/ IMG_TOP <= id) /\
  (id + 38 <= SBi \/ SBi + 2 ^ 44 <= id) /\ (id + 38 <= spZ regs - INGEST_STK \/ spZ regs <= id).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id idb HJ H1 H2 HR.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HR as (Hal8 & Hloc & Hsp & Hwr & Hra & Hlen & Hmb).
  destruct Hloc as [(cid & pos & Hin & Hr) | (Hlo & Hhi)].
  - pose proof (Hr id ltac:(lia)) as R0. pose proof (Hr (id + 37) ltac:(lia)) as R1.
    unfold in_zr, frame_rng in R0, R1. cbn [fst snd] in R0, R1.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
    pose proof (YC1h.frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hoi.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hfa. unfold SBi.
    repeat split; try lia.
  - destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
    pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    unfold kHighMemEnd, kHighMemBeg in *. unfold SBi. rewrite Elo in Hlo. rewrite Ehi in Hhi.
    repeat split; try lia.
Qed.

Lemma ing_pay_bounds : forall lyc Sc W memc mdc p len pb,
  AR SEGS B lyc Sc W memc mdc -> ting_pay_ok lyc Sc W memc p len pb -> 0 < len ->
  exists bi Li, In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + len <= bi + req_size Li /\
  4096 <= p /\ p + len <= alloc_ceiling /\ (p + len <= IMG_LO \/ IMG_TOP <= p) /\
  (p + len <= SBi \/ SBi + 2 ^ 44 <= p).
Proof.
  intros lyc Sc W memc mdc p len pb HAR (Hblk & Hmb) Hl.
  destruct (Hblk Hl) as (bi & Li & Hin & H1 & H2).
  destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bi Li HAR Hin) as (B16 & B4096 & Bceil & Bia & _).
  pose proof (req_size_pos Li ltac:(lia)) as [Q1 Q2].
  pose proof (blk_off_imgP B lyc Sc W memc mdc bi Li HAR Hin) as Hoi.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Bia. unfold SBi.
  exists bi, Li. split; [exact Hin|]. repeat split; lia.
Qed.

Lemma ing_rec_pay_disj : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) id idb p len pb,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  ting_pay_ok lyc Sc W memc p len pb -> 0 < len ->
  p + len <= id \/ id + 38 <= p.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id idb p len pb HJ HR (Hblk & Hmb) Hl.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  destruct (Hblk Hl) as (bi & Li & Hin & H1 & H2).
  destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bi Li HAR Hin) as (B16 & B4096 & Bceil & Bia & _).
  pose proof (req_size_pos Li ltac:(lia)) as [Q1 Q2].
  destruct HR as (Hal8 & Hloc & _).
  destruct Hloc as [(cid & pos & Hinf & Hr) | (Hlo & Hhi)].
  - pose proof (Hr id ltac:(lia)) as R0. pose proof (Hr (id + 37) ltac:(lia)) as R1.
    unfold in_zr, frame_rng in R0, R1. cbn [fst snd] in R0, R1.
    pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc bi Li cid pos HAR Hin Hinf) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & _).
    rewrite Elo in Hlo. lia.
Qed.

Lemma base_EI : forall regs idb pb n v, ew (EI regs idb pb) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (EI regs idb pb) (Some n) = v.
Proof. intros regs idb pb n v H Hv. cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma base_sp : forall regs idb pb, base_val (EI regs idb pb) (Some 2%nat) = spZ regs.
Proof. intros. cbn [base_val]. rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]). reflexivity. Qed.

Lemma ro_stack : forall (W : world SEGS) memc regs idb pb,
  32 <= spZ regs -> spZ regs <= 2 ^ 47 ->
  (forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) memc a) ->
  region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc) (stack_region 32).
Proof.
  intros W memc regs idb pb H1 H2 Hp. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite base_sp.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

Lemma ro_got : forall lyc Sc (W : world SEGS) memc mdc regs idb pb,
  AR SEGS B lyc Sc W memc mdc ->
  region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc) got_regionP /\
  region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc) (bcell_regionP 32).
Proof.
  intros lyc Sc W memc mdc regs idb pb HAR.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_val_range (A_OBJ 1)) as R1. pose proof (pa_val_range (A_OBJ 31)) as R31.
  pose proof (pa_obj_img 1 ltac:(lia)) as I1. pose proof (pa_obj_img 31 ltac:(lia)) as I31.
  unfold region_ok, got_regionP, bcell_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (base_EI regs idb pb (A_OBJ 1) (VAL (A_OBJ 1)) (EI_obj regs idb pb 1 ltac:(lia))) by lia.
  rewrite (base_EI regs idb pb (A_OBJ 31) (VAL (A_OBJ 31)) (EI_obj regs idb pb 31 ltac:(lia))) by lia.
  split.
  - split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
    [cbn [sv_denot]; rewrite (EI_obj regs idb pb 31 ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  - split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 31)) 0 8 IBx SHADOW_OFF);
    [cbn [sv_denot IBx]; rewrite EI_sb, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
Qed.

Lemma ro_rec : forall STK sp0 FP ly S own lyc Sc (W : world SEGS) memc regs id idb pb,
  getr regs 10 = w64 id -> 0 <= id -> id + 38 <= 2 ^ 64 ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc) REC.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc regs id idb pb H10 H0 H1 HR.
  destruct HR as (Hal8 & Hloc & Hsp & Hwr & Hra & Hlen & Hmb).
  unfold region_ok, REC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (base_EI regs idb pb 10 id) by (try rewrite (EI_reg regs idb pb 10 10%bv) by (first [lia | vm_compute; reflexivity]); first [exact H10 | lia]).
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply (proj2 (Hwr (id + o) ltac:(lia))). }
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  apply (chunk_ok_val SEGS _ _ id (Z.of_nat j) 1 (SOff (33 + j) 0) (rbyte idb j)).
  - cbn [sv_denot]. rewrite (EI_rec regs idb pb j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (rbyte_range idb j). zside.
  - zside.
  - change (N.to_nat 1) with 1%nat. unfold rbyte. apply val1_of_mbyte.
    rewrite (Hmb j ltac:(unfold RcIdentModel.ID_SIZE in Hlen; lia)).
    apply nth_error_nth'. unfold RcIdentModel.ID_SIZE in Hlen. lia.
Qed.

Lemma ro_pay : forall lyc Sc (W : world SEGS) memc regs p len idb pb (n : nat),
  getr regs 12 = w64 p -> 0 <= p < 2 ^ 64 -> p + Z.of_nat n <= 2 ^ 64 ->
  ting_pay_ok lyc Sc W memc p len pb -> length pb = Z.to_nat len -> Z.of_nat n <= len -> (n <= 17)%nat ->
  region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc) (PAY n).
Proof.
  intros lyc Sc W memc regs p len idb pb n H12 H0 H1 (Hblk & Hmb) Hpl Hn Hn17.
  unfold region_ok, PAY. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (base_EI regs idb pb 12 p) by (try rewrite (EI_reg regs idb pb 12 12%bv) by (first [lia | vm_compute; reflexivity]); first [exact H12 | lia]).
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
  apply (chunk_ok_val SEGS _ _ p (Z.of_nat i) 1 (SOff (71 + i) 0) (rbyte pb i)).
  - cbn [sv_denot]. rewrite (EI_pay regs idb pb i ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (rbyte_range pb i). zside.
  - zside.
  - change (N.to_nat 1) with 1%nat. unfold rbyte. apply val1_of_mbyte.
    rewrite (Hmb i ltac:(lia)). apply nth_error_nth'. lia.
Qed.

Lemma ing_entry : forall (W : world SEGS) memc (regs : bvmap 5 word) idb pb rs G,
  regions_wf rs = true ->
  Forall (region_ok SEGS (EI regs idb pb) (mrestrict (w_H W) memc)) rs ->
  pairwise_disjoint (EI regs idb pb) rs ->
  facts_ok (EI regs idb pb) G ->
  st_ok_pi SEGS VAL (EI regs idb pb) (mkSS AF_reac_identity_ingest sr_atoms rs None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))).
Proof.
  intros W memc regs idb pb rs G Hwf Hro Hpd HG. rewrite restrict_mkst_fx.
  unfold A_reac_identity_ingest. apply pa_entry_st_ok_full; try assumption.
  unfold EI. apply regs_ok_Eimg_Ereg.
Qed.

(* What the walk carries from run to run: the memory changed only in the 32-byte frame below sp and, when the
   call is not refused, in the record; and no byte disappeared. *)
Definition ing_inv (sp id : Z) (rec : bool) (W : world SEGS) (memc m : word -> option byte) : Prop :=
  (forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> ~ (rec = true /\ id <= bv_unsigned x < id + 38) -> m x = memc x) /\
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m).

Lemma ing_inv_init : forall sp id rec W memc, ing_inv sp id rec W memc memc.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma ing_inv_step : forall sp id rec W memc m m' E rs,
  ing_inv sp id rec W memc m ->
  frame_of E rs m m' ->
  (forall a, in_wrange E rs a -> (sp - 32 <= a < sp) \/ (rec = true /\ id <= a < id + 38)) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  ing_inv sp id rec W memc m'.
Proof.
  intros sp id rec W memc m m' E rs (H1 & H2) HF HW HG. split.
  - intros x Hs Hr. rewrite <- (H1 x Hs Hr). apply HF. intros Hin. destruct (HW _ Hin); contradiction.
  - exact (mem_grows_trans _ _ _ H2 HG).
Qed.


Lemma ing_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regs2 : bvmap 5 word) mem2 md2
    id ad p len idb pb,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (reac_identity_ingest_c.ingest_ret id ad p len idb pb) ->
  ing_inv (spZ regs) id (negb (reac_identity_ingest_c.ingest_refused id p len)) W memc mem2 ->
  (reac_identity_ingest_c.ingest_refused id p len = false -> id + 38 <= IMG_LO \/ IMG_TOP <= id) ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     mbytes_at SEGS (mrestrict (w_H W) mem2) id (snd (RcIdentModel.ING idb ad pb))) ->
  treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb W
    (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 id ad p len idb pb
    HJ0 HJ2 HS1 HS2 HP H10 (HI1 & HI2) Hoff HR.
  pose proof (ing_sp_bounds STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ0 HS1 HS2) as (Sp1 & Sp2 & _).
  pose proof HJ0 as (HAR & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ ting_E id p len a ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hs He. apply (aview_eq_of SEGS). unfold mrestrict. rewrite HI1; [reflexivity | | ];
    rewrite unsigned_lit_small by lia; [exact Hs|].
    intros (Hr & Hin). apply He. split; [|exact Hin]. destruct (reac_identity_ingest_c.ingest_refused id p len); [discriminate Hr | reflexivity]. }
  unfold treac_identity_ingest_post. split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [unfold EV_INGEST; rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP|]. split; [exact H10|]. split; [|exact HR].
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw He. apply KEEP; [lia | lia | exact He].
  - intros b m i Hin Hi He.
    destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b m HAR Hin) as (B16 & B4096 & Bceil & _).
    apply KEEP; [lia | lia | exact He].
  - intros a Himg Hown Herr. pose proof (pa_img_range a Himg) as Hr.
    apply KEEP; [lia | lia |]. intros (Hnr & Hin). destruct (Hoff Hnr); lia.
  - intros cid pos a Hin Hz He.
    destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hz) as (Hc & Hz2).
    apply KEEP; [|lia | exact He].
    destruct Hz2 as [(Hz2 & Happ) | Hz2]; [unfold in_app in Happ | unfold kLowMemEnd, kHighShadowEnd in Hz2]; lia.
  - intros a Ha Hw Hpr. exact (apresent_grows (w_H W) memc mem2 a HI2 Hpr).
  - intros a Ha. apply Hpres2. lia.
Qed.

Definition G_C (fad flen : afact) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 38) 3); (11%nat, fad);
             (12%nat, mkAF 4096 (2 ^ 47 - 32) 0); (13%nat, flen); (32%nat, mkAF SBi SBi 0) ] ++ byte_atoms) [] [].

Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [Ha Hb]. split; [exact Ha | exact (IH l2 Hb H2)].
Qed.

Lemma byte_atoms_ok : forall regs idb pb, atoms_ok (EI regs idb pb) byte_atoms.
Proof.
  intros regs idb pb. unfold byte_atoms.
  assert (G : forall l, (forall j, In j l -> (33 <= j < 88)%nat) ->
            atoms_ok (EI regs idb pb) (map (fun j => (j, mkAF 0 255 0)) l)).
  { induction l as [|j l IH]; intros Hl; cbn [map atoms_ok]; [exact I|]. split.
    - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Z.pow_0_r, Z.mod_1_r.
      pose proof (Hl j (or_introl eq_refl)) as Hj.
      destruct (Nat.lt_ge_cases j 71) as [Hj7|Hj7].
      + replace j with (33 + (j - 33))%nat by lia. rewrite (EI_rec regs idb pb (j - 33)) by lia.
        pose proof (rbyte_range idb (j - 33)). rewrite unsigned_lit_small by lia. lia.
      + replace j with (71 + (j - 71))%nat by lia. rewrite (EI_pay regs idb pb (j - 71)) by lia.
        pose proof (rbyte_range pb (j - 71)). rewrite unsigned_lit_small by lia. lia.
    - apply IH. intros j' Hj'. apply Hl. right. exact Hj'. }
  apply G. intros j Hj. apply in_seq in Hj. lia.
Qed.

Lemma facts_C : forall (regs : bvmap 5 word) idb pb id p fad flen,
  getr regs 10 = w64 id -> getr regs 12 = w64 p ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= id <= 2 ^ 47 - 38 -> id mod 8 = 0 -> 4096 <= p <= 2 ^ 47 - 32 ->
  afact_ok (EI regs idb pb) 11 fad -> afact_ok (EI regs idb pb) 13 flen ->
  facts_ok (EI regs idb pb) (G_C fad flen).
Proof.
  intros regs idb pb id p fad flen H10 H12 Hsp Hal Hid Hid8 Hp F11 F13.
  unfold facts_ok, G_C. cbn [f_atoms f_conds f_alias conds_ok alias_ok]. split; [|split; exact I].
  apply atoms_ok_app; [|apply byte_atoms_ok].
  cbn [atoms_ok]. unfold afact_ok in *. cbn [af_lo af_hi af_al2] in *.
  rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]).
  rewrite (EI_reg regs idb pb 10 10%bv), H10 by (first [lia | vm_compute; reflexivity]).
  rewrite (EI_reg regs idb pb 12 12%bv), H12 by (first [lia | vm_compute; reflexivity]).
  rewrite EI_sb. unfold w64. rewrite !unsigned_lit_small by (unfold SBi; lia).
  change (bv_unsigned (getr regs 2)) with (spZ regs). change (2 ^ 4) with 16. change (2 ^ 3) with 8.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact F11 | exact F13 | lia].
Qed.

Lemma shok_C : forall lyc Sc (W : world SEGS) memc mdc (regs : bvmap 5 word) id p len idb pb (n : nat) bi Li,
  AR SEGS B lyc Sc W memc mdc ->
  getr regs 10 = w64 id -> getr regs 12 = w64 p -> 0 <= id < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 ->
  (id + 38 <= SBi \/ SBi + 2 ^ 44 <= id) ->
  In (bi, Li) (ablocks B lyc Sc) -> bi <= p -> p + len <= bi + req_size Li -> Z.of_nat n <= len ->
  (p + len <= SBi \/ SBi + 2 ^ 44 <= p) ->
  sh_ok SEGS IBx (SHC n) (EI regs idb pb) (mrestrict (w_H W) memc).
Proof.
  intros lyc Sc W memc mdc regs id p len idb pb n bi Li HAR H10 H12 Hid Hp Hra Hrs Hbi Hb1 Hb2 Hn Hps.
  pose proof (EI_reg regs idb pb 10 10%bv ltac:(lia) eq_refl) as E10. rewrite H10 in E10.
  pose proof (EI_reg regs idb pb 12 12%bv ltac:(lia) eq_refl) as E12. rewrite H12 in E12.
  unfold sh_ok, SHC. constructor; [|constructor; [|constructor]];
  unfold shent_ok, app_apart, IBx; cbn [she_m she_lo she_hi];
  rewrite (U_atom _ 32 SBi (EI_sb regs idb pb)) by (unfold SBi; lia).
  - rewrite (U_atom _ 10 id E10) by lia. split.
    + rewrite Z.add_0_r, Z.sub_0_r, <- (aview_rd_of SEGS). exact Hra.
    + intros a Ha. unfold SBi in *. lia.
  - rewrite (U_atom _ 12 p E12) by lia. split.
    + rewrite Z.add_0_r, Z.sub_0_r, <- (aview_rd_of SEGS).
      apply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc bi Li p (Z.of_nat n) HAR Hbi); lia.
    + intros a Ha. unfold SBi in *. lia.
Qed.

Lemma ing_entry_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) id p len idb pb
    (n : nat) fad flen,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 id -> getr regs 12 = w64 p -> 0 <= id < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  ting_pay_ok lyc Sc W memc p len pb ->
  (0 < n <= 17)%nat -> Z.of_nat n <= len -> regions_wf (regsC n) = true ->
  afact_ok (EI regs idb pb) 11 fad -> afact_ok (EI regs idb pb) 13 flen ->
  st_ok_pi SEGS VAL (EI regs idb pb) (mkSS AF_reac_identity_ingest sr_atoms (regsC n) None (G_C fad flen))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) /\
  sh_ok SEGS IBx (SHC n) (EI regs idb pb) (mrestrict (w_H W) memc).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb n fad flen
    HJ H10 H12 Hid Hp Hal HS1 HS2 Hpl HR HPy Hn Hnl Hwf F11 F13.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HJ as (HAR & _).
  destruct (ing_pay_bounds lyc Sc W memc mdc p len pb HAR HPy ltac:(lia)) as (bi & Li & Hbi & Hb1 & Hb2 & P1 & P2 & P3 & P4).
  pose proof (ing_rec_pay_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb p len pb HJ HR HPy ltac:(lia)) as RP.
  pose proof (pa_obj_img 1 ltac:(lia)) as I1. pose proof (pa_obj_img 31 ltac:(lia)) as I31.
  pose proof (pa_val_range (A_OBJ 1)) as V1. pose proof (pa_val_range (A_OBJ 31)) as V31.
  pose proof (pal_got_cell B TL) as Igc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof (EI_reg regs idb pb 10 10%bv ltac:(lia) eq_refl) as E10. rewrite H10 in E10.
  pose proof (EI_reg regs idb pb 12 12%bv ltac:(lia) eq_refl) as E12. rewrite H12 in E12.
  split.
  - apply ing_entry; [exact Hwf | | |].
    + destruct (ro_got lyc Sc W memc mdc regs idb pb HAR) as [Rg Rc].
      unfold regsC. repeat apply Forall_cons; try apply Forall_nil.
      * apply ro_stack; [lia | lia | intros a Ha; apply Swin; lia].
      * exact Rg.
      * exact Rc.
      * apply (ro_rec STK sp0 FP ly S own lyc Sc W memc regs id idb pb H10); [lia | lia | exact HR].
      * apply (ro_pay lyc Sc W memc regs p len idb pb n H12); [lia | lia | exact HPy | exact Hpl | lia | lia].
    + apply pairwise_disjoint_of_extents. unfold regsC, stack_region, got_regionP, bcell_regionP, REC, PAY, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite base_sp.
      rewrite (base_EI regs idb pb (A_OBJ 1) (VAL (A_OBJ 1)) (EI_obj regs idb pb 1 ltac:(lia))) by lia.
      rewrite (base_EI regs idb pb (A_OBJ 31) (VAL (A_OBJ 31)) (EI_obj regs idb pb 31 ltac:(lia))) by lia.
      rewrite (base_EI regs idb pb 10 id E10) by lia. rewrite (base_EI regs idb pb 12 p E12) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + apply (facts_C regs idb pb id p fad flen H10 H12); try lia; assumption.
  - apply (shok_C lyc Sc W memc mdc regs id p len idb pb n bi Li HAR H10 H12 Hid Hp); try lia; try assumption.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.

(* ---- walk tactics ------------------------------------------------------------------------------ *)
Ltac ing_ewn := repeat rewrite ew_ewset_other by lia.
Ltac ing_ewn_in H := repeat rewrite ew_ewset_other in H by lia.
(* The run's write right: the frame lies in the caller's window below sp, the image cells and the
   payload are not written, and the caller lets the call write the record. *)
Ltac ing_awr regs sp0 id Usp E10 HWR :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [ reflexivity | ing_ewn; rewrite Usp; lia
    | cbn [YP09.r_wlo YP09.r_whi]; unfold INGEST_STK, ESTACK in *; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat id);
    [ reflexivity | ing_ewn; rewrite E10; apply unsigned_lit_small; lia
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      exact (proj1 (HWR a ltac:(lia))) | ] ].
(* Where a run may write: its frame or the record. *)
Ltac ing_wr Usp E10 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat destruct Hin as [<- | Hin]; try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ing_ewn_in Ha;
  try rewrite Usp in Ha; try (rewrite E10, unsigned_lit_small in Ha by lia);
  first [ left; lia | right; split; [reflexivity | lia] ].
(* After a run: carry the invariant over the run's frame_of and mem_grows. *)
Ltac ing_keep HI Usp E10 :=
  lazymatch type of HI with ing_inv _ _ _ _ _ ?m0 =>
  lazymatch goal with HF : frame_of ?Ef ?rs m0 ?m2, HG : mem_grows (mrestrict _ m0) (mrestrict _ ?m2') |- _ =>
    let HI2 := fresh "HI2" in
    pose proof (ing_inv_step _ _ _ _ _ _ _ Ef rs HI HF ltac:(ing_wr Usp E10) HG) as HI2;
    clear HI; rename HI2 into HI
  end end;
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end;
  repeat match goal with Hg : mem_grows _ _ |- _ => clear Hg end.
(* ---- the leaves: the record's bytes at the return, from the final state's record region ---------- *)
Definition ing_j0 (P : Prop) : Prop := P.
Lemma rec_bytes : forall E (m : word -> option byte) id cs (l : list byte),
  Forall (YP09.chunk_ok SEGS E m id) cs -> length l = 38%nat ->
  (forall j, (j < 38)%nat ->
     match YP09.find_chunk cs (Z.of_nat j) 1 with
     | Some c => cbyte SEGS E (id + YP09.c_off c) (YP09.c_val c) (Z.of_nat j - YP09.c_off c) = Some (nth j l (Z_to_bv 8 0))
     | None => False end) ->
  mbytes_at SEGS m id l.
Proof.
  intros E m id cs l Hcs Hl H j Hj. rewrite Hl in Hj. specialize (H j Hj).
  destruct (YP09.find_chunk cs (Z.of_nat j) 1) as [c|] eqn:Hf; [|destruct H].
  destruct (YP09.find_chunk_sound cs _ _ c Hf) as (Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) Hcs c Hin) as Hc.
  destruct (Hc (Z.of_nat j - YP09.c_off c) ltac:(lia)) as (b & Hb1 & Hb2).
  rewrite H in Hb1. injection Hb1 as Hb1. subst b.
  replace (id + Z.of_nat j) with (id + YP09.c_off c + (Z.of_nat j - YP09.c_off c)) by lia.
  rewrite Hb2. symmetry. apply nth_error_nth'. lia.
Qed.
Lemma byte_of_lit : forall v k, 0 <= v < 2 ^ 64 -> byte_of_word (Z_to_bv 64 v) k = Z_to_bv 8 (Z.shiftr v (8 * k)).
Proof. intros v k Hv. unfold byte_of_word. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Lemma denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U. rewrite (U_atom E n v H Hv). reflexivity. Qed.
Lemma byte_atom : forall E n (b : byte), ew E n = Z_to_bv 64 (bv_unsigned b) -> byte_of_word (sv_denot E (SOff n 0)) 0 = b.
Proof.
  intros E n b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite (denot_atom E n (bv_unsigned b) H) by lia. rewrite byte_of_lit by lia.
  rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma byte_slit : forall E z, 0 <= z < 256 -> byte_of_word (sv_denot E (SLit z)) 0 = Z_to_bv 8 z.
Proof. intros E z Hz. cbn [sv_denot]. rewrite byte_of_lit by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma hc_ltu_k_atom : forall E n k v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SLit k)) (sv_denot E (SOff n 0)) = b -> (k <? v) = b.
Proof.
  intros E n k v b H Hv Hk Hc. rewrite branch_ltu_U, U_SLit, (U_atom E n v H Hv) in Hc.
  rewrite zcanon_id in Hc by (unfold M64; lia). exact Hc.
Qed.
Lemma rbyte_cons0 : forall (x : byte) l, rbyte (x :: l) 0 = bv_unsigned x.
Proof. reflexivity. Qed.
(* The generic return: RET, then ing_fin; leaves the result register and the record clause. *)
Ltac ing_leaf_gen :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msf') _ _,
    HJ0 : ing_j0 _, Hra : YK0s.ret_ok (getr ?regs 1),
    E1 : ew (EI ?regs ?idb ?pb) 1 = getr ?regs 1, HAE : env_agree 32 _ _,
    HS1 : ?sp0 - _ <= spZ ?regs - INGEST_STK, HS2 : spZ ?regs <= ?sp0, HI : ing_inv _ _ _ _ _ _ |- _ =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in
    prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat := fresh "mat" in intros mat; cbv beta;
    replace (v_jalr (getr (ms_regs msf) 1) 0) with (getr regs 1)
      by (rewrite R1; ing_ewn; rewrite E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity);
    eapply (ing_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs (ms_regs msf) (ms_mem msf));
    [ exact HJ0 | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact HS1 | exact HS2
    | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ing_extra idb pb) HS); [env_agree_chain HAE | vm_compute; reflexivity]
    | | lazymatch goal with Href : reac_identity_ingest_c.ingest_refused _ _ _ = ?r |- _ => rewrite Href; cbn [negb]; exact HI end
    | lazymatch goal with Href : reac_identity_ingest_c.ingest_refused _ _ _ = ?r |- _ =>
        let Hq := fresh "Hq" in intros Hq; first [assumption | rewrite Href in Hq; discriminate Hq] end
    | ]
  end.
(* What the walk does at a return. *)
Ltac ing_leaf := ing_leaf_gen.
(* The walk: run to the next stop; at a branch, walk both sides; at the return, ing_leaf. *)
Ltac ing_go regs sp0 id Usp E10 HWR HI :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Ispan; [ing_awr regs sp0 id Usp E10 HWR |];
  ing_keep HI Usp E10;
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ ?SH _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM IBx SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K IBx Ispan SH (start K IBx Ispan SH ss) end in
    lazymatch why with
    | SR_jalr _ => ing_leaf
    | SR_branch _ _ _ =>
        psrr_branch_tok RUN BR HS' SHOK' Ispan;
        [ ing_go regs sp0 id Usp E10 HWR HI | ing_go regs sp0 id Usp E10 HWR HI ]
    | _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
    end
  end end.

(* ---- the firmware arm (ad = 0, 4 <= len) ----------------------------------------------------------- *)
Lemma bz_nthb_rbyte : forall l i, RcIdentModel.bz (RcIdentModel.nthb l i) = rbyte l i.
Proof. reflexivity. Qed.
Lemma fw_denot : forall E a b c d,
  ew E 71 = Z_to_bv 64 a -> ew E 72 = Z_to_bv 64 b -> ew E 73 = Z_to_bv 64 c -> ew E 74 = Z_to_bv 64 d ->
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 71 0) (SLit 1000)) (SMd M_MUL (SOff 72 0) (SLit 100)))
    (SMd M_MUL (SOff 73 0) (SLit 10))) (SOff 74 0)) = Z_to_bv 64 (a * 1000 + b * 100 + c * 10 + d).
Proof.
  intros E a b c d Ha Hb Hc Hd Ra Rb Rc Rd. rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu, !U_SMd, !U_SLit. cbn [zalu_raw zmd_raw].
  rewrite (U_atom E 71 a Ha), (U_atom E 72 b Hb), (U_atom E 73 c Hc), (U_atom E 74 d Hd) by lia.
  rewrite !(zcanon_id 1000), !(zcanon_id 100), !(zcanon_id 10) by (unfold M64; lia).
  rewrite (zcanon_id (a * 1000)), (zcanon_id (b * 100)), (zcanon_id (c * 10)) by (unfold M64; lia).
  rewrite (zcanon_id (a * 1000 + b * 100)) by (unfold M64; lia).
  rewrite (zcanon_id (a * 1000 + b * 100 + c * 10)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma byte_word0 : forall v, 0 <= v < 2 ^ 64 -> byte_of_word (Z_to_bv 64 v) 0 = RcIdentModel.zb (v mod 256).
Proof. intros v Hv. rewrite byte_of_lit by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. unfold RcIdentModel.zb. symmetry. apply Z_to_bv8_mod. Qed.
Lemma byte_word1 : forall v, 0 <= v < 2 ^ 64 -> byte_of_word (Z_to_bv 64 v) 1 = RcIdentModel.zb ((v / 256) mod 256).
Proof.
  intros v Hv. rewrite byte_of_lit by lia. change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  unfold RcIdentModel.zb. symmetry. apply Z_to_bv8_mod.
Qed.
Ltac ing_len_side :=
  rewrite ?RcIdentLib.upd_len_full, ?RcIdentLib.length_le16, ?length_app, ?length_firstn, ?length_skipn;
  cbn [length]; lia.
(* The bytes of a record after one or two writes, one index at a time. *)
Ltac ing_nth_upd :=
  unfold RcIdentModel.OFF_FW, RcIdentModel.OFF_HAS_FW, RcIdentModel.OFF_NAME, RcIdentModel.OFF_HAS_NAME,
    RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH, RcIdentModel.OFF_RAW, RcIdentModel.OFF_HAS_VER;
  change (nth ?j ?l (Z_to_bv 8 0)) with (RcIdentModel.nthb l j);
  repeat first
  [ rewrite RcIdentLib.nthb_upd_in by ing_len_side
  | rewrite RcIdentLib.nthb_upd_lt by ing_len_side
  | rewrite RcIdentLib.nthb_upd_ge by ing_len_side ];
  cbn [Nat.sub RcIdentModel.nthb nth RcIdentModel.le16].
(* Branch conditions on a payload byte, as (k <? byte) = b. *)
Ltac ing_pay_hcs :=
  repeat match goal with
  | Hc : branch_taken BC_LTU (sv_denot ?E' (SLit ?k)) (sv_denot ?E' (SOff ?n 0)) = ?b |- _ =>
    lazymatch E' with context [EI ?regs ?idb ?pb] =>
    let i := eval cbv in (n - 71)%nat in
    let D := fresh "D" in
    assert (D : (k <? rbyte pb i) = b)
      by (apply (hc_ltu_k_atom E' n k (rbyte pb i) b);
          [ ing_ewn; exact (EI_pay regs idb pb i ltac:(lia)) | pose proof (rbyte_range pb i); lia | lia | exact Hc ]);
    clear Hc end
  end.

(* The result register at a leaf: a0 = the model's result; leaves  Z_to_bv 64 c = Z_to_bv 64 (model). *)
Ltac ing_r10 :=
  lazymatch goal with R10 : getr _ 10 = _ |- getr _ 10 = w64 (reac_identity_ingest_c.ingest_ret _ _ _ _ _ _) =>
    rewrite R10; unfold w64, reac_identity_ingest_c.ingest_ret;
    lazymatch goal with Href : reac_identity_ingest_c.ingest_refused _ _ _ = _ |- _ => rewrite Href end;
    cbv iota end.
(* The firmware arm's model: ING_fw with the digit tests the walk took. *)
Ltac fw_ing_rw :=
  rewrite RcIdentLib.ING_fw by lia; rewrite ?bz_nthb_rbyte, ?Z.leb_antisym;
  repeat match goal with D : (9 <? rbyte ?pb ?i) = _ |- context [9 <? rbyte ?pb ?i] => rewrite D end;
  cbn [negb andb fst snd].
(* The record region of the final state and the chunk facts it gives. *)
Ltac ing_find10 l :=
  lazymatch l with
  | (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) :: _ => constr:(YP09.mkRegion (Some 10%nat) lo hi wlo whi cs)
  | _ :: ?t => ing_find10 t
  end.
Ltac ing_rec_chunks HCH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ef _ (restrict (w_H ?W) ?msf), E10 : ew (EI _ _ _) 10 = Z_to_bv 64 ?id |- _ =>
    let HRok := fresh "HRok" in let HR10 := fresh "HR10" in let B10 := fresh "B10" in
    pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
    lazymatch type of HRok with Forall _ ?rs =>
      let rs' := eval vm_compute in rs in
      let r := ing_find10 rs' in
      assert (HR10 : YP09.region_ok SEGS Ef (ms_mem (restrict (w_H W) msf)) r)
        by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In];
            repeat (first [left; reflexivity | right]))
    end;
    destruct HR10 as (_ & _ & _ & HCH); cbn [YP09.r_chunks YP09.r_base base_val] in HCH;
    assert (B10 : bv_unsigned (ew Ef 10) = id) by (ing_ewn; rewrite E10; apply unsigned_lit_small; lia);
    rewrite B10 in HCH; cbn [restrict ms_mem] in HCH; clear HRok
  end.
(* One byte of the record at a leaf. *)
Ltac ing_rec_byte_solve :=
  first
  [ apply byte_atom; ing_ewn;
    lazymatch goal with |- ew _ ?n = _ => let jj := eval cbv in (n - 33)%nat in exact (EI_rec _ _ _ jj ltac:(lia)) end
  | rewrite byte_slit by lia; reflexivity
  | lazymatch goal with |- byte_of_word (sv_denot ?Ef _) ?k = _ =>
    lazymatch Ef with context [EI ?regs ?idb ?pb] =>
    rewrite (fw_denot Ef (rbyte pb 0) (rbyte pb 1) (rbyte pb 2) (rbyte pb 3));
    [ first [rewrite byte_word0 | rewrite byte_word1];
      [ unfold RcIdentModel.fw_value; rewrite ?bz_nthb_rbyte; reflexivity
      | pose proof (rbyte_range pb 0); pose proof (rbyte_range pb 1); pose proof (rbyte_range pb 2);
        pose proof (rbyte_range pb 3); lia ]
    | ing_ewn; exact (EI_pay regs idb pb 0 ltac:(lia)) | ing_ewn; exact (EI_pay regs idb pb 1 ltac:(lia))
    | ing_ewn; exact (EI_pay regs idb pb 2 ltac:(lia)) | ing_ewn; exact (EI_pay regs idb pb 3 ltac:(lia))
    | apply rbyte_range | apply rbyte_range | apply rbyte_range | apply rbyte_range ] end end ].
Ltac ing_rec_j :=
  lazymatch goal with |- match YP09.find_chunk ?cs ?o 1 with _ => _ end =>
    let r := eval vm_compute in (YP09.find_chunk cs o 1) in change (YP09.find_chunk cs o 1) with r end;
  cbv iota beta; cbn [cbyte YP09.c_off YP09.c_val];
  lazymatch goal with |- context [Z.of_nat ?j - ?o] => let r := eval vm_compute in (Z.of_nat j - o) in change (Z.of_nat j - o) with r end;
  f_equal; ing_nth_upd; ing_rec_byte_solve.
(* The length of a record after writes. *)
Ltac ing_len38 :=
  unfold RcIdentModel.OFF_FW, RcIdentModel.OFF_HAS_FW, RcIdentModel.OFF_NAME, RcIdentModel.OFF_HAS_NAME,
    RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH, RcIdentModel.OFF_RAW, RcIdentModel.OFF_HAS_VER;
  rewrite ?RcIdentLib.upd_len_full; cbn [length RcIdentModel.le16]; rewrite ?length_app, ?length_firstn, ?length_skipn;
  cbn [length]; lia.
(* The record clause at a leaf: the final record region gives the bytes. *)
Ltac ing_mb :=
  lazymatch goal with |- reac_identity_ingest_c.ingest_refused _ _ _ = false -> mbytes_at _ _ _ _ =>
    let Hq := fresh "Hq" in intros Hq; cbn [snd];
    let HCH := fresh "HCH" in ing_rec_chunks HCH;
    apply (rec_bytes _ _ _ _ _ HCH);
    [ ing_len38
    | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
      do 38 (destruct j as [|j]; [ing_rec_j|]); lia ] end.

Lemma ing_arm_fw : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 0 -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 4 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  reac_identity_ingest_c.ingest_refused id p len = false ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  ting_pay_ok lyc Sc W memc p len pb ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id 0 p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Hp Hlen Hal16 HS1 HS2 Hpl Href HR HPy.
  pose proof HR as (_ & _ & _ & _ & _ & HIdl & _). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HR as (_ & _ & _ & HWR & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof (EI_reg regs idb pb 1 1%bv ltac:(lia) eq_refl) as E1.
  pose proof (EI_reg regs idb pb 10 10%bv ltac:(lia) eq_refl) as E10. rewrite H10 in E10. unfold w64 in E10.
  assert (Usp : bv_unsigned (ew (EI regs idb pb) 2) = spZ regs) by (rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]); reflexivity).
  assert (HEI : img_env VAL A_LIM (EI regs idb pb)) by (unfold EI; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ing_extra idb pb)) (EI regs idb pb))
    by (split; [intros n Hn; unfold EI; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (ing_entry_C STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb 4
    (mkAF 0 0 0) (mkAF 4 (2 ^ 64 - 1) 0) HJ0 H10 H12 Hid Hp Hal16 HS1 HS2 Hpl HR HPy ltac:(lia) ltac:(lia)
    ltac:(vm_compute; reflexivity)) as [HS0 SHOK].
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EI_reg regs idb pb 11 11%bv) by (first [lia | vm_compute; reflexivity]).
    rewrite H11. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EI_reg regs idb pb 13 13%bv) by (first [lia | vm_compute; reflexivity]).
    rewrite H13. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  (* a1 is 0: the walk knows it, so the dispatch on the address is decided. *)
  pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 0 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  pose proof HJ0 as HJ.
  change memc with (ms_mem (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) in HJ.
  change (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k) with
    (ing_j0 (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k)) in HJ0.
  pose proof (ing_inv_init (spZ regs) id true W memc) as HI.
  unfold cfg_at. change (w64 A_reac_identity_ingest) with (Z_to_bv 64 A_reac_identity_ingest).
  ing_go regs sp0 id Usp E10 HWR HI.
  all: ing_pay_hcs.
  all: first [ ing_r10; fw_ing_rw; reflexivity | idtac ].
  all: intros Hq; fw_ing_rw; ing_rec_chunks HCH; apply (rec_bytes _ _ _ _ _ HCH); [ing_len38|];
       intros j Hj; do 38 (destruct j as [|j]; [ing_rec_j|]); lia.
Qed.

(* ---- the version arm (ad = 1536, 8 <= len) ------------------------------------------------------- *)
(* The version arm stores the raw word p[0..7] as four halfwords (id+28..id+35) and the three big-endian
   halfwords at id+22, id+24, id+26; these lemmas give the bytes of those chunk values. *)
Lemma ver_lor_add : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
  intros a b k Hk Ha Hb.
  assert (L : Z.land (a * 2 ^ k) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ k) Hb). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.
Lemma ver_U_sll : forall E a x m t, U E a = x -> zcanon t = t -> Z.land t 63 = t -> m = 2 ^ t -> 0 <= t ->
  0 <= x -> x * m < 2 ^ 64 -> U E (SAlu ALU_SLL a (SLit t)) = x * m.
Proof.
  intros E a x m t Hx Hz Hl Hm Ht H0 H1. subst m.
  rewrite U_SAlu, Hx, U_SLit, Hz. cbn [zalu_raw]. rewrite Hl, Z.shiftl_mul_pow2 by exact Ht.
  apply zcanon_id. unfold M64. pose proof (Z.mul_nonneg_nonneg x (2 ^ t) H0 (Z.pow_nonneg 2 t ltac:(lia))). lia.
Qed.
Lemma ver_U_or : forall E a b Av Bv x m t, U E a = Av -> U E b = Bv -> m = 2 ^ t -> 0 <= t -> Av = x * m -> 0 <= x ->
  0 <= Bv < m -> Av + Bv < 2 ^ 64 -> U E (SAlu ALU_OR a b) = Av + Bv.
Proof.
  intros E a b Av Bv x m t HA HB Hm Ht HAx Hx HBm Hlt. subst m.
  pose proof (Z.mul_nonneg_nonneg x (2 ^ t) Hx (Z.pow_nonneg 2 t ltac:(lia))) as Hn.
  rewrite U_SAlu, HA, HB. cbn [zalu_raw]. rewrite HAx, ver_lor_add by lia. rewrite <- HAx.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma ver_U_srl : forall E a x m t, U E a = x -> zcanon t = t -> Z.land t 63 = t -> m = 2 ^ t -> 0 <= t ->
  U E (SAlu ALU_SRL a (SLit t)) = x / m.
Proof.
  intros E a x m t Hx Hz Hl Hm Ht. subst m.
  pose proof (U_range E a) as R. rewrite Hx in R. unfold M64 in R.
  pose proof (Z.pow_pos_nonneg 2 t ltac:(lia) Ht) as P.
  rewrite U_SAlu, Hx, U_SLit, Hz. cbn [zalu_raw]. rewrite Hl, Z.shiftr_div_pow2 by exact Ht.
  apply zcanon_id. unfold M64.
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ x); [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma ver_byte_lit : forall v k d (b : byte), 0 <= v < 2 ^ 64 -> 0 <= k -> d = 2 ^ (8 * k) ->
  (v / d) mod 256 = bv_unsigned b -> byte_of_word (Z_to_bv 64 v) k = b.
Proof.
  intros v k d b Hv Hk Hd H. rewrite byte_of_lit by exact Hv. rewrite Z.shiftr_div_pow2 by lia. rewrite <- Hd.
  apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2 ^ 8). change (2 ^ 8) with 256. exact H.
Qed.
(* The byte goals of a value v: (v / 2^(8k)) mod 256 = byte. *)
Ltac ver_byte_goals :=
  lazymatch goal with |- byte_of_word _ ?k = _ =>
    let d := eval vm_compute in (2 ^ (8 * k)) in
    apply (ver_byte_lit _ k d); [Z.div_mod_to_equations; lia | lia | reflexivity | Z.div_mod_to_equations; lia] end.
Lemma ver_be_bytes : forall E na nb (x y : byte),
  ew E na = Z_to_bv 64 (bv_unsigned x) -> ew E nb = Z_to_bv 64 (bv_unsigned y) ->
  byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff na 0) (SLit 8)) (SOff nb 0))) 0 = y /\
  byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff na 0) (SLit 8)) (SOff nb 0))) 1 = x.
Proof.
  intros E na nb x y Hx Hy.
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry.
  change (bv_modulus 8) with 256 in Rx, Ry.
  assert (Ax : U E (SOff na 0) = bv_unsigned x) by (apply U_atom; [exact Hx | lia]).
  assert (Ay : U E (SOff nb 0) = bv_unsigned y) by (apply U_atom; [exact Hy | lia]).
  assert (S1 : U E (SAlu ALU_SLL (SOff na 0) (SLit 8)) = bv_unsigned x * 256)
    by (apply (ver_U_sll E _ _ 256 8 Ax); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (V : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff na 0) (SLit 8)) (SOff nb 0)) = bv_unsigned x * 256 + bv_unsigned y)
    by (apply (ver_U_or E _ _ _ _ (bv_unsigned x) 256 8 S1 Ay); [reflexivity | lia | lia | lia | lia | lia]).
  rewrite denot_lit_U, V. split; ver_byte_goals.
Qed.
Definition ver_rawT : sv :=
  SAlu ALU_OR
    (SAlu ALU_SLL
       (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 78 0) (SLit 24)) (SAlu ALU_SLL (SOff 77 0) (SLit 16)))
          (SAlu ALU_OR (SAlu ALU_SLL (SOff 76 0) (SLit 8)) (SOff 75 0)))
       (SLit 32))
    (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 74 0) (SLit 24)) (SAlu ALU_SLL (SOff 73 0) (SLit 16)))
       (SAlu ALU_OR (SAlu ALU_SLL (SOff 72 0) (SLit 8)) (SOff 71 0))).
Lemma ver_raw_U : forall E q0 q1 q2 q3 q4 q5 q6 q7,
  ew E 71 = Z_to_bv 64 q0 -> ew E 72 = Z_to_bv 64 q1 -> ew E 73 = Z_to_bv 64 q2 -> ew E 74 = Z_to_bv 64 q3 ->
  ew E 75 = Z_to_bv 64 q4 -> ew E 76 = Z_to_bv 64 q5 -> ew E 77 = Z_to_bv 64 q6 -> ew E 78 = Z_to_bv 64 q7 ->
  0 <= q0 < 256 -> 0 <= q1 < 256 -> 0 <= q2 < 256 -> 0 <= q3 < 256 ->
  0 <= q4 < 256 -> 0 <= q5 < 256 -> 0 <= q6 < 256 -> 0 <= q7 < 256 ->
  U E ver_rawT = (q7 * 16777216 + q6 * 65536 + (q5 * 256 + q4)) * 4294967296
                 + (q3 * 16777216 + q2 * 65536 + (q1 * 256 + q0)).
Proof.
  intros E q0 q1 q2 q3 q4 q5 q6 q7 H0 H1 H2 H3 H4 H5 H6 H7 R0 R1 R2 R3 R4 R5 R6 R7.
  assert (A0 : U E (SOff 71 0) = q0) by (apply U_atom; [exact H0 | lia]).
  assert (A1 : U E (SOff 72 0) = q1) by (apply U_atom; [exact H1 | lia]).
  assert (A2 : U E (SOff 73 0) = q2) by (apply U_atom; [exact H2 | lia]).
  assert (A3 : U E (SOff 74 0) = q3) by (apply U_atom; [exact H3 | lia]).
  assert (A4 : U E (SOff 75 0) = q4) by (apply U_atom; [exact H4 | lia]).
  assert (A5 : U E (SOff 76 0) = q5) by (apply U_atom; [exact H5 | lia]).
  assert (A6 : U E (SOff 77 0) = q6) by (apply U_atom; [exact H6 | lia]).
  assert (A7 : U E (SOff 78 0) = q7) by (apply U_atom; [exact H7 | lia]).
  assert (L1 : U E (SAlu ALU_SLL (SOff 72 0) (SLit 8)) = q1 * 256)
    by (apply (ver_U_sll E _ _ 256 8 A1); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (L2 : U E (SAlu ALU_SLL (SOff 73 0) (SLit 16)) = q2 * 65536)
    by (apply (ver_U_sll E _ _ 65536 16 A2); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (L3 : U E (SAlu ALU_SLL (SOff 74 0) (SLit 24)) = q3 * 16777216)
    by (apply (ver_U_sll E _ _ 16777216 24 A3); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (L5 : U E (SAlu ALU_SLL (SOff 76 0) (SLit 8)) = q5 * 256)
    by (apply (ver_U_sll E _ _ 256 8 A5); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (L6 : U E (SAlu ALU_SLL (SOff 77 0) (SLit 16)) = q6 * 65536)
    by (apply (ver_U_sll E _ _ 65536 16 A6); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (L7 : U E (SAlu ALU_SLL (SOff 78 0) (SLit 24)) = q7 * 16777216)
    by (apply (ver_U_sll E _ _ 16777216 24 A7); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  assert (O1 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 72 0) (SLit 8)) (SOff 71 0)) = q1 * 256 + q0)
    by (apply (ver_U_or E _ _ _ _ q1 256 8 L1 A0); [reflexivity | lia | lia | lia | lia | lia]).
  assert (O2 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 74 0) (SLit 24)) (SAlu ALU_SLL (SOff 73 0) (SLit 16)))
               = q3 * 16777216 + q2 * 65536)
    by (apply (ver_U_or E _ _ _ _ q3 16777216 24 L3 L2); [reflexivity | lia | lia | lia | lia | lia]).
  assert (O3 : U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 74 0) (SLit 24)) (SAlu ALU_SLL (SOff 73 0) (SLit 16)))
                      (SAlu ALU_OR (SAlu ALU_SLL (SOff 72 0) (SLit 8)) (SOff 71 0)))
               = q3 * 16777216 + q2 * 65536 + (q1 * 256 + q0))
    by (apply (ver_U_or E _ _ _ _ (q3 * 256 + q2) 65536 16 O2 O1); [reflexivity | lia | lia | lia | lia | lia]).
  assert (O4 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 76 0) (SLit 8)) (SOff 75 0)) = q5 * 256 + q4)
    by (apply (ver_U_or E _ _ _ _ q5 256 8 L5 A4); [reflexivity | lia | lia | lia | lia | lia]).
  assert (O5 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 78 0) (SLit 24)) (SAlu ALU_SLL (SOff 77 0) (SLit 16)))
               = q7 * 16777216 + q6 * 65536)
    by (apply (ver_U_or E _ _ _ _ q7 16777216 24 L7 L6); [reflexivity | lia | lia | lia | lia | lia]).
  assert (O6 : U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 78 0) (SLit 24)) (SAlu ALU_SLL (SOff 77 0) (SLit 16)))
                      (SAlu ALU_OR (SAlu ALU_SLL (SOff 76 0) (SLit 8)) (SOff 75 0)))
               = q7 * 16777216 + q6 * 65536 + (q5 * 256 + q4))
    by (apply (ver_U_or E _ _ _ _ (q7 * 256 + q6) 65536 16 O5 O4); [reflexivity | lia | lia | lia | lia | lia]).
  assert (L8 : U E (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 78 0) (SLit 24))
                      (SAlu ALU_SLL (SOff 77 0) (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 76 0) (SLit 8)) (SOff 75 0)))
                      (SLit 32))
               = (q7 * 16777216 + q6 * 65536 + (q5 * 256 + q4)) * 4294967296)
    by (apply (ver_U_sll E _ _ 4294967296 32 O6); [reflexivity | reflexivity | reflexivity | lia | lia | lia]).
  unfold ver_rawT.
  apply (ver_U_or E _ _ _ _ (q7 * 16777216 + q6 * 65536 + (q5 * 256 + q4)) 4294967296 32 L8 O3);
    [reflexivity | lia | lia | lia | lia | lia].
Qed.
Lemma ver_raw_bytes : forall E (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  ew E 71 = Z_to_bv 64 (bv_unsigned b0) -> ew E 72 = Z_to_bv 64 (bv_unsigned b1) ->
  ew E 73 = Z_to_bv 64 (bv_unsigned b2) -> ew E 74 = Z_to_bv 64 (bv_unsigned b3) ->
  ew E 75 = Z_to_bv 64 (bv_unsigned b4) -> ew E 76 = Z_to_bv 64 (bv_unsigned b5) ->
  ew E 77 = Z_to_bv 64 (bv_unsigned b6) -> ew E 78 = Z_to_bv 64 (bv_unsigned b7) ->
  byte_of_word (sv_denot E ver_rawT) 0 = b0 /\ byte_of_word (sv_denot E ver_rawT) 1 = b1 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 16))) 0 = b2 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 16))) 1 = b3 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 32))) 0 = b4 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 32))) 1 = b5 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 48))) 0 = b6 /\
  byte_of_word (sv_denot E (SAlu ALU_SRL ver_rawT (SLit 48))) 1 = b7.
Proof.
  intros E b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 H2 H3 H4 H5 H6 H7.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5.
  pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
  change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
  pose proof (ver_raw_U E _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4 H5 H6 H7 R0 R1 R2 R3 R4 R5 R6 R7) as V.
  pose proof (ver_U_srl E ver_rawT _ 65536 16 V eq_refl eq_refl eq_refl ltac:(lia)) as V16.
  pose proof (ver_U_srl E ver_rawT _ 4294967296 32 V eq_refl eq_refl eq_refl ltac:(lia)) as V32.
  pose proof (ver_U_srl E ver_rawT _ 281474976710656 48 V eq_refl eq_refl eq_refl ltac:(lia)) as V48.
  rewrite !denot_lit_U, V16, V32, V48, V.
  repeat split; ver_byte_goals.
Qed.
Lemma ver_byte_one : forall E, byte_of_word (sv_denot E (SLit 1)) 0 = RcIdentModel.zb 1.
Proof. intros E. rewrite byte_slit by lia. reflexivity. Qed.
(* Leaf tactics of the version arm: copies of ing_len38 / ing_nth_upd / ing_rec_j / ing_rec_byte_solve whose
   arithmetic side goals see only the record-length hypothesis, plus the raw-word and big-endian chunks. *)
Ltac ver_len_side :=
  rewrite ?RcIdentLib.upd_len_full, ?RcIdentLib.length_le16, ?length_app, ?length_firstn, ?length_skipn;
  cbn [length]; lazymatch goal with H : length ?l = 38%nat |- _ => clear - H; lia end.
Ltac ver_len38 :=
  unfold RcIdentModel.OFF_FW, RcIdentModel.OFF_HAS_FW, RcIdentModel.OFF_NAME, RcIdentModel.OFF_HAS_NAME,
    RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH, RcIdentModel.OFF_RAW, RcIdentModel.OFF_HAS_VER;
  rewrite ?RcIdentLib.upd_len_full; cbn [length RcIdentModel.le16]; rewrite ?length_app, ?length_firstn, ?length_skipn;
  cbn [length]; lazymatch goal with H : length ?l = 38%nat |- _ => clear - H; lia end.
Ltac ver_nth_upd :=
  unfold RcIdentModel.OFF_FW, RcIdentModel.OFF_HAS_FW, RcIdentModel.OFF_NAME, RcIdentModel.OFF_HAS_NAME,
    RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH, RcIdentModel.OFF_RAW, RcIdentModel.OFF_HAS_VER;
  change (nth ?j ?l (Z_to_bv 8 0)) with (RcIdentModel.nthb l j);
  repeat first
  [ rewrite RcIdentLib.nthb_upd_in by ver_len_side
  | rewrite RcIdentLib.nthb_upd_lt by ver_len_side
  | rewrite RcIdentLib.nthb_upd_ge by ver_len_side ];
  cbn [Nat.sub RcIdentModel.nthb nth RcIdentModel.le16].
(* A premise  ew Ef n = Z_to_bv 64 (bv_unsigned (nth i pb _))  for a payload atom n = 71 + i. *)
Ltac ver_pay_goal regs idb pb :=
  ing_ewn;
  lazymatch goal with |- ew _ ?n = _ =>
    let i := eval cbv in (n - 71)%nat in exact (EI_pay regs idb pb i (proj1 (Nat.ltb_lt i 17) eq_refl)) end.
Ltac ver_prem regs idb pb P :=
  repeat lazymatch type of P with
  | ?A -> _ => let Q := fresh "Q" in assert (Q : A) by ver_pay_goal regs idb pb; specialize (P Q); clear Q
  end.
Ltac ver_rec_byte_solve :=
  lazymatch goal with
  | |- byte_of_word (sv_denot _ (SOff ?n 0)) _ = _ =>
    apply byte_atom; ing_ewn;
    let jj := eval cbv in (n - 33)%nat in exact (EI_rec _ _ _ jj (proj1 (Nat.ltb_lt jj 38) eq_refl))
  | |- byte_of_word (sv_denot _ (SLit 1)) 0 = _ => exact (ver_byte_one _)
  | |- byte_of_word (sv_denot ?Ef (SAlu ALU_OR (SAlu ALU_SLL (SOff ?na 0) (SLit 8)) (SOff ?nb 0))) ?k = _ =>
    lazymatch Ef with context [EI ?regs ?idb ?pb] =>
    let ia := eval cbv in (na - 71)%nat in let ib := eval cbv in (nb - 71)%nat in
    let P := fresh "P" in
    pose proof (ver_be_bytes Ef na nb (nth ia pb (Z_to_bv 8 0)) (nth ib pb (Z_to_bv 8 0))) as P;
    ver_prem regs idb pb P;
    lazymatch k with Z0 => exact (proj1 P) | Zpos xH => exact (proj2 P) end end
  | |- byte_of_word (sv_denot ?Ef ?t) ?k = _ =>
    lazymatch Ef with context [EI ?regs ?idb ?pb] =>
    let P := fresh "P" in
    pose proof (ver_raw_bytes Ef (nth 0 pb (Z_to_bv 8 0)) (nth 1 pb (Z_to_bv 8 0)) (nth 2 pb (Z_to_bv 8 0))
      (nth 3 pb (Z_to_bv 8 0)) (nth 4 pb (Z_to_bv 8 0)) (nth 5 pb (Z_to_bv 8 0)) (nth 6 pb (Z_to_bv 8 0))
      (nth 7 pb (Z_to_bv 8 0))) as P;
    ver_prem regs idb pb P;
    let V0 := fresh "VB" in let V1 := fresh "VB" in let V2 := fresh "VB" in let V3 := fresh "VB" in
    let V4 := fresh "VB" in let V5 := fresh "VB" in let V6 := fresh "VB" in let V7 := fresh "VB" in
    destruct P as (V0 & V1 & V2 & V3 & V4 & V5 & V6 & V7);
    lazymatch t with
    | SAlu ALU_SRL _ (SLit 16) => lazymatch k with Z0 => exact V2 | Zpos xH => exact V3 end
    | SAlu ALU_SRL _ (SLit 32) => lazymatch k with Z0 => exact V4 | Zpos xH => exact V5 end
    | SAlu ALU_SRL _ (SLit 48) => lazymatch k with Z0 => exact V6 | Zpos xH => exact V7 end
    | SAlu ALU_OR _ _ => lazymatch k with Z0 => exact V0 | Zpos xH => exact V1 end
    end end
  end.
(* One byte of the record at the version arm's leaf. *)
Ltac ver_rec_j :=
  lazymatch goal with |- match YP09.find_chunk ?cs ?o 1 with _ => _ end =>
    let r := eval vm_compute in (YP09.find_chunk cs o 1) in change (YP09.find_chunk cs o 1) with r end;
  cbv iota beta; cbn [cbyte YP09.c_off YP09.c_val];
  lazymatch goal with |- context [Z.of_nat ?j - ?o] => let r := eval vm_compute in (Z.of_nat j - o) in change (Z.of_nat j - o) with r end;
  f_equal; ver_nth_upd; ver_rec_byte_solve.

Lemma ing_arm_ver : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 1536 -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 8 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  reac_identity_ingest_c.ingest_refused id p len = false ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  ting_pay_ok lyc Sc W memc p len pb ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id 1536 p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Hp Hlen Hal16 HS1 HS2 Hpl Href HR HPy.
  pose proof HR as (_ & _ & _ & _ & _ & HIdl & _). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HR as (_ & _ & _ & HWR & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof (EI_reg regs idb pb 1 1%bv ltac:(lia) eq_refl) as E1.
  pose proof (EI_reg regs idb pb 10 10%bv ltac:(lia) eq_refl) as E10. rewrite H10 in E10. unfold w64 in E10.
  assert (Usp : bv_unsigned (ew (EI regs idb pb) 2) = spZ regs) by (rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]); reflexivity).
  assert (HEI : img_env VAL A_LIM (EI regs idb pb)) by (unfold EI; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ing_extra idb pb)) (EI regs idb pb))
    by (split; [intros n Hn; unfold EI; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (ing_entry_C STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb 8
    (mkAF 1536 1536 0) (mkAF 8 (2 ^ 64 - 1) 0) HJ0 H10 H12 Hid Hp Hal16 HS1 HS2 Hpl HR HPy ltac:(lia) ltac:(lia)
    ltac:(vm_compute; reflexivity)) as [HS0 SHOK].
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EI_reg regs idb pb 11 11%bv) by (first [lia | vm_compute; reflexivity]).
    rewrite H11. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EI_reg regs idb pb 13 13%bv) by (first [lia | vm_compute; reflexivity]).
    rewrite H13. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  (* a1 is 1536: the walk knows it, so the dispatch on the address is decided. *)
  pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 1536 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  pose proof HJ0 as HJ.
  change memc with (ms_mem (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) in HJ.
  change (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k) with
    (ing_j0 (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k)) in HJ0.
  pose proof (ing_inv_init (spZ regs) id true W memc) as HI.
  unfold cfg_at. change (w64 A_reac_identity_ingest) with (Z_to_bv 64 A_reac_identity_ingest).
  (* One path: the engine decides every branch (the dispatch from the pinned a1, the length test from
     8 <= len, the UBSan trap branches from the facts on id and p) and stops at the return. *)
  ing_go regs sp0 id Usp E10 HWR HI.
  - ing_r10. rewrite (RcIdentLib.ING_ver idb pb) by (clear - Hpl Hlen; lia). reflexivity.
  - intros Hq. rewrite (RcIdentLib.ING_ver idb pb) by (clear - Hpl Hlen; lia).
    rewrite !RcIdentLib.le16_be16. cbn [snd].
    ing_rec_chunks HCH. apply (rec_bytes _ _ _ _ _ HCH); [ver_len38|].
    intros j Hj. do 38 (destruct j as [|j]; [ver_rec_j|]). clear - Hj; lia.
Qed.

(* ---- the calls that write no record byte: refused (id = 0, or p = 0 with len <> 0), len = 0, a payload too
   short for its address, an address that is not 0, 0x600 or 0x1000. The walk starts from the stack and the two
   image cells only (regs0, no shadow entry: no path checks a shadow byte), and it carries ing_inv with the record
   not writable; at the return the record clause comes from the record at the call (ing0_rec_keep). ---------- *)
Definition ing0_G (al : list (nat * afact)) (cs : list acond) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBi SBi 0) ] ++ al) cs [].

Lemma ing0_facts : forall (regs : bvmap 5 word) idb pb al cs,
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  atoms_ok (EI regs idb pb) al -> conds_ok (EI regs idb pb) cs ->
  facts_ok (EI regs idb pb) (ing0_G al cs).
Proof.
  intros regs idb pb al cs Hsp Hal Ha Hc.
  unfold facts_ok, ing0_G. cbn [f_atoms f_conds f_alias alias_ok]. split; [|split; [exact Hc | exact I]].
  apply atoms_ok_app; [|exact Ha].
  cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]).
  rewrite EI_sb. rewrite unsigned_lit_small by (unfold SBi; lia).
  change (bv_unsigned (getr regs 2)) with (spZ regs). change (2 ^ 4) with 16.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* A register's entry value in [lo, hi]. *)
Lemma ing0_afact : forall (regs : bvmap 5 word) idb pb (n : nat) (r : bv 5) v lo hi,
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok (EI regs idb pb) n (mkAF lo hi 0).
Proof.
  intros regs idb pb n r v lo hi Hn Hr H Hv Hlh. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EI_reg regs idb pb n r Hn Hr), H. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* A register's entry value differs from the literal c: the engine decides beq/bne of that register and c. *)
Lemma ing0_acond : forall (regs : bvmap 5 word) idb pb (n : nat) (r : bv 5) v c,
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> v <> c ->
  acond_ok (EI regs idb pb) (mkAC BC_NE (SOff n 0) (SLit c)).
Proof.
  intros regs idb pb n r v c Hn Hr H Hv Hc Hne. unfold acond_ok. cbn [ac_c ac_a ac_b].
  assert (U1 : U (EI regs idb pb) (SOff n 0) = v)
    by (apply U_atom; [rewrite (EI_reg regs idb pb n r Hn Hr), H; reflexivity | exact Hv]).
  rewrite branch_ne_U, U_SLit, U1. rewrite zcanon_id by (unfold M64; lia).
  apply negb_true_iff, Z.eqb_neq. exact Hne.
Qed.

Lemma ing0_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) idb pb al cs,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  atoms_ok (EI regs idb pb) al -> conds_ok (EI regs idb pb) cs ->
  st_ok_pi SEGS VAL (EI regs idb pb) (mkSS AF_reac_identity_ingest sr_atoms regs0 None (ing0_G al cs))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) /\
  sh_ok SEGS IBx [] (EI regs idb pb) (mrestrict (w_H W) memc).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb al cs HJ Hal HS1 HS2 Ha Hc.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof HJ as (HAR & _).
  pose proof (pa_obj_img 1 ltac:(lia)) as I1. pose proof (pa_obj_img 31 ltac:(lia)) as I31.
  pose proof (pa_val_range (A_OBJ 1)) as V1. pose proof (pa_val_range (A_OBJ 31)) as V31.
  pose proof (pal_got_cell B TL) as Igc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  split; [|unfold sh_ok; constructor].
  apply ing_entry; [vm_compute; reflexivity | | |].
  - destruct (ro_got lyc Sc W memc mdc regs idb pb HAR) as [Rg Rc].
    unfold regs0. repeat apply Forall_cons; try apply Forall_nil.
    + apply ro_stack; [lia | lia | intros a Ha'; apply Swin; lia].
    + exact Rg.
    + exact Rc.
  - apply pairwise_disjoint_of_extents. unfold regs0, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite base_sp.
    rewrite (base_EI regs idb pb (A_OBJ 1) (VAL (A_OBJ 1)) (EI_obj regs idb pb 1 ltac:(lia))) by lia.
    rewrite (base_EI regs idb pb (A_OBJ 31) (VAL (A_OBJ 31)) (EI_obj regs idb pb 31 ltac:(lia))) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - apply ing0_facts; [lia | exact Hal | exact Ha | exact Hc].
Qed.

Lemma ing_inv_weak : forall sp id W memc m, ing_inv sp id false W memc m -> ing_inv sp id true W memc m.
Proof.
  intros sp id W memc m (H1 & H2). split; [|exact H2].
  intros x Hs _. apply H1; [exact Hs|]. intros (Hf & _). discriminate Hf.
Qed.

(* The record is apart from the frame, so a run that wrote only the frame left its bytes as they were. *)
Lemma ing0_rec_keep : forall sp id W memc m idb,
  ing_inv sp id false W memc m -> 0 <= id -> id + 38 <= 2 ^ 64 -> (id + 38 <= sp - 32 \/ sp <= id) ->
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb -> length idb = 38%nat ->
  mbytes_at SEGS (mrestrict (w_H W) m) id idb.
Proof.
  intros sp id W memc m idb (HI & _) H0 H1 Hsp Hmb Hl j Hj. rewrite <- (Hmb j Hj).
  rewrite Hl in Hj. unfold mbyte, mrestrict. cbv beta.
  rewrite (HI (Z_to_bv 64 (id + Z.of_nat j))); [reflexivity | |].
  - rewrite unsigned_lit_small by lia. lia.
  - intros (Hf & _). discriminate Hf.
Qed.

Lemma ing0_nref : forall id p len, reac_identity_ingest_c.ingest_refused id p len = false ->
  id <> 0 /\ (len <> 0 -> p <> 0).
Proof.
  intros id p len H. unfold reac_identity_ingest_c.ingest_refused in H.
  apply orb_false_iff in H as [H1 H2]. apply Z.eqb_neq in H1. split; [exact H1|].
  intros Hl Hp. subst p. rewrite (proj2 (Z.eqb_neq len 0) Hl) in H2. cbn in H2. discriminate H2.
Qed.

Lemma ing0_ING_nil : forall idb ad, RcIdentModel.ING idb ad [] = (0, idb).
Proof.
  intros idb ad.
  destruct (Z.eq_dec ad 0) as [->|H0]; [apply RcIdentLib.ING_fw_short; cbn; lia|].
  destruct (Z.eq_dec ad 4096) as [->|H1]; [apply RcIdentLib.ING_name_zero; cbn; lia|].
  destruct (Z.eq_dec ad 1536) as [->|H2]; [apply RcIdentLib.ING_ver_short; cbn; lia|].
  apply RcIdentLib.ING_other; assumption.
Qed.

(* ing_leaf_gen with the record not writable: when the call is not refused, ing_fin's invariant (record
   writable) follows from the walk's (ing_inv_weak). *)
Ltac ing_leaf0 :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msf') _ _,
    HJ0 : ing_j0 _, Hra : YK0s.ret_ok (getr ?regs 1),
    E1 : ew (EI ?regs ?idb ?pb) 1 = getr ?regs 1, HAE : env_agree 32 _ _,
    HS1 : ?sp0 - _ <= spZ ?regs - INGEST_STK, HS2 : spZ ?regs <= ?sp0, HI : ing_inv _ _ _ _ _ _ |- _ =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in
    prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat := fresh "mat" in intros mat; cbv beta;
    replace (v_jalr (getr (ms_regs msf) 1) 0) with (getr regs 1)
      by (rewrite R1; ing_ewn; rewrite E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity);
    eapply (ing_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs (ms_regs msf) (ms_mem msf));
    [ exact HJ0 | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact HS1 | exact HS2
    | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ing_extra idb pb) HS); [env_agree_chain HAE | vm_compute; reflexivity]
    | | lazymatch goal with Href : reac_identity_ingest_c.ingest_refused _ _ _ = ?r |- _ =>
          rewrite Href; cbn [negb]; first [exact HI | exact (ing_inv_weak _ _ _ _ _ HI)] end
    | lazymatch goal with Href : reac_identity_ingest_c.ingest_refused _ _ _ = ?r |- _ =>
        let Hq := fresh "Hq" in intros Hq; first [assumption | rewrite Href in Hq; discriminate Hq] end
    | ]
  end.
(* ing_go with ing_leaf0 at a return. *)
Ltac ing0_go regs sp0 id Usp E10 HWR HI :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Ispan; [ing_awr regs sp0 id Usp E10 HWR |];
  ing_keep HI Usp E10;
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ ?SH _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM IBx SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K IBx Ispan SH (start K IBx Ispan SH ss) end in
    lazymatch why with
    | SR_jalr _ => ing_leaf0
    | SR_branch _ _ _ =>
        psrr_branch_tok RUN BR HS' SHOK' Ispan;
        [ ing0_go regs sp0 id Usp E10 HWR HI | ing0_go regs sp0 id Usp E10 HWR HI ]
    | _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
    end
  end end.
(* What a call that is not refused knows before the walk: the record of any memory the walk can reach is idb. *)
Definition ing0_keep (sp id : Z) (W : world SEGS) (memc : word -> option byte) (idb : list byte) : Prop :=
  forall m, ing_inv sp id false W memc m -> mbytes_at SEGS (mrestrict (w_H W) m) id idb.
(* The two goals ing_leaf0 leaves: a0, and the record clause. A call that is not refused has, from before the
   walk, M : ING idb ad pb = (0, idb) and K : ing0_keep (spZ regs) id W memc idb. *)
Ltac ing0_close :=
  lazymatch goal with
  | |- getr _ 10 = w64 _ =>
      ing_r10;
      first [ lazymatch goal with M : RcIdentModel.ING _ _ _ = _ |- _ => rewrite M end; cbn [fst]; reflexivity
            | reflexivity
            | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ]
  | Href : reac_identity_ingest_c.ingest_refused _ _ _ = true |- reac_identity_ingest_c.ingest_refused _ _ _ = false -> _ =>
      let Hq := fresh "Hq" in intros Hq; rewrite Href in Hq; discriminate Hq
  | HI : ing_inv _ _ false _ _ _, M : RcIdentModel.ING _ _ _ = _, K : ing0_keep _ _ _ _ _
    |- reac_identity_ingest_c.ingest_refused _ _ _ = false -> mbytes_at _ _ _ _ =>
      let Hq := fresh "Hq" in intros Hq; rewrite M; cbn [snd]; exact (K _ HI)
  end.
(* From the entry state HS (regs0, at most one register pinned): the environment facts, the journal, the
   invariant, then the walk. *)
Ltac ing0_walk regs sp0 id H10 HJ0 HWR :=
  lazymatch type of HJ0 with ajournal ?segs ?b ?STK ?sp0' ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?W ?memc ?mdc ?k =>
  lazymatch goal with HS : st_ok_pi _ _ (EI regs ?idb ?pb) _ _ |- _ =>
    let E1 := fresh "E1" in let E10 := fresh "E10" in let Usp := fresh "Usp" in let HEI := fresh "HEI" in
    let HAE := fresh "HAE" in let HJ := fresh "HJ" in let HI := fresh "HI" in
    pose proof (EI_reg regs idb pb 1 1%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl) as E1;
    pose proof (EI_reg regs idb pb 10 10%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl) as E10;
    rewrite H10 in E10; unfold w64 in E10;
    assert (Usp : bv_unsigned (ew (EI regs idb pb) 2) = spZ regs)
      by (rewrite (EI_reg regs idb pb 2 2%bv) by (first [apply Nat.ltb_lt; reflexivity | vm_compute; reflexivity]);
          reflexivity);
    assert (HEI : img_env VAL A_LIM (EI regs idb pb)) by (unfold EI; apply Eimg_env);
    assert (HAE : env_agree 32 (Ereg regs (ing_extra idb pb)) (EI regs idb pb))
      by (split; [let n := fresh "n" in let Hn := fresh "Hn" in
                  intros n Hn; unfold EI; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]);
    pose proof HJ0 as HJ;
    change memc with (ms_mem (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) in HJ;
    change (ing_j0 (ajournal segs b STK sp0' FP ly S W0 mem0 md0 own lyc Sc W memc mdc k)) in HJ0;
    pose proof (ing_inv_init (spZ regs) id false W memc) as HI;
    unfold cfg_at; change (w64 A_reac_identity_ingest) with (Z_to_bv 64 A_reac_identity_ingest);
    ing0_go regs sp0 id Usp E10 HWR HI
  end end.

(* Refused, id = 0: beqz a0 at 0x83abc goes to the return with a0 = -1. *)
Lemma ing_refused_id0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\ ting_pay_ok lyc Sc W memc p len pb) ->
  id = 0 ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl Hok Hc.
  subst id. clear Hok.
  assert (Href : reac_identity_ingest_c.ingest_refused 0 p len = true) by reflexivity.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb [] [] HJ0 Hal16 HS1 HS2 I I)
    as [HS0 SHOK].
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H10; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  ing0_walk regs sp0 0 H10 HJ0 HS1.
  all: ing0_close.
Qed.

(* Refused, p = 0 and len <> 0: bnez a3 at 0x83ad0 goes to the return with a0 = -1. *)
Lemma ing_refused_p0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\ ting_pay_ok lyc Sc W memc p len pb) ->
  id <> 0 -> p = 0 -> len <> 0 ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl Hok Hid0 Hp0 Hlen0.
  subst p. clear Hok.
  assert (Href : reac_identity_ingest_c.ingest_refused id 0 len = true).
  { unfold reac_identity_ingest_c.ingest_refused. rewrite (proj2 (Z.eqb_neq len 0) Hlen0).
    destruct (id =? 0); reflexivity. }
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (HA : atoms_ok (EI regs idb pb) [(10%nat, mkAF 1 (2 ^ 64 - 1) 0); (13%nat, mkAF 1 (2 ^ 64 - 1) 0)]).
  { cbn [atoms_ok]. split; [|split; [|exact I]].
    - apply (ing0_afact regs idb pb 10 10%bv id); [lia | reflexivity | exact H10 | lia | lia].
    - apply (ing0_afact regs idb pb 13 13%bv len); [lia | reflexivity | exact H13 | lia | lia]. }
  destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ [] HJ0 Hal16 HS1 HS2 HA I)
    as [HS0 SHOK].
  pose proof (st_ok_pi_pin_reg' _ _ _ (12%bv : bv 5) 0 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H12; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  ing0_walk regs sp0 id H10 HJ0 HS1.
  all: ing0_close.
Qed.

(* Not refused, len = 0: every address returns 0 at 0x83d44 and writes nothing (ING with pb = []). *)
Lemma ing_len0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\ ting_pay_ok lyc Sc W memc p len pb) ->
  reac_identity_ingest_c.ingest_refused id p len = false -> len = 0 ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl Hok Href Hl0.
  subst len. destruct (Hok Href) as [HR HPy]. clear Hok.
  destruct pb as [|b0 pb]; [|cbn in Hpl; lia].
  pose proof HR as (_ & _ & _ & _ & _ & HIdl & HMB). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof (ing0_ING_nil idb ad) as ING0.
  assert (KEEP : ing0_keep (spZ regs) id W memc idb)
    by (intros m HIm; apply (ing0_rec_keep (spZ regs) id W memc m idb HIm); [lia | lia | lia | exact HMB | exact HIdl]).
  assert (HA : atoms_ok (EI regs idb []) [(10%nat, mkAF 1 (2 ^ 64 - 1) 0)]).
  { cbn [atoms_ok]. split; [|exact I].
    apply (ing0_afact regs idb [] 10 10%bv id); [lia | reflexivity | exact H10 | lia | lia]. }
  destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb [] _ [] HJ0 Hal16 HS1 HS2 HA I)
    as [HS0 SHOK].
  pose proof (st_ok_pi_pin_reg' _ _ _ (13%bv : bv 5) 0 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H13; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  ing0_walk regs sp0 id H10 HJ0 HS1.
  all: ing0_close.
Qed.

(* Not refused, a payload too short for its address: a1 is pinned, so the dispatch and the length test are
   decided; the walk returns 0 at 0x83d44 and writes nothing (ING_fw_short, ING_ver_short, ING_name_zero). *)
Lemma ing_short : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\ ting_pay_ok lyc Sc W memc p len pb) ->
  reac_identity_ingest_c.ingest_refused id p len = false -> 1 <= len ->
  (ad = 0 /\ len < 4 \/ ad = 1536 /\ len < 8 \/ ad = 4096 /\ len < 2) ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl Hok Href Hl1 Hsh.
  destruct (Hok Href) as [HR HPy]. clear Hok.
  destruct (ing0_nref id p len Href) as [Hid0 Hpn]. specialize (Hpn ltac:(lia)).
  pose proof HR as (_ & _ & _ & _ & _ & HIdl & HMB). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (KEEP : ing0_keep (spZ regs) id W memc idb)
    by (intros m HIm; apply (ing0_rec_keep (spZ regs) id W memc m idb HIm); [lia | lia | lia | exact HMB | exact HIdl]).
  assert (HA : forall hi, len <= hi -> atoms_ok (EI regs idb pb)
    [(10%nat, mkAF 1 (2 ^ 64 - 1) 0); (12%nat, mkAF 1 (2 ^ 64 - 1) 0); (13%nat, mkAF 1 hi 0)]).
  { intros hi Hhi. cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
    - apply (ing0_afact regs idb pb 10 10%bv id); [lia | reflexivity | exact H10 | lia | lia].
    - apply (ing0_afact regs idb pb 12 12%bv p); [lia | reflexivity | exact H12 | lia | lia].
    - apply (ing0_afact regs idb pb 13 13%bv len); [lia | reflexivity | exact H13 | lia | lia]. }
  destruct Hsh as [(-> & Hl) | [(-> & Hl) | (-> & Hl)]].
  - assert (ING0 : RcIdentModel.ING idb 0 pb = (0, idb))
      by (apply RcIdentLib.ING_fw_short; clear - Hpl Hl Hl1; lia).
    destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ [] HJ0 Hal16 HS1 HS2
      (HA 3 ltac:(lia)) I) as [HS0 SHOK].
    pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 0 HS0
      ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
    clear HS0.
    ing0_walk regs sp0 id H10 HJ0 HS1.
    all: ing0_close.
  - assert (ING0 : RcIdentModel.ING idb 1536 pb = (0, idb))
      by (apply RcIdentLib.ING_ver_short; clear - Hpl Hl Hl1; lia).
    destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ [] HJ0 Hal16 HS1 HS2
      (HA 7 ltac:(lia)) I) as [HS0 SHOK].
    pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 1536 HS0
      ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
    clear HS0.
    ing0_walk regs sp0 id H10 HJ0 HS1.
    all: ing0_close.
  - assert (ING0 : RcIdentModel.ING idb 4096 pb = (0, idb))
      by (apply RcIdentLib.ING_name_zero; left; clear - Hpl Hl Hl1; lia).
    destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ [] HJ0 Hal16 HS1 HS2
      (HA 1 ltac:(lia)) I) as [HS0 SHOK].
    pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 4096 HS0
      ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
    clear HS0.
    ing0_walk regs sp0 id H10 HJ0 HS1.
    all: ing0_close.
Qed.

(* Not refused, 1 <= len, an address other than 0, 0x600, 0x1000: the facts say a1 <> 0x1000, 0x600, 0, so
   the dispatch is decided (0x83ad8, 0x83ae0, 0x83ae4) and the walk returns 0 at 0x83d44 (ING_other). *)
Lemma ing_other : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\ ting_pay_ok lyc Sc W memc p len pb) ->
  reac_identity_ingest_c.ingest_refused id p len = false -> 1 <= len -> ad <> 0 -> ad <> 1536 -> ad <> 4096 ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl Hok Href Hl1 Ha0 Ha1536 Ha4096.
  destruct (Hok Href) as [HR HPy]. clear Hok.
  destruct (ing0_nref id p len Href) as [Hid0 Hpn]. specialize (Hpn ltac:(lia)).
  pose proof HR as (_ & _ & _ & _ & _ & HIdl & HMB). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof (RcIdentLib.ING_other idb ad pb Ha0 Ha4096 Ha1536) as ING0.
  assert (KEEP : ing0_keep (spZ regs) id W memc idb)
    by (intros m HIm; apply (ing0_rec_keep (spZ regs) id W memc m idb HIm); [lia | lia | lia | exact HMB | exact HIdl]).
  assert (HA : atoms_ok (EI regs idb pb)
    [(10%nat, mkAF 1 (2 ^ 64 - 1) 0); (12%nat, mkAF 1 (2 ^ 64 - 1) 0); (13%nat, mkAF 1 (2 ^ 64 - 1) 0)]).
  { cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
    - apply (ing0_afact regs idb pb 10 10%bv id); [lia | reflexivity | exact H10 | lia | lia].
    - apply (ing0_afact regs idb pb 12 12%bv p); [lia | reflexivity | exact H12 | lia | lia].
    - apply (ing0_afact regs idb pb 13 13%bv len); [lia | reflexivity | exact H13 | lia | lia]. }
  assert (HC : conds_ok (EI regs idb pb)
    [mkAC BC_NE (SOff 11 0) (SLit 4096); mkAC BC_NE (SOff 11 0) (SLit 1536); mkAC BC_NE (SOff 11 0) (SLit 0)]).
  { cbn [conds_ok]. split; [|split; [|split; [|exact I]]];
    apply (ing0_acond regs idb pb 11 11%bv ad); first [exact H11 | reflexivity | lia]. }
  destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ _ HJ0 Hal16 HS1 HS2 HA HC)
    as [HS SHOK].
  ing0_walk regs sp0 id H10 HJ0 HS1.
  all: ing0_close.
Qed.

(* ================================================================================================
   The name arm (ad = 0x1000, 2 <= len). The text from the listing offsets to nm_at_zero is
   a Theorem Labs lane's frozen interface, copied as it is except that its
   `B` arguments are dropped (inside Section h, B is a section variable). a Theorem Labs lane proves nm_loop
   (the loop head -> an end, by induction on the iterations left); this lane proves the three ends:
   nm_ent (the function entry -> the loop head at i = 0, then nm_loop), nm_exit_ok (0x83eb0 -> the
   return) and nm_zero_ok (0x83d44 -> the return). The owner composes
     ing_arm_name := nm_ent (nm_loop nm_exit_ok nm_zero_ok).                                        *)
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation bz := RcIdentModel.bz.
Let RUNTO := paj_run_to B LAWS.

(* ---- listing offsets ---------------------------------------------------------------------------- *)
Definition AF_nm_head : Z := AF_reac_identity_ingest + 0x2d0.   (* 0x83d78 *)
Definition AF_nm_exit : Z := AF_reac_identity_ingest + 0x408.   (* 0x83eb0 *)
Definition AF_nm_zero : Z := AF_reac_identity_ingest + 0x29c.   (* 0x83d44 *)

(* ---- the loop-head symbolic state (a Theorem Labs lane's; the ends do not need it) --------------------------- *)
(* a6 (atom 16) holds the shadow base in the whole arm. *)
Definition BXN : sv := SOff 16 0.
Definition nm_loop_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
    YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))] ].
Definition nm_loop_facts : facts :=
  mkFacts [ (16%nat, mkAF SBi SBi 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (5%nat, mkAF 0 0 0); (13%nat, mkAF 0 15 0);
            (7%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0);
            (17%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0);
            (15%nat, mkAF 1 16 0); (12%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (6%nat, mkAF 4096 (2 ^ 47 - 8) 0); (14%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (10%nat, mkAF 4096 (2 ^ 47 - 8) 0) ]
          [ mkAC BC_EQ (SOff 5 0) (SLit 0) ]
          [ (SAlu ALU_ADD (SOff 6 0) (SOff 13 0), SOff 32 0);
            (SAlu ALU_ADD (SOff 14 0) (SOff 13 0), SOff 33 0) ].
Definition ss_nm_loop : sstate := mkSS AF_nm_head sr_atoms nm_loop_regions None nm_loop_facts.
Definition SH_nm_loop : list shent := [mkSHE 32 0 1; mkSHE 33 0 1].
Definition nm_extra (pa ra : Z) (b c : byte) : list word :=
  [w64 pa; w64 ra; w64 (RcIdentModel.bz b); w64 (RcIdentModel.bz c)].

(* ---- the states of the two ends ------------------------------------------------------------------ *)
(* The 32-byte frame, read-only for both ends (neither writes it): s1 at sp' + 8, s0 at + 16, ra at
   + 24, with sp' = spZ regs - 32 (atom 2) the arm's stack pointer. *)
Definition nm2_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 9 0)); YP09.mkChunk 16 (CVal 8 (SOff 8 0));
     YP09.mkChunk 24 (CVal 8 (SOff 1 0))].
(* 0x83d44 .. the return: a4 := 0, a0 := a4, the three reloads; no branch, no store, no shadow test. *)
Definition nm2_zregions : smem := [nm2_frame].
Definition nm2_zfacts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 0) ] [] [].
Definition ss_nm2_zero : sstate := mkSS AF_nm_zero sr_atoms nm2_zregions None nm2_zfacts.
(* 0x83eb0 .. the return: the NUL at a4 + a3 (the alias names that address atom 32) and the flag at
   a0 + 20; the trap branch at 0x83eb0 and the two __asan_report_store1 branches are decided by the
   facts on a7 / a3 and by the two shadow entries. *)
Definition nm2_xregions : smem :=
  [ nm2_frame;
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 10%nat) 20 21 20 21 [] ].
Definition nm2_xfacts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (10%nat, mkAF 4096 (2 ^ 47 - 38) 0);
            (13%nat, mkAF 1 16 0); (14%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (16%nat, mkAF SBi SBi 0); (17%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0) ]
          []
          [ (SAlu ALU_ADD (SOff 14 0) (SOff 13 0), SOff 32 0) ].
Definition ss_nm2_exit : sstate := mkSS AF_nm_exit sr_atoms nm2_xregions None nm2_xfacts.
Definition SH_nm2_exit : list shent := [mkSHE 32 0 1; mkSHE 10 20 21].
(* The callee-saved registers but sp: no path of the arm writes one of them. *)
Definition NM2_KEPT : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- small generic facts ------------------------------------------------------------------------- *)
Lemma nm2_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma nm2_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma nm2_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma nm2_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma nm2_wrange : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma nm2_w64_getr : forall (rg : bvmap 5 word) (r : bv 5), w64 (bv_unsigned (getr rg r)) = getr rg r.
Proof. intros rg r. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
(* id is 8-aligned, so id & 1 = 0. *)
Lemma nm2_land1 : forall x, x mod 8 = 0 -> Z.land x 1 = 0.
Proof.
  intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 2 8); [exists 4; reflexivity|].
  apply Z.mod_divide; [lia | exact Hx].
Qed.
(* ~(id + 3), as the machine computes it: xor with -1. *)
Lemma nm2_not : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx.
  assert (HE : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
  { unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (- x)) 1 (2 ^ 64)) by lia.
    rewrite Z.mod_small by lia. lia. }
  rewrite HE. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
    rewrite Z.ones_spec_low by lia. apply xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 1) with ((2 ^ 64 - 1) mod 2 ^ 64) by (rewrite Z.mod_small; lia).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma nm2_ra_kept : forall (rd rd' : Z -> option Z) Bs a n,
  range_addressable rd Bs a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr Bs x) = rd (shadow_of_addr Bs x)) ->
  range_addressable rd' Bs a n.
Proof.
  intros rd rd' Bs a n H Hs x Hx. destruct (H x Hx) as (s & Hs1 & Hs2). exists s.
  rewrite (Hs x Hx). split; assumption.
Qed.
(* A one-byte chunk of a region of a symbolic state is the byte in memory. *)
Lemma nm2_val1 : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 v).
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  pose proof (val_of_chunk_ok SEGS E (ms_mem ms) _ off 1 e v Hck He Hv ltac:(lia) 0%nat ltac:(cbn; lia)) as Hvm.
  rewrite Z.add_0_r in Hvm. rewrite Hvm. f_equal.
  rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* An 8-byte chunk of a region of a symbolic state is the word in memory. *)
Lemma nm2_val8 : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) 8 v.
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off 8 e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma nm2_in_kept : forall (l : list (bv 5)) q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) l = true -> In (Z_to_bv 5 q) l.
Proof.
  intros l q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* The callee-saved registers but sp of a stopped state are those of the state its env was built from. *)
Lemma nm2_cs_of : forall E ss ms (regsL : bvmap 5 word) extra,
  st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsL extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NM2_KEPT = true ->
  forall q, acallee_saved q -> q <> 2 -> getr (ms_regs ms) (Z_to_bv 5 q) = getr regsL (Z_to_bv 5 q).
Proof.
  intros E ss ms regsL extra HS HAE Hl q Hq Hq2.
  eapply (regs_kept_of_st_ok_pi _ _ _ _ _ NM2_KEPT HS HAE Hl).
  apply nm2_in_kept; [unfold acallee_saved in Hq; clear - Hq; lia|].
  assert (Hc : q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
               \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
    by (unfold acallee_saved in Hq; clear - Hq Hq2; lia).
  clear - Hc.
  repeat (destruct Hc as [Hc | Hc]; [subst q; vm_compute; reflexivity |]).
  subst q; vm_compute; reflexivity.
Qed.

(* ---- tactics of this lane (copies of the owner's, extended; the owner's are unchanged) ----------- *)
(* ew of an extended environment at a low atom (the side goals are closed: no lia on a run's context). *)
Ltac nm2_ew := repeat first
  [ rewrite ew_ewset_other by (first [discriminate | lia])
  | rewrite ew_havoc_old by (first [apply Nat.ltb_lt; reflexivity | lia]) ].
Ltac nm2_ew_in H := repeat first
  [ rewrite ew_ewset_other in H by (first [discriminate | lia])
  | rewrite ew_havoc_old in H by (first [apply Nat.ltb_lt; reflexivity | lia]) ].
(* A register of a stopped state as the denotation of its symbolic value (prreg without the
   normalisation, so that the nm2_U / nm2_sv lemmas apply). *)
Ltac nm2_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* The region of a stopped state whose base is a given atom, and the chunk at a given offset. *)
Ltac nm2_find rs n :=
  lazymatch rs with
  | (YP09.mkRegion (Some n) ?lo ?hi ?wlo ?whi ?cs) :: _ =>
      constr:(YP09.mkRegion (Some n) lo hi wlo whi cs)
  | _ :: ?t => nm2_find t n
  end.
Ltac nm2_chunk_at cs off :=
  lazymatch cs with
  | (YP09.mkChunk off ?v) :: _ => constr:(v)
  | _ :: ?t => nm2_chunk_at t off
  end.


(* ---- a Theorem Labs lane: the generic facts the copy loop uses ------------------------------------------ *)
Lemma nm_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma nm_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma nm_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma nm_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma nm_bz : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma nm_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
Lemma nm_val1 : forall (W : world SEGS) m a (b : byte),
  mbyte SEGS (mrestrict (w_H W) m) a = Some b -> val_mem SEGS (mrestrict (w_H W) m) a 1 (bz b).
Proof.
  intros W m a b H kk Hk. assert (kk = 0%nat) as -> by lia. rewrite Z.add_0_r, H. f_equal.
  pose proof (nm_bz b) as Hb.
  rewrite le_byte_small by (cbn; lia). rewrite Z.shiftr_0_r. symmetry. apply nm_byte_of_bz.
Qed.
Section arm.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (id p len : Z) (idb pb : list byte).
Hypothesis HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis H10 : getr regs 10 = w64 id.
Hypothesis H11 : getr regs 11 = w64 4096.
Hypothesis H12 : getr regs 12 = w64 p.
Hypothesis H13 : getr regs 13 = w64 len.
Hypothesis Hid : 0 <= id < 2 ^ 64.
Hypothesis Hp : 0 <= p < 2 ^ 64.
Hypothesis Hlen : 2 <= len < 2 ^ 64.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis HS1 : sp0 - STK <= spZ regs - INGEST_STK.
Hypothesis HS2 : spZ regs <= sp0.
Hypothesis Hpl : length pb = Z.to_nat len.
Hypothesis Href : reac_identity_ingest_c.ingest_refused id p len = false.
Hypothesis HREC : ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb.
Hypothesis HPAY : ting_pay_ok lyc Sc W memc p len pb.
Let POST := treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id 4096 p len idb pb.
Let NN : nat := Nat.min (length pb - 1) 16.

(* ---- FROZEN: the state the arm carries ---------------------------------------------------------- *)
Definition nm_regs (regsL : bvmap 5 word) (i : nat) : Prop :=
  getr regsL 1 = getr regs 1 /\
  getr regsL 2 = w64 (spZ regs - 32) /\
  getr regsL 5 = w64 0 /\
  getr regsL 6 = w64 (p + 1) /\
  getr regsL 7 = w64 (2 ^ 64 - 1) /\
  getr regsL 10 = w64 id /\
  getr regsL 12 = w64 p /\
  getr regsL 13 = w64 (Z.of_nat i) /\
  getr regsL 14 = w64 (id + 3) /\
  getr regsL 15 = w64 (Z.of_nat NN) /\
  getr regsL 16 = w64 SBi /\
  getr regsL 17 = w64 (2 ^ 64 - 1 - (id + 3)) /\
  (forall q, acallee_saved q -> q <> 2 -> getr regsL (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)).

Definition nm_mem (i : nat) (memL : word -> option byte) (mdL : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a) /\
  (forall j, (j < i)%nat ->
     mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat j) = Some (RcIdentModel.nthb pb (1 + j))) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memL a) /\
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 8) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 24) 8 (bv_unsigned (getr regs 1)).

Definition nm_at_head (i : nat) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  (i <= NN)%nat /\ nm_regs regsL i /\ nm_mem i memL mdL /\
  (forall j, (j < i)%nat -> RcIdentModel.bz (RcIdentModel.nthb pb (1 + j)) <> 0).

Definition nm_at_exit (w : nat) (regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) : Prop :=
  (1 <= w <= NN)%nat /\ RcIdentModel.name_len pb = w /\ nm_regs regsX w /\ nm_mem w memX mdX.

Definition nm_at_zero (regsZ : bvmap 5 word) (memZ : word -> option byte) (mdZ : Model) : Prop :=
  RcIdentModel.name_len pb = 0%nat /\ nm_regs regsZ 0 /\ nm_mem 0 memZ mdZ.

(* ---- what a run of an end keeps (the arm's ing_inv, with the written bytes named) ----------------- *)
Definition nm2_inv (Zs : Z -> Prop) (m0 m1 : word -> option byte) : Prop :=
  (forall x : word, ~ Zs (bv_unsigned x) -> m1 x = m0 x) /\
  mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) m1).
Lemma nm2_inv_init : forall Zs m, nm2_inv Zs m m.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
Lemma nm2_inv_step : forall Zs m0 m1 m2 E rs,
  nm2_inv Zs m0 m1 -> frame_of E rs m1 m2 ->
  (forall a, in_wrange E rs a -> Zs a) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> nm2_inv Zs m0 m2.
Proof.
  intros Zs m0 m1 m2 E rs (H1 & H2) HF HW HG. split.
  - intros x Hx. rewrite <- (H1 x Hx). apply HF. intros Hin. exact (Hx (HW _ Hin)).
  - exact (mem_grows_trans _ _ _ H2 HG).
Qed.
Lemma nm2_mbyte_keep : forall (Zs : Z -> Prop) m0 m1 a,
  nm2_inv Zs m0 m1 -> 0 <= a < 2 ^ 64 -> ~ Zs a ->
  mbyte SEGS (mrestrict (w_H W) m1) a = mbyte SEGS (mrestrict (w_H W) m0) a.
Proof.
  intros Zs m0 m1 a HI Ha HZ. destruct HI as (H1 & _). unfold mbyte, mrestrict. cbv beta.
  rewrite (H1 (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact HZ.
Qed.
Lemma nm2_aview_keep : forall (Zs : Z -> Prop) m0 m1 a,
  nm2_inv Zs m0 m1 -> 0 <= a < 2 ^ 64 -> ~ Zs a ->
  aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Proof.
  intros Zs m0 m1 a HI Ha HZ. unfold aview.
  rewrite (nm2_mbyte_keep Zs m0 m1 a HI Ha HZ). reflexivity.
Qed.

(* ---- the numbers the ends need ------------------------------------------------------------------- *)
Lemma nm2_lay :
  2 ^ 46 + 4128 <= spZ regs <= 2 ^ 47 /\ 4096 <= id /\ id + 38 <= 2 ^ 47 /\ id mod 8 = 0 /\
  (id + 38 <= IMG_LO \/ IMG_TOP <= id) /\ (id + 38 <= SBi \/ SBi + 2 ^ 44 <= id) /\
  (id + 38 <= spZ regs - INGEST_STK \/ spZ regs <= id) /\ length idb = 38%nat /\
  (forall a, id <= a < id + 38 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 /\
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb.
Proof.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & _).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HREC)
    as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HREC as (_ & _ & _ & HWR & HRA & HIdl & HMB). unfold RcIdentModel.ID_SIZE in HIdl.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [clear - Sp1 Sp2 C1; unfold INGEST_STK, ESTACK in *; lia|].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact R6|]. split; [exact HIdl|].
  split; [exact HWR|]. split; [exact HRA | exact HMB].
Qed.

(* ---- the frame region of both ends --------------------------------------------------------------- *)
Lemma nm2_frame_ok : forall (E : env) (memL : word -> option byte),
  ew E 1 = getr regs 1 -> ew E 2 = w64 (spZ regs - 32) ->
  ew E 8 = getr regs 8 -> ew E 9 = getr regs 9 ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 8) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 24) 8 (bv_unsigned (getr regs 1)) ->
  region_ok SEGS E (mrestrict (w_H W) memL) nm2_frame.
Proof.
  intros E memL E1 E2 E8 E9 V8 V16 V24.
  destruct nm2_lay as (Hsp & _).
  assert (HB : base_val E (Some 2%nat) = spZ regs - 32)
    by (cbn [base_val]; rewrite E2; apply nm2_unsigned; clear - Hsp; lia).
  unfold region_ok, nm2_frame.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite HB.
  split; [clear - Hsp; lia|]. split; [clear - Hsp; lia|]. split; [intros o Ho; clear - Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ (spZ regs - 32) 8 8 (SOff 9 0) (bv_unsigned (getr regs 9)));
    [ apply (denot_atom E 9%nat); [rewrite E9; symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange]
    | pose proof (nm2_wrange (getr regs 9)) as Hr9; cbn; clear - Hr9; lia | cbn; lia | exact V8 ].
  - apply (chunk_ok_val SEGS E _ (spZ regs - 32) 16 8 (SOff 8 0) (bv_unsigned (getr regs 8)));
    [ apply (denot_atom E 8%nat); [rewrite E8; symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange]
    | pose proof (nm2_wrange (getr regs 8)) as Hr8; cbn; clear - Hr8; lia | cbn; lia | exact V16 ].
  - apply (chunk_ok_val SEGS E _ (spZ regs - 32) 24 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
    [ apply (denot_atom E 1%nat); [rewrite E1; symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange]
    | pose proof (nm2_wrange (getr regs 1)) as Hr1; cbn; clear - Hr1; lia | cbn; lia | exact V24 ].
Qed.

(* The record's shadow bytes, for a memory that changed only in the record and in the arm's frame. *)
Lemma nm2_shadow : forall (memL : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (id <= a < id + 38) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF id 38.
Proof.
  intros memL Hm.
  destruct nm2_lay as (Hsp & Hid0 & Hid1 & _ & _ & R5 & _ & _ & _ & HRA & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (nm2_ra_kept (aview SEGS (w_H W) memc)); [exact HRA|].
  intros x Hx. unfold shadow_of_addr.
  assert (Hd : 512 <= x / 8 < 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound];
        clear - Hx Hid0 Hid1; lia).
  apply Hm; clear - Hd Hsp R5 C1 C2 C3 C4 C5; unfold SHADOW_OFF, SBi in *; lia.
Qed.

(* ---- the return of an end ------------------------------------------------------------------------ *)
(* ing_fin with the memory bookkeeping of a cut: what the end kept of the call's memory and that it
   lost no byte (the arm's ing_inv is relative to memc, which an end does not see). *)
Lemma nm2_fin : forall (regs2 : bvmap 5 word) mem2 md2,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (reac_identity_ingest_c.ingest_ret id 4096 p len idb pb) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (id <= a < id + 38) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  mbytes_at SEGS (mrestrict (w_H W) mem2) id (snd (RcIdentModel.ING idb 4096 pb)) ->
  POST W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros regs2 mem2 md2 HJ2 HP H10r KEEP GROW HRec.
  pose proof (ing_sp_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs HJ0 HS1 HS2) as (Sp1 & Sp2 & _).
  pose proof (ing_rec_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs id idb HJ0 HS1 HS2 HREC)
    as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HJ0 as (HAR & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (KEEPE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ ting_E id p len a ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hs He. apply KEEP; [exact Ha | exact Hs|].
    intros Hin. apply He. split; [exact Href | exact Hin]. }
  unfold POST, treac_identity_ingest_post. split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [unfold EV_INGEST; rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP|]. split; [exact H10r|]. split; [|intros _; exact HRec].
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw He. apply KEEPE; [lia | lia | exact He].
  - intros b m i Hin Hi He.
    destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b m HAR Hin) as (B16 & B4096 & Bceil & _).
    apply KEEPE; [lia | lia | exact He].
  - intros a Himg Hown Herr. pose proof (pa_img_range a Himg) as Hr.
    apply KEEPE; [lia | lia |]. intros (Hnr & Hin). destruct R4; lia.
  - intros cid pos a Hin Hz He.
    destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hz) as (Hc & Hz2).
    apply KEEPE; [|lia | exact He].
    destruct Hz2 as [(Hz2 & Happ) | Hz2]; [unfold in_app in Happ | unfold kLowMemEnd, kHighShadowEnd in Hz2]; lia.
  - intros a Ha Hw Hpr. exact (GROW a Hpr).
  - intros a Ha. apply Hpres2. lia.
Qed.

(* ---- the record the exit leaves ------------------------------------------------------------------ *)
Lemma nm2_rec_bytes : forall (w : nat) (m : word -> option byte),
  (1 <= w <= 16)%nat -> (w <= length pb - 1)%nat -> length idb = 38%nat ->
  (forall j, (j < 38)%nat -> (j < 3 \/ 3 + w < j < 20 \/ 20 < j)%nat ->
     mbyte SEGS (mrestrict (w_H W) m) (id + Z.of_nat j) = Some (RcIdentModel.nthb idb j)) ->
  (forall j, (j < w)%nat ->
     mbyte SEGS (mrestrict (w_H W) m) (id + 3 + Z.of_nat j) = Some (RcIdentModel.nthb pb (1 + j))) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + 3 + Z.of_nat w) = Some (RcIdentModel.zb 0) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + 20) = Some (RcIdentModel.zb 1) ->
  mbytes_at SEGS (mrestrict (w_H W) m) id
    (RcIdentModel.upd (RcIdentModel.upd idb 3 (firstn w (skipn 1 pb) ++ [RcIdentModel.zb 0])) 20
       [RcIdentModel.zb 1]).
Proof.
  intros w m Hw Hwp Hlidb Hkept NBm M0 M1.
  set (X := firstn w (skipn 1 pb) ++ [RcIdentModel.zb 0]).
  assert (HX : length X = (w + 1)%nat)
    by (subst X; rewrite length_app, length_firstn, length_skipn; cbn [length]; clear - Hwp; lia).
  assert (L1 : length (RcIdentModel.upd idb 3 X) = 38%nat)
    by (rewrite RcIdentModel.upd_length; [exact Hlidb | clear - HX Hw Hlidb; lia]).
  assert (L2 : length (RcIdentModel.upd (RcIdentModel.upd idb 3 X) 20 [RcIdentModel.zb 1]) = 38%nat)
    by (rewrite RcIdentModel.upd_length; [exact L1 | cbn [length]; clear - L1; lia]).
  intros j Hj. rewrite L2 in Hj.
  rewrite (nth_error_nth' _ (RcIdentModel.zb 0)) by (clear - Hj L2; lia).
  fold (RcIdentModel.nthb (RcIdentModel.upd (RcIdentModel.upd idb 3 X) 20 [RcIdentModel.zb 1]) j).
  destruct (Nat.lt_ge_cases j 3) as [Hj3 | Hj3].
  - rewrite RcIdentLib.nthb_upd_lt by (clear - Hj3 L1; lia).
    rewrite RcIdentLib.nthb_upd_lt by (clear - Hj3 Hlidb; lia). apply Hkept; clear - Hj Hj3; lia.
  - destruct (Nat.lt_ge_cases j (3 + w)) as [Hjc | Hjc].
    + rewrite RcIdentLib.nthb_upd_lt by (clear - Hjc Hw L1; lia).
      rewrite RcIdentLib.nthb_upd_in by (clear - Hjc Hj3 HX Hlidb; lia).
      subst X. rewrite RcIdentLib.nthb_name_in by (clear - Hwp Hjc Hj3; lia).
      replace (id + Z.of_nat j) with (id + 3 + Z.of_nat (j - 3)) by (clear - Hj3; lia).
      exact (NBm (j - 3)%nat ltac:(clear - Hjc Hj3; lia)).
    + destruct (Nat.eq_dec j (3 + w)) as [Hje | Hje].
      * rewrite RcIdentLib.nthb_upd_lt by (clear - Hje Hw L1; lia).
        rewrite RcIdentLib.nthb_upd_in by (clear - Hje HX Hlidb; lia).
        subst X. replace (j - 3)%nat with w by (clear - Hje; lia).
        rewrite RcIdentLib.nthb_name_end by (clear - Hwp; lia).
        replace (id + Z.of_nat j) with (id + 3 + Z.of_nat w) by (clear - Hje; lia). exact M0.
      * destruct (Nat.lt_ge_cases j 20) as [Hj20 | Hj20].
        -- rewrite RcIdentLib.nthb_upd_lt by (clear - Hj20 L1; lia).
           rewrite RcIdentLib.nthb_upd_ge by (clear - Hjc Hje HX Hlidb; lia).
           apply Hkept; clear - Hj Hjc Hje Hj20; lia.
        -- destruct (Nat.eq_dec j 20) as [-> | Hj20'].
           ++ rewrite RcIdentLib.nthb_upd_in by (cbn [length]; clear - L1; lia). exact M1.
           ++ rewrite RcIdentLib.nthb_upd_ge by (cbn [length]; clear - Hj20 Hj20' L1; lia).
              rewrite RcIdentLib.nthb_upd_ge by (clear - Hjc Hje Hj20 Hj20' HX Hlidb; lia).
              apply Hkept; clear - Hj Hj20 Hj20' Hjc Hje; lia.
Qed.

(* ---- 0x83d44 -> the return: the empty name ------------------------------------------------------- *)
Lemma nm_zero_ok : forall regsZ memZ mdZ, nm_at_zero regsZ memZ mdZ ->
  SRr SEGS W (mkCfg (mkst regsZ (Z_to_bv 64 (BASE + AF_nm_zero)) memZ (seg_rom SEGS)) mdZ) POST.
Proof.
  intros regsZ memZ mdZ (HNL & XR & XM).
  pose proof XR as (X1 & X2 & X5 & X6 & X7 & X10 & X12 & X13 & X14 & X15 & X16 & X17 & XCS).
  pose proof XM as (HJ & KL & NB & GL & V8 & V16 & V24).
  destruct nm2_lay as (Hsp & Hid0 & Hid1 & Hid8 & R4 & R5 & R6 & HIdl & HWR & HRA & HMB).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (E8v : getr regsZ 8 = getr regs 8)
    by (pose proof (XCS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) as Hq;
        replace (Z_to_bv 5 8) with (8%bv : bv 5) in Hq by (apply bv_eq; reflexivity); exact Hq).
  assert (E9v : getr regsZ 9 = getr regs 9)
    by (pose proof (XCS 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) as Hq;
        replace (Z_to_bv 5 9) with (9%bv : bv 5) in Hq by (apply bv_eq; reflexivity); exact Hq).
  remember (Eimg (Ereg regsZ [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsZ []) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E1 : ew E 1 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsZ _ 1 1%bv eq_refl); exact X1).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsZ _ 2 2%bv eq_refl); exact X2).
  assert (E8 : ew E 8 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsZ _ 8 8%bv eq_refl); exact E8v).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsZ _ 9 9%bv eq_refl); exact E9v).
  assert (HAE : env_agree 32 (Ereg regsZ []) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (HS : st_ok_pi SEGS VAL E ss_nm2_zero
                 (restrict (w_H W) (mkst regsZ (Z_to_bv 64 (BASE + AF_nm_zero)) memZ (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_nm2_zero. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - unfold nm2_zregions. repeat apply Forall_cons; try apply Forall_nil.
      apply (nm2_frame_ok E memZ E1 E2 E8 E9 V8 V16 V24).
    - unfold nm2_zregions. cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - unfold facts_ok, nm2_zfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
      rewrite nm2_unsigned by (clear - Hsp; lia). rewrite Z.pow_0_r, Z.mod_1_r.
      clear - Hsp; lia. }
  assert (SHOK : sh_ok SEGS BXN [] E (mrestrict (w_H W) memZ)) by apply Forall_nil.
  clear HE EL.
  pose proof (nm2_inv_init (fun a => spZ regs - 32 <= a < spZ regs) memZ) as HK.
  paj_run_tok RUN HS HJ SHOK Ispan;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
    repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |] ] |].
  lazymatch type of HK with nm2_inv _ _ ?m1 =>
  lazymatch goal with
  | HF : frame_of ?Ef ?rs m1 ?m2, HG : mem_grows (mrestrict _ m1) (mrestrict _ ?m2') |- _ =>
    let HK2 := fresh "HK2" in
    pose proof (nm2_inv_step _ _ _ _ Ef rs HK HF ltac:(
      let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
      intros a (r & Hin & Ha); vm_compute in Hin;
      repeat destruct Hin as [<- | Hin]; try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; cbv beta; clear - Ha; lia) HG) as HK2;
    clear HK; rename HK2 into HK
  end end.
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
  repeat match goal with Hg : mem_grows _ _ |- _ => clear Hg end.
  nm2_reg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. nm2_reg HS (2%bv : bv 5) Q2.
  pose proof (nm2_cs_of _ _ _ regsZ _ HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RCS.
  cbn [ms_regs restrict] in RCS.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msf) =>
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat := fresh "mat" in intros mat; cbv beta;
    replace (v_jalr (getr (ms_regs msf) 1) 0) with (getr regs 1)
      by (rewrite Q1; nm2_ew; rewrite E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity)
  end.
  eapply nm2_fin.
  - apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
  - intros q Hq. destruct (Z.eq_dec q 2) as [->|Hq2].
    + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q2. rewrite <- (nm2_w64_getr regs 2). change (bv_unsigned (getr regs 2)) with (spZ regs).
      apply nm2_sv. rewrite (nm2_U _ 2%nat (spZ regs - 32) 32) by (nm2_ew; exact E2). f_equal. ring.
    + rewrite (RCS q Hq Hq2). exact (XCS q Hq Hq2).
  - rewrite Q10. unfold reac_identity_ingest_c.ingest_ret. rewrite Href. cbv iota.
    rewrite (RcIdentLib.ING_name_zero idb pb ltac:(right; exact HNL)). cbn [fst].
    apply nm2_sv. rewrite nm2_Ulit. reflexivity.
  - intros a Ha Hw Hrec. rewrite (nm2_aview_keep _ _ _ a HK Ha ltac:(exact Hw)).
    apply KL; [exact Ha | exact Hw | clear - Hrec; lia].
  - intros a Hpr. destruct HK as (_ & HKG). apply (apresent_grows (w_H W) memZ _ a HKG).
    exact (GL a Hpr).
  - rewrite (RcIdentLib.ING_name_zero idb pb ltac:(right; exact HNL)). cbn [snd].
    intros j Hj. rewrite HIdl in Hj.
    rewrite (nm2_mbyte_keep _ _ _ (id + Z.of_nat j) HK
               ltac:(clear - Hid0 Hid1 Hj; lia) ltac:(cbv beta; clear - R6 Hj WS; lia)).
    rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc memZ (id + Z.of_nat j)
               (KL (id + Z.of_nat j) ltac:(clear - Hid0 Hid1 Hj; lia)
                   ltac:(clear - R6 Hj WS; lia) ltac:(clear - Hj; lia))).
    exact (HMB j ltac:(clear - Hj HIdl; lia)).
Qed.

(* ---- 0x83eb0 -> the return: the NUL, the flag and the result 1 ------------------------------------ *)
Lemma nm_exit_ok : forall (w : nat) regsX memX mdX, nm_at_exit w regsX memX mdX ->
  SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + AF_nm_exit)) memX (seg_rom SEGS)) mdX) POST.
Proof.
  intros w regsX memX mdX (Hw & HNL & XR & XM).
  pose proof XR as (X1 & X2 & X5 & X6 & X7 & X10 & X12 & X13 & X14 & X15 & X16 & X17 & XCS).
  pose proof XM as (HJ & KL & NB & GL & V8 & V16 & V24).
  destruct nm2_lay as (Hsp & Hid0 & Hid1 & Hid8 & R4 & R5 & R6 & HIdl & HWR & HRA & HMB).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hw16 : (1 <= w <= 16)%nat /\ (w <= length pb - 1)%nat) by (rewrite HNN in Hw; clear - Hw; lia).
  destruct Hw16 as [Hw16 Hwp].
  assert (Hwz : 1 <= Z.of_nat w <= 16) by (clear - Hw16; lia).
  assert (E8v : getr regsX 8 = getr regs 8)
    by (pose proof (XCS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) as Hq;
        replace (Z_to_bv 5 8) with (8%bv : bv 5) in Hq by (apply bv_eq; reflexivity); exact Hq).
  assert (E9v : getr regsX 9 = getr regs 9)
    by (pose proof (XCS 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) as Hq;
        replace (Z_to_bv 5 9) with (9%bv : bv 5) in Hq by (apply bv_eq; reflexivity); exact Hq).
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (id <= a < id + 38) ->
            aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hs Hn; apply KL; [exact Ha | exact Hs | clear - Hn Hwz; lia]).
  remember (Eimg (Ereg regsX [w64 (id + 3 + Z.of_nat w)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsX [w64 (id + 3 + Z.of_nat w)]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E1 : ew E 1 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 1 1%bv eq_refl); exact X1).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 2 2%bv eq_refl); exact X2).
  assert (E8 : ew E 8 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 8 8%bv eq_refl); exact E8v).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 9 9%bv eq_refl); exact E9v).
  assert (E10e : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 10 10%bv eq_refl); exact X10).
  assert (E13 : ew E 13 = w64 (Z.of_nat w))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 13 13%bv eq_refl); exact X13).
  assert (E14 : ew E 14 = w64 (id + 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 14 14%bv eq_refl); exact X14).
  assert (E16 : ew E 16 = w64 SBi)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 16 16%bv eq_refl); exact X16).
  assert (E17 : ew E 17 = w64 (2 ^ 64 - 1 - (id + 3)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 17 17%bv eq_refl); exact X17).
  assert (E32 : ew E 32 = w64 (id + 3 + Z.of_nat w))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 0)).
  assert (HAE : env_agree 32 (Ereg regsX [w64 (id + 3 + Z.of_nat w)]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (U10 : bv_unsigned (ew E 10) = id)
    by (rewrite E10e; apply nm2_unsigned; clear - Hid0 Hid1; lia).
  assert (U32 : bv_unsigned (ew E 32) = id + 3 + Z.of_nat w)
    by (rewrite E32; apply nm2_unsigned; clear - Hid0 Hid1 Hwz; lia).
  assert (UB : U E BXN = SHADOW_OFF)
    by (unfold BXN; rewrite (nm2_U E 16%nat SBi 0 E16); reflexivity).
  assert (HS : st_ok_pi SEGS VAL E ss_nm2_exit
                 (restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + AF_nm_exit)) memX (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_nm2_exit. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - unfold nm2_xregions. repeat apply Forall_cons; try apply Forall_nil.
      + apply (nm2_frame_ok E memX E1 E2 E8 E9 V8 V16 V24).
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        cbn [base_val]. rewrite U32.
        split; [clear - Hid0 Hid1 Hwz; lia|]. split; [clear - Hid0 Hid1 Hwz; lia|].
        split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply GL.
        exact (proj2 (HWR (id + 3 + Z.of_nat w + o) ltac:(clear - Ho Hwz; lia))).
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        cbn [base_val]. rewrite U10.
        split; [clear - Hid0 Hid1; lia|]. split; [clear - Hid0 Hid1; lia|].
        split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply GL.
        exact (proj2 (HWR (id + o) ltac:(clear - Ho; lia))).
    - apply pairwise_disjoint_of_extents. unfold nm2_xregions, nm2_frame, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
      rewrite U10, U32, E2. rewrite nm2_unsigned by (clear - Hsp; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hid0 Hid1 Hwz Hsp R6 WS. repeat split; lia.
    - unfold facts_ok, nm2_xfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I|]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E2, E10e, E13, E14, E16, E17, E32.
        rewrite !nm2_unsigned by (unfold SBi; clear - Hid0 Hid1 Hwz Hsp; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SBi.
        clear - Hid0 Hid1 Hwz Hsp.
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
      + split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (nm2_U E 14%nat (id + 3) 0 E14), (nm2_U E 13%nat (Z.of_nat w) 0 E13),
                (nm2_U E 32%nat (id + 3 + Z.of_nat w) 0 E32).
        rewrite !Z.add_0_r. rewrite (Z.mod_small (id + 3)) by (clear - Hid0 Hid1; lia).
        rewrite (Z.mod_small (Z.of_nat w)) by (clear - Hwz; lia). unfold zcanon, M64.
        f_equal; clear - Hid0 Hid1 Hwz; lia. }
  assert (SHOK : sh_ok SEGS BXN SH_nm2_exit E (mrestrict (w_H W) memX)).
  { pose proof (nm2_shadow memX KR) as RAr.
    unfold sh_ok, SH_nm2_exit. repeat apply Forall_cons; try apply Forall_nil.
    - apply (shent_ok_of_range SEGS (w_H W) memX E BXN 32 id 38 (id + 3 + Z.of_nat w) 0 1 RAr UB).
      + rewrite (nm2_U E 32%nat (id + 3 + Z.of_nat w) 0 E32), Z.add_0_r. apply Z.mod_small.
        clear - Hid0 Hid1 Hwz; lia.
      + clear - Hwz; lia.
      + clear - Hwz; lia.
      + intros x Hx. clear - Hx Hid0 Hid1 Hwz R5 C1 C2 C3 C4 C5. unfold SHADOW_OFF, SBi in *. lia.
    - apply (shent_ok_of_range SEGS (w_H W) memX E BXN 10 id 38 id 20 21 RAr UB).
      + rewrite (nm2_U E 10%nat id 0 E10e), Z.add_0_r. apply Z.mod_small. clear - Hid0 Hid1; lia.
      + lia.
      + lia.
      + intros x Hx. clear - Hx Hid0 Hid1 R5 C1 C2 C3 C4 C5. unfold SHADOW_OFF, SBi in *. lia. }
  clear HE EL.
  pose proof (nm2_inv_init
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ a = id + 3 + Z.of_nat w \/ a = id + 20) memX) as HK.
  paj_run_tok RUN HS HJ SHOK Ispan;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
    repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (id + 3 + Z.of_nat w));
      [ reflexivity | nm2_ew; exact U32
      | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
        exact (proj1 (HWR aq ltac:(clear - Haq Hwz; lia))) | ]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat id);
      [ reflexivity | nm2_ew; exact U10
      | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
        exact (proj1 (HWR aq ltac:(clear - Haq; lia))) | ] ] |].
  lazymatch type of HK with nm2_inv _ _ ?m1 =>
  lazymatch goal with
  | HF : frame_of ?Ef ?rs m1 ?m2, HG : mem_grows (mrestrict _ m1) (mrestrict _ ?m2') |- _ =>
    let HK2 := fresh "HK2" in
    pose proof (nm2_inv_step _ _ _ _ Ef rs HK HF ltac:(
      let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
      intros a (r & Hin & Ha); vm_compute in Hin;
      repeat destruct Hin as [<- | Hin]; try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; nm2_ew_in Ha;
      try rewrite U32 in Ha; try rewrite U10 in Ha; try rewrite E2 in Ha;
      try rewrite nm2_unsigned in Ha by (clear - Hsp; lia);
      cbv beta;
      first [ left; clear - Ha; lia | right; left; clear - Ha; lia
            | right; right; clear - Ha; lia ]) HG) as HK2;
    clear HK; rename HK2 into HK
  end end.
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
  repeat match goal with Hg : mem_grows _ _ |- _ => clear Hg end.
  nm2_reg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. nm2_reg HS (2%bv : bv 5) Q2.
  pose proof (nm2_cs_of _ _ _ regsX _ HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RCS.
  cbn [ms_regs restrict] in RCS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let r0 := nm2_find rs 32%nat in
    let r1 := nm2_find rs 10%nat in
    lazymatch r0 with YP09.mkRegion _ _ _ _ _ ?cs0 =>
      lazymatch nm2_chunk_at cs0 0 with
      | CVal 1 (SLit ?z0) =>
        pose proof (nm2_val1 Ex ssx _ r0 32%nat 0 (SLit z0) z0 HS
          ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat first [left; reflexivity | right])
          eq_refl
          ltac:(cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right])
          ltac:(cbn [sv_denot]; reflexivity) ltac:(vm_compute; split; congruence)) as M0
      end end;
    lazymatch r1 with YP09.mkRegion _ _ _ _ _ ?cs1 =>
      lazymatch nm2_chunk_at cs1 20 with
      | CVal 1 (SLit ?z1) =>
        pose proof (nm2_val1 Ex ssx _ r1 10%nat 20 (SLit z1) z1 HS
          ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat first [left; reflexivity | right])
          eq_refl
          ltac:(cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right])
          ltac:(cbn [sv_denot]; reflexivity) ltac:(vm_compute; split; congruence)) as M1
      end end
  end.
  cbn [ms_mem restrict] in M0, M1. nm2_ew_in M0. nm2_ew_in M1.
  rewrite U32, Z.add_0_r in M0. rewrite U10 in M1.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msf) =>
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat := fresh "mat" in intros mat; cbv beta;
    replace (v_jalr (getr (ms_regs msf) 1) 0) with (getr regs 1)
      by (rewrite Q1; nm2_ew; rewrite E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity)
  end.
  eapply nm2_fin.
  - apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
  - intros q Hq. destruct (Z.eq_dec q 2) as [->|Hq2].
    + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q2. rewrite <- (nm2_w64_getr regs 2). change (bv_unsigned (getr regs 2)) with (spZ regs).
      apply nm2_sv. rewrite (nm2_U _ 2%nat (spZ regs - 32) 32) by (nm2_ew; exact E2). f_equal; ring.
    + rewrite (RCS q Hq Hq2). exact (XCS q Hq Hq2).
  - rewrite Q10. unfold reac_identity_ingest_c.ingest_ret. rewrite Href. cbv iota.
    rewrite (RcIdentLib.ING_name idb pb ltac:(clear - Hw16 Hwp; lia)
               ltac:(rewrite HNL; clear - Hw16; lia)). cbn [fst].
    apply nm2_sv. rewrite nm2_Ulit. reflexivity.
  - intros a Ha Hwq Hrec.
    rewrite (nm2_aview_keep _ _ _ a HK Ha ltac:(cbv beta; clear - Hwq Hrec Hwz; lia)).
    apply KL; [exact Ha | exact Hwq | clear - Hrec Hwz; lia].
  - intros a Hpr. destruct HK as (_ & HKG). apply (apresent_grows (w_H W) memX _ a HKG).
    exact (GL a Hpr).
  - rewrite (RcIdentLib.ING_name idb pb ltac:(clear - Hw16 Hwp; lia)
               ltac:(rewrite HNL; clear - Hw16; lia)).
    rewrite HNL. cbn [snd].
    apply (nm2_rec_bytes w _); [clear - Hw16; lia | clear - Hwp; lia | exact HIdl | | | |].
    + intros j Hj Hr.
      rewrite (nm2_mbyte_keep _ _ _ (id + Z.of_nat j) HK
                 ltac:(clear - Hid0 Hid1 Hj; lia)
                 ltac:(cbv beta; clear - R6 Hj WS Hwz Hr; lia)).
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc memX (id + Z.of_nat j)
                 (KL (id + Z.of_nat j) ltac:(clear - Hid0 Hid1 Hj; lia)
                     ltac:(clear - R6 Hj WS; lia) ltac:(clear - Hj Hr Hwz; lia))).
      rewrite (HMB j ltac:(clear - Hj HIdl; lia)). unfold RcIdentModel.nthb.
      apply nth_error_nth'. clear - Hj HIdl; lia.
    + intros j Hj.
      rewrite (nm2_mbyte_keep _ _ _ (id + 3 + Z.of_nat j) HK
                 ltac:(clear - Hid0 Hid1 Hj Hwz; lia)
                 ltac:(cbv beta; clear - R6 Hj WS Hwz; lia)).
      exact (NB j Hj).
    + exact M0.
    + exact M1.
Qed.

(* ---- the entry -> the loop head at i = 0 ---------------------------------------------------------- *)
(* nm_at_head 0 from the registers and the memory the walk leaves at 0x83d78. *)
Lemma nm2_head_of : forall (regsL : bvmap 5 word) memL mdL,
  getr regsL 1 = getr regs 1 -> getr regsL 2 = w64 (spZ regs - 32) -> getr regsL 5 = w64 0 ->
  getr regsL 6 = w64 (p + 1) -> getr regsL 7 = w64 (2 ^ 64 - 1) -> getr regsL 10 = w64 id ->
  getr regsL 12 = w64 p -> getr regsL 13 = w64 0 -> getr regsL 14 = w64 (id + 3) ->
  getr regsL 15 = w64 (Z.of_nat NN) -> getr regsL 16 = w64 SBi ->
  getr regsL 17 = w64 (2 ^ 64 - 1 - (id + 3)) ->
  (forall q, acallee_saved q -> q <> 2 -> getr regsL (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memL a) ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 8) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 32 + 24) 8 (bv_unsigned (getr regs 1)) ->
  nm_at_head 0 regsL memL mdL.
Proof.
  intros regsL memL mdL Y1 Y2 Y5 Y6 Y7 Y10 Y12 Y13 Y14 Y15 Y16 Y17 YCS YJ YK YG Y8m Y16m Y24m.
  split; [lia|].
  split.
  { unfold nm_regs. repeat (split; [eassumption|]). exact YCS. }
  split.
  { unfold nm_mem. split; [exact YJ|].
    split; [intros a Ha Hs _; exact (YK a Ha Hs)|].
    split; [intros j Hj; clear - Hj; lia|].
    split; [exact YG|]. split; [exact Y8m|]. split; [exact Y16m | exact Y24m]. }
  intros j Hj. clear - Hj. lia.
Qed.


(* ================= a Theorem Labs lane: the copy loop (nm_loop) and its helpers ========================= *)
Ltac nclean :=
  repeat match goal with
  | H : st_ok_pi _ _ _ _ _ |- _ => clear H
  | H : sh_ok _ _ _ _ _ |- _ => clear H
  | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
  | H : ting_rec_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
  | H : ting_pay_ok _ _ _ _ _ _ _ _ |- _ => clear H
  | H : AR _ _ _ _ _ _ _ |- _ => clear H
  | H : AR_laws _ _ |- _ => clear H
  | H : PALib _ |- _ => clear H
  | H : mbytes_at _ _ _ _ |- _ => clear H
  | H : range_addressable _ _ _ _ |- _ => clear H
  | H : val_mem _ _ _ _ _ |- _ => clear H
  | H : env_agree _ _ _ |- _ => clear H
  | H : YP09.region_ok _ _ _ _ |- _ => clear H
  | H : Forall _ _ |- _ => clear H
  | H : apresent _ _ _ |- _ => clear H
  end.
Ltac nlia := nclean; lia.

(* The layout facts the arm needs. *)
Lemma nm_lay :
  alloc_ceiling + INGEST_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  4096 <= id /\ id + 38 <= 2 ^ 47 /\ id mod 8 = 0 /\
  (id + 38 <= IMG_LO \/ IMG_TOP <= id) /\
  (id + 38 <= SBi \/ SBi + 2 ^ 44 <= id) /\
  (id + 38 <= spZ regs - INGEST_STK \/ spZ regs <= id) /\
  4096 <= p /\ p + len <= alloc_ceiling /\
  (p + len <= SBi \/ SBi + 2 ^ 44 <= p) /\
  (p + len <= id \/ id + 38 <= p) /\
  (forall a, spZ regs - INGEST_STK <= a < spZ regs -> apresent (w_H W) memc a) /\
  AR SEGS B lyc Sc W memc mdc.
Proof.
  pose proof (ing_sp_bounds STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ0 HS1 HS2)
    as (Sp1 & Sp2 & Swin).
  pose proof (ing_rec_bounds STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id idb
                HJ0 HS1 HS2 HREC) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof HJ0 as (HARc & _).
  destruct (ing_pay_bounds lyc Sc W memc mdc p len pb HARc HPAY ltac:(lia))
    as (bi & Li & Hbin & Hb1 & Hb2 & P1 & P2 & P3 & P4).
  pose proof (ing_rec_pay_disj STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id idb
                p len pb HJ0 HREC HPAY ltac:(lia)) as RP.
  split; [exact Sp1|]. split; [exact Sp2|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact P1|]. split; [exact P2|].
  split; [exact P4|]. split; [exact RP|]. split; [exact Swin | exact HARc].
Qed.

(* The call-time facts of the record and the payload. *)
Lemma nm_cfacts :
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p len /\
  (forall a, id <= a < id + 38 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb /\ length idb = 38%nat /\
  mbytes_at SEGS (mrestrict (w_H W) memc) p pb.
Proof.
  pose proof HJ0 as (HARc & _).
  pose proof HREC as (Hal8 & Hloc & Hsp & HW & HRA & HL & HMB).
  pose proof HPAY as (HBl & HMP).
  destruct (HBl ltac:(lia)) as (bi & Li & Hbin & Hb1 & Hb2).
  unfold RcIdentModel.ID_SIZE in HL.
  assert (HrqL : Li <= req_size Li)
    by (unfold req_size; destruct (Li =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia).
  split; [exact HRA|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc bi Li p len HARc Hbin Hb1 ltac:(lia))|].
  split; [exact HW|]. split; [exact HMB|]. split; [exact HL | exact HMP].
Qed.
(* The shadow bytes of the record and the payload are kept by a memory that changed only in the callee's
   frame and in the name bytes. *)
Lemma nm_shadow : forall (i : nat) (m : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  (Z.of_nat i <= 17) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF id 38 /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p len.
Proof.
  intros i m Hm Hi.
  destruct nm_lay as (Sp1 & Sp2 & R1 & R2 & R3 & R4 & R5 & R6 & P1 & P2 & P3 & P4 & Swin & HARc).
  destruct nm_cfacts as (RAr & RAp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs : forall x, 4096 <= x < 2 ^ 47 ->
            aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. unfold shadow_of_addr.
    assert (Hd : 512 <= x / 8 < 2 ^ 44)
      by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
    apply Hm; unfold SHADOW_OFF, SBi, INGEST_STK, ESTACK in *; nlia. }
  split.
  - intros x Hx. destruct (RAr x Hx) as (s & Hs1 & Hs2). exists s.
    split; [rewrite Hs by nlia; exact Hs1 | exact Hs2].
  - intros x Hx. destruct (RAp x Hx) as (s & Hs1 & Hs2). exists s.
    split; [rewrite Hs by nlia; exact Hs1 | exact Hs2].
Qed.

(* A record byte the arm has not written, and a payload byte. *)
Lemma nm_idb_byte : forall (i : nat) (m : word -> option byte) j, (j < 38)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  ~ (id + 3 <= id + Z.of_nat j < id + 3 + Z.of_nat i) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + Z.of_nat j) = Some (nthb idb j).
Proof.
  intros i m j Hj Hm Hout.
  destruct nm_lay as (Sp1 & Sp2 & R1 & R2 & R3 & R4 & R5 & R6 & P1 & P2 & P3 & P4 & Swin & HARc).
  destruct nm_cfacts as (_ & _ & _ & MBr & Hlidb & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc m _
             (Hm (id + Z.of_nat j) ltac:(nlia) ltac:(unfold INGEST_STK, ESTACK in *; nlia) Hout)).
  rewrite (MBr j ltac:(lia)). unfold RcIdentModel.nthb. apply nth_error_nth'. lia.
Qed.
Lemma nm_pb_byte : forall (i : nat) (m : word -> option byte) j, (j < length pb)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  (Z.of_nat i <= 17) ->
  mbyte SEGS (mrestrict (w_H W) m) (p + Z.of_nat j) = Some (nthb pb j).
Proof.
  intros i m j Hj Hm Hi.
  destruct nm_lay as (Sp1 & Sp2 & R1 & R2 & R3 & R4 & R5 & R6 & P1 & P2 & P3 & P4 & Swin & HARc).
  destruct nm_cfacts as (_ & _ & _ & _ & _ & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hjl : Z.of_nat j < len) by (rewrite Hpl in Hj; lia).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc m _
             (Hm (p + Z.of_nat j) ltac:(nlia) ltac:(unfold INGEST_STK, ESTACK in *; nlia) ltac:(nlia))).
  rewrite (MBp j Hj). unfold RcIdentModel.nthb. apply nth_error_nth'. lia.
Qed.

(* ---- the state at the loop head ----------------------------------------------------------------- *)
Lemma nm_loop_ok : forall (i : nat) regsL memL mdL,
  (i < NN)%nat -> nm_regs regsL i -> nm_mem i memL mdL ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                         (nthb pb (1 + i)) (nthb idb (3 + i))))) ss_nm_loop
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + AF_nm_head)) memL (seg_rom SEGS))) /\
  sh_ok SEGS BXN SH_nm_loop
    (Eimg (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                         (nthb pb (1 + i)) (nthb idb (3 + i)))))
    (mrestrict (w_H W) memL).
Proof.
  intros i regsL memL mdL Hi HRG HM.
  pose proof HRG as (R1 & R2 & R5 & R6 & R7 & R10 & R12 & R13 & R14 & R15 & R16 & R17 & RCS).
  pose proof HM as (HJ & KL & NB & GL & V8 & V16 & V24).
  destruct nm_lay as (Sp1 & Sp2 & L1 & L2 & L3 & L4 & L5 & L6 & P1 & P2 & P3 & P4 & Swin & HARc).
  destruct nm_cfacts as (RAr0 & RAp0 & RW & MBr & Hlidb & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hpn : Z.of_nat (length pb) = len) by (rewrite Hpl; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hi15 : 0 <= Z.of_nat i <= 15) by (rewrite HNN in Hi; nlia).
  assert (Hil : Z.of_nat i + 2 <= len) by (rewrite HNN in Hi; nlia).
  pose proof (nm_bz (nthb pb (1 + i))) as Hbz. pose proof (nm_bz (nthb idb (3 + i))) as Hcbz.
  destruct (nm_shadow i memL KL ltac:(lia)) as [RAr RAp].
  remember (Eimg (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                (nthb pb (1 + i)) (nthb idb (3 + i))))) as E eqn:HE.
  assert (EL : forall n, (n < A_TEXT)%nat ->
            ew E n = ew (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                       (nthb pb (1 + i)) (nthb idb (3 + i)))) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E6 : ew E 6 = w64 (p + 1))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 6 6%bv eq_refl); exact R6).
  assert (E13 : ew E 13 = w64 (Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 (id + 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 14 14%bv eq_refl); exact R14).
  assert (E16 : ew E 16 = w64 SBi)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 16 16%bv eq_refl); exact R16).
  assert (E5 : ew E 5 = w64 0)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 5 5%bv eq_refl); exact R5).
  assert (E7 : ew E 7 = w64 (2 ^ 64 - 1))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 7 7%bv eq_refl); exact R7).
  assert (E10 : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 p)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E15 : ew E 15 = w64 (Z.of_nat NN))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 15 15%bv eq_refl); exact R15).
  assert (E17 : ew E 17 = w64 (2 ^ 64 - 1 - (id + 3)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E32 : ew E 32 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (E34 : ew E 34 = w64 (bz (nthb pb (1 + i))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
  assert (E35 : ew E 35 = w64 (bz (nthb idb (3 + i))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply nm_unsigned; exact Hv).
  assert (Mq : mbyte SEGS (mrestrict (w_H W) memL) (p + 1 + Z.of_nat i) = Some (nthb pb (1 + i))).
  { replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (1 + i)) by lia.
    apply (nm_pb_byte i); [rewrite Hpl; nlia | exact KL | lia]. }
  assert (Md : mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat i) = Some (nthb idb (3 + i))).
  { replace (id + 3 + Z.of_nat i) with (id + Z.of_nat (3 + i)) by lia.
    apply (nm_idb_byte i); [lia | exact KL | nlia]. }
  split.
  - rewrite restrict_mkst_fx. unfold ss_nm_loop. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold nm_loop_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 32%nat (p + 1 + Z.of_nat i) E32) by nlia.
        split; [nlia|]. split; [nlia|]. split; [intros o Ho; nlia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (p + 1 + Z.of_nat i) 0 1 (SOff 34 0) (bz (nthb pb (1 + i)))).
        -- apply nm_sv. rewrite (nm_U E 34 _ 0 E34), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hbz.
        -- cbn. nlia.
        -- change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. apply nm_val1. exact Mq.
      * rewrite (VB 33%nat (id + 3 + Z.of_nat i) E33) by nlia.
        split; [nlia|]. split; [nlia|]. split.
        -- intros o Ho. apply (apresent_writable SEGS). apply GL.
           exact (proj2 (RW (id + 3 + Z.of_nat i + o) ltac:(nlia))).
        -- constructor; [|constructor].
           apply (chunk_ok_val SEGS E _ (id + 3 + Z.of_nat i) 0 1 (SOff 35 0) (bz (nthb idb (3 + i)))).
           ++ apply nm_sv. rewrite (nm_U E 35 _ 0 E35), Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 1)) with 256. exact Hcbz.
           ++ cbn. nlia.
           ++ change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. apply nm_val1. exact Md.
    + apply pairwise_disjoint_of_extents. unfold nm_loop_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 32%nat (p + 1 + Z.of_nat i) E32) by nlia.
      rewrite (VB 33%nat (id + 3 + Z.of_nat i) E33) by nlia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. nclean. repeat split; lia.
    + split; [|split].
      * cbn [nm_loop_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E16, E34, E35, E32, E33, E5, E13, E7, E17, E15, E12, E6, E14, E10.
        rewrite !nm_unsigned by (unfold SBi in *; nlia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. nclean. unfold SBi. repeat split; lia.
      * cbn [nm_loop_facts f_conds conds_ok]. split; [|exact I].
        unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_eq_U, (nm_U E 5 0 0 E5), nm_Ulit. reflexivity.
      * cbn [nm_loop_facts f_alias alias_ok]. split; [|split; [|exact I]].
        -- rewrite !denot_lit_U. f_equal.
           rewrite U_SAlu. cbn [zalu_raw].
           rewrite (nm_U E 6 (p + 1) 0 E6), (nm_U E 13 (Z.of_nat i) 0 E13),
                   (nm_U E 32 (p + 1 + Z.of_nat i) 0 E32), !Z.add_0_r.
           rewrite !Z.mod_small by nlia. unfold zcanon, M64. apply Z.mod_small. nlia.
        -- rewrite !denot_lit_U. f_equal.
           rewrite U_SAlu. cbn [zalu_raw].
           rewrite (nm_U E 14 (id + 3) 0 E14), (nm_U E 13 (Z.of_nat i) 0 E13),
                   (nm_U E 33 (id + 3 + Z.of_nat i) 0 E33), !Z.add_0_r.
           rewrite !Z.mod_small by nlia. unfold zcanon, M64. apply Z.mod_small. nlia.
  - assert (UB : U E BXN = SHADOW_OFF) by (unfold BXN; rewrite (nm_U E 16 SBi 0 E16); unfold SBi, SHADOW_OFF; reflexivity).
    unfold sh_ok, SH_nm_loop. repeat apply Forall_cons; try apply Forall_nil.
    + apply (shent_ok_of_range SEGS (w_H W) memL E BXN 32 p len (p + 1 + Z.of_nat i) 0 1 RAp UB).
      * rewrite (nm_U E 32 _ 0 E32), Z.add_0_r. apply Z.mod_small. nlia.
      * nlia.
      * nlia.
      * intros x Hx. unfold SHADOW_OFF, SBi in *. nlia.
    + apply (shent_ok_of_range SEGS (w_H W) memL E BXN 33 id 38 (id + 3 + Z.of_nat i) 0 1 RAr UB).
      * rewrite (nm_U E 33 _ 0 E33), Z.add_0_r. apply Z.mod_small. nlia.
      * nlia.
      * nlia.
      * intros x Hx. unfold SHADOW_OFF, SBi in *. nlia.
Qed.

(* ---- what the runs of the arm keep ------------------------------------------------------------- *)
Definition nm_win (d a : Z) : Prop := d <= a < d + 1.
Definition nm_kept (Zs : Z -> Prop) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Definition nm_grown (m0 m1 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a.
Lemma nm_kept_of_frame : forall Ex rs (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of Ex rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
  intros Ex rs m m' Zs HFR Hw a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFR.
  rewrite unsigned_lit_small by lia.
  intros Hin. destruct (in_wrange_windows Ex rs a Hin) as (b & wlo & whi & Hi & Hr).
  exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma nm_keep_step : forall Ex rs m0 m1 m2 (Zs : Z -> Prop),
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nm_kept Zs m0 m1 -> nm_grown m0 m1 ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> Zs a) ->
  nm_kept Zs m0 m2 /\ nm_grown m0 m2.
Proof.
  intros Ex rs m0 m1 m2 Zs HFr HG K1 G1 Hw. split.
  - intros a Ha Hz. rewrite <- (K1 a Ha Hz). exact (nm_kept_of_frame Ex rs m1 m2 Zs HFr Hw a Ha Hz).
  - intros a Hpa. exact (apresent_grows (w_H W) m1 m2 a HG (G1 a Hpa)).
Qed.
Lemma nm_val_kept : forall (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W) m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
  intros m m' a n v Hk Hv j Hj. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' _ (Hk j Hj)). exact (Hv j Hj).
Qed.
(* The registers the arm never writes. *)
Definition NM_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma nm_in_kept : forall (l : list (bv 5)) q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) l = true -> In (Z_to_bv 5 q) l.
Proof.
  intros l q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma nm_cs_of : forall E ss ms (regsL : bvmap 5 word) extra,
  st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsL extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NM_KEPT = true ->
  (forall q, acallee_saved q -> q <> 2 -> getr (ms_regs ms) (Z_to_bv 5 q) = getr regsL (Z_to_bv 5 q)) /\
  getr (ms_regs ms) 1 = getr regsL 1.
Proof.
  intros E ss ms regsL extra HS HAE Hl. split.
  - intros q Hq Hq2.
    eapply (regs_kept_of_st_ok_pi E ss ms regsL extra NM_KEPT HS HAE Hl).
    apply nm_in_kept; [unfold acallee_saved in Hq; lia|].
    assert (Hc : q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
                 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
      by (unfold acallee_saved in Hq; lia).
    clear - Hc.
    repeat (destruct Hc as [Hc | Hc]; [subst q; vm_compute; reflexivity |]).
    subst q; vm_compute; reflexivity.
  - exact (regs_kept_of_st_ok_pi E ss ms regsL extra NM_KEPT HS HAE Hl 1%bv ltac:(cbn [In]; left; reflexivity)).
Qed.
Lemma nm_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.

(* ---- tactics for one iteration ------------------------------------------------------------------ *)
Ltac ewo := repeat rewrite ew_ewset_other by lia.
Ltac ewo_in H := repeat rewrite ew_ewset_other in H by lia.
Ltac nm_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                      SHOK : sh_ok _ _ _ _ _ |- _ => paj_run_tok RUN HS HJ SHOK Ispan end.
Ltac nm_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                      SHOK : sh_ok _ _ _ _ _ |- _ => paj_run_to_tok RUNTO HS HJ SHOK Ispan stop end.
Ltac nm_branch :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUN BR HS SHOK Ispan end.
(* The write right: the only writable window is the record byte at id + 3 + i. *)
Ltac nm_awr U33 RW :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' b1 b2 b3 b4 b5 b6 b7) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply awr_ok_cons_gen;
        [ reflexivity | ewo; exact U33
        | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; exact (proj1 (RW a ltac:(nlia)))
        | ] ].
(* After a run: chain its frame onto KEEPI / GROWI; every window it wrote is the record byte. *)
Ltac nm_keep U33 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    KI : nm_kept _ _ _, GI : nm_grown _ _ |- _ =>
      let Hw := fresh "Hw" in
      pose proof (nm_keep_step _ _ _ _ _ _ HFr HG KI GI) as Hw;
      let K2 := fresh "K2" in let G2 := fresh "G2" in
      lazymatch type of Hw with ?P -> _ =>
        let HP := fresh "HP" in
        assert (HP : P) by
          (let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
           let Hin := fresh "Hin" in let Hr := fresh "Hr" in
           intros bb wl wh aa Hin Hr;
           lazymatch type of Hin with In _ (windows ?rs) =>
             let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
           repeat (destruct Hin as [Hin | Hin];
                   [ injection Hin as <- <- <-; cbn [base_val] in Hr; ewo_in Hr;
                     first [ nclean; lia | rewrite ?U33 in Hr; unfold nm_win; nlia ] | ]);
           destruct Hin);
        destruct (Hw HP) as [K2 G2]; clear HP Hw end;
      clear KI GI HFr HG; rename K2 into KEEPI; rename G2 into GROWI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
Ltac nreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
Ltac nm_cs HS HAE :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch type of HAE with env_agree _ ?A _ =>
    let HAE' := fresh "HAE'" in
    assert (HAE' : env_agree 32 A Ex)
      by (eapply nm_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
    let RC := fresh "RCS'" in
    pose proof (nm_cs_of _ _ _ _ _ HS HAE' ltac:(vm_compute; reflexivity)) as RC;
    cbn [ms_regs restrict] in RC; clear HAE'
  end end.
(* ---- the loop's memory bookkeeping -------------------------------------------------------------- *)
Lemma nm_aview_of_mbyte : forall (m m' : word -> option byte) a,
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros m m' a E. unfold aview. rewrite E. reflexivity. Qed.
Lemma nm_kl_same : forall (i : nat) (mL mF : word -> option byte), (i <= 16)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) mL a = aview SEGS (w_H W) memc a) ->
  nm_kept (nm_win (id + 3 + Z.of_nat i)) mL mF ->
  mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat i) = Some (nthb idb (3 + i)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) memc a.
Proof.
  intros i mL mF Hi KL KI Hd a Ha Hs Hn.
  destruct nm_lay as (Sp1 & Sp2 & L1 & L2 & L3 & L4 & L5 & L6 & _).
  destruct nm_cfacts as (_ & _ & _ & MBr & Hlidb & _).
  destruct (Z.eq_dec a (id + 3 + Z.of_nat i)) as [-> | Hne].
  - apply nm_aview_of_mbyte. rewrite Hd.
    replace (id + 3 + Z.of_nat i) with (id + Z.of_nat (3 + i)) by nlia.
    rewrite (MBr (3 + i)%nat ltac:(nlia)). unfold RcIdentModel.nthb. f_equal.
    symmetry. apply nth_error_nth'. nlia.
  - rewrite (KI a Ha ltac:(unfold nm_win; nlia)). apply KL; assumption.
Qed.
Lemma nm_kl_step : forall (i : nat) (mL mF : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     ~ (id + 3 <= a < id + 3 + Z.of_nat i) -> aview SEGS (w_H W) mL a = aview SEGS (w_H W) memc a) ->
  nm_kept (nm_win (id + 3 + Z.of_nat i)) mL mF ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (id + 3 <= a < id + 3 + Z.of_nat (Datatypes.S i)) ->
    aview SEGS (w_H W) mF a = aview SEGS (w_H W) memc a.
Proof.
  intros i mL mF KL KI a Ha Hs Hn.
  rewrite (KI a Ha ltac:(unfold nm_win; nlia)). apply KL; [exact Ha | exact Hs | nlia].
Qed.
Lemma nm_nb_same : forall (i : nat) (mL mF : word -> option byte), (i <= 16)%nat ->
  (forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) mL) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) ->
  nm_kept (nm_win (id + 3 + Z.of_nat i)) mL mF ->
  forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j)).
Proof.
  intros i mL mF Hi NB KI j Hj.
  destruct nm_lay as (Sp1 & Sp2 & L1 & L2 & _).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mL mF (id + 3 + Z.of_nat j)
             (KI (id + 3 + Z.of_nat j) ltac:(nlia) ltac:(unfold nm_win; nlia))).
  exact (NB j Hj).
Qed.
Lemma nm_nb_step : forall (i : nat) (mL mF : word -> option byte), (i <= 16)%nat ->
  (forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) mL) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) ->
  nm_kept (nm_win (id + 3 + Z.of_nat i)) mL mF ->
  mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat i) = Some (nthb pb (1 + i)) ->
  forall j, (j < Datatypes.S i)%nat ->
    mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j)).
Proof.
  intros i mL mF Hi NB KI Hd j Hj.
  destruct (Nat.eq_dec j i) as [-> | Hne]; [exact Hd | exact (nm_nb_same i mL mF Hi NB KI j ltac:(nlia))].
Qed.
Lemma nm_slots_kept : forall (i : nat) (mL mF : word -> option byte), (i <= 16)%nat ->
  nm_kept (nm_win (id + 3 + Z.of_nat i)) mL mF ->
  val_mem SEGS (mrestrict (w_H W) mL) (spZ regs - 32 + 8) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) mL) (spZ regs - 32 + 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) mL) (spZ regs - 32 + 24) 8 (bv_unsigned (getr regs 1)) ->
  val_mem SEGS (mrestrict (w_H W) mF) (spZ regs - 32 + 8) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) mF) (spZ regs - 32 + 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) mF) (spZ regs - 32 + 24) 8 (bv_unsigned (getr regs 1)).
Proof.
  intros i mL mF Hi KI A8 A16 A24.
  destruct nm_lay as (Sp1 & Sp2 & L1 & L2 & L3 & L4 & L5 & L6 & _).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HK : forall d, spZ regs - 32 <= d -> d + 8 <= spZ regs ->
            forall j, (j < 8)%nat -> aview SEGS (w_H W) mF (d + Z.of_nat j) = aview SEGS (w_H W) mL (d + Z.of_nat j)).
  { intros d Hd1 Hd2 j Hj. apply KI; unfold nm_win; nlia. }
  split; [|split].
  - apply (nm_val_kept mL); [apply HK; nlia | exact A8].
  - apply (nm_val_kept mL); [apply HK; nlia | exact A16].
  - apply (nm_val_kept mL); [apply HK; nlia | exact A24].
Qed.

(* ---- one iteration ------------------------------------------------------------------------------ *)
Ltac nm_uatoms :=
  repeat match goal with
  | H : ew ?E0 ?n = w64 ?v |- context [U ?Ex (SOff ?n ?c)] =>
      rewrite (nm_U Ex n v c) by (ewo; exact H)
  end.
Ltac nm_rv :=
  apply nm_sv; rewrite ?U_SAlu; cbn [zalu_raw]; rewrite ?nm_Ulit; nm_uatoms;
  unfold zcanon, M64; rewrite ?Z.mod_small by nlia; first [reflexivity | f_equal; nlia | nlia].
Ltac nm_mkreg HS r := let Q := fresh "Q" in nreg HS r Q; rewrite Q; nm_rv.
(* A one-byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma nm_mb_of_chunk : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 v).
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  pose proof (val_of_chunk_ok SEGS E (ms_mem ms) _ off 1 e v Hck He Hv ltac:(lia) 0%nat ltac:(cbn; lia)) as Hvm.
  rewrite Z.add_0_r in Hvm. rewrite Hvm. f_equal.
  rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* The registers at an end of the arm. *)
Ltac nm_regs_blk HS RCSF R1 RCS :=
  split; [ rewrite (proj2 RCSF); exact R1 |];
  split; [ nm_mkreg HS (2%bv : bv 5) |];
  split; [ nm_mkreg HS (5%bv : bv 5) |];
  split; [ nm_mkreg HS (6%bv : bv 5) |];
  split; [ nm_mkreg HS (7%bv : bv 5) |];
  split; [ nm_mkreg HS (10%bv : bv 5) |];
  split; [ nm_mkreg HS (12%bv : bv 5) |];
  split; [ nm_mkreg HS (13%bv : bv 5) |];
  split; [ nm_mkreg HS (14%bv : bv 5) |];
  split; [ nm_mkreg HS (15%bv : bv 5) |];
  split; [ nm_mkreg HS (16%bv : bv 5) |];
  split; [ nm_mkreg HS (17%bv : bv 5) |];
  intros q Hq Hq2; rewrite ((proj1 RCSF) q Hq Hq2); exact (RCS q Hq Hq2).

(* ---- the copy loop: 0x83d78 .. 0x83dc0, induction on the iterations still to run ---------------- *)
Lemma nm_loop :
  (forall (w : nat) regsX memX mdX, nm_at_exit w regsX memX mdX ->
     SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + AF_nm_exit)) memX (seg_rom SEGS)) mdX) POST) ->
  (forall regsZ memZ mdZ, nm_at_zero regsZ memZ mdZ ->
     SRr SEGS W (mkCfg (mkst regsZ (Z_to_bv 64 (BASE + AF_nm_zero)) memZ (seg_rom SEGS)) mdZ) POST) ->
  forall (n i : nat) regsL memL mdL, (i + n = NN)%nat -> (0 < n)%nat ->
  nm_at_head i regsL memL mdL ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + AF_nm_head)) memL (seg_rom SEGS)) mdL) POST.
Proof.
  intros HEXIT HZERO n. induction n as [|n IH]; intros i regsL memL mdL Hin Hn HAT; [lia|].
  destruct HAT as (HiN & HRG & HM & Hnz).
  assert (Hi : (i < NN)%nat) by lia.
  destruct (nm_loop_ok i regsL memL mdL Hi HRG HM) as [HS SHOK].
  pose proof HRG as (R1 & R2 & R5 & R6 & R7 & R10 & R12 & R13 & R14 & R15 & R16 & R17 & RCS).
  pose proof HM as (HJ & KL & NB & GL & V8 & V16 & V24).
  destruct nm_lay as (Sp1 & Sp2 & L1 & L2 & L3 & L4 & L5 & L6 & P1 & P2 & P3 & P4 & Swin & HARc).
  destruct nm_cfacts as (RAr0 & RAp0 & RW & MBr & Hlidb & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hpn : Z.of_nat (length pb) = len) by (rewrite Hpl; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hi15 : 0 <= Z.of_nat i <= 15) by (rewrite HNN in Hi; nlia).
  assert (HN16 : 1 <= Z.of_nat NN <= 16) by (rewrite HNN; nlia).
  assert (Hplen : (2 <= length pb)%nat) by (rewrite HNN in Hi; nlia).
  pose proof (nm_bz (nthb pb (1 + i))) as Hbz. pose proof (nm_bz (nthb idb (3 + i))) as Hcbz.
  remember (Eimg (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                (nthb pb (1 + i)) (nthb idb (3 + i))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall nn, (nn < A_TEXT)%nat ->
            ew E nn = ew (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                        (nthb pb (1 + i)) (nthb idb (3 + i)))) nn)
    by (intros nn Hnn; subst E; apply Eimg_low; exact Hnn).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 2 2%bv eq_refl); exact R2).
  assert (E5 : ew E 5 = w64 0)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 5 5%bv eq_refl); exact R5).
  assert (E6 : ew E 6 = w64 (p + 1))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 6 6%bv eq_refl); exact R6).
  assert (E7 : ew E 7 = w64 (2 ^ 64 - 1))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 7 7%bv eq_refl); exact R7).
  assert (E10 : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 p)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 (id + 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 14 14%bv eq_refl); exact R14).
  assert (E15 : ew E 15 = w64 (Z.of_nat NN))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 15 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 SBi)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 16 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 (2 ^ 64 - 1 - (id + 3)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E32 : ew E 32 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (E34 : ew E 34 = w64 (bz (nthb pb (1 + i))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
  assert (E35 : ew E 35 = w64 (bz (nthb idb (3 + i))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
  assert (HAE : env_agree 32 (Ereg regsL (nm_extra (p + 1 + Z.of_nat i) (id + 3 + Z.of_nat i)
                                            (nthb pb (1 + i)) (nthb idb (3 + i)))) E)
    by (split; [intros nn Hnn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  clear HE EL.
  assert (U33 : bv_unsigned (ew E 33) = id + 3 + Z.of_nat i) by (rewrite E33; apply nm_unsigned; nlia).
  assert (KEEPI : nm_kept (nm_win (id + 3 + Z.of_nat i)) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : nm_grown memL memL) by (intros a Ha; exact Ha).
  nm_run; [nm_awr U33 RW|]. nm_keep U33.
  nm_branch.
  - (* p[1 + i] = 0: the name ends here *)
    assert (Hb0 : bz (nthb pb (1 + i)) = 0).
    { rewrite branch_eq_U in Hc. rewrite (nm_U _ 34%nat (bz (nthb pb (1 + i))) 0) in Hc by (ewo; exact E34).
      rewrite nm_Ulit in Hc. apply Z.eqb_eq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. exact Hc. }
    clear Hc.
    nm_run; [nm_awr U33 RW|]. nm_keep U33.
    nm_branch.
    + (* i = 0: 0x83d44, the result is 0 *)
      assert (Hi0 : i = 0%nat).
      { rewrite branch_eq_U in Hc. rewrite (nm_U _ 13%nat (Z.of_nat i) 0) in Hc by (ewo; exact E13).
        rewrite nm_Ulit in Hc. apply Z.eqb_eq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. nlia. }
      clear Hc.
      nm_runto AF_nm_zero; [nm_awr U33 RW|]. nm_keep U33.
      pmkst HS. nm_cs HS HAE.
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
        pose proof (nm_mb_of_chunk _ _ _ (YP09.mkRegion (Some 33%nat) 0 1 0 1
                                            [YP09.mkChunk 0 (CVal 1 (SOff 35 0))])
                      33%nat 0 (SOff 35 0) (bz (nthb idb (3 + i))) HSx
                      ltac:(cbn [ss_mem In]; first [left; reflexivity | right; left; reflexivity]) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 35%nat (bz (nthb idb (3 + i))) 0) by (ewo; exact E35);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U33, Z.add_0_r, nm_byte_of_bz in Md;
        apply (HZERO (ms_regs ms) (ms_mem ms) _)
      end.
      split; [| split].
      * apply RcIdentLib.name_len_hit;
          [nlia | rewrite <- HNN; nlia | rewrite Hi0 in Hb0; exact Hb0 | intros j Hj; nlia].
      * rewrite Hi0 in *. nm_regs_blk HS RCS' R1 RCS.
      * split; [exact HJ|]. split; [|split; [|split; [|split; [|split]]]].
        -- rewrite Hi0 in *. exact (nm_kl_same 0%nat memL _ ltac:(nlia) KL KEEPI Md).
        -- intros j Hj. nlia.
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
        -- exact (proj1 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24)).
        -- exact (proj1 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
        -- exact (proj2 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
    + (* i > 0: 0x83eb0, the NUL after i bytes *)
      assert (Hi0 : (0 < i)%nat).
      { rewrite branch_eq_U in Hc. rewrite (nm_U _ 13%nat (Z.of_nat i) 0) in Hc by (ewo; exact E13).
        rewrite nm_Ulit in Hc. apply Z.eqb_neq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. nlia. }
      clear Hc.
      nm_runto AF_nm_exit; [nm_awr U33 RW|]. nm_keep U33.
      pmkst HS. nm_cs HS HAE.
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
        pose proof (nm_mb_of_chunk _ _ _ (YP09.mkRegion (Some 33%nat) 0 1 0 1
                                            [YP09.mkChunk 0 (CVal 1 (SOff 35 0))])
                      33%nat 0 (SOff 35 0) (bz (nthb idb (3 + i))) HSx
                      ltac:(cbn [ss_mem In]; first [left; reflexivity | right; left; reflexivity]) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 35%nat (bz (nthb idb (3 + i))) 0) by (ewo; exact E35);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U33, Z.add_0_r, nm_byte_of_bz in Md;
        apply (HEXIT i (ms_regs ms) (ms_mem ms) _)
      end.
      split; [nlia|]. split; [|split].
      * apply RcIdentLib.name_len_hit; [nlia | rewrite <- HNN; nlia | exact Hb0 | exact Hnz].
      * nm_regs_blk HS RCS' R1 RCS.
      * split; [exact HJ|]. split; [|split; [|split; [|split; [|split]]]].
        -- exact (nm_kl_same i memL _ ltac:(nlia) KL KEEPI Md).
        -- exact (nm_nb_same i memL _ ltac:(nlia) NB KEEPI).
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
        -- exact (proj1 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24)).
        -- exact (proj1 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
        -- exact (proj2 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
  - (* p[1 + i] <> 0: the byte is copied *)
    assert (Hb0 : bz (nthb pb (1 + i)) <> 0).
    { rewrite branch_eq_U in Hc. rewrite (nm_U _ 34%nat (bz (nthb pb (1 + i))) 0) in Hc by (ewo; exact E34).
      rewrite nm_Ulit in Hc. apply Z.eqb_neq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. exact Hc. }
    clear Hc.
    assert (Hnz' : forall j, (j < Datatypes.S i)%nat -> bz (nthb pb (1 + j)) <> 0).
    { intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hji]; [exact Hb0 | apply Hnz; nlia]. }
    nm_run; [nm_awr U33 RW|]. nm_keep U33.
    nm_branch.
    + (* i + 1 <> NN: the next iteration *)
      assert (HnN : Datatypes.S i <> NN).
      { rewrite branch_ne_U in Hc. rewrite (nm_U _ 15%nat (Z.of_nat NN) 0) in Hc by (ewo; exact E15).
        rewrite (nm_U _ 13%nat (Z.of_nat i) 1) in Hc by (ewo; exact E13).
        apply negb_true_iff, Z.eqb_neq in Hc. rewrite !Z.mod_small in Hc by nlia. nlia. }
      clear Hc.
      nm_runto AF_nm_head; [nm_awr U33 RW|]. nm_keep U33.
      pmkst HS. nm_cs HS HAE.
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
        pose proof (nm_mb_of_chunk _ _ _ (YP09.mkRegion (Some 33%nat) 0 1 0 1
                                            [YP09.mkChunk 0 (CVal 1 (SOff 34 0))])
                      33%nat 0 (SOff 34 0) (bz (nthb pb (1 + i))) HSx
                      ltac:(cbn [ss_mem In]; first [left; reflexivity | right; left; reflexivity]) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 34%nat (bz (nthb pb (1 + i))) 0) by (ewo; exact E34);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U33, Z.add_0_r, nm_byte_of_bz in Md;
        apply (IH (Datatypes.S i) (ms_regs ms) (ms_mem ms) _)
      end.
      * nlia.
      * nlia.
      * split; [nlia|]. split; [|split].
        -- nm_regs_blk HS RCS' R1 RCS.
        -- split; [exact HJ|]. split; [|split; [|split; [|split; [|split]]]].
           ++ exact (nm_kl_step i memL _ KL KEEPI).
           ++ exact (nm_nb_step i memL _ ltac:(nlia) NB KEEPI Md).
           ++ intros a Hpa. apply GROWI. apply GL. exact Hpa.
           ++ exact (proj1 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24)).
           ++ exact (proj1 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
           ++ exact (proj2 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
        -- exact Hnz'.
    + (* i + 1 = NN: the loop is done *)
      assert (HnN : Datatypes.S i = NN).
      { rewrite branch_ne_U in Hc. rewrite (nm_U _ 15%nat (Z.of_nat NN) 0) in Hc by (ewo; exact E15).
        rewrite (nm_U _ 13%nat (Z.of_nat i) 1) in Hc by (ewo; exact E13).
        apply negb_false_iff, Z.eqb_eq in Hc. rewrite !Z.mod_small in Hc by nlia. nlia. }
      clear Hc.
      nm_runto AF_nm_exit; [nm_awr U33 RW|]. nm_keep U33.
      pmkst HS. nm_cs HS HAE.
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
        pose proof (nm_mb_of_chunk _ _ _ (YP09.mkRegion (Some 33%nat) 0 1 0 1
                                            [YP09.mkChunk 0 (CVal 1 (SOff 34 0))])
                      33%nat 0 (SOff 34 0) (bz (nthb pb (1 + i))) HSx
                      ltac:(cbn [ss_mem In]; first [left; reflexivity | right; left; reflexivity]) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 34%nat (bz (nthb pb (1 + i))) 0) by (ewo; exact E34);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U33, Z.add_0_r, nm_byte_of_bz in Md;
        apply (HEXIT (Datatypes.S i) (ms_regs ms) (ms_mem ms) _)
      end.
      split; [nlia|]. split; [|split].
      * rewrite HnN, HNN. apply RcIdentLib.name_len_full; [nlia|].
        intros j Hj. apply Hnz'. rewrite <- HNN, <- HnN in Hj. nlia.
      * nm_regs_blk HS RCS' R1 RCS.
      * split; [exact HJ|]. split; [|split; [|split; [|split; [|split]]]].
        -- exact (nm_kl_step i memL _ KL KEEPI).
        -- exact (nm_nb_step i memL _ ltac:(nlia) NB KEEPI Md).
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
        -- exact (proj1 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24)).
        -- exact (proj1 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
        -- exact (proj2 (proj2 (nm_slots_kept i memL _ ltac:(nlia) KEEPI V8 V16 V24))).
Qed.

Lemma nm_ent :
  (forall (n i : nat) regsL memL mdL, (i + n = NN)%nat -> (0 < n)%nat ->
     nm_at_head i regsL memL mdL ->
     SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + AF_nm_head)) memL (seg_rom SEGS)) mdL) POST) ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc) POST.
Proof.
  intros HLOOP.
  destruct nm2_lay as (Hsp & Hid0 & Hid1 & Hid8 & R4 & R5 & R6 & HIdl & HWR & HRA & HMB).
  pose proof HJ0 as (HAR & _).
  destruct (ing_pay_bounds lyc Sc W memc mdc p len pb HAR HPAY ltac:(lia))
    as (bi & Li & Hbi & Hb1 & Hb2 & P1 & P2 & P3 & P4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : INGEST_STK = 4128) by reflexivity.
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (HN1 : (1 <= NN)%nat) by (rewrite HNN, Hpl; clear - Hlen; lia).
  assert (HA : atoms_ok (EI regs idb pb)
    [(10%nat, mkAF 4096 (2 ^ 47 - 38) 0); (12%nat, mkAF 4096 (2 ^ 47 - 32) 0);
     (13%nat, mkAF 2 (2 ^ 64 - 1) 0)]).
  { cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
    - apply (ing0_afact regs idb pb 10 10%bv id); [lia | reflexivity | exact H10 | lia | lia].
    - apply (ing0_afact regs idb pb 12 12%bv p); [lia | reflexivity | exact H12 | lia | lia].
    - apply (ing0_afact regs idb pb 13 13%bv len); [lia | reflexivity | exact H13 | lia | lia]. }
  destruct (ing0_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs idb pb _ []
              HJ0 Hal16 HS1 HS2 HA I) as [HS0 SHOK].
  pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) 4096 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H11; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  pose proof (EI_reg regs idb pb 1 1%bv ltac:(lia) eq_refl) as E1.
  pose proof (EI_reg regs idb pb 10 10%bv ltac:(lia) eq_refl) as E10. rewrite H10 in E10. unfold w64 in E10.
  pose proof (EI_reg regs idb pb 12 12%bv ltac:(lia) eq_refl) as E12. rewrite H12 in E12. unfold w64 in E12.
  pose proof (EI_reg regs idb pb 13 13%bv ltac:(lia) eq_refl) as E13. rewrite H13 in E13. unfold w64 in E13.
  assert (Usp : bv_unsigned (ew (EI regs idb pb) 2) = spZ regs)
    by (rewrite (EI_reg regs idb pb 2 2%bv) by (first [lia | vm_compute; reflexivity]); reflexivity).
  assert (HEI : img_env VAL A_LIM (EI regs idb pb)) by (unfold EI; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ing_extra idb pb)) (EI regs idb pb))
    by (split; [intros n Hn; unfold EI; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof HJ0 as HJ.
  change memc with (ms_mem (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS))) in HJ.
  pose proof (ing_inv_init (spZ regs) id false W memc) as HI.
  unfold cfg_at. change (w64 A_reac_identity_ingest) with (Z_to_bv 64 A_reac_identity_ingest).
  paj_run_tok RUN HS HJ SHOK Ispan; [ing_awr regs sp0 id Usp E10 HWR |].
  ing_keep HI Usp E10.
  psrr_branch_tok RUN BR HS SHOK Ispan.
  (* the two sides of  bltu a5,16 : NN = len - 1, or NN = 16 *)
  all: rewrite branch_ltu_U in Hc;
       rewrite (nm2_U _ 13%nat len (-1)) in Hc by (nm2_ew; rewrite E13; reflexivity);
       rewrite nm2_Ulit in Hc; rewrite !Z.mod_small in Hc by (clear - Hlen; lia).
  1: apply Z.ltb_lt in Hc;
     assert (HNv : Z.of_nat NN = len - 1) by (rewrite HNN, Hpl; clear - Hc Hlen; lia).
  2: apply Z.ltb_ge in Hc;
     assert (HNv : Z.of_nat NN = 16) by (rewrite HNN, Hpl; clear - Hc Hlen; lia).
  (* 0x83d5c .. 0x83d74, then the loop head *)
  all: paj_run_to_tok RUNTO HS HJ SHOK Ispan AF_nm_head; [ing_awr regs sp0 id Usp E10 HWR |].
  all: ing_keep HI Usp E10.
  all: pmkst HS.
  all: nm2_reg HS (1%bv : bv 5) Q1; nm2_reg HS (2%bv : bv 5) Q2; nm2_reg HS (5%bv : bv 5) Q5;
       nm2_reg HS (6%bv : bv 5) Q6; nm2_reg HS (7%bv : bv 5) Q7; nm2_reg HS (10%bv : bv 5) Q10;
       nm2_reg HS (12%bv : bv 5) Q12; nm2_reg HS (13%bv : bv 5) Q13; nm2_reg HS (14%bv : bv 5) Q14;
       nm2_reg HS (15%bv : bv 5) Q15; nm2_reg HS (16%bv : bv 5) Q16; nm2_reg HS (17%bv : bv 5) Q17.
  all: pose proof (nm2_cs_of _ _ _ regs _ HS ltac:(env_agree_chain HAE)
                     ltac:(vm_compute; reflexivity)) as RCS;
       cbn [ms_regs restrict] in RCS.
  (* the three slots the prologue wrote, read back from the stack region's chunks *)
  all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let r2 := nm2_find rs 2%nat in
    lazymatch r2 with YP09.mkRegion _ _ _ _ _ ?cs =>
      lazymatch nm2_chunk_at cs (-24) with
      | CVal 8 (SOff ?n9 0) =>
        pose proof (nm2_val8 Ex ssx _ r2 2%nat (-24) (SOff n9 0) (bv_unsigned (getr regs 9)) HS
          ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat first [left; reflexivity | right])
          eq_refl
          ltac:(cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right])
          ltac:(apply (denot_atom Ex n9); [nm2_ew;
                  rewrite (EI_reg regs idb pb n9 9%bv ltac:(apply Nat.ltb_lt; reflexivity) ltac:(vm_compute; reflexivity));
                  symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange])
          ltac:(apply nm2_wrange)) as F8
      end;
      lazymatch nm2_chunk_at cs (-16) with
      | CVal 8 (SOff ?n8 0) =>
        pose proof (nm2_val8 Ex ssx _ r2 2%nat (-16) (SOff n8 0) (bv_unsigned (getr regs 8)) HS
          ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat first [left; reflexivity | right])
          eq_refl
          ltac:(cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right])
          ltac:(apply (denot_atom Ex n8); [nm2_ew;
                  rewrite (EI_reg regs idb pb n8 8%bv ltac:(apply Nat.ltb_lt; reflexivity) ltac:(vm_compute; reflexivity));
                  symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange])
          ltac:(apply nm2_wrange)) as F16
      end;
      lazymatch nm2_chunk_at cs (-8) with
      | CVal 8 (SOff ?n1 0) =>
        pose proof (nm2_val8 Ex ssx _ r2 2%nat (-8) (SOff n1 0) (bv_unsigned (getr regs 1)) HS
          ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat first [left; reflexivity | right])
          eq_refl
          ltac:(cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right])
          ltac:(apply (denot_atom Ex n1); [nm2_ew;
                  rewrite (EI_reg regs idb pb n1 1%bv ltac:(apply Nat.ltb_lt; reflexivity) ltac:(vm_compute; reflexivity));
                  symmetry; apply Z_to_bv_bv_unsigned | apply nm2_wrange])
          ltac:(apply nm2_wrange)) as F24
      end
    end
  end.
  all: cbn [ms_mem restrict] in F8, F16, F24; nm2_ew_in F8; nm2_ew_in F16; nm2_ew_in F24;
       rewrite Usp in F8, F16, F24.
  (* the loop lemma at n = NN, i = 0 *)
  all: eapply (HLOOP NN 0%nat); [clear - HN1; lia | clear - HN1; lia |].
  all: apply nm2_head_of;
  [ rewrite Q1; rewrite <- (nm2_w64_getr regs 1); apply nm2_sv;
    rewrite (nm2_U _ 1%nat (bv_unsigned (getr regs 1)) 0)
      by (nm2_ew; rewrite E1; symmetry; apply nm2_w64_getr);
    f_equal; ring
  | rewrite Q2; apply nm2_sv;
    rewrite (nm2_U _ 2%nat (spZ regs) (-32)) by
      (nm2_ew; rewrite (EI_reg regs idb pb 2 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity | lia]);
       symmetry; apply nm2_w64_getr);
    f_equal; ring
  | rewrite Q5; apply nm2_sv; rewrite U_SAlu; cbn [zalu_raw];
    rewrite (nm2_U _ 10%nat id 0) by (nm2_ew; rewrite E10; reflexivity); rewrite nm2_Ulit;
    rewrite Z.add_0_r, (Z.mod_small id) by (clear - Hid; lia);
    change (1 mod 2 ^ 64) with 1; rewrite (nm2_land1 id Hid8);
    unfold zcanon, M64; reflexivity
  | rewrite Q6; apply nm2_sv;
    rewrite (nm2_U _ 12%nat p 1) by (nm2_ew; rewrite E12; reflexivity); f_equal; ring
  | rewrite Q7; apply nm2_sv; rewrite nm2_Ulit; reflexivity
  | rewrite Q10; apply nm2_sv;
    rewrite (nm2_U _ 10%nat id 0) by (nm2_ew; rewrite E10; reflexivity); f_equal; ring
  | rewrite Q12; apply nm2_sv;
    rewrite (nm2_U _ 12%nat p 0) by (nm2_ew; rewrite E12; reflexivity); f_equal; ring
  | rewrite Q13; apply nm2_sv; rewrite nm2_Ulit; reflexivity
  | rewrite Q14; apply nm2_sv;
    rewrite (nm2_U _ 10%nat id 3) by (nm2_ew; rewrite E10; reflexivity); f_equal; ring
  | rewrite Q15; apply nm2_sv;
    first [ rewrite (nm2_U _ 13%nat len (-1)) by (nm2_ew; rewrite E13; reflexivity)
          | rewrite nm2_Ulit ];
    rewrite HNv; f_equal; ring
  | rewrite Q16; apply nm2_sv; rewrite (nm2_U _ 32%nat SBi 0) by (nm2_ew; apply EI_sb);
    f_equal; ring
  | rewrite Q17; apply nm2_sv; rewrite U_SAlu; cbn [zalu_raw];
    rewrite (nm2_U _ 10%nat id 3) by (nm2_ew; rewrite E10; reflexivity); rewrite nm2_Ulit;
    rewrite (Z.mod_small (id + 3)) by (clear - Hid Hid1; lia);
    first [ change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1)
          | change ((2 ^ 64 - 1) mod 2 ^ 64) with (2 ^ 64 - 1) ];
    rewrite (nm2_not (id + 3) ltac:(clear - Hid Hid1; lia)); unfold zcanon, M64; reflexivity
  | intros q Hq Hq2; rewrite (RCS q Hq Hq2); reflexivity
  | exact HJ
  | intros a Ha Hs; destruct HI as (HI1 & _); apply (aview_eq_of SEGS); unfold mrestrict;
    rewrite HI1; [reflexivity | rewrite unsigned_lit_small by exact Ha; exact Hs
                 | intros (Hf & _); discriminate Hf]
  | intros a Hpr; destruct HI as (_ & HI2); exact (apresent_grows (w_H W) memc _ a HI2 Hpr)
  | replace (spZ regs - 32 + 8) with (spZ regs + -24) by ring; exact F8
  | replace (spZ regs - 32 + 16) with (spZ regs + -16) by ring; exact F16
  | replace (spZ regs - 32 + 24) with (spZ regs + -8) by ring; exact F24 ].
Qed.

(* ---- the arm: the entry, the loop and the three ends ------------------------------------------- *)
Lemma nm_arm : SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc) POST.
Proof. exact (nm_ent (nm_loop nm_exit_ok nm_zero_ok)). Qed.
End arm.

(* The model-name arm (ad = 0x1000, 2 <= len), as treac_identity_ingest_spec needs it. *)
Lemma ing_arm_name : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 id -> getr regs 11 = w64 4096 -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 2 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  reac_identity_ingest_c.ingest_refused id p len = false ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb ->
  ting_pay_ok lyc Sc W memc p len pb ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id 4096 p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
    HJ0 Hra H10 H11 H12 H13 Hid Hp Hlen Hal16 HS1 HS2 Hpl Href HREC HPAY.
  apply nm_arm; assumption.
Qed.
Theorem pb_reac_identity_ingest : treac_identity_ingest_spec.
Proof.
  unfold treac_identity_ingest_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ Hra Hra4 H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Hev Hlive.
  case_eq (reac_identity_ingest_c.ingest_refused id p len); intros Href.
  - (* refused: the walk returns -1 at 0x83abc (id = 0) or 0x83ad0 (p = 0, len <> 0) *)
    destruct (Z.eq_dec id 0) as [I0 | I0].
    + exact (ing_refused_id0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
               HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR I0).
    + assert (Hpl0 : p = 0 /\ len <> 0).
      { unfold reac_identity_ingest_c.ingest_refused in Href.
        apply orb_true_iff in Href as [Hi | Hpl0]; [apply Z.eqb_eq in Hi; contradiction|].
        apply andb_true_iff in Hpl0 as [Hl0 Hp0]. apply negb_true_iff, Z.eqb_neq in Hl0. apply Z.eqb_eq in Hp0.
        split; assumption. }
      exact (ing_refused_p0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
               HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR I0 (proj1 Hpl0) (proj2 Hpl0)).
  - pose proof (HNR Href) as [HR HPy].
    destruct (Z.eq_dec len 0) as [L0 | L0].
    { exact (ing_len0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
               HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Href L0). }
    assert (L1 : 1 <= len) by lia.
    destruct (Z.eq_dec ad 0) as [A0 | A0].
    { subst ad. destruct (Z_lt_le_dec len 4) as [Ls | Ls].
      - exact (ing_short STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id 0 p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Href L1 (or_introl (conj eq_refl Ls))).
      - exact (ing_arm_fw STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Hp ltac:(lia) Hal16 HS1 HS2 Hpl Href HR HPy). }
    destruct (Z.eq_dec ad 1536) as [A1 | A1].
    { subst ad. destruct (Z_lt_le_dec len 8) as [Ls | Ls].
      - exact (ing_short STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id 1536 p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Href L1
                 (or_intror (or_introl (conj eq_refl Ls)))).
      - exact (ing_arm_ver STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Hp ltac:(lia) Hal16 HS1 HS2 Hpl Href HR HPy). }
    destruct (Z.eq_dec ad 4096) as [A4 | A4].
    { subst ad. destruct (Z_lt_le_dec len 2) as [Ls | Ls].
      - exact (ing_short STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id 4096 p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Href L1
                 (or_intror (or_intror (conj eq_refl Ls)))).
      - exact (ing_arm_name STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb
                 HJ Hra H10 H11 H12 H13 Hid Hp ltac:(lia) Hal16 HS1 HS2 Hpl Href HR HPy). }
    exact (ing_other STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
             HJ Hra H10 H11 H12 H13 Hid Had Hp Hlen Hal16 HS1 HS2 Hpl HNR Href L1 A0 A1 A4).
Qed.
End h.
End f.
End d.
