(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* sb_dec (fuzz_identity.asan 0x83494, 0x31c bytes, listing offset AF_sb_dec = 0x2d88): its ASan-build
   contract tsb_dec_spec, in cgif's caller-journal form (CONVENTIONS.md §2; cgif lib/YC20.v:311-365,
   tlzw_kept / tlzw_post / tlzw_spec): sb_dec writes its caller's struct sb (on the caller's machine
   stack) and the caller's buffer (in the caller's side-stack frame).
   DRAFT: statement and the walk's Section hypotheses only; the walk pb_sb_dec is not written yet. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
(* The side-stack frame helpers (identity twins of cgif YC44 PALibF / aj_flag_store_pi and YC85
   aj_stack_malloc_atS): lib/A/Prog/IdentFrame.v and the YC files Required below, in the integration
   branch. Only the walk uses them. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
(* The shared caller-journal shapes tcj_kept / twr_ok / tdst_ok: lib/A/Prog/IdentCJ.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
(* The plain model of sb_dec (released, origin/ossv/recipes c8557374ad2e), used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition A_sb_dec : Z := BASE + AF_sb_dec.
(* The stack the call needs, measured from the listing: the 96-byte frame (0x83494 addi sp,sp,-96),
   the 32-byte alignment of sp (0x834c4 andi sp,sp,-32: up to 16 more bytes, sp0 is 16-aligned), and
   below the aligned sp the ESTACK window of the class-0 side-stack frame allocation at 0x834f8.
   The real-stack fallback (0x8350c..0x83524: frame at s1-64, one probe store at s1-4096) is not
   reached (the use-after-return flag cell holds 1, AR_const_law); it would also stay inside
   [sp0 - 4208, sp0). *)
Definition SB_DEC_STK : Z := 112 + ESTACK.
(* Allocator events and live heap bytes of one call: none. The plain model allocates nothing, and the
   ASan listing calls no allocator; the class-0 side-stack frame allocation counts no event (YG00.v
   stack_malloc has no tick) and adds no heap block. Both must fit under the shared EV_MAX / LIVE_MAX. *)
Definition EV_SB_DEC : Z := 0.
Definition LIVE_SB_DEC : Z := 0.
(* ---- the walk's symbolic states ------------------------------------------------------------------
   Atoms: 0..31 the registers at entry (2 = sp0, 10 = b, 11 = v, 12 = md), 32 = SB (the shadow base),
   33 = the use-after-return flag cell, 34..37 = p, cap, n, over (the struct sb's fields), 38 = p + n
   (the buffer's write base, named by an alias so that p + n + j is the region offset j). *)
Definition sbd_Bx : sv := SOff 32 0.
Definition sbd_rtop : YP09.region := YP09.mkRegion (Some 2%nat) (-72) 0 (-72) 0 [].
Definition sbd_rprobe : YP09.region := YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [].
Definition sbd_rb : YP09.region := YP09.mkRegion (Some 10%nat) 0 28 16 28
  [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0));
   YP09.mkChunk 16 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 4 (SOff 37 0))].
Definition sbd_rq (acc : Z) : YP09.region := YP09.mkRegion (Some 38%nat) 0 acc 0 acc [].
Definition sbd_qr (acc : Z) : smem := if acc =? 0 then [] else [sbd_rq acc].
Definition sbd_regs0 (acc : Z) : smem :=
  [sbd_rtop; sbd_rprobe; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33; sbd_rb] ++ sbd_qr acc.
Definition sbd_atoms0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (11%nat, mkAF 0 (2 ^ 31 - 1) 0);
   (12%nat, mkAF 1 2 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF IMG_LO IMG_TOP 2);
   (34%nat, mkAF 0 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 (2 ^ 64 - 1) 0); (36%nat, mkAF 0 (2 ^ 64 - 5) 0);
   (37%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition sbd_qa (acc : Z) : list (nat * afact) := if acc =? 0 then [] else [(38%nat, HPTR 0)].
Definition sbd_alias0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 34 0) (SOff 36 0), SOff 38 0)].
Definition sbd_facts0 (acc : Z) : facts := mkFacts (sbd_atoms0 ++ sbd_qa acc) [] sbd_alias0.
Definition sbd_ss0 (acc : Z) : sstate := mkSS AF_sb_dec sr_atoms (sbd_regs0 acc) None (sbd_facts0 acc).
Definition sbd_SH0 (acc : Z) : list shent := mkSHE 10 0 32 :: (if acc =? 0 then [] else [mkSHE 38 0 acc]).
Definition sbd_extra (uarc p cap n ov : Z) : list word := map (Z_to_bv 64) [SB; uarc; p; cap; n; ov; p + n].
Section h.
Variable B : asyms.
(* The bytes sb_dec writes outside its own stack window and its own side-stack frame:
   b->n and b->over (b+16 .. b+28) and the emitted digits p[n .. n + acc). *)
Definition tsb_dec_wr (b p n acc : Z) (a : Z) : Prop :=
  (b + 16 <= a < b + 28) \/ (p + n <= a < p + n + acc).
(* Where the caller's struct sb lies: in the caller's machine stack, with the whole 32-byte slot
   [b, b+32) inside it (AR_zshadow_law then gives zero shadow for the four granules). The 4-byte store
   check of b->over (0x836a4 lb, 0x836a8 bnez -> 0x836d0 bge t6,a5) has its andi hoisted out of the loop
   (t6 = (b+24)&7 + 3, 0x83620/0x83630), so the walk decides it only with the whole granule [b+24, b+32)
   addressable (YCbn.v tok_branch: no slow block at 0x836d0). In fuzz_identity b is reac_box_name's
   machine stack (s1+152 and s1+120). *)
Definition tsb_dec_rec_at (lyc : alayout) (b : Z) : Prop :=
  ly_stk_lo lyc <= b /\ b + 32 <= ly_stk_hi lyc.
(* The post: cgif tlzw_post, YC20.v:328-346, with sb_dec's result (the plain sb_dec_c model: the struct
   sb record sb_rec p cap n' over' and the digits firstn acc (sb_dec_D v md) at p + n). *)
Definition tsb_dec_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b v md p cap n ov : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_SB_DEC) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    tcj_kept B SB_DEC_STK lyc Sc W memc W2 mem2 (spZ regs) (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n)) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) b 8 p /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 8) 8 cap /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 24) 4
      (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else ov) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (p + n)
      (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)).
(* The pre-condition: cgif tlzw_spec, YC20.v:347-365. a0 = b (struct sb { char *p; size_t cap, n;
   int over; }, 28 bytes), a1 = v, a2 = md (min_digits). *)
Definition tsb_dec_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b v md p cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  (* the struct sb: read (p, cap, n), written (n, over) *)
  b mod 8 = 0 -> 0 <= b -> b + 28 <= 2 ^ 63 -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_DEC_STK) ->
  tsb_dec_rec_at lyc b ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 4 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (* the buffer: written p[n .. n + acc) when there is room *)
  (0 < sb_dec_c.sb_dec_room cap n ->
     0 <= p /\ p + cap <= 2 ^ 63 /\
     tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= b \/ b + 28 <= p + n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK \/ spZ regs <= p + n)) ->
  (* room for sb_dec's own class-0 side-stack frame; the allocator budget (both increments are 0) *)
  Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV_SB_DEC <= EV_MAX -> blocks_bytes Sc + LIVE_SB_DEC <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS A_sb_dec regs memc mdc)
    (tsb_dec_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov).
(* The walk's Section hypotheses (CONVENTIONS.md §4; cgif lib/A/AChf.v:47-76 for a function with a
   side-stack frame). pb_sb_dec : tsb_dec_spec is proved under them in lib/A/Prog/sb_decWalk.v:52. *)
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* identity's PALibF (IdentFrame.v): as_got_uar B = VAL (A_OBJ 0) and
   SIGMA IS___asan_stack_malloc_c = pc_stack_malloc (as_code B) c for c = 0, 3, 4. *)
Hypothesis TLF : PALibF B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* The caller's machine stack has zero shadow (AR_zshadow_law, the stack range is its first entry). *)
Lemma sbd_stack_zero : forall ly0 S0 W1 mem1 md1 a, AR SEGS B ly0 S0 W1 mem1 md1 ->
  ly_stk_lo ly0 <= a -> a + 32 <= ly_stk_hi ly0 -> a mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF a 32.
Proof.
intros ly0 S0 W1 mem1 md1 a HAR Hlo Hhi Ha.
pose proof (al_zshadow _ _ LAWS ly0 S0 W1 mem1 md1 _ HAR (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
assert (Hal : ly_stk_lo ly0 mod 8 = 0).
{ destruct HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (_ & _ & _ & _ & T5 & _). unfold page_aligned in T5.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia. }
intros x Hx. exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod (ly_stk_lo ly0) 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2. pose proof (Z.div_mod a 8 ltac:(lia)) as D3.
pose proof (Z.div_mod (ly_stk_hi ly0 - ly_stk_lo ly0) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (ly_stk_hi ly0 - ly_stk_lo ly0) 8 ltac:(lia)) as M4.
replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly0) + (x / 8 - ly_stk_lo ly0 / 8))
  by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.
(* Where the buffer's bytes lie: each in a heap block or a side-stack frame of Sc (tdst_ok), so in
   application memory, off the image and below the allocator ceiling. *)
Lemma sbd_dst_byte : forall lyc Sc W memc mdc q n x, AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n ->
  q <= x < q + n ->
  4096 <= x < alloc_ceiling /\ (x < IMG_LO \/ IMG_TOP <= x) /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros lyc Sc W memc mdc q n x HAR Hd Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hd x Hx) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & H4096 & Hceil & Happ & _).
  pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hin) as Himg.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hceil & Happ).
  pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hin) as Himg.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* lia case-splits every disjunction of the context; the walks' contexts carry many, so the arithmetic
   steps clear them first (an unbounded lia here ran for 50 minutes). *)
Ltac sbd_nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
(* The symbolic state at sb_dec's first slot holds, with its shadow entries. *)
Lemma sbd_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b v md p cap n ov acc : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  b mod 8 = 0 -> tsb_dec_rec_at lyc b -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_DEC_STK) ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 4 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (acc = 0 \/ acc = 1 \/ acc = 2 \/ acc = 3) ->
  (0 < acc -> tdst_ok B lyc Sc (p + n) acc /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) acc /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) acc /\
     (p + n + acc <= b \/ b + 28 <= p + n) /\
     (p + n + acc <= spZ regs - SB_DEC_STK \/ spZ regs <= p + n)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (sbd_extra (as_uar_cell B) p cap n ov))) (sbd_ss0 acc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sb_dec)) memc (seg_rom SEGS))) /\
  sh_ok SEGS sbd_Bx (sbd_SH0 acc) (Eimg (Ereg regs (sbd_extra (as_uar_cell B) p cap n ov))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov acc
  HJ Hal16 Hwin Hsp H10 H11 H12 Hv Hmd Hb8 Hbstk Hbsp Vp Vcap Vn Vov Rp Rcap Rn Rn4 Rov HWRb Hacc HQ.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hst16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hbstk as [Hblo Hbhi].
assert (WS : SB_DEC_STK = 4208) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huimg. pose proof (palf_uar_al B TLF) as Hual. pose proof (palf_sep B TLF) as Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 30 ltac:(lia)) as HO30.
set (uarc := as_uar_cell B) in *.
set (E := Eimg (Ereg regs (sbd_extra uarc p cap n ov))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (sbd_extra uarc p cap n ov)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 md) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 uarc) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 ov) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (p + n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall i z, ew E i = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some i) = z).
{ intros i z Hi Hz. cbn [base_val]. rewrite Hi. apply unsigned_lit_small. exact Hz. }
assert (Hmd' : 1 <= md <= 2) by lia. clear Hmd.
assert (Hacc' : 0 <= acc <= 3) by lia.
(* the buffer's facts, when there is one *)
assert (HQF : 0 < acc -> 4096 <= p + n /\ p + n + acc <= alloc_ceiling /\
  (forall x, p + n <= x < p + n + acc -> (x < IMG_LO \/ IMG_TOP <= x) /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))).
{ intros Hpos. destruct (HQ Hpos) as (Hd & _).
  pose proof (sbd_dst_byte lyc Sc W memc mdc (p + n) acc (p + n) HAR Hd ltac:(lia)) as (A1 & _).
  pose proof (sbd_dst_byte lyc Sc W memc mdc (p + n) acc (p + n + acc - 1) HAR Hd ltac:(lia)) as (A2 & _).
  split; [lia|]. split; [lia|]. intros x Hx. exact (proj2 (sbd_dst_byte lyc Sc W memc mdc (p + n) acc x HAR Hd Hx)). }
assert (Hbwin : forall a, b + 16 <= a < b + 28 -> apresent (w_H W) memc a) by (intros a Ha; exact (proj1 (proj2 (HWRb a ltac:(lia))))).
split.
- rewrite restrict_mkst_fx. unfold sbd_ss0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + destruct Hacc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
  + unfold sbd_regs0. apply Forall_app. split.
    * unfold sbd_rtop, sbd_rprobe, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, sbd_rb.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      -- cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
         intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      -- cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
         intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      -- rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
         [cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
      -- rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
         rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
      -- rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) uarc);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
      -- rewrite (VB 33%nat uarc E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ uarc 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
      -- rewrite (VB 10%nat b E10) by lia. split; [lia|]. split; [lia|].
         split; [intros o Ho; apply (apresent_writable SEGS); apply Hbwin; lia|].
         constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
         ++ apply (chunk_ok_val SEGS E _ b 0 8 _ p); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vp].
         ++ apply (chunk_ok_val SEGS E _ b 8 8 _ cap); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcap].
         ++ apply (chunk_ok_val SEGS E _ b 16 8 _ n); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
         ++ apply (chunk_ok_val SEGS E _ b 24 4 _ ov); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vov].
    * unfold sbd_qr. destruct (Z.eqb_spec acc 0) as [Ha0 | Ha0]; [apply Forall_nil|].
      destruct (HQ ltac:(lia)) as (Hd & Hra & Hwq & Hdb & Hds). destruct (HQF ltac:(lia)) as (Q1 & Q2 & Q3).
      apply Forall_cons; [|apply Forall_nil]. unfold region_ok, sbd_rq.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 38%nat (p + n) E38) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (Hwq (p + n + o) ltac:(lia)))).
  + apply pairwise_disjoint_of_extents. unfold sbd_regs0, sbd_qr.
    unfold sbd_rtop, sbd_rprobe, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, sbd_rb, sbd_rq.
    unfold zseps, zseps_from in Hsep. cbn [fst snd] in Hsep.
    destruct Hsep as ((S1 & S2 & S3 & _) & (S4 & S5 & _) & (S6 & _) & _). clear Hacc.
    assert (BVs : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z) by (intros z Hz; apply unsigned_lit_small; exact Hz).
    destruct (Z.eqb_spec acc 0) as [Ha0 | Ha0].
    * replace (acc =? 0) with true by (symmetry; apply Z.eqb_eq; exact Ha0).
      cbn [app map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite Usp, E10, E33, EO0, EO1, EO30, !BVs by (sbd_nodisj; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite ?Z.add_0_r.
      destruct Hbsp as [Hbsp | Hbsp];
      repeat match goal with |- _ /\ _ => split end;
      first [exact I | assumption | (apply or_comm; assumption) | (sbd_nodisj; lia)].
    * replace (acc =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha0).
      destruct (HQ ltac:(sbd_nodisj; lia)) as (Hd & Hra & Hwq & Hdb & Hds). destruct (HQF ltac:(sbd_nodisj; lia)) as (Q1 & Q2 & Q3).
      assert (QI : forall c, IMG_LO <= c -> c + 8 <= IMG_TOP -> p + n + acc <= c \/ c + 8 <= p + n).
      { intros c Hc1 Hc2. destruct (Z_le_gt_dec (p + n + acc) c) as [|Hl]; [left; sbd_nodisj; lia|].
        destruct (Z_le_gt_dec (c + 8) (p + n)) as [|Hr]; [right; sbd_nodisj; lia|]. exfalso.
        destruct (Q3 (Z.max (p + n) c) ltac:(lia)) as [[Q31 | Q31] _]; sbd_nodisj; lia. }
      pose proof (QI _ (proj1 HO0) (proj2 HO0)) as Q0. pose proof (QI _ (proj1 HO1) (proj2 HO1)) as Q1'.
      pose proof (QI _ (proj1 HO30) (proj2 HO30)) as Q30.
      assert (Qu : p + n + acc <= uarc \/ uarc + 4 <= p + n)
        by (destruct (QI uarc ltac:(lia) ltac:(lia)) as [Qu|Qu]; [left|right]; sbd_nodisj; lia).
      cbn [app map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite Usp, E10, E38, E33, EO0, EO1, EO30, !BVs by (sbd_nodisj; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite ?Z.add_0_r.
      destruct Hbsp as [Hbsp | Hbsp]; destruct Hdb as [Hdb | Hdb]; destruct Hds as [Hds | Hds];
      repeat match goal with |- _ /\ _ => split end;
      first [exact I | assumption | (apply or_comm; assumption) | (sbd_nodisj; lia)].
  + split; [|split; [exact I|]].
    * unfold sbd_facts0, sbd_atoms0, sbd_qa. cbn [f_atoms]. clear Hacc.
      destruct (Z.eqb_spec acc 0) as [Ha0 | Ha0];
      [replace (acc =? 0) with true by (symmetry; apply Z.eqb_eq; exact Ha0)
      |replace (acc =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha0); destruct (HQF ltac:(lia)) as (Q1 & Q2 & Q3)];
      cbn [app atoms_ok]; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2];
      rewrite Usp, E10, E11, E12, E32, E33, E34, E35, E36, E37, ?E38, !unsigned_lit_small by (unfold SB; sbd_nodisj; lia);
      change (2 ^ 4) with 16; change (2 ^ 3) with 8; change (2 ^ 2) with 4; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
      unfold SB; sbd_nodisj; repeat match goal with |- _ /\ _ => split end; try lia.
    * cbn [sbd_facts0 f_alias sbd_alias0 alias_ok]. split; [|exact I].
      cbn [sv_denot]. rewrite E34, E36, E38, !Z.add_0_r, !Z_to_bv_bv_unsigned. apply YI08.alu64_add_lit.
- unfold sh_ok, sbd_SH0. apply Forall_cons.
  + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (UB : U E sbd_Bx = SHADOW_OFF) by (unfold U, sbd_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
    assert (U10 : U E (SOff 10 0) = b) by (unfold U; cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by lia; reflexivity).
    rewrite UB, U10, Z.add_0_r. rewrite <- (aview_rd_of SEGS). split.
    * replace (32 - 0) with 32 by lia. apply (sbd_stack_zero lyc Sc W memc mdc b HAR); lia.
    * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF. lia.
  + destruct (Z.eqb_spec acc 0) as [Ha0 | Ha0]; [apply Forall_nil|].
    destruct (HQ ltac:(lia)) as (Hd & Hra & Hwq & Hdb & Hds). destruct (HQF ltac:(lia)) as (Q1 & Q2 & Q3).
    apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (UB : U E sbd_Bx = SHADOW_OFF) by (unfold U, sbd_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
    assert (U38 : U E (SOff 38 0) = p + n) by (unfold U; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by lia; reflexivity).
    rewrite UB, U38, Z.add_0_r. rewrite <- (aview_rd_of SEGS). split.
    * replace (acc - 0) with acc by lia. exact Hra.
    * intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
      exact (proj2 (Q3 a ltac:(lia))).
Qed.
(* Theorem pb_sb_dec : tsb_dec_spec is proved in lib/A/Prog/sb_decWalk.v:52. *)
End walk.
End h.
End f.
End d.
