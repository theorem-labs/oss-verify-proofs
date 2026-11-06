(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:358-361 [Apache-2.0];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* sb_ch (fuzz_identity.asan-ubsan 0x83838, 0x10c bytes, listing offset AF_sb_ch = 0x30c4): its ASan+UBSan-build
   contract tsb_ch_spec, in cgif's caller-journal form (CONVENTIONS.md section 2; cgif lib/YC20.v:311-365, as
   fuzz_grant's lib/A/Prog/CtrlFinish.v states it): sb_ch writes its caller's struct sb (on the caller's machine
   stack) and one byte of the caller's buffer (in the caller's side-stack frame).
   On the ASan build sb_ch is inlined into sb_dec and reac_box_name, so no A twin exists; the struct and buffer
   premises follow those the A draft of sb_dec (lib/A/Prog/sb_dec.v tsb_dec_spec) states for the same struct, with these differences: tsb_ch_rec_at below also allows a live side-stack frame of the caller and bounds 28 bytes where the draft's tsb_dec_rec_at bounds 32 bytes of the machine stack; sb_ch also asks the struct's 28 bytes addressable and n + 1 < 2 ^ 64 where the draft asks n + 4 < 2 ^ 64; and for the byte p[n] it writes when n + 1 < cap it asks 0 < p where the draft asks 0 <= p.
   C (fuzz_identity.c): static void sb_ch(struct sb *b, char c)
     { if (b->n + 1 < b->cap) b->p[b->n++] = c; else b->over = 1; }
   The released ubsan template is lib/U/Prog/sb_ch_c.v (sb_ch_contract, ubsan 0x14864); its sb_rec is the same
   28 bytes (p, cap, n at b, b + 8, b + 16; over at b + 24). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81 YC4b.
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
Definition A_sb_ch : Z := BASE + AF_sb_ch.
(* The stack the call needs, measured from the listing: the 16-byte frame (0x83838 addi sp,sp,-16; ra at sp+8)
   and ESTACK for the runtime below it. sb_ch calls nothing but the error path (__asan_report_store4/store1/load8/
   store8 at 0x83918..0x83940), which the walk shows is never reached. *)
Definition SB_CH_STK : Z := 16 + ESTACK.
(* Allocator events of one call: none (sb_ch calls no allocator). *)
Definition EV_SB_CH : Z := 0.
Section h.
Variable B : asyms.
(* The bytes sb_ch may write outside its own stack window: b->n and b->over (b + 16 .. b + 28) and, when there is
   room (n + 1 < cap), p[n] (the shape sb_dec's lane asked for, sbdecb/sb_ch-at-sb_dec.md; the post says which of
   b->n / b->over keeps its value). *)
Definition tsb_ch_wr (b p n cap : Z) (a : Z) : Prop :=
  (b + 16 <= a < b + 28) \/ (n + 1 < cap /\ a = p + n).
(* Where the caller's struct sb lies: in one live side-stack frame of the caller's current state or in the
   machine stack (the A draft of sb_dec, tsb_dec_rec_at; cgif tlzw_pR_ok, YC20.v:324-327). In fuzz_identity.asan-
   ubsan it is reac_box_name's machine stack (s1 + 152, s1 + 120, s1 + 88), passed on by sb_dec. *)
Definition tsb_ch_rec_at (lyc : alayout) (Sc : astate) (b : Z) : Prop :=
  (exists cid pos, In (cid, pos) (frames Sc) /\ forall a, b <= a < b + 28 -> in_zr a (frame_rng lyc (cid, pos))) \/
  (ly_stk_lo lyc <= b /\ b + 28 <= ly_stk_hi lyc).
(* The post (CtrlFinish's tctrl_finish_post; cgif tlzw_post, YC20.v:328-346): back at ra, the caller's journal
   extended with no event, the world and the caller's layout and allocator state unchanged, callee-saved registers
   kept, every byte but sb_ch's own window and tsb_ch_wr kept, and the struct as sb_ch leaves it (the ubsan
   template's two cases): with room, n + 1 at b + 16 and c at p + n; without, 1 at b + 24. *)
Definition tsb_ch_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b c p cap n ov : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 (k + EV_SB_CH) /\
    aregs_preserved regs regs2 /\
    tcj_kept B SB_CH_STK lyc Sc W memc W2 mem2 (spZ regs) (tsb_ch_wr b p n cap) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) b 8 p /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 8) 8 cap /\
    (if n + 1 <? cap
     then val_mem SEGS (mrestrict (w_H W2) mem2) (b + 16) 8 (n + 1) /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (b + 24) 4 ov /\
          garr8 SEGS (mrestrict (w_H W2) mem2) (p + n) [c]
     else val_mem SEGS (mrestrict (w_H W2) mem2) (b + 16) 8 n /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (b + 24) 4 1).
(* The pre-condition (CtrlFinish's tctrl_finish_spec; cgif tlzw_spec, YC20.v:347-365). a0 = b (struct sb { char *p;
   size_t cap, n; int over; }, 28 bytes), a1 = c (a char: every caller passes a zero-extended byte).
   The listing's UBSan checks add to the A draft's struct premises: b 8-aligned (0x83840, alignment trap at
   0x83908) and, when there is room, p <> 0 and p + n without wrap (0x838b0..0x838c4, the pointer-overflow traps). *)
Definition tsb_ch_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b c p cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_CH_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> getr regs 11 = w64 c -> 0 <= c < 256 ->
  (* the struct sb: read (p, cap, n), written (n or over) *)
  b mod 8 = 0 -> 0 <= b -> b + 28 <= 2 ^ 63 -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_CH_STK) ->
  tsb_ch_rec_at lyc Sc b ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b 28 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (* the buffer byte p[n], written when there is room *)
  (n + 1 < cap ->
     0 < p /\ p + cap <= 2 ^ 63 /\
     tdst_ok B lyc Sc (p + n) 1 /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) 1 /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) 1 /\
     (p + n + 1 <= b \/ b + 28 <= p + n) /\
     (p + n + 1 <= spZ regs - SB_CH_STK \/ spZ regs <= p + n)) ->
  SRr SEGS W (cfg_at SEGS A_sb_ch regs memc mdc)
    (tsb_ch_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b c p cap n ov).
(* ---- The walk (CONVENTIONS.md section 5; the templates are lib/A/Prog/reac_box_catalogue.v, a caller-journal
   leaf with shadow-checked accesses, and lib/A/Prog/check_str.v, an alias fact for a computed address). ---- *)
(* The walk's environment: the registers, then the extra atoms 32 p, 33 cap, 34 n, 35 ov (the struct's fields),
   36 the shadow base SB (the shadow cell's value) and 37 p + n (the byte sb_ch stores when there is room). *)
Definition SbBx : sv := SOff 36 0.
Definition sb_extra (p cap n ov : Z) : list word := map (Z_to_bv 64) [p; cap; n; ov; SB; p + n].
Definition ESB (regs : bvmap 5 word) (p cap n ov : Z) : env := Eimg (Ereg regs (sb_extra p cap n ov)).
(* The struct sb at a0: 28 bytes read, b + 16 .. b + 28 (n and over) writable. *)
Definition sb_rec_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 28 16 28
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
     YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SOff 35 0))].
(* The byte p[n], present only when there is room. *)
Definition sb_pn_region : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 1 [].
Definition sb_regions (room : bool) : smem :=
  [sb_rec_region; stack_region 16; got_regionP; bcell_regionP 36] ++ (if room then [sb_pn_region] else []).
Definition sb_atoms0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 28) 3); (36%nat, mkAF SB SB 0)].
(* With room, p is non-null and below 2 ^ 63, p + n is a byte of a heap block or a frame, and the address the
   walk computes at 0x838a8 (add a0,a5,a6: p + n) is the atom 37. *)
Definition sb_facts (room : bool) : facts :=
  if room
  then mkFacts (sb_atoms0 ++ [(32%nat, mkAF 1 (2 ^ 63 - 1) 0); (37%nat, mkAF 4096 (2 ^ 47 - 1) 0)]) []
         [(SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 37 0)]
  else mkFacts sb_atoms0 [] [].
Definition ss_sb (room : bool) : sstate := mkSS AF_sb_ch sr_atoms (sb_regions room) None (sb_facts room).
(* The shadow entries: the struct's 28 bytes and, with room, the byte p[n]. *)
Definition sb_SH (room : bool) : list shent := mkSHE 10 0 28 :: (if room then [mkSHE 37 0 1] else []).
(* The bytes the walk's regions may write: its 16-byte frame, b + 16 .. b + 28 and [q, q + ql). *)
Definition sbz (sp b q ql : Z) (a : Z) : Prop := (sp - 16 <= a < sp) \/ (b + 16 <= a < b + 28) \/ (q <= a < q + ql).
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
(* Where the struct lies (tsb_ch_rec_at): a side-stack frame or the machine stack. *)
Lemma sb_rec_where : forall lyc Sc (W : world SEGS) memc mdc b,
  AR SEGS B lyc Sc W memc mdc -> tsb_ch_rec_at lyc Sc b ->
  4096 <= b /\ b + 28 <= 2 ^ 47 /\ (b + 28 <= IMG_LO \/ IMG_TOP <= b) /\
  (b + 28 <= kLowShadowBeg \/ kHighMemBeg <= b).
Proof.
intros lyc Sc W memc mdc b HAR Hrec.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hrec as [(cid & pos & Hin & Hrng) | (Hlo & Hhi)].
- destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Himg.
  pose proof (Hrng b ltac:(lia)) as Ha1. pose proof (Hrng (b + 27) ltac:(lia)) as Ha2.
  unfold frame_rng, in_zr in Ha1, Ha2. cbn [fst snd] in Ha1, Ha2.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfh.
  unfold kLowShadowBeg, kHighMemBeg. lia.
- pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (L1 & [L2 L3] & L4 & L5 & L6 & L7 & L8).
  unfold kHighMemBeg, kHighMemEnd in *. unfold kLowShadowBeg. lia.
Qed.
(* Where the byte p[n] lies (tdst_ok): a heap block or a side-stack frame. *)
Lemma sb_dst_where : forall lyc Sc (W : world SEGS) memc mdc q,
  AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc q 1 ->
  4096 <= q /\ q < alloc_ceiling /\ (q + 1 <= IMG_LO \/ IMG_TOP <= q) /\
  (q + 1 <= kLowShadowBeg \/ kHighMemBeg <= q).
Proof.
intros lyc Sc W memc mdc q HAR HD.
destruct (HD q ltac:(lia)) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & H4096 & Hce & Happ & _).
  pose proof (blk_off_imgP _ _ _ _ _ _ bb m HAR Hin) as Himg.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowShadowBeg, kHighMemBeg. lia.
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hce & Happ).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Himg.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowShadowBeg, kHighMemBeg. lia.
Qed.
(* The symbolic state at sb_ch's first slot, and its shadow entries. *)
Lemma sb_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (b p cap n ov : Z) (room : bool),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_CH_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> b mod 8 = 0 -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_CH_STK) ->
  tsb_ch_rec_at lyc Sc b ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b 28 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (room = true ->
     0 < p /\ p + cap <= 2 ^ 63 /\ n + 1 < cap /\
     tdst_ok B lyc Sc (p + n) 1 /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) 1 /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) 1 /\
     (p + n + 1 <= b \/ b + 28 <= p + n) /\
     (p + n + 1 <= spZ regs - SB_CH_STK \/ spZ regs <= p + n)) ->
  st_ok_pi SEGS VAL (ESB regs p cap n ov) (ss_sb room)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sb_ch)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS SbBx (sb_SH room) (ESB regs p cap n ov) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b p cap n ov room
  HJc Hal16 Hwlo Hwhi H10 Hb8 Hbside Hrec Vp Vcap Vn Vov Rp Rcap Rn Rn1 Rov HRA HWR HROOM.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
destruct (sb_rec_where lyc Sc W memc mdc b HAR Hrec) as (Hb4096 & Hb47 & Hbimg & Hbband).
assert (Hsplo : 2 ^ 46 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 31)) as Vc.
rewrite restrict_mkst_fx.
set (E := ESB regs p cap n ov).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (sb_extra p cap n ov)) i)
  by (intros i Hi; subst E; unfold ESB; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 ov) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (p + n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold ESB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
  by (subst E; unfold ESB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ub : bv_unsigned (ew E 10) = b) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 36) = SB) by (rewrite E36; apply unsigned_lit_small; unfold SB; lia).
assert (Ug : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite Eg; apply unsigned_lit_small; lia).
assert (Uc : bv_unsigned (ew E (A_OBJ 31)) = VAL (A_OBJ 31)) by (rewrite Ec; apply unsigned_lit_small; lia).
assert (UBx : U E SbBx = SHADOW_OFF) by (unfold SbBx; rewrite (U_atom E 36 SB E36) by (unfold SB; lia); reflexivity).
assert (U10 : U E (SOff 10 0) = b) by (exact (U_atom E 10 b E10 ltac:(lia))).
assert (RO_rec : region_ok SEGS E (mrestrict (w_H W) memc) sb_rec_region).
{ unfold region_ok, sb_rec_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Ub. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (HWR (b + o) ltac:(lia)))).
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (chunk_ok_val SEGS E _ b 0 8 _ p);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Vp.
    + apply (chunk_ok_val SEGS E _ b 8 8 _ cap);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcap].
    + apply (chunk_ok_val SEGS E _ b 16 8 _ n);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
    + apply (chunk_ok_val SEGS E _ b 24 4 _ ov);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vov]. }
assert (RO_stk : region_ok SEGS E (mrestrict (w_H W) memc) (stack_region 16)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RO_got : region_ok SEGS E (mrestrict (w_H W) memc) got_regionP).
{ unfold region_ok, got_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Ug. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
  [cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot). }
assert (RO_cell : region_ok SEGS E (mrestrict (w_H W) memc) (bcell_regionP 36)).
{ unfold region_ok, bcell_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Uc. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 36 0) SB);
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell). }
assert (A2 : afact_ok E 2 (mkAF (2 ^ 46) (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
  split; [lia|]. split; [exact Hal16 | lia]. }
assert (A10 : afact_ok E 10 (mkAF 4096 (2 ^ 47 - 28) 3)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ub. change (2 ^ 3) with 8.
  split; [lia|]. split; [exact Hb8 | lia]. }
assert (A36 : afact_ok E 36 (mkAF SB SB 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite USB, Z.pow_0_r, Z.mod_1_r. unfold SB. lia. }
assert (SH_rec : shent_ok SEGS SbBx E (mrestrict (w_H W) memc) (mkSHE 10 0 28)).
{ apply (shent_ok_of_range SEGS (w_H W) memc E SbBx 10 b 28 b 0 28 HRA UBx U10); [lia | lia |].
  intros x Hx. unfold kLowShadowBeg, kHighMemBeg in Hbband. unfold SHADOW_OFF. lia. }
destruct room.
- destruct (HROOM eq_refl) as (Hp0 & Hpcap & Hlt & HDST & HRApn & HWRpn & Hpnb & Hpnsp).
  destruct (sb_dst_where lyc Sc W memc mdc (p + n) HAR HDST) as (Hq4096 & Hqce & Hqimg & Hqband).
  assert (U32 : bv_unsigned (ew E 32) = p) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (Upn : bv_unsigned (ew E 37) = p + n) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (RO_pn : region_ok SEGS E (mrestrict (w_H W) memc) sb_pn_region).
  { unfold region_ok, sb_pn_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Upn. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (HWRpn (p + n + o) ltac:(lia)))). }
  assert (SH_pn : shent_ok SEGS SbBx E (mrestrict (w_H W) memc) (mkSHE 37 0 1)).
  { apply (shent_ok_of_range SEGS (w_H W) memc E SbBx 37 (p + n) 1 (p + n) 0 1 HRApn UBx);
    [exact (U_atom E 37 (p + n) E37 ltac:(lia)) | lia | lia |].
    intros x Hx. unfold kLowShadowBeg, kHighMemBeg in Hqband. unfold SHADOW_OFF. lia. }
  assert (A32 : afact_ok E 32 (mkAF 1 (2 ^ 63 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, Z.pow_0_r, Z.mod_1_r. lia. }
  assert (A37 : afact_ok E 37 (mkAF 4096 (2 ^ 47 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Upn, Z.pow_0_r, Z.mod_1_r. lia. }
  split.
  + unfold ss_sb. apply pa_entry_st_ok_full.
    * apply regs_ok_Eimg_Ereg.
    * vm_compute. reflexivity.
    * unfold sb_regions. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
      first [exact RO_rec | exact RO_stk | exact RO_got | exact RO_cell | exact RO_pn].
    * apply pairwise_disjoint_of_extents.
      unfold sb_regions, sb_rec_region, sb_pn_region, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite Ub, Usp, Ug, Uc, Upn.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    * unfold facts_ok, sb_facts, sb_atoms0. cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I|]].
      -- repeat match goal with |- _ /\ _ => split end;
         first [exact A2 | exact A10 | exact A36 | exact A32 | exact A37 | exact I].
      -- split; [|exact I].
         apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 32 p E32), (U_atom E 34 n E34), (U_atom E 37 (p + n) E37) by lia.
         unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
  + unfold sh_ok. cbn [sb_SH]. repeat apply Forall_cons; try apply Forall_nil; first [exact SH_rec | exact SH_pn].
- split.
  + unfold ss_sb. apply pa_entry_st_ok_full.
    * apply regs_ok_Eimg_Ereg.
    * vm_compute. reflexivity.
    * unfold sb_regions. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
      first [exact RO_rec | exact RO_stk | exact RO_got | exact RO_cell].
    * apply pairwise_disjoint_of_extents.
      unfold sb_regions, sb_rec_region, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite Ub, Usp, Ug, Uc.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    * unfold facts_ok, sb_facts, sb_atoms0. cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I].
      repeat match goal with |- _ /\ _ => split end; first [exact A2 | exact A10 | exact A36 | exact I].
  + unfold sh_ok. cbn [sb_SH]. repeat apply Forall_cons; try apply Forall_nil; exact SH_rec.
Qed.
(* The post from the return slot: the journal, ra, the callee-saved registers, what the run kept (KEEP, the
   windows of the walk's regions) and the struct's fields as the final symbolic memory holds them. *)
Lemma sb_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
  (b c p cap n ov ql : Z) (regsF : bvmap 5 word) memF mdF,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  YK0s.ret_ok (getr regs 1) -> getr regsF 1 = getr regs 1 -> aregs_preserved regs regsF ->
  sp0 - STK <= spZ regs - SB_CH_STK -> spZ regs <= sp0 ->
  (b + 28 <= IMG_LO \/ IMG_TOP <= b) ->
  ((ql = 0 /\ cap <= n + 1) \/ (ql = 1 /\ n + 1 < cap /\ (p + n + 1 <= IMG_LO \/ IMG_TOP <= p + n))) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sbz (spZ regs) b (p + n) ql a ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memF a) ->
  val_mem SEGS (mrestrict (w_H W) memF) b 8 p -> val_mem SEGS (mrestrict (w_H W) memF) (b + 8) 8 cap ->
  (if n + 1 <? cap
   then val_mem SEGS (mrestrict (w_H W) memF) (b + 16) 8 (n + 1) /\
        val_mem SEGS (mrestrict (w_H W) memF) (b + 24) 4 ov /\
        garr8 SEGS (mrestrict (w_H W) memF) (p + n) [c]
   else val_mem SEGS (mrestrict (w_H W) memF) (b + 16) 8 n /\
        val_mem SEGS (mrestrict (w_H W) memF) (b + 24) 4 1) ->
  tsb_ch_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b c p cap n ov W
    (mkCfg (mkst regsF (v_jalr (getr regsF 1) 0) memF (seg_rom SEGS)) mdF).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b c p cap n ov ql regsF memF mdF
  HJ Hra R1 HP Hwlo Hwhi Hbimg Hql KEEP HPRES Fp Fcap Fif.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (KEEP' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SB_CH_STK <= a < spZ regs) -> ~ tsb_ch_wr b p n cap a ->
  aview SEGS (w_H W) memF a = aview SEGS (w_H W) memc a).
{ intros a Ha Hs Hw. apply KEEP; [exact Ha|]. unfold sbz, tsb_ch_wr in *.
  intros [Hz | [Hz | Hz]]; [lia | apply Hw; left; lia |].
  destruct Hql as [(-> & _) | (-> & Hlt & _)]; [lia | apply Hw; right; split; [exact Hlt | lia]]. }
unfold tsb_ch_post. split; [reflexivity|].
exists regsF, memF, mdF.
split; [rewrite R1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [replace (k + EV_SB_CH) with k by (unfold EV_SB_CH; lia); exact HJ|].
split; [exact HP|].
split.
{ unfold tcj_kept.
  split.
  { intros a Ha Hs Hw. apply KEEP'; [lia | exact Hs | exact Hw]. }
  split.
  { intros bb m i Hin Hi Hw.
    destruct (al_blocks SEGS B LAWS lyc Sc W memF mdF bb m HAR Hin) as (_ & H4096 & Hce & _ & _).
    apply KEEP'; [lia | lia | exact Hw]. }
  split.
  { intros a Hi Hns He. pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hrng.
    unfold kLowMemEnd in Hlow.
    apply KEEP'; [lia | lia |].
    unfold tsb_ch_wr. intros [Hw | (Hlt & ->)]; [lia |].
    destruct Hql as [(_ & Hge) | (_ & _ & Hq)]; lia. }
  split.
  { intros cid pos a Hin Hr Hw.
    destruct (frame_zone SEGS B LAWS lyc Sc W memF mdF cid pos a HAR Hin Hr) as (Hz & _).
    apply KEEP'; [| lia | exact Hw].
    destruct Hr as [Hr | Hr]; unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
    pose proof (frames_bounds SEGS B LAWS lyc Sc W memF mdF cid pos HAR Hin) as (Hf0 & Hfc & _);
    pose proof (fs_frame_bytes_nonneg cid) as Hfb;
    [lia | pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb; unfold kLowMemEnd in *; lia]. }
  split.
  { intros a Ha Hs Hp. apply HPRES. exact Hp. }
  { intros a Ha. apply Hpres. lia. } }
split; [exact Fp|]. split; [exact Fcap|]. exact Fif.
Qed.
(* ---- The driver: run, refute the branches the pre-condition rules out, follow the others. ---- *)
Local Ltac sb_uval :=
  lazymatch goal with |- bv_unsigned (ew ?E0 ?i) = _ =>
    match goal with H : bv_unsigned (ew E0 i) = _ |- _ => exact H end end.
Local Ltac sb_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx);
    lazymatch goal with Usp : bv_unsigned (ew _ 2%nat) = ?SP |- _ =>
    repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (SP - spx));
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
    | eapply awr_ok_cons_gen;
      [ reflexivity
      | cbn [ew ewset Nat.eqb]; sb_uval
      | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        match goal with HW : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 (HW a ltac:(lia))) end
      | ] ]
    end
  end.
Local Ltac sb_win :=
  let bb0 := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb0 wlo whi x Hin Hr;
  vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hr;
      repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hr end;
      unfold sbz; lia
    | ]);
  try destruct Hin.
Local Ltac sb_keep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1), HG : mem_grows _ _,
    KEEP : forall a, _ -> ~ sbz ?sp ?bb ?q ?ql a -> aview ?sg ?H ?m0 a = aview _ _ ?mem a,
    HPRES : forall a, apresent ?H ?mem a -> apresent ?H ?m0 a |- _ =>
    let K2 := fresh "KEEP" in let P2 := fresh "HPRES" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ sbz sp bb q ql a -> aview sg H m1 a = aview sg H mem a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz;
      refine (eq_trans (kept_of_frame Ex rs H m0 m1 (sbz sp bb q ql) HFr _ a Ha Hz) (KEEP a Ha Hz)); sb_win
    | assert (P2 : forall a, apresent H mem a -> apresent H m1 a)
        by (let a := fresh "a" in let Hp := fresh "Hp" in
            intros a Hp; exact (apresent_grows H m0 m1 a HG (HPRES a Hp)));
      clear KEEP HPRES HG; repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end ]
  end.
Local Ltac sb_Ux Ex H :=
  repeat match type of H with
  | context [U Ex (SOff ?i ?c)] =>
      lazymatch goal with Ei : ew ?E0 i = Z_to_bv 64 ?v |- _ =>
        let Xi := fresh "X" in
        assert (Xi : ew Ex i = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; exact Ei);
        rewrite (U_atom_off Ex i v c Xi) in H by lia; clear Xi
      end
  | context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in H by lia
  end.
Local Ltac sb_kill :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) (sv_denot ?Ex _) = _ |- _ =>
    exfalso;
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
    sb_Ux Ex Hc; revert Hc;
    repeat match goal with
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
    end;
    cbn [negb]; intros Hc; first [discriminate Hc | lia]
  end.
Local Ltac sb_inl := repeat first [left; reflexivity | right].
Local Ltac sb_den :=
  cbn [sv_denot ew ewset Nat.eqb];
  first
  [ reflexivity
  | match goal with Ei : ew _ ?i = Z_to_bv 64 _ |- context [ew _ ?i] => rewrite Ei end;
    rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity ].
Local Ltac sb_fld HR nb vb od w v :=
  eapply (field_of_region _ _ nb vb _ _ _ _ _ od w _ v HR);
  [ cbn [ew ewset Nat.eqb]; sb_uval | sb_inl | sb_den | zside | zside ].
Local Ltac sb_ret :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?W) ?msF), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    KEEP : forall a, _ -> ~ sbz _ _ _ ?ql a -> _, HAE : env_agree 32 (Ereg ?regs ?extra) _,
    Hsegs : forall a, in_img _ a -> 0 <= a < kLowMemEnd
    |- SRr _ _ _ (tsb_ch_post ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc _ ?memc ?k _ ?b ?c ?p ?cap ?n ?ov) =>
    let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
    let HR0 := fresh "HR0" in
    pose proof (st_ok_pi_region_nth Ex _ (restrict (w_H W) msF) 0%nat _ HS eq_refl) as HR0;
    cbn [restrict ms_mem] in HR0;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    apply (sb_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b c p cap n ov ql
             (ms_regs msF) (ms_mem msF) _);
    [ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
    | assumption
    | rewrite R1; assumption
    | eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs extra HS);
      [ split;
        [ let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn;
          repeat (rewrite ew_ewset_other by lia); exact (proj1 HAE nn Hnn)
        | cbn [ed ewset]; exact (proj2 HAE) ]
      | vm_compute; reflexivity ]
    | assumption | assumption | assumption | assumption | exact KEEP | assumption
    | rewrite <- (Z.add_0_r b); sb_fld HR0 10%nat b 0 8%N p
    | sb_fld HR0 10%nat b 8 8%N cap
    | first
      [ rewrite (proj2 (Z.ltb_lt (n + 1) cap) ltac:(lia));
        let HR4 := fresh "HR4" in
        pose proof (st_ok_pi_region_nth Ex _ (restrict (w_H W) msF) 4%nat _ HS eq_refl) as HR4;
        cbn [restrict ms_mem] in HR4;
        split; [sb_fld HR0 10%nat b 16 8%N (n + 1) | split; [sb_fld HR0 10%nat b 24 4%N ov |]];
        let j := fresh "j" in let Hj := fresh "Hj" in
        intros j Hj; cbn [length] in Hj; assert (j = 0%nat) by lia; subst j; cbn [nth Z.of_nat];
        split; [sb_fld HR4 37%nat (p + n) 0 1%N c | lia]
      | rewrite (proj2 (Z.ltb_ge (n + 1) cap) ltac:(lia));
        split; [sb_fld HR0 10%nat b 16 8%N n | sb_fld HR0 10%nat b 24 4%N 1] ] ]
  end.
Local Ltac sb_go :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok RUN HS HJ SHOK Bspan; [sb_awr | ];
    sb_keep;
    lazymatch goal with
    | HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => fail "sb_go: the run stopped at a call"
    | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx Bspan SH (start K Bx Bspan SH ss) end in
      lazymatch why with
      | SR_jalr _ => sb_ret
      | SR_branch _ _ _ =>
        psrr_branch_tok RUN BR HS' SHOK' Bspan; [ first [ sb_kill | sb_go ] | first [ sb_kill | sb_go ] ]
      | _ => let pc := eval vm_compute in (ss_pc ss) in fail "sb_go: the run stopped at" pc why
      end
    end
  end.
Theorem pb_sb_ch : tsb_ch_spec.
Proof.
unfold tsb_ch_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b c p cap n ov
  HJc Hra Hra4 Hgp Htp Hal16 Hwlo Hwhi H10 H11 Hc Hb8 Hb0 Hb63 Hbside Hrec Vp Vcap Vn Vov
  Rp Rcap Rn Rn1 Rov HRA HWR HROOM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
destruct (sb_rec_where lyc Sc W memc mdc b HAR Hrec) as (Hb4096 & Hb47 & Hbimg & Hbband).
assert (Hsplo : 2 ^ 46 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
remember (ESB regs p cap n ov) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ESB; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (sb_extra p cap n ov)) i)
  by (intros i Hi; subst E; unfold ESB; apply Eimg_low; exact Hi).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 ov) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (p + n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ub : bv_unsigned (ew E 10) = b) by (rewrite E10; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (sb_extra p cap n ov)) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear EL.
unfold cfg_at, A_sb_ch. change (w64 (BASE + AF_sb_ch)) with (Z_to_bv 64 (BASE + AF_sb_ch)).
destruct (Z.ltb_spec (n + 1) cap) as [Hlt | Hge].
- (* room: n + 1 < cap, the byte p[n] is written *)
  pose proof (HROOM Hlt) as (Hp0 & Hpcap & HDST & HRApn & HWRpn & Hpnb & Hpnsp).
  destruct (sb_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b p cap n ov true
    HJc Hal16 Hwlo Hwhi H10 Hb8 Hbside Hrec Vp Vcap Vn Vov Rp Rcap Rn Rn1 Rov HRA HWR
    (fun _ => conj Hp0 (conj Hpcap (conj Hlt (conj HDST (conj HRApn (conj HWRpn (conj Hpnb Hpnsp))))))))
    as [HS SHOK].
  rewrite <- HE in HS, SHOK. clear HE.
  assert (Upn : bv_unsigned (ew E 37) = p + n) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ sbz (spZ regs) b (p + n) 1 a ->
    aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
  assert (HPRES : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
  assert (HQL : (1 = 0 /\ cap <= n + 1) \/ (1 = 1 /\ n + 1 < cap /\ (p + n + 1 <= IMG_LO \/ IMG_TOP <= p + n))).
  { right. split; [reflexivity|]. split; [exact Hlt|].
    destruct (sb_dst_where lyc Sc W memc mdc (p + n) HAR HDST) as (_ & _ & Hq & _). exact Hq. }
  sb_go.
- (* no room: cap <= n + 1, over is set *)
  destruct (sb_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b p cap n ov false
    HJc Hal16 Hwlo Hwhi H10 Hb8 Hbside Hrec Vp Vcap Vn Vov Rp Rcap Rn Rn1 Rov HRA HWR
    (fun Hf => False_ind _ (diff_false_true Hf))) as [HS SHOK].
  rewrite <- HE in HS, SHOK. clear HE.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ sbz (spZ regs) b (p + n) 0 a ->
    aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
  assert (HPRES : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
  assert (HQL : (0 = 0 /\ cap <= n + 1) \/ (0 = 1 /\ n + 1 < cap /\ (p + n + 1 <= IMG_LO \/ IMG_TOP <= p + n)))
    by (left; split; [reflexivity | exact Hge]).
  sb_go.
Qed.
End walk.
End h.
End f.
End d.
