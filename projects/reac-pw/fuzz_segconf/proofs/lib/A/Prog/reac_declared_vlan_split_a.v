(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 429 of its 479 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A: the entry segment (0x89b8c, the prologue, the four beqz tests,
   the load of the shadow base, the call of the strrchr wrapper at 0x89be8) up to the point K1, and the segment from
   K2 (0x89c60: li a2,10 ; li a1,0 ; jal to the strtol wrapper, NULL end pointer) to K3. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec __intscan_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* strrchr's answer in the model's terms, on a NUL-free text *)
Lemma vs_last_idx_none : forall c l i acc, ~ In c l -> SegModel.last_idx c l i acc = acc.
Proof.
intros c l. induction l as [|b l IH]; intros i acc H; cbn [SegModel.last_idx]; [reflexivity|].
destruct (Z.eqb_spec b c) as [->|Hb]; [exfalso; apply H; left; reflexivity|].
apply IH. intros Hi. apply H. right. exact Hi.
Qed.
Lemma vs_last_idx_at : forall c l i acc j, (j < length l)%nat -> nth j l 0 = c -> ~ In c (skipn (S j) l) ->
  SegModel.last_idx c l i acc = Some (i + j)%nat.
Proof.
intros c l. induction l as [|b l IH]; intros i acc j Hj Hn Hs; cbn [length] in Hj; [lia|].
cbn [SegModel.last_idx]. destruct j as [|j].
- cbn [nth] in Hn. subst b. rewrite Z.eqb_refl. cbn [skipn] in Hs.
  rewrite (vs_last_idx_none c l (S i) (Some i) Hs). f_equal. lia.
- cbn [nth] in Hn. cbn [skipn] in Hs. rewrite (IH (S i) _ j ltac:(lia) Hn Hs). f_equal. lia.
Qed.
Lemma vs_strrchr_none : forall s c, SegModel.nulfree s -> ~ In c s -> SegModel.strrchr s c = None.
Proof. intros s c Hn H. unfold SegModel.strrchr. rewrite (SegModel.cut_nul_id s Hn). apply vs_last_idx_none. exact H. Qed.
Lemma vs_strrchr_some : forall s c j, SegModel.nulfree s -> RtSeg.last_at s c j -> SegModel.strrchr s c = Some j.
Proof.
intros s c j Hn (Hj & Hc & Hs). unfold SegModel.strrchr. rewrite (SegModel.cut_nul_id s Hn).
exact (vs_last_idx_at c s 0 None j Hj Hc Hs).
Qed.
(* the four bytes of a 32-bit cell do not see the bits above 2 ^ 64 *)
Lemma vs_le_byte4_mod : forall v k, YG0f.le_byte (v mod 2 ^ 64) 4 k = YG0f.le_byte v 4 k.
Proof.
intros v k. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
rewrite (Z.mod_eq v (2 ^ 64)) by lia.
replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 32 * (v / 2 ^ 64))) * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
(* a sub-range of a range whose shadow hull is mapped has its shadow hull mapped *)
Lemma vs_hull_sub : forall (rd : reader) x n y m, shadow_hull_vis rd x n -> x <= y -> y + m <= x + n -> 0 < m ->
  shadow_hull_vis rd y m.
Proof.
intros rd x n y m H Hxy Hm Hm0 s Hs. apply H.
assert (A1 : shadow_addr x <= shadow_addr y) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : shadow_addr (y + m - 1) <= shadow_addr (x + n - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A1). pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A2). lia.
Qed.
Lemma vs_amem_sub : forall x n y m, amem_range x n -> x <= y -> y + m <= x + n -> amem_range y m.
Proof. intros x n y m H H1 H2. unfold amem_range in *. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis ERRNO : errno_rom SEGS B.
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis ASTRTOL0 : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strtol) gotw guard.
(* the stack-protector cells the strtol row reads lie below the allocator's ceiling, off the stack window (image A:
   gotw = SegInstA.gotwA 0xa36d8, guard = SegInstA.guardA 0x5ff078) *)
Hypothesis GW : 0 <= gotw /\ gotw + 8 <= alloc_ceiling /\ 0 <= guard /\ guard + 8 <= alloc_ceiling.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* aj_art_at, keeping art_post's presence conjunct *)
Lemma vs_art_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
  (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
  getr regsT 1 = raw ->
  (forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
  SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
   aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
    rdW W mem2 a = rdW W memT a) /\
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using TL.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
eapply SRr_mono.
- apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
    mdc k o raw (fun regs2 mem2 => Qr regs2 mem2 /\ (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))
    HJ Hsp Hal Hneg Hstk Hbud Hraw HEb).
  eapply SRr_mono; [exact HC|].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
  split; [exact (conj HQ Hpres2)|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hscr].
- cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQ & HPr) & HK2).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HQ|]. split; [exact HK2 | exact HPr].
Qed.

(* where an object of sa_loc lies: at or above 4096, below the allocator's ceiling, off the errno cell *)
Lemma vs_seg_place : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling /\ (forall x, q <= x < q + n -> ~ (as_errno B <= x < as_errno B + 4)).
Proof using TL.
intros ly S W mem md q n HAR HL Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as (_ & HEI & _).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2].
  split; [lia|]. split; [lia|]. intros x Hx Hx'.
  exact (blk_img SEGS B LAWS ly S W mem md b m x HAR Hin ltac:(lia) (HEI x Hx')).
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2).
  split; [lia|]. split; [lia|]. intros x Hx Hx'.
  exact (frm_img SEGS B LAWS ly S W mem md cid pos x HAR Hin ltac:(lia) (HEI x Hx')).
- destruct (HI q ltac:(lia)) as (Hq & _ & _). destruct (HI (q + n - 1) ltac:(lia)) as (Hq' & _ & _).
  pose proof (pa_img_range q Hq). pose proof (pa_img_range _ Hq').
  split; [lia|]. split; [unfold kImgEnd in *; lia|]. intros x Hx. exact (proj2 (proj2 (HI x Hx))).
Qed.

(* the segment's tail from byte j on, at a state kept from the entry outside the stack window: the premises the
   string rows ask of it *)
Lemma vs_seg_at : forall e (mem' : word -> option byte) (regs' : bvmap 5 word) stk j,
  vs_entry B gotw guard e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_sp e - STK_reac_declared_vlan_split <= a < e_sp e) -> rdW (e_W e) mem' a = rdW (e_W e) (e_mem e) a) ->
  e_sp e - STK_reac_declared_vlan_split <= spZ regs' - stk -> (j <= length (e_s e))%nat ->
  astr_at SEGS (e_W e) mem' (e_seg e + Z.of_nat j) (seg_spec.zb (skipn j (e_s e))) /\
  aread_ok SEGS stk (e_W e) regs' mem' (e_seg e + Z.of_nat j) (astr_len (seg_spec.zb (skipn j (e_s e))) + 1) /\
  amem_range (e_seg e + Z.of_nat j) (astr_len (seg_spec.zb (skipn j (e_s e))) + 8) /\
  atail_vis SEGS (e_W e) mem' (e_seg e + Z.of_nat j + astr_len (seg_spec.zb (skipn j (e_s e)))) /\
  astr_len (seg_spec.zb (skipn j (e_s e))) = Z.of_nat (length (e_s e)) - Z.of_nat j.
Proof using TL.
intros e mem' regs' stk j HE HK Hw Hj.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (_ & HCm). unfold ASAN_CEIL in HCm.
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & _).
destruct (vs_seg_place _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as (P0 & P1 & _).
destruct Hsadd as (A0 & A1 & A2 & A3 & A4).
destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (HB & HNZ & HZS).
unfold e_sp in *.
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Ez : seg_spec.zb (skipn j (e_s e)) = skipn j (seg_spec.zb (e_s e))) by (unfold seg_spec.zb; rewrite skipn_map; reflexivity).
assert (Hlz : astr_len (seg_spec.zb (skipn j (e_s e))) = Z.of_nat (length (e_s e)) - Z.of_nat j).
{ unfold astr_len, seg_spec.zb. rewrite length_map, length_skipn. lia. }
assert (HKo : kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) mem') (spZ (e_regs e) - STK_reac_declared_vlan_split) (spZ (e_regs e))) by exact HK.
assert (HS0 : astr_atR (rdW (e_W e) (e_mem e)) (e_seg e) (seg_spec.zb (e_s e))) by exact (conj HB HNZ).
pose proof (astr_atR_skipn _ _ _ j HS0 ltac:(unfold seg_spec.zb; rewrite length_map; exact Hj)) as HSj.
rewrite <- Ez in HSj.
set (x := e_seg e + Z.of_nat j) in *.
set (t := seg_spec.zb (skipn j (e_s e))) in *.
assert (Hx : x + astr_len t + 1 <= alloc_ceiling) by (unfold x; rewrite Hlz; lia).
split.
{ apply astr_atR_view. apply (astr_atR_kept _ _ _ _ _ _ HKo HSj); [unfold x; lia | unfold astr_len in Hx; lia | lia]. }
split.
{ split; [unfold x; lia|]. split; [lia|]. split; [unfold astr_len in *; lia|]. split.
  - intros a Ha. split; [|unfold ascratch_stk; lia].
    rewrite (HK a) by lia. destruct HSj as [HSb _].
    replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite HSb; [discriminate|].
    rewrite length_app. unfold astr_len in Ha. cbn [length]. lia.
  - split; [apply (vs_amem_sub _ _ _ _ A2); [unfold x; lia | rewrite Hlz; unfold x; lia]|]. split.
    + apply (range_addressable_kept_win _ _ (spZ (e_regs e) - STK_reac_declared_vlan_split) (spZ (e_regs e)) x (astr_len t + 1) HK); [lia | unfold x; lia | unfold amem_range in A2; lia |].
      apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact A3 | unfold x; lia | rewrite Hlz; unfold x; lia].
    + intros Hn. apply (shadow_hull_vis_kept_win _ _ (spZ (e_regs e) - STK_reac_declared_vlan_split) (spZ (e_regs e)) x (astr_len t + 1) HK);
        [lia | unfold x; lia | unfold amem_range in A2; lia | lia |].
      apply (vs_hull_sub _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact (A4 ltac:(lia)) | unfold x; lia | rewrite Hlz; unfold x; lia | lia]. }
split; [apply (vs_amem_sub _ _ _ _ Hamr); [unfold x; lia | rewrite Hlz; unfold x; lia]|].
split; [|exact Hlz].
intros a Ha. replace (x + astr_len t) with (e_seg e + Z.of_nat (length (e_s e))) in Ha by (rewrite Hlz; unfold x; lia).
assert (Htb : e_seg e + Z.of_nat (length (e_s e)) - (e_seg e + Z.of_nat (length (e_s e))) mod 8 + 8 <= alloc_ceiling)
  by (apply PaArt.tail_below; [lia | exact HCm]).
rewrite (HK a) by lia. exact (proj2 Hstr a Ha).
Qed.

(* the read-only words the rows read, at such a state *)
Lemma vs_rom_at : forall e (mem' : word -> option byte),
  vs_entry B gotw guard e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_sp e - STK_reac_declared_vlan_split <= a < e_sp e) -> rdW (e_W e) mem' a = rdW (e_W e) (e_mem e) a) ->
  rt_rom_view SEGS B (e_W e) mem'.
Proof using.
intros e mem' HE HK a Hr Ho Hne.
pose proof HE as (HPRE & HROD & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hr as (sg & Hsg & Hw & Hra').
pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hra'))) as Hia.
unfold e_sp in HK. rewrite (HK a) by (unfold kImgEnd in Hia; assert (STK_reac_declared_vlan_split = 12352) by reflexivity; lia).
exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hra')))) Ho Hne).
Qed.

(* a word the frame region of a symbolic state holds, read back *)
Lemma vs_rd_chunk : forall E (H : word -> bool) mem r off n b,
  region_ok SEGS E (mrestrict H mem) r -> In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
  base_val E (YP09.r_base r) = b -> rdword (aview SEGS H mem) (b + off) = Some (bv_unsigned (ew E n)).
Proof using.
intros E H mem r off n b HR Hin Hb.
pose proof (region_ok_chunk SEGS E _ r _ HR Hin) as Hc. rewrite Hb in Hc.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Rn. change (bv_modulus 64) with (2 ^ 64) in Rn.
apply rdword_of_val_mem; [|exact Rn].
apply (val_of_chunk_ok SEGS E _ b off 8 (SOff n 0) (bv_unsigned (ew E n)) Hc); [| exact Rn | lia].
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* a register of a symbolic state after a run, as its term *)
Ltac vsa_reg HS :=
  rewrite (st_ok_restrict_reg _ _ _ _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- context [sr_get ?a ?rr] =>
    let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
  cbn [sv_denot].
Ltac vsa_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.

Lemma vs_entry_walk : vs_K1_stmt B gotw guard -> forall e, vs_entry B gotw guard e ->
  vs_goal B e (e_W e) (vs_cfg AF_reac_declared_vlan_split (e_regs e) (e_mem e) (e_md e)).
Proof using TL ASTRRCHR.
clear GW ERRNO ASTRTOL0.
intros HK1 e HE.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (vs_seg_place _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as (P0 & P1 & _).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & _).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 2 HAR Hstk ltac:(lia) Hvdst) as (Vlo & Vhi & _).
pose proof (vs_seed B LAWS TL (e_W e) (e_regs e) (e_mem e) (e_ly e) (e_S e) (e_md e) (e_ch e) (e_seg e) (e_parent e) (e_vid e)
  HPRE H10 ltac:(lia) H11 ltac:(lia) H12 H13 ltac:(lia) Hv2) as HS.
pose proof (ajournal_init SEGS B STK_reac_declared_vlan_split (e_FP e) (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) HPRE) as HJ.
set (E := Eimg (Ereg (e_regs e) vs_extra0)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (e_regs e) r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ (e_regs e)) by (rewrite (EV 2%nat 2%bv eq_refl); reflexivity).
unfold vs_goal, vs_cfg.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (Hsp1 : spZ (ms_regs ms) = spZ (e_regs e) + -64).
{ unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3, (EV 3%nat 3%bv eq_refl); exact Hgp).
assert (R4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4, (EV 4%nat 4%bv eq_refl); exact Htp).
(* the run wrote only its frame *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - 64 <= a < spZ (e_regs e)) ->
  rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hna. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ (e_regs e) - 64 <= a < spZ (e_regs e)) HFr);
    [|exact Ha|exact Hna].
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
  destruct Hin. }
assert (KEEPW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_sp e - STK_reac_declared_vlan_split <= a < e_sp e) ->
  rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (e_mem e) a)
  by (intros a Ha Hna; apply KEEP1; [exact Ha | unfold e_sp in Hna; lia]).
destruct (vs_seg_at e (ms_mem ms) (ms_regs ms) (2 * ESTACK) 0 HE KEEPW1 ltac:(unfold e_sp; lia) ltac:(lia))
  as (Hstr1 & Hrd1 & Ham1 & Htv1 & Hl1).
change (skipn 0 (e_s e)) with (e_s e) in Hstr1, Hrd1, Ham1, Htv1, Hl1.
change (Z.of_nat 0) with 0 in Hstr1, Hrd1, Ham1, Htv1, Hl1.
rewrite Z.add_0_r in Hstr1, Hrd1, Ham1, Htv1.
(* the saved words of the frame *)
assert (SL1 : vs_slots (rdW (e_W e) (ms_mem ms)) (e_sp e) (e_regs e)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) vs_slots_r) in
    pose proof (st_ok_region_nth E ss _ 0 r HS ltac:(vm_compute; reflexivity)) as R0 end.
  cbn [ms_mem restrict] in R0.
  intros i r Hr. unfold e_sp.
  do 8 (destruct i as [|i]; [cbn [nth_error vs_saved] in Hr; injection Hr as <-;
    lazymatch goal with |- rdword _ (?sp - 8 - 8 * Z.of_nat ?k) = Some (bv_unsigned (getr _ ?rr)) =>
      let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
      let off := eval vm_compute in (-8 - 8 * Z.of_nat k) in
      replace (sp - 8 - 8 * Z.of_nat k) with (bv_unsigned (ew E 2) + off) by (rewrite Usp; lia);
      rewrite <- (EV n rr eq_refl);
      apply (vs_rd_chunk E _ _ _ off n _ R0); [cbn [In YP09.r_chunks]; repeat (first [left; reflexivity | right]) | reflexivity]
    end |]).
  destruct i; cbn in Hr; discriminate. }
eapply SRr_bind.
{ eapply (vs_art_at (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strrchr)
    (e_W e) (ms_regs ms) (ms_mem ms) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) _ 0 (-64) (getr (ms_regs ms) 1) _ HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HVS; lia)
    eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRRCHR fx (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) _ (e_seg e) 46 (seg_spec.zb (e_s e))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
      [] (e_ly e) (e_S e) (e_W e) (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ Hsp1 eq_refl ltac:(lia)
      ltac:(rewrite Hes; lia) ltac:(rewrite Hes, HVS; lia) HraT R3' R4').
  - rewrite R10, (EV 10%nat 10%bv eq_refl). exact H10.
  - rewrite R11. reflexivity.
  - lia.
  - lia.
  - exact Hstr1.
  - exact Hrd1.
  - exact Ham1.
  - exact Htv1.
  - exact (vs_rom_at e (ms_mem ms) HE KEEPW1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hq & HK2 & HPr2).
rewrite R1.
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. specialize (HP2 (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in HP2. exact HP2. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_sp e - STK_reac_declared_vlan_split <= a < e_sp e) ->
  rdW (e_W e) mem2 a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hna. unfold e_sp in Hna. rewrite (HK2 a Ha) by (try tauto; rewrite Hes; lia). apply KEEPW1; [exact Ha | unfold e_sp; exact Hna]. }
assert (HC0 : vs_ctx0 B e regs2 mem2 md2).
{ unfold vs_ctx0, vs_ctxW. split; [exact HJ2|]. split.
  - unfold vs_regs. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + unfold e_sp. unfold spZ at 1. rewrite (P2 2%bv) by vsa_cs.
      change (bv_unsigned (getr (ms_regs ms) 2)) with (spZ (ms_regs ms)). rewrite Hsp1. lia.
    + rewrite (P2 3%bv) by vsa_cs. rewrite R3. apply EV. reflexivity.
    + rewrite (P2 4%bv) by vsa_cs. rewrite R4. apply EV. reflexivity.
    + rewrite (P2 8%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 13%nat 13%bv eq_refl). exact H13.
    + rewrite (P2 9%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 11%nat 11%bv eq_refl). exact H11.
    + rewrite (P2 18%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 10%nat 10%bv eq_refl). exact H10.
    + rewrite (P2 19%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 12%nat 12%bv eq_refl). exact H12.
    + rewrite (P2 22%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. subst E. exact (vs_E32 (e_regs e) SB).
    + intros r Hr. rewrite (HP2 r) by (unfold acallee_saved; lia).
      assert (Hc : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [-> | Hc]); try subst r;
      vsa_reg HS; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EV; reflexivity.
  - split; [apply (vs_slots_kept (rdW (e_W e) (ms_mem ms))); [exact SL1|]; intros a Ha; unfold e_sp in Ha;
      apply HK2; [lia | rewrite Hes; lia | tauto]|].
    split; [intros a Ha Hw _; exact (KEEP2 a Ha Hw)|].
    intros a Ha. apply HPr2. exact (apresent_grows _ _ _ a HG Ha). }
destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (_ & _ & HZS).
assert (HZ2 : map (fun b : byte => bv_unsigned b) (seg_spec.zb (e_s e)) = e_s e) by exact HZS.
assert (Hnf : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
rewrite HZ2 in Hq.
destruct Hq as [(Ha0 & Hn46) | (j & Hj & Ha0)].
- apply (HK1 e regs2 mem2 md2 0 HE HC0 Ha0). left. split; [reflexivity | exact (vs_strrchr_none _ _ Hnf Hn46)].
- apply (HK1 e regs2 mem2 md2 (e_seg e + Z.of_nat j) HE HC0 Ha0). right. exists j.
  split; [exact (vs_strrchr_some _ _ _ Hnf Hj) | reflexivity].
Qed.

(* K2, 0x89c60: li a2,10 ; li a1,0 ; jal to the strtol wrapper with a0 = dot + 1, the tail; it comes back at K3 with
   a0 = strtol10 of the tail and the errno cell as it was *)
Lemma vs_K2 : vs_K3_stmt B gotw guard -> vs_K2_stmt B gotw guard.
Proof using TL ERRNO ASTRTOL0 GW.
clear ASTRRCHR.
intros HK3. unfold vs_K2_stmt. intros e regs' mem' md' di HE HC Hdi Hdi0 Hne Hdig R10 R20.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
pose proof HC as (HJ & HR & HSL & HK & HPr).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof (pal_env B TL) as ((Er0 & Er1) & _).
pose proof GW as (GW0 & GW1 & GW2 & GW3).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold e_sp in *.
destruct (vs_seg_place _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as (P0 & P1 & PE).
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (reac_declared_vlan_split_lem.vs_di_lt _ _ Hnul Hdi) as Hdil.
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K2 [])
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K2)) mem' (seg_rom SEGS)))).
{ apply vs_seedK; [replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL | lia | | exact G22 | exact I].
  rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
assert (Usp : bv_unsigned (ew E 2) = spZ (e_regs e) - 64) by (rewrite (EV 2%nat 2%bv eq_refl); exact Hsp).
unfold vs_goal, vs_cfg.
paj_run_shc RUNP RUNC HS HJ.
{ vs_awr_ro. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Hsp1 : spZ (ms_regs ms) = spZ (e_regs e) + -64) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EV 3%nat 3%bv eq_refl), G3; exact Hgp).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EV 4%nat 4%bv eq_refl), G4; exact Htp).
(* the run wrote nothing *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) (ms_mem ms) a = rdW (e_W e) mem' a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin. }
assert (KEEPW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - STK_reac_declared_vlan_split <= a < spZ (e_regs e)) ->
  rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (e_mem e) a)
  by (intros a Ha Hna; rewrite (KEEP1 a Ha); exact (HK a Ha Hna (fun x => x))).
destruct (vs_seg_at e (ms_mem ms) (ms_regs ms) (3 * ESTACK) (S di) HE KEEPW1 ltac:(unfold e_sp; lia) ltac:(lia))
  as (Hstr1 & Hrd1 & Ham1 & Htv1 & Hl1).
change (skipn (S di) (e_s e)) with (vs_tail e di) in Hstr1, Hrd1, Ham1, Htv1, Hl1.
replace (e_seg e + Z.of_nat (S di)) with (e_seg e + Z.of_nat di + 1) in Hstr1, Hrd1, Ham1, Htv1 by lia.
set (str := seg_spec.zb (vs_tail e di)) in *.
destruct (AR_errno_present SEGS B (e_W e) (ms_mem ms) ERRNO) as (ev & Hev).
eapply SRr_bind.
{ eapply (vs_art_at (3 * ESTACK) (aerrno_cell B) (SIG SS___interceptor_trampoline_strtol)
    (e_W e) (ms_regs ms) (ms_mem ms) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) _ 0 (-64) (getr (ms_regs ms) 1) _ HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HVS; lia)
    eq_refl (fun a (H : aerrno_cell B a) => H)).
  apply (ASTRTOL0 fx (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) _ (e_seg e + Z.of_nat di + 1) str ev).
  - eapply aguard_ok_kept; [exact KEEPW1 | exact Hssp | lia | lia | lia | lia | lia].
  - exact (ecall_pre_stk_at SEGS B (3 * ESTACK) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
      [] (e_ly e) (e_S e) (e_W e) (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ Hsp1 eq_refl ltac:(lia)
      ltac:(rewrite Hes; lia) ltac:(rewrite Hes, HVS; lia) HraT Q3' Q4').
  - rewrite Q10, (EV 10%nat 10%bv eq_refl). exact R10.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - lia.
  - exact Hstr1.
  - rewrite Hl1. lia.
  - exact Hrd1.
  - exact Ham1.
  - exact Htv1.
  - rewrite Hl1. destruct (Z_lt_le_dec (as_errno B) (e_seg e + Z.of_nat di + 1)) as [Hlt|Hge].
    + left. destruct (Z_le_gt_dec (as_errno B + 4) (e_seg e + Z.of_nat di + 1)) as [Hok|Hbad]; [exact Hok|].
      exfalso. apply (PE (e_seg e + Z.of_nat di + 1)); lia.
    + right. destruct (Z_le_gt_dec (e_seg e + Z.of_nat di + 1 + (Z.of_nat (length (e_s e)) - Z.of_nat (S di)) + 1) (as_errno B))
        as [Hok|Hbad]; [exact Hok|].
      exfalso. apply (PE (as_errno B)); lia.
  - exact Hev.
  - exact (vs_rom_at e (ms_mem ms) HE KEEPW1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Hv & Herr) & HK2 & HPr2).
rewrite Q1.
(* the bridge from the row's answer to the model *)
destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (_ & _ & HZS).
assert (HZt : seg_spec.zs str = vs_tail e di).
{ subst str. unfold vs_tail. unfold seg_spec.zs, seg_spec.zb in *. rewrite <- !skipn_map, HZS. reflexivity. }
assert (Hstr0 : str <> []) by (subst str; unfold seg_spec.zb; destruct (vs_tail e di); [contradiction | discriminate]).
assert (Hdig' : forallb SegModel.isdigit (seg_spec.zs str) = true) by (rewrite HZt; exact Hdig).
assert (Hlen' : (length str <= 18)%nat).
{ subst str. unfold seg_spec.zb, vs_tail. rewrite length_map, length_skipn. lia. }
rewrite (SegBridge.bridge_strtol10_str str Hstr0 Hdig' Hlen'), HZt in Hv.
rewrite (SegBridge.bridge_strtol10_errno str (Z_to_bv 64 ev) Hstr0 Hdig' Hlen') in Herr.
rewrite Z_to_bv_unsigned in Herr. unfold bv_wrap in Herr. change (bv_modulus 64) with (2 ^ 64) in Herr.
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. specialize (HP2 (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in HP2. exact HP2. }
(* the call kept every byte outside its window, the errno cell's at its value *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - STK_reac_declared_vlan_split <= a < spZ (e_regs e)) ->
  rdW (e_W e) mem2 a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hna.
  destruct (Z_lt_le_dec a (as_errno B)) as [Hl|Hl]; [|destruct (Z_lt_le_dec a (as_errno B + 4)) as [Hh|Hh]].
  - rewrite (HK2 a Ha) by (try (unfold aerrno_cell; lia); rewrite Hes; lia). apply KEEPW1; [exact Ha | exact Hna].
  - replace a with (as_errno B + Z.of_nat (Z.to_nat (a - as_errno B))) by lia.
    assert (Hk : (Z.to_nat (a - as_errno B) < 4)%nat) by lia.
    rewrite (Herr _ Hk), vs_le_byte4_mod, <- (Hev _ Hk).
    apply KEEPW1; lia.
  - rewrite (HK2 a Ha) by (try (unfold aerrno_cell; lia); rewrite Hes; lia). apply KEEPW1; [exact Ha | exact Hna]. }
assert (HC2 : vs_ctx0 B e regs2 mem2 md2).
{ unfold vs_ctx0, vs_ctxW. split; [exact HJ2|]. split.
  - unfold vs_regs. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + unfold e_sp. unfold spZ at 1. rewrite (P2 2%bv) by vsa_cs.
      change (bv_unsigned (getr (ms_regs ms) 2)) with (spZ (ms_regs ms)). rewrite Hsp1. lia.
    + rewrite (P2 3%bv) by vsa_cs. rewrite Q3, (EV 3%nat 3%bv eq_refl). exact G3.
    + rewrite (P2 4%bv) by vsa_cs. rewrite Q4, (EV 4%nat 4%bv eq_refl). exact G4.
    + rewrite (P2 8%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 8%nat 8%bv eq_refl). exact G8.
    + rewrite (P2 9%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 9%nat 9%bv eq_refl). exact G9.
    + rewrite (P2 18%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 18%nat 18%bv eq_refl). exact G18.
    + rewrite (P2 19%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 19%nat 19%bv eq_refl). exact G19.
    + rewrite (P2 22%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 22%nat 22%bv eq_refl). exact G22.
    + intros r Hr. rewrite (HP2 r) by (unfold acallee_saved; lia).
      assert (Hc : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [-> | Hc]); try subst r;
      vsa_reg HS; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      lazymatch goal with |- ew _ ?k = getr _ ?rr => rewrite (EV k rr eq_refl) end; apply G27; lia.
  - split.
    { apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha. unfold e_sp in Ha.
      rewrite (HK2 a ltac:(lia)) by (try (unfold aerrno_cell; lia); rewrite Hes; lia). apply KEEP1. lia. }
    split; [intros a Ha Hw _; exact (KEEP2 a Ha Hw)|].
    intros a Ha. apply HPr2. apply (apresent_grows _ _ _ a HG). apply HPr. exact Ha. }
apply (HK3 e regs2 mem2 md2 di HE HC2 Hdi Hdi0 Hne Hdig).
- exact Hv.
- rewrite (P2 20%bv) by vsa_cs. vsa_reg HS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 20%nat 20%bv eq_refl). exact R20.
Qed.

End e.
End f.
End d.
