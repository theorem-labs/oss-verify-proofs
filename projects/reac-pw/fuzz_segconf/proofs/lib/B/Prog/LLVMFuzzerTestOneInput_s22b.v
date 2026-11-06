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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 513 of its 557 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece b (p2) of
   segment S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
   the statement s22_p2_stmt of LLVMFuzzerTestOneInput_s22k.v, from the return of the strrchr
   wrapper (S22_VR, 0x85ba4) to the continue join (S22_JOIN, 0x85b58) or the head of the digit loop (S22_VD,
   0x85be8).

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new)

   THE FORM: plugin-hostd/fuzz_command's harness walk (origin/ossv/recipes 3abc3740de97): a seed symbolic state at
   the point, one paj_run_tok / paj_run_to_tok per straight stretch, psrr_branch_tok at each branch the facts do not
   decide, the instrumented check as an obligation closed from the block (obl_of_block), and the next point's
   premises from the run's registers (prreg) and the run's frame (no write window: every byte is kept).
   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s:891-907, 927-928; SegList.v slots 889-905, 925-926):
   - 0x85ba4 beqz a0 -> 0x85c34: strrchr found no '.': ld a6,200(s1) (the shadow base), j 0x85b58 -> JOIN
     (SegModel.m_split = None by s22_split_none_nodot).
   - 0x85ba8 .. 0x85bb8: a6 := 200(s1), a5 := -1, a7 := -10, t0 := 10, t1 := 136(s1) = 4094 (the a0 = 0 test is
     decided by the fact 4096 <= DOT).
   - 0x85bbc beq a0,s3 -> JOIN: the '.' is the name's first byte (j = 0, s22_split_none_dot0).
   - 0x85bc0 beq a0,a5 -> the trap: decided in the run by the fact DOT <= 0x7fffff800000 < 2 ^ 64 - 1.
   - 0x85bc4 .. 0x85bd4: check 31 (the 1-byte load at DOT + 1; the slow block 0x85e3c is never entered): its
     obligation, DOT + 1 is in m's block (M + 256 i + j + 1 < M + 9236).
   - 0x85bd8 lbu a3,0(a1): dot[1], the byte after the '.', which is the name's byte j + 1 or its NUL.
   - 0x85bdc beqz a3 -> JOIN: dot[1] = 0 (s22_split_none_empty: hd0 (skipn (S j) name) = dot[1]).
   - 0x85be0 .. 0x85be4: s5 := 0, a2 := DOT + 2 -> VD with t = 0, v = 0.
   No byte is stored: the run's regions have no write window, so the memory is kept and s22_inv carries
   (s22b_inv_kept).
   Section hypotheses: none (LAWS is YG0q.AR_laws_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaSB SegGlob PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the symbolic states at 0x85ba4 ----
   Every register is its own atom. Extra atoms: 32 = the shadow base (the word at 200(s1)), 33 = dot[1] (the byte at
   DOT + 1). Regions: the two s1 slots the stretch reads (136: 4094, 200: the shadow base), read only; and, when
   strrchr found a '.', the byte at DOT + 1 (atom 10 = a0 = DOT), read only. NULL state: a0 is the literal 0. *)
Definition p2_s1r : YP09.region := YP09.mkRegion (Some 9%nat) 136 208 136 136
  [YP09.mkChunk 136 (CVal 8 (SLit 4094)); YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition p2_nmr : YP09.region := YP09.mkRegion (Some 10%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition p2_factsN : facts := mkFacts [(32%nat, mkAF SB SB 0)] [] [].
Definition p2_factsF : facts :=
  mkFacts [(10%nat, mkAF 4096 0x7fffff800000 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_N : sstate := mkSS S22_VR (sr_set sr_atoms (10%bv : bv 5) (SLit 0)) [p2_s1r] None p2_factsN.
Definition ss_F : sstate := mkSS S22_VR sr_atoms [p2_s1r; p2_nmr] None p2_factsF.
(* the shadow base a6 (atom 32, reloaded from 200(s1)) and the band of shadow addresses *)
Definition p2x : sv := SOff 32 0.
Definition p2span : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- list facts ---- *)
(* the byte after index n - 1 of a C string: its n-th byte, or its NUL *)
Lemma p2_hd0_skipn : forall (l : list Z) n, SegModel.hd0 (skipn n l) = nth n (l ++ [0]) 0.
Proof.
intros l. induction l as [|a l IH]; intros n.
- destruct n as [|[|n]]; reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [skipn app nth]. exact (IH n).
Qed.

Ltac p2_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ================= readers that agree everywhere carry every fact the cut points state ================= *)
Lemma s22b_word : forall (rd rd' : reader) a, (forall x, rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a HK. unfold rdword. rewrite !HK. reflexivity. Qed.
Lemma s22b_zs : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK. exact (H i Hi). Qed.
Lemma s22b_bytes : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK. exact (H i Hi). Qed.
Lemma s22b_val : forall (rd rd' : reader) a n v, (forall x, rd' x = rd x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite HK. exact (H k Hk). Qed.
Lemma s22b_str : forall (rd rd' : reader) a s, (forall x, rd' x = rd x) -> sa_str rd a s -> sa_str rd' a s.
Proof.
intros rd rd' a s HK ((Hz & Hn) & Ht). split; [split; [exact (s22b_zs rd rd' a _ HK Hz) | exact Hn]|].
intros y Hy. rewrite HK. exact (Ht y Hy).
Qed.
Lemma s22b_lit : forall segs B (rd rd' : reader) a s, (forall x, rd' x = rd x) ->
  sa_lit segs B rd a s -> sa_lit segs B rd' a s.
Proof.
intros segs B rd rd' a s HK (H0 & Hs & Hp & Hr & Hi). split; [exact H0|].
split; [exact (s22b_str rd rd' a s HK Hs)|]. exact (conj Hp (conj Hr Hi)).
Qed.
Lemma s22b_ra : forall (rd rd' : reader) b a n, (forall x, rd' x = rd x) ->
  range_addressable rd b a n -> range_addressable rd' b a n.
Proof. intros rd rd' b a n HK H y Hy. rewrite HK. exact (H y Hy). Qed.
Lemma s22b_addr : forall (rd rd' : reader) q n, (forall x, rd' x = rd x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (s22b_ra rd rd' _ q n HK H4)|]. intros Hn s Hs. rewrite HK. exact (H5 Hn s Hs).
Qed.
Lemma s22b_himg : forall B (rd rd' : reader) L M C Wd R G Gd lf lr, (forall x, rd' x = rd x) ->
  seg_himg SEGS B L M C Wd R G Gd lf lr rd -> seg_himg SEGS B L M C Wd R G Gd lf lr rd'.
Proof.
intros B rd rd' L M C Wd R G Gd lf lr HK
  (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [exact (s22b_val rd rd' _ _ _ HK Hm40)|]. split; [exact Hm40i|].
split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (s22b_lit _ _ rd rd' _ _ HK H1) H2)|].
split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (s22b_lit _ _ rd rd' _ _ HK H1) H2)|].
split.
{ destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
  intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp.
  split; [rewrite (s22b_word rd rd' _ HK); exact Htp | exact (s22b_lit _ _ rd rd' _ _ HK Hl)]. }
split; [exact Hcata|].
split.
{ destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
  intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp.
  split; [rewrite (s22b_word rd rd' _ HK); exact Hwp' | exact (s22b_lit _ _ rd rd' _ _ HK Hl)]. }
split.
{ destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
  intros i Hi. exact (s22b_val rd rd' _ _ _ HK (Hrs i Hi)). }
split.
{ destruct Hssp as [Hg1 (g & Hg2)]. split; [rewrite (s22b_word rd rd' _ HK); exact Hg1|].
  exists g. rewrite (s22b_word rd rd' _ HK). exact Hg2. }
exact (conj Hpin (conj Hrt (conj Hli (conj Hd1 (conj Hd2 Hd3))))).
Qed.
Lemma s22b_slots : forall cx (rd rd' : reader) L, (forall x, rd' x = rd x) -> lt_slots cx rd L -> lt_slots cx rd' L.
Proof. intros cx rd rd' L HK H o v Hin. rewrite (s22b_word rd rd' _ HK). exact (H o v Hin). Qed.
Lemma s22b_cm : forall (rd rd' : reader) c m st, (forall x, rd' x = rd x) -> lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st HK. unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp.
intros ((bs & Hb & He) & (bs' & Hb' & He')).
split; [exists bs; exact (conj (s22b_bytes rd rd' _ _ HK Hb) He) | exists bs'; exact (conj (s22b_bytes rd rd' _ _ HK Hb') He')].
Qed.
Lemma s22b_tabs : forall cx (rd rd' : reader) tab mt t, (forall x, rd' x = rd x) ->
  lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t HK. unfold lt_tabs, sa_rtab, sa_mtab, sa_guardtab.
intros (H1 & (bs & Hb & He) & Hg & Hv & (bs' & Hb' & He') & H6).
split; [exact H1|]. split; [exists bs; exact (conj (s22b_bytes rd rd' _ _ HK Hb) He)|].
split; [exact (s22b_bytes rd rd' _ _ HK Hg)|]. split; [exact (s22b_val rd rd' _ _ _ HK Hv)|].
split; [exists bs'; exact (conj (s22b_bytes rd rd' _ _ HK Hb') He') | exact H6].
Qed.

(* a run whose regions have no write window keeps every byte *)
Lemma s22b_nowin_kept : forall E rs (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, rdW W m' a = rdW W m a.
Proof.
intros E rs W m m' HF Hw a. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). rewrite forallb_forall in Hw. specialize (Hw r Hin). apply Z.leb_le in Hw. lia.
Qed.

(* ================= the seeds ================= *)
Definition p2_E (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).
Lemma p2_E_reg : forall regs xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p2_E regs xs) n = getr regs r.
Proof.
intros regs xs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold p2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma p2_E_extra : forall regs xs j, (32 + j < A_TEXT)%nat ->
  ew (p2_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j Hj2. unfold p2_E. rewrite Eimg_low by exact Hj2.
rewrite ew_Ereg_extra. apply map_nth.
Qed.
Lemma p2_denot_of_U : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. apply bv_eq. rewrite unsigned_lit_small by lia. exact H. Qed.
Lemma p2_rd_byte : forall (W : world SEGS) mem a v, rdW W mem a = Some v -> 0 <= v < 256.
Proof.
intros W mem a v H. unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [bb|]; [|discriminate H].
cbn [option_map] in H. injection H as <-. pose proof (bv_unsigned_in_range 8 bb) as R.
change (bv_modulus 8) with 256 in R. lia.
Qed.
Lemma p2_chunk8 : forall (W : world SEGS) mem E base off e v,
  rdword (rdW W mem) (base + off) = Some v -> 0 <= v < 2 ^ 64 -> U E e = v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros W mem E base off e v Hw Hv HU.
apply (chunk_ok_val SEGS E _ base off 8 e v); [exact (p2_denot_of_U E e v HU Hv) | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS (w_H W) mem _ v Hw).
Qed.
Lemma p2_chunk1 : forall (W : world SEGS) mem E base off (n : nat) b,
  ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> rdW W mem (base + off) = Some b ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W mem E base off n b En Hb Hrd i Hi.
assert (Hi0 : i = 0) by (cbn in Hi; lia). subst i.
cbn [YP09.c_val YP09.c_off]. rewrite Z.add_0_r.
unfold aview in Hrd. destruct (mbyte SEGS (mrestrict (w_H W) mem) (base + off)) as [bb|] eqn:Eb; [|discriminate Hrd].
cbn [option_map] in Hrd. injection Hrd as Hrd.
exists bb. split; [|first [exact Eb | reflexivity]].
cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. apply bv_eq.
assert (HU : U E (SOff n 0) = b) by (apply U_atom; [exact En | lia]).
rewrite (p2_denot_of_U E (SOff n 0) b HU ltac:(lia)), unsigned_lit_small by lia.
rewrite Z_to_bv_unsigned. try change (8 * 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. try change (bv_modulus 8) with 256. rewrite Z.mod_small by (cbn; lia). symmetry. exact Hrd.
Qed.
Lemma p2_s1r_ok : forall (W : world SEGS) mem E s1,
  bv_unsigned (ew E 9) = s1 -> 0 <= s1 -> s1 + 208 <= 2 ^ 64 -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 136) = Some 4094 -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) p2_s1r.
Proof.
intros W mem E s1 U9 Hs0 Hs1 E32 H136 H200. unfold YP09.region_ok, p2_s1r.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (p2_chunk8 W mem E s1 136 (SLit 4094) 4094 H136); [lia | apply U_lit; lia].
- apply (p2_chunk8 W mem E s1 200 (SOff 32 0) SHADOW_OFF H200); [unfold SHADOW_OFF; lia|].
  apply U_atom; [exact E32 | unfold SHADOW_OFF; lia].
Qed.

(* the state at 0x85ba4 when strrchr returned NULL *)
Lemma p2_seedN : forall (W : world SEGS) (regs : bvmap 5 word) mem s1,
  getr regs 9 = w64 s1 -> getr regs 10 = w64 0 -> 0 <= s1 -> s1 + 208 <= 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 136) = Some 4094 -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (p2_E regs [SHADOW_OFF]) ss_N
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VR)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 R9 R10 Hs0 Hs1 H136 H200.
set (E := p2_E regs [SHADOW_OFF]).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (p2_E_reg _ _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; exact (p2_E_extra regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; unfold p2_E; apply regs_ok_Eimg_Ereg).
clearbody E.
unfold ss_N. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [exact HRO | reflexivity | rewrite R10; reflexivity].
- vm_compute. reflexivity.
- apply Forall_cons; [exact (p2_s1r_ok W mem E s1 U9 Hs0 Hs1 E32 H136 H200) | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; exact I].
  cbn [p2_factsN f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the state at 0x85ba4 when strrchr returned DOT = r <> 0, dot[1] = b *)
Lemma p2_seedF : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 r b,
  getr regs 9 = w64 s1 -> getr regs 10 = w64 r ->
  0 <= s1 -> s1 + 208 <= 2 ^ 64 -> 4096 <= r <= 0x7fffff800000 -> 0 <= b <= 255 ->
  rdword (rdW W mem) (s1 + 136) = Some 4094 -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  rdW W mem (r + 1) = Some b ->
  (r + 2 <= s1 + 136 \/ s1 + 208 <= r + 1) ->
  st_ok_pi SEGS VAL (p2_E regs [SHADOW_OFF; b]) ss_F
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VR)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 r b R9 R10 Hs0 Hs1 Hr Hb H136 H200 Hrb Hdj.
set (E := p2_E regs [SHADOW_OFF; b]).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (p2_E_reg _ _ 9 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (subst E; rewrite (p2_E_reg _ _ 10 10%bv eq_refl); exact R10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; exact (p2_E_extra regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (subst E; exact (p2_E_extra regs _ 1 ltac:(unfold A_TEXT; lia))).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = r) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = b) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; unfold p2_E; apply regs_ok_Eimg_Ereg).
clearbody E.
unfold ss_F. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HRO.
- vm_compute. reflexivity.
- apply Forall_cons; [exact (p2_s1r_ok W mem E s1 U9 Hs0 Hs1 E32 H136 H200)|].
  apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, p2_nmr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil]. exact (p2_chunk1 W mem E r 1 33 b E33 ltac:(lia) Hrb).
- apply pairwise_disjoint_of_extents. unfold p2_s1r, p2_nmr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
- split; [|split; exact I].
  cbn [p2_factsF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U32, U33.
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma s22b_img : forall cx (rd rd' : reader), (forall x, rd' x = rd x) -> lt_img B cx rd -> lt_img B cx rd'.
Proof.
intros cx rd rd' HK (HRO & HIMG & HGI). split; [|split].
- intros a H1 H2 H3. rewrite HK. exact (HRO a H1 H2 H3).
- exact (s22b_himg B rd rd' _ _ _ _ _ _ _ _ _ HK HIMG).
- intros j Hj. rewrite HK. exact (HGI j Hj).
Qed.
Lemma s22b_hblk : forall ly S (rd rd' : reader) a n, (forall x, rd' x = rd x) ->
  lt_hblk B ly S rd a n -> lt_hblk B ly S rd' a n.
Proof.
intros ly S rd rd' a n HK (H1 & H2 & H3 & H4). exact (conj H1 (conj H2 (conj H3 (s22b_addr rd rd' a n HK H4)))).
Qed.
Lemma s22b_frame : forall cx ly S (W : world SEGS) regs mem md k o regs' mem' md',
  lt_frame B cx ly S W regs mem md k o ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_frame B cx ly S W regs' mem' md' k o.
Proof.
intros cx ly S W regs mem md k o regs' mem' md' HF HJ' HK P2 P3 P4 P8 P9.
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
split; [exact HJ'|]. rewrite P2, P3, P4, P8, P9.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [intros i r Hi; rewrite (s22b_word _ _ _ HK); exact (HSV i r Hi)|].
rewrite !(s22b_word _ _ _ HK).
split; [exact HH0|]. split; [exact HH8|]. split; [exact HH16|]. split; [exact HFL|]. split; [exact H200|].
split; [exact (s22b_zs _ _ _ _ HK HSH) | exact H184].
Qed.
(* s22_inv is kept by a stretch that keeps every byte, sp, gp, tp, s0, s1 and the journal's count *)
Lemma s22b_inv_kept : forall cx i c m tab mt o ly S (W : world SEGS) regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s22_inv B MT cx i c m tab mt o ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o ly S W regs mem md k acc regs' mem' md'
  (Hi & Hd & (HF & HI & HBL & HBUD) & Hc & Hm & Ht & Hmt & HSL & HCM & HT) HJ' HK P2 P3 P4 P8 P9.
split; [exact Hi|]. split; [exact Hd|].
split; [split; [exact (s22b_frame cx ly S W regs mem md k o regs' mem' md' HF HJ' HK P2 P3 P4 P8 P9)|]|].
{ split; [exact (s22b_img cx _ _ HK HI)|]. exact (conj HBL HBUD). }
split; [exact (s22b_hblk ly S _ _ _ _ HK Hc)|]. split; [exact (s22b_hblk ly S _ _ _ _ HK Hm)|].
split; [exact (s22b_hblk ly S _ _ _ _ HK Ht)|]. split; [exact (s22b_hblk ly S _ _ _ _ HK Hmt)|].
split; [exact (s22b_slots cx _ _ _ HK HSL)|]. split; [exact (s22b_cm _ _ _ _ _ HK HCM)|].
exact (s22b_tabs cx _ _ _ _ _ HK HT).
Qed.

(* the entry sp and the realigned base S1 (B s12k's lk_sp) *)
Lemma s22b_sp : forall cx, lt_base B MT cx ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx - 384 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* ---- the exits ---- *)
(* to the continue join: turn i adds nothing (m_split gave None), the memory and the kept registers are the VR
   point's *)
Lemma p2_to_join : forall i cx ly S (W : world SEGS) regs mem md k acc c m tab mt regs' mem' md',
  S22_JOIN_stmt B MT i -> lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs mem md k acc ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = None ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 20; 22; 24; 26; 27]%bv -> getr regs' rr = getr regs rr) ->
  getr regs' 16 = w64 SHADOW_OFF -> getr regs 24 = w64 m -> s22_rk m i regs ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_JOIN)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros i cx ly S W regs mem md k acc c m tab mt regs' mem' md' HJOIN HB Hfrm HINV Hsplit HJ' HK KR R16 R24 HRK.
assert (Hdecl : x_decl cx (Datatypes.S i) = x_decl cx i).
{ pose proof HINV as (Hi & Hpos & _). unfold x_decl.
  apply s22_decl_step_skip; [exact Hi | exact (proj1 Hpos) | right; exact Hsplit]. }
apply (HJOIN cx ly S W regs' mem' md' k acc c m tab mt HB Hfrm Hdecl).
- exact (s22b_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc regs' mem' md' HINV HJ' HK
    (KR 2%bv ltac:(p2_in)) (KR 3%bv ltac:(p2_in)) (KR 4%bv ltac:(p2_in)) (KR 8%bv ltac:(p2_in))
    (KR 9%bv ltac:(p2_in))).
- exact R16.
- rewrite (KR 24%bv ltac:(p2_in)). exact R24.
- unfold s22_rk. rewrite !KR by p2_in. exact HRK.
Qed.

(* to the head of the digit loop with t = 0, v = 0 *)
Lemma p2_to_vd : forall i cx ly S (W : world SEGS) regs mem md k acc c m tab mt regs' mem' md' (di : nat) b,
  S22_VD_stmt B MT i -> lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  SegModel.hd0 (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) = b -> b <> 0 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 19; 20; 22; 24; 26; 27]%bv -> getr regs' rr = getr regs rr) ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 24 = w64 m -> s22_rk m i regs ->
  getr regs' 5 = w64 10 -> getr regs' 6 = w64 LT_VIDMAX ->
  getr regs' 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat di) ->
  getr regs' 11 = w64 (seg_spec.mseg_addr m i + Z.of_nat di + 1) ->
  getr regs' 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat di + 2) ->
  getr regs' 13 = w64 b ->
  getr regs' 15 = w64 (-1) -> getr regs' 16 = w64 SHADOW_OFF -> getr regs' 17 = w64 (-10) ->
  getr regs' 21 = w64 0 ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_VD)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros i cx ly S W regs mem md k acc c m tab mt regs' mem' md' di b HVD HB Hfrm HINV Hign Hsome Hdi Hhd Hb0 HJ' HK KR
  R19 R24 HRK P5 P6 P10 P11 P12 P13 P15 P16 P17 P21.
assert (Ht : (0 < length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))))%nat).
{ revert Hhd. destruct (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) as [|z zs];
    cbn [SegModel.hd0 length]; intros Hhd; [congruence | lia]. }
apply (HVD cx ly S W regs' mem' md' k acc c m tab mt di 0%nat 0 HB Hfrm
  (s22b_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc regs' mem' md' HINV HJ' HK
    (KR 2%bv ltac:(p2_in)) (KR 3%bv ltac:(p2_in)) (KR 4%bv ltac:(p2_in)) (KR 8%bv ltac:(p2_in))
    (KR 9%bv ltac:(p2_in)))
  Hign Hsome Hdi Ht).
- reflexivity.
- reflexivity.
- lia.
- exact P5.
- exact P6.
- exact P10.
- rewrite P11. unfold w64. f_equal. lia.
- rewrite P12. unfold w64. f_equal. lia.
- rewrite P13. unfold w64. f_equal. rewrite <- Hhd.
  destruct (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))); reflexivity.
- exact P15.
- exact P16.
- exact P17.
- rewrite (KR 19%bv ltac:(p2_in)). exact R19.
- exact P21.
- rewrite (KR 24%bv ltac:(p2_in)). exact R24.
- unfold s22_rk. rewrite !KR by p2_in. exact HRK.
Qed.

(* the registers a stretch keeps, read back from its final state *)
Ltac p2_kr HS EEo :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr; cbn [In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?r0 = _ => prreg HS r0 P end;
      rewrite P; apply EEo; reflexivity | ]);
  destruct Hrr.
(* an atom of the seed read under the tokens a run added *)
Ltac p2_U H n v Ev :=
  lazymatch type of H with context [U ?E2 (SOff n 0)] =>
    rewrite (U_atom E2 n v ltac:(repeat rewrite ew_ewset_other by lia; exact Ev)
      ltac:(first [lia | unfold SHADOW_OFF; lia])) in H end.
Ltac p2_md md' :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md' := d) in *; clearbody md' end.

Lemma s22_p2 : s22_p2_stmt B MT.
Proof.
unfold s22_p2_stmt, S22_VR_stmt.
intros i HJOIN HVD cx ly S W regs mem md k acc c m tab mt r HB Hfrm HINV Hign Hr R10 R19 R24 HRK.
pose proof HINV as (Hi & Hdecl & HCORE & HhC & Hm & HhT & HhMT & HSL & HCM & HTABS).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
destruct (s22b_sp cx HB) as (Hsp0 & Hsp47 & Hs1lo & Hs1hi).
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof asan_consts as (C1 & _).
pose proof Hm as (HinM & Hm4 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE (proj1 HJ) HinM) as (_ & _ & HMceil & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMceil.
assert (Hi32 : (i < 32)%nat).
{ pose proof HCM as (_ & (bs & _ & Henc)). destruct Henc as (_ & Hle & _). unfold x_mcF in Hi. lia. }
assert (H136 : rdword (rdW W mem) (x_s1 cx + 136) = Some 4094).
{ apply (HSL 136 LT_VIDMAX). unfold LT_LV, LT_LD. apply in_or_app. right. p2_in. }
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hstr & Hn16 & Hnf).
set (x := seg_spec.mseg_addr m i) in *.
assert (Hx : x = m + 256 * Z.of_nat i) by (unfold x, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
set (name := SegModel.ms_name (x_seg cx i)) in *.
destruct Hr as [(Hr0 & Hnone) | (j & Hsome & Hrj)].
- (* ---- strrchr found no '.': 0x85ba4 beqz a0 -> 0x85c34: a6 := 200(s1), j 0x85b58 ---- *)
  subst r.
  pose proof (p2_seedN W regs mem (x_s1 cx) R9 R10 ltac:(lia) ltac:(lia) H136 H200) as HS.
  assert (HEI : img_env VAL A_LIM (p2_E regs [SHADOW_OFF])) by (unfold p2_E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS p2x [] (p2_E regs [SHADOW_OFF]) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (p2_E regs [SHADOW_OFF]) n = getr regs rr)
    by (intros n rr Hn; exact (p2_E_reg regs _ n rr Hn)).
  assert (E32 : ew (p2_E regs [SHADOW_OFF]) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (p2_E_extra regs _ 0 ltac:(unfold A_TEXT; lia)).
  remember (p2_E regs [SHADOW_OFF]) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
  { awr_ok_tac. }
  p2_md md1.
  pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K1.
  pmkst HS.
  prreg HS (16%bv : bv 5) P16.
  apply (p2_to_join i cx ly S W regs mem md k acc c m tab mt _ _ _ HJOIN HB Hfrm HINV
    (s22_split_none_nodot name Hnone) HJ K1).
  + p2_kr HS EEo.
  + rewrite P16. exact E32.
  + exact R24.
  + exact HRK.
- (* ---- strrchr found the last '.' at index j: DOT = r = x + j ---- *)
  assert (Hjl : (j < length name)%nat).
  { pose proof (SegModel.strrchr_lt name 46 j Hsome) as Hl. rewrite (SegModel.cut_nul_id name Hnf) in Hl. exact Hl. }
  set (b := nth (Datatypes.S j) (name ++ [0]) 0).
  assert (Hrb : rdW W mem (r + 1) = Some b).
  { destruct Hstr as [Hz _]. rewrite Hrj.
    replace (x + Z.of_nat j + 1) with (x + Z.of_nat (Datatypes.S j)) by lia.
    apply Hz. rewrite length_app. cbn [length]. lia. }
  assert (Hb : 0 <= b <= 255) by (pose proof (p2_rd_byte W mem _ _ Hrb); lia).
  assert (Hhd : SegModel.hd0 (skipn (Datatypes.S j) name) = b) by (unfold b; apply p2_hd0_skipn).
  clearbody b.
  pose proof (p2_seedF W regs mem (x_s1 cx) r b R9 R10 ltac:(lia) ltac:(lia) ltac:(lia) Hb H136 H200 Hrb
    ltac:(lia)) as HS.
  assert (HEI : img_env VAL A_LIM (p2_E regs [SHADOW_OFF; b])) by (unfold p2_E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS p2x [] (p2_E regs [SHADOW_OFF; b]) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (p2_E regs [SHADOW_OFF; b]) n = getr regs rr)
    by (intros n rr Hn; exact (p2_E_reg regs _ n rr Hn)).
  assert (E32 : ew (p2_E regs [SHADOW_OFF; b]) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (p2_E_extra regs _ 0 ltac:(unfold A_TEXT; lia)).
  assert (E33 : ew (p2_E regs [SHADOW_OFF; b]) 33 = Z_to_bv 64 b)
    by exact (p2_E_extra regs _ 1 ltac:(unfold A_TEXT; lia)).
  remember (p2_E regs [SHADOW_OFF; b]) as E eqn:HE. clear HE.
  assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E19 : ew E 19 = Z_to_bv 64 x) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  unfold cfg_at, w64.
  (* 0x85ba4 .. 0x85bb8: the NULL test (decided by DOT >= 4096), a6, a5, a7, t0, t1; stops at beq a0,s3 *)
  paj_run_tok RUN HS HJ SHOK p2span.
  { awr_ok_tac. }
  p2_md md1.
  pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
  rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK p2span.
  + (* 0x85bbc beq a0,s3 taken: the '.' is the name's first byte, j = 0 -> JOIN *)
    rewrite branch_eq_U in Hc. p2_U Hc 10%nat r E10. p2_U Hc 19%nat x E19. apply Z.eqb_eq in Hc.
    assert (Hj0 : j = 0%nat) by lia. rewrite Hj0 in Hsome.
    paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
    { awr_ok_tac. }
    p2_md md2.
    pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K2.
    assert (K : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite K2, K1; reflexivity).
    pmkst HS.
    prreg HS (16%bv : bv 5) P16.
    apply (p2_to_join i cx ly S W regs mem md k acc c m tab mt _ _ _ HJOIN HB Hfrm HINV
      (s22_split_none_dot0 name Hsome) HJ K).
    * p2_kr HS EEo.
    * rewrite P16. exact E32.
    * exact R24.
    * exact HRK.
  + (* 0x85bbc not taken: j <> 0; the trap DOT = -1 decided; check 31 at DOT + 1; lbu dot[1]; stops at beqz a3 *)
    rewrite branch_eq_U in Hc. p2_U Hc 10%nat r E10. p2_U Hc 19%nat x E19. apply Z.eqb_neq in Hc.
    assert (Hj0 : j <> 0%nat) by (intros Hq; apply Hc; rewrite Hrj, Hq; lia). clear Hc.
    paj_run_tok RUN HS HJ SHOK p2span.
    { (* check 31: DOT + 1 lies in m's block *)
      apply (obl_of_block SEGS B LAWS ly S W (ms_mem ms1) md1 E p2x _ 1 m seg_spec.SEG_M_SIZE (proj1 HJ) HinM).
      - unfold p2x. apply U_atom; [exact E32 | unfold SHADOW_OFF; lia].
      - rewrite (U_atom_off E 10 r 1 E10) by lia. lia.
      - rewrite (U_atom_off E 10 r 1 E10) by lia. change (req_size seg_spec.SEG_M_SIZE) with 9236. lia. }
    { awr_ok_tac. }
    p2_md md2.
    pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
    assert (K12 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite K2, K1; reflexivity).
    clear K1 K2. rename ms into ms2.
    psrr_branch_tok RUN BR HS SHOK p2span.
    * (* 0x85bdc beqz a3 taken: dot[1] = 0 -> JOIN *)
      rewrite branch_eq_U in Hc. p2_U Hc 33%nat b E33. rewrite (U_lit _ 0) in Hc by lia. apply Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
      { awr_ok_tac. }
      p2_md md3.
      pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K3.
      assert (K : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite K3, K12; reflexivity).
      pmkst HS.
      prreg HS (16%bv : bv 5) P16.
      apply (p2_to_join i cx ly S W regs mem md k acc c m tab mt _ _ _ HJOIN HB Hfrm HINV
        (s22_split_none_empty name j Hsome ltac:(rewrite Hhd; exact Hc)) HJ K).
      -- p2_kr HS EEo.
      -- rewrite P16. exact E32.
      -- exact R24.
      -- exact HRK.
    * (* 0x85bdc not taken: s5 := 0, a2 := DOT + 2 -> VD *)
      rewrite branch_eq_U in Hc. p2_U Hc 33%nat b E33. rewrite (U_lit _ 0) in Hc by lia. apply Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK p2span S22_VD.
      { awr_ok_tac. }
      p2_md md3.
      pose proof (s22b_nowin_kept _ _ _ _ _ HFr eq_refl) as K3.
      assert (K : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite K3, K12; reflexivity).
      pmkst HS.
      prreg HS (5%bv : bv 5) P5. prreg HS (6%bv : bv 5) P6. prreg HS (10%bv : bv 5) P10.
      prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
      prreg HS (15%bv : bv 5) P15. prreg HS (16%bv : bv 5) P16. prreg HS (17%bv : bv 5) P17.
      prreg HS (21%bv : bv 5) P21.
      apply (p2_to_vd i cx ly S W regs mem md k acc c m tab mt _ _ _ j b HVD HB Hfrm HINV Hign Hsome Hj0 Hhd Hc HJ K).
      -- p2_kr HS EEo.
      -- exact R19.
      -- exact R24.
      -- exact HRK.
      -- rewrite P5. reflexivity.
      -- rewrite P6. reflexivity.
      -- rewrite P10, E10. unfold w64. f_equal. exact Hrj.
      -- rewrite P11, E10, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hrj. reflexivity.
      -- rewrite P12, E10, unsigned_lit_small by lia. unfold w64. f_equal. rewrite Hrj. reflexivity.
      -- rewrite P13. exact E33.
      -- rewrite P15. apply Z_to_bv64_eq_mod. vm_compute. reflexivity.
      -- rewrite P16. exact E32.
      -- rewrite P17. apply Z_to_bv64_eq_mod. vm_compute. reflexivity.
      -- rewrite P21. reflexivity.
Qed.

End e.
End f.
End d.
