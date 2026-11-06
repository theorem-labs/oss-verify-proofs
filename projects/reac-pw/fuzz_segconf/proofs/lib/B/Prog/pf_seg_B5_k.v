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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 534 of its 586 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B11b_k.v, with its module names changed; 440 of its 609 lines of code are new or changed and 417 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the kit of segment B5 of
   reac_segconf_parse_file (the B5 segment lane of the image-B G3 walk owner, 2026-10-30). Shared by the B5 piece files.
   ADAPTED from the image-A G3 walk owner's image-A files lib/A/Prog/pf_a2_g.v (commit 096053c62900: the write set,
   the kept relation and the keep lemmas of the cut's objects), lib/A/Prog/pf_a5_k.v (commit
   385fd095481f: the rebuild of pf_base after a step, the text, the read-only view, the frame chain, the line's post)
   and lib/A/Prog/pf_a7_d.v (commit ebe0b30cca65: buf's shadow cells and the facts every callee
   asks of a range of buf), re-derived for image B:
   - b5_geoP / b5_geo: the numbers at a cut (afn_pre's astk_ok for sp0; B's realigned locals base s1 = (sp0 - 0x160)
     & -32, so sp0 - 368 <= s1 <= sp0 - 352 (0x87e38 `addi sp,sp,-352`, 0x87e78 `andi sp,sp,-32`, 0x87e7c `mv s1,sp`);
     the class-5 frame F of the journal, 32-aligned, an application range outside the image range [0x10000, kImgEnd)
     by the AR's client-image law and the ledger's image cover);
   - b5_Wr: every byte a B5 step writes -- the callees' windows below s1 (strchr 2 * ESTACK, strlen / memcpy /
     meta_fill ESTACK, trim STK_trim, all inside parse_file's window [sp0 - STK, s1)), buf (memcpy 0x882c8, the NUL
     stores 0x882e0 and 0x88384, trim's NUL), and buf's 64 shadow cells SH + 8 .. SH + 72 (meta_fill_00 0x8824c,
     meta_fill_f8 0x88608). B5 writes no spill slot (pf_seg_B5_d.v's head comment), so unlike A5's kit there is no
     slot clause;
   - b5_kept and the keep lemmas: bytes outside b5_Wr keep their value and mapped bytes stay mapped, so every cut
     object (the text, the block c, the catalogue, the literals, the read-only view, the stack-protector cells, c's
     state, cur_name, the 29 slots, the saved registers, the flag word, the frame's shadow outside buf's cells) is
     carried. The image range [0x10000, kImgEnd) lies outside the frame, so neither SSPX nor VRO is needed;
   - b5_move: pf_base after a step from the journal it returned;
   - the buf facts (B's twin of pf_a7_d.v): buf's cells are 0 under PF_SC_LINE, so a range of buf is addressable
     (b5_addr_buf) and lies in the live class-5 frame (b5_fframe_buf). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B5_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= arithmetic ======================= *)
Lemma b5_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b5_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's first 256 cells *)
Lemma b5_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma b5_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b5_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma b5_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* a register of a list *)
Lemma b5_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma b5_rg_bv : forall rX L r v (b : bv 5), pf_rg rX L -> In (r, v) L -> bv_unsigned b = r -> getr rX b = w64 v.
Proof. intros rX L r v b H Hin Hb. rewrite <- (Z_to_bv_bv_unsigned 5 b), Hb. exact (b5_rg rX L r v H Hin). Qed.
Lemma b5_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Lemma b5_rg_incl : forall rX L1 L2, incl L2 L1 -> pf_rg rX L1 -> pf_rg rX L2.
Proof. intros rX L1 L2 Hi H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin. exact (H rv (Hi rv Hin)). Qed.
Lemma b5_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Ltac b5_in := cbn [In app]; repeat first [left; reflexivity | right].
Lemma b5_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma b5_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.
(* buf's shadow cells (8 .. 71) per scope *)
Lemma b5_shb_in : forall sc i, 8 <= i < 72 -> pf_shb sc i = pf_io (sc_buf sc).
Proof.
intros sc i H. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 72) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma b5_shb_buf : forall sc b i, ~ (8 <= i < 72) ->
  pf_shb (PFSc (sc_cn sc) b (sc_low sc) (sc_l146 sc) (sc_known sc)) i = pf_shb sc i.
Proof.
intros [cn bf lw l1 kn] b i H. unfold pf_shb. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8) eqn:E3; [reflexivity|].
destruct (i <? 72) eqn:E4; [|reflexivity]. apply Z.ltb_ge in E3. apply Z.ltb_lt in E4. lia.
Qed.
Lemma b5_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof. intros i Hi. rewrite b5_shb_in by exact Hi. reflexivity. Qed.
(* the two scopes B5 moves between: buf in (PF_SC_LINE) and buf out (PF_SC_HEAD) *)
Lemma b5_sc_line : PF_SC_LINE = PFSc (sc_cn PF_SC_HEAD) true (sc_low PF_SC_HEAD) (sc_l146 PF_SC_HEAD) (sc_known PF_SC_HEAD).
Proof. reflexivity. Qed.
Lemma b5_sc_head : PF_SC_HEAD = PFSc (sc_cn PF_SC_LINE) false (sc_low PF_SC_LINE) (sc_l146 PF_SC_LINE) (sc_known PF_SC_LINE).
Proof. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* every register of PF_RL, PF_RM and pf_fi's list is callee-saved *)
Lemma b5_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof. intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b5_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof. intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
(* pf_fi's register list (pf_pieces.v: sp, gp, tp, s0, s1, s4) *)
Definition b5_FI (B : asyms) (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Lemma b5_FI_cs : forall B v, Forall (fun rv => acallee_saved (fst rv)) (b5_FI B v).
Proof. intros B v. unfold b5_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================= the segment's write set and what keeps outside it ======================= *)
Definition b5_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/ (b5_buf v pos <= a < b5_buf v pos + 512) \/
  (pf_SH v pos + 8 <= a < pf_SH v pos + 72).
Definition b5_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b5_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma b5_kept_refl : forall v pos rd, b5_kept v pos rd rd.
Proof. intros v pos rd. split; [intros; reflexivity | intros a _ H; exact H]. Qed.
Lemma b5_kept_trans : forall v pos rd1 rd2 rd3, b5_kept v pos rd1 rd2 -> b5_kept v pos rd2 rd3 ->
  b5_kept v pos rd1 rd3.
Proof.
intros v pos rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.
(* the numbers of the frame and the stack at a cut (afn_pre's astk_ok, the journal's class-5 frame) *)
Definition b5_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b5_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b5_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b5_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b5_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b5_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b5_geoP v pos.
Lemma b5_F8 : pf_F v pos mod 8 = 0.
Proof.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma b5_SHv : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
pose proof b5_F8 as F8.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.
(* a byte the segment never touches, nor its shadow cell: below the allocator's ceiling, an application byte, and
   outside the class-5 frame *)
Definition b5_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Lemma b5_out_nw : forall x, b5_out x ->
  0 <= x < 2 ^ 64 /\ ~ b5_Wr v pos x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b5_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_F8 as F8.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (b5_granule (pf_F v pos) x F8 Hx3 ltac:(lia)) as Gr.
unfold b5_Wr, b5_buf, PF_O_BUF, pf_SH, shadow_addr, SHADOW_OFF. rewrite ESTK.
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma b5_out_img : forall x, 0x10000 <= x < kImgEnd -> b5_out x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1). pose proof asan_consts as (C1 & _).
unfold kImgEnd in *. split; [lia|]. split; [lia|]. exact (I1 x Hx).
Qed.
Lemma b5_out_inimg : forall x, in_img SEGS x -> b5_out x.
Proof. intros x Hx. apply b5_out_img. exact (pa_img_range x Hx). Qed.
(* the stack slots of the prologue's saved registers, the 29 spill slots, the frame's flag word, cur_name, and the
   frame's shadow cells other than buf's *)
Lemma b5_saved_nw : forall a, pf_sp0 v - 104 <= a < pf_sp0 v -> 0 <= a < 2 ^ 64 /\ ~ b5_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_SHv as (E1 & E2 & E3 & E4).
unfold b5_Wr, b5_buf, PF_O_BUF. rewrite ESTK. lia.
Qed.
Lemma b5_slot_nw : forall a, pf_s1 v <= a < pf_s1 v + 0xe0 -> 0 <= a < 2 ^ 64 /\ ~ b5_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_SHv as (E1 & E2 & E3 & E4).
unfold b5_Wr, b5_buf, PF_O_BUF. rewrite ESTK. lia.
Qed.
Lemma b5_flag_nw : forall a, pf_F v pos + 2040 <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ b5_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_SHv as (E1 & E2 & E3 & E4).
unfold b5_Wr, b5_buf, PF_O_BUF. rewrite ESTK. lia.
Qed.
Lemma b5_cn_nw : forall a, pf_F v pos + PF_O_CN <= a < pf_F v pos + PF_O_BUF -> 0 <= a < 2 ^ 64 /\ ~ b5_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_SHv as (E1 & E2 & E3 & E4).
unfold PF_O_CN, PF_O_BUF in Ha. unfold b5_Wr, b5_buf, PF_O_BUF. rewrite ESTK. lia.
Qed.
Lemma b5_shc_nw : forall i, 0 <= i < 144 -> ~ (8 <= i < 72) ->
  0 <= pf_SH v pos + i < 2 ^ 64 /\ ~ b5_Wr v pos (pf_SH v pos + i).
Proof.
intros i Hi Hn. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof b5_SHv as (E1 & E2 & E3 & E4).
unfold b5_Wr, b5_buf, PF_O_BUF. rewrite ESTK. lia.
Qed.
(* buf's own shadow cells are b5_Wr's, and buf's bytes are *)
Lemma b5_bufsh_range : forall i, 8 <= i < 72 -> 0 <= pf_SH v pos + i < 2 ^ 64.
Proof. intros i Hi. pose proof b5_SHv as (E1 & E2 & E3 & E4). lia. Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : b5_kept v pos rd rd'.
Lemma b5_k_byte : forall x, b5_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (b5_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma b5_k_shadow : forall x, b5_out x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (b5_out_nw x Hx) as (_ & _ & H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b5_k_zs : forall p l, (forall i, (i < length l)%nat -> b5_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b5_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b5_k_bytes : forall p l, (forall i, (i < length l)%nat -> b5_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b5_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b5_k_rdword : forall a, (forall k, 0 <= k < 8 -> b5_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (b5_k_byte _ (Ho k Hk)). Qed.
Lemma b5_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b5_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b5_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b5_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (b5_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b5_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b5_k_addr : forall q n, (forall x, q <= x < q + n -> b5_out x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b5_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b5_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b5_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b5_k_str a s); [|exact Hs]. intros x Hx. apply b5_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma b5_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b5_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b5_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b5_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b5_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b5_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b5_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply b5_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b5_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b5_out (a + k))
  by (intros a Ha k Hk; apply b5_out_img; lia).
split; [rewrite (b5_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b5_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
(* the 29 slots (pf_sl at s1 + off, off + 8 <= 0xe0), the saved registers, the flag word, cur_name, the frame's
   shadow outside buf's cells *)
Lemma b5_k_sl : forall L, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0xe0) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros L HL H. unfold pf_sl in *. rewrite Forall_forall in *.
intros [off val] Hin. specialize (H _ Hin). specialize (HL _ Hin). cbn [fst snd] in *.
rewrite (rdword_ext rd rd'); [exact H|]. intros k Hk.
destruct (b5_slot_nw (pf_s1 v + off + k) ltac:(lia)) as (H0 & H1).
replace (pf_s1 v + off + k) with (pf_s1 v + off + k) in H1 by reflexivity. exact (proj1 K _ H0 H1).
Qed.
Lemma b5_k_saved : forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros regs H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
intros k Hk. destruct (b5_saved_nw (pf_sp0 v - 8 - 8 * Z.of_nat j + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma b5_k_flag : forall x, rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros x H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (b5_flag_nw (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma b5_k_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros nm (f & Hf & Hfe). exists f. split; [|exact Hfe].
pose proof Hfe as [Hl _].
intros i Hi. rewrite Hl in Hi.
destruct (b5_cn_nw (pf_F v pos + PF_O_CN + Z.of_nat i) ltac:(unfold PF_O_CN, PF_O_BUF; lia)) as (H0 & H1).
rewrite (proj1 K _ H0 H1). exact (Hf i ltac:(rewrite Hl; exact Hi)).
Qed.
Lemma b5_k_fsh_out : forall sc i, 0 <= i < 144 -> ~ (8 <= i < 72) -> pf_fsh rd (pf_SH v pos) sc ->
  rd' (pf_SH v pos + i) = Some (pf_shb sc i).
Proof.
intros sc i Hi Hn H. destruct (b5_shc_nw i Hi Hn) as (H0 & H1). rewrite (proj1 K _ H0 H1). exact (H i Hi).
Qed.
End r.
End k.

(* a range inside a live heap block of the cut's state lies outside the frame *)
Lemma b5_out_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  b5_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> b5_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold b5_out. lia.
Qed.
Lemma b5_out_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  b5_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n -> b5_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (b5_out_heap v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb). lia.
Qed.

(* ======================= the cut's objects, carried across a step ======================= *)
Lemma b5_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b5_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b5_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hin EF K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> b5_out v pos x)
  by (intros x Hx; exact (b5_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H3 Hx)).
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> b5_out v pos x)
  by (intros x Hx; exact (b5_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H5 Hx)).
split; [apply (b5_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (b5_k_addr v pos HG rd rd' K _ _ Ht H2)|]. split; [exact H3|].
split; [exact (b5_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (b5_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (b5_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (b5_k_rod v pos HG rd rd' K H8) | exact (b5_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma b5_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf,
  b5_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b5_kept v pos rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf HG HAR Hin EF K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (b5_k_bytes v pos HG rd rd' K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
apply (b5_out_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hin EF Hh). lia.
Qed.
(* the spine's state at a cut (pf_st): c's bytes, cur_name, the slot 0xc0 *)
Lemma b5_keep_st : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf cur nm k,
  b5_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b5_kept v pos rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos rd cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf cur nm k HG HAR Hin EF K Hh (H1 & H2 & H3 & H4 & H5).
split; [exact (b5_keep_rconf v pos lyc Sc Wc memc mdc rd rd' cf HG HAR Hin EF K Hh H1)|].
split; [exact H2|]. split; [exact (b5_k_nm v pos HG rd rd' K nm H3)|]. split; [exact H4|].
assert (HS : pf_sl rd' (pf_s1 v) [(0xc0, pf_cur_ptr (p_c v) cur)]).
{ apply (b5_k_sl v pos HG rd rd' K); [repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia|].
  unfold pf_sl. apply Forall_cons; [exact H5 | apply Forall_nil]. }
exact (Forall_inv HS).
Qed.
Lemma b5_PF_SL_rng : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0xe0) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. Qed.
(* the frame's shadow after a step that kept every cell but buf's, which it set to pf_io b *)
Lemma b5_keep_fsh : forall v pos rd rd' sc b, b5_geoP v pos -> b5_kept v pos rd rd' ->
  (forall i, 8 <= i < 72 -> rd' (pf_SH v pos + i) = Some (pf_io b)) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) (PFSc (sc_cn sc) b (sc_low sc) (sc_l146 sc) (sc_known sc)).
Proof.
intros v pos rd rd' sc b HG K HF H i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8 | Hi8]; [|destruct (Z_lt_le_dec i 72) as [Hi72 | Hi72]].
- rewrite b5_shb_buf by lia. exact (b5_k_fsh_out v pos HG rd rd' K sc i Hi ltac:(lia) H).
- rewrite (HF i ltac:(lia)), b5_shb_in by lia. reflexivity.
- rewrite b5_shb_buf by lia. exact (b5_k_fsh_out v pos HG rd rd' K sc i Hi ltac:(lia) H).
Qed.
(* the same when buf's cells keep their scope (no fill in the step) *)
Lemma b5_keep_fsh_same : forall v pos rd rd' sc, b5_geoP v pos -> b5_kept v pos rd rd' ->
  (forall i, 8 <= i < 72 -> rd' (pf_SH v pos + i) = rd (pf_SH v pos + i)) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sc HG K HF H i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8 | Hi8]; [|destruct (Z_lt_le_dec i 72) as [Hi72 | Hi72]].
- exact (b5_k_fsh_out v pos HG rd rd' K sc i Hi ltac:(lia) H).
- rewrite (HF i ltac:(lia)). exact (H i Hi).
- exact (b5_k_fsh_out v pos HG rd rd' K sc i Hi ltac:(lia) H).
Qed.

(* ======================= the cut state after a step ======================= *)
(* pf_base after a step that kept every byte off b5_Wr (and every visible byte visible), with the journal it
   returned at the same layout, the frame state changed at most (set_fs), the live blocks permuted *)
Lemma b5_move : forall v pos lyc Sc Wc rX memc mdc sc Sc' rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  b5_kept v pos (rdW Wc memc) (rdW Wc memc') ->
  pf_rg rX' (b5_FI B v) ->
  pf_fsh (rdW Wc memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm K HRG HFSH.
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct (b5_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
destruct HFI as (_ & Hly & (f0 & HS0) & HP0 & HSV & HFL & HFRM & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply b5_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (b5_k_saved v pos HG _ _ K _ HSV)|].
  split; [exact (b5_k_flag v pos HG _ _ K _ HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [apply (b5_k_sl v pos HG _ _ K); [repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia | exact HC8]|].
  exact HRG. }
split.
{ pose proof (b5_keep_obj v pos lyc Sc Wc memc mdc _ _ HG HAR Hin EF K HOBJ) as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (b5_k_sl v pos HG _ _ K _ (b5_PF_SL_rng v pos) HSL) | exact HFSH].
Qed.

(* ======================= the text, the read-only view, the frame chain ======================= *)
Lemma b5_text : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ~ In 0 (p_s v) /\ (length (p_s v) <= 65535)%nat /\ sa_str (rdW Wc memc) (p_t v) (p_s v) /\
  sa_addr (rdW Wc memc) (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & HOBJ & _).
destruct HOBJ as (HSTR & HADDR & HHEAP & _ & HC & _).
destruct HFI as (_ & _ & _ & _ & _ & _ & _ & HTF & _).
destruct HTF as (_ & _ & _ & _ & HLS).
split; [exact (proj2 (proj1 HSTR))|]. split; [exact HLS|]. auto.
Qed.
Lemma b5_rom : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
intros a (sg & Hsg & Hw & Hr) Ho He. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* the frame chain at a call from B5 (s0 = sp0, the frame pointer): the prologue's record (ra at sp0 - 8, the entry
   s0 at sp0 - 16, pf_saved) on afn_pre's chain, which the journal keeps above sp0 *)
Lemma b5_chain : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof HB as (HCX0 & HFI0 & _).
destruct (b5_geo v pos lyc Sc Wc rX memc mdc HCX0 HFI0) as (HG & Hin & EF & Hfrs & HAR).
destruct HB as (HCX & HFI & _).
destruct HFI as (HJ & Hly & _ & _ & HSV & _).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof HG as (G1 & G2 & G3 & G4 & G5 & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | lia |].
    intros Hf. apply b5_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

(* ======================= buf (B's twin of pf_a7_d.v) ======================= *)
(* buf's shadow cell for an address of buf, while buf is in scope *)
Lemma b5_sh_at : forall v pos lyc Sc Wc rX memc mdc x, pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  b5_buf v pos <= x < b5_buf v pos + 512 -> rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros v pos lyc Sc Wc rX memc mdc x HB Hx.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & _).
pose proof (b5_F8 v pos HG) as HF8. pose proof HG as (_ & _ & _ & _ & _ & _ & H1 & _).
unfold b5_buf, PF_O_BUF in Hx.
replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
rewrite (HFSH ((x - pf_F v pos) / 8)).
- f_equal. apply b5_shb_line.
  split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
(* a range of buf is addressable, with its shadow mapped: what every inline check of B5 on buf and every range
   check of memcpy / trim asks *)
Lemma b5_addr_buf : forall v pos lyc Sc Wc rX memc mdc q n, pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  b5_buf v pos <= q -> 0 <= n -> q + n <= b5_buf v pos + 512 -> sa_addr (rdW Wc memc) q n.
Proof.
intros v pos lyc Sc Wc rX memc mdc q n HB Hq Hn Hqn.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & _).
pose proof HG as (_ & _ & _ & _ & _ & _ & H1 & H2 & H4 & H3 & _).
pose proof (b5_F8 v pos HG) as HF8.
pose proof alloc_ceiling_lt as HC.
unfold b5_buf, PF_O_BUF in Hq, Hqn.
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia]. destruct H3 as [H3 | H3]; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply (b5_sh_at v pos lyc Sc Wc rX memc mdc x HB). unfold b5_buf, PF_O_BUF. lia.
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
  { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
  { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
  assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  rewrite (HFSH (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.
(* a range of buf lies in the live class-5 side-stack frame *)
Lemma b5_fframe_buf : forall v pos lyc Sc Wc rX memc mdc sc q n, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  b5_buf v pos <= q -> 0 <= n -> q + n <= b5_buf v pos + 512 -> sa_fframe lyc Sc q n.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc q n HB Hq Hn Hqn.
pose proof HB as (HCX & HFI & _).
destruct (b5_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & _).
exists 5, pos. split; [exact Hin|]. split; [lia|].
rewrite EF. change (fs_frame_bytes 5) with 2048. unfold b5_buf, PF_O_BUF in Hq, Hqn. lia.
Qed.

(* ======================= the line ======================= *)
Lemma b5_post_step : forall v cf cur nm o ln, (o < length (p_s v))%nat ->
  b5_post B v cf cur nm o ln = pf_postm B v (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) o ln.
Proof.
intros v cf cur nm o ln H. unfold b5_post, pf_postm. rewrite (r_lines_skipn_step (p_s v) o (cf, cur, nm) ln H).
reflexivity.
Qed.
Lemma b5_mid : forall n v pos rd cf cur nm o ln d, ~ In 0 (p_s v) -> b5_ln n v pos rd cf cur nm o ln d ->
  pf_mid v o ln (d ++ [pf_line (p_s v) o]) n.
Proof.
intros n v pos rd cf cur nm o ln d Hn (Hl & Ho & Hk & _). unfold pf_mid.
split; [exact Ho|]. split; [exact Hk|]. exact (pf_lctx_next _ _ _ _ Hn Hl Ho).
Qed.
End x.
End d.
