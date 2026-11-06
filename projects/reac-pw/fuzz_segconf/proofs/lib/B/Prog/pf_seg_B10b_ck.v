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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 199 of its 241 lines of code are new or changed and 411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_b2.v, with its module paths and module names changed; 443 of its 542 lines of code are new or changed and 142 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the helper lemmas of
   piece PB10_C of segment B10b of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B10b_k.v; the five bcmp calls
   0x888e4 .. 0x8895c, INTENT -> ROLEV / BAD). No instruction is walked here. A B10b sub-lane of
   the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's walk, helpers of
   piece PB10_C of segment B10b).
   ADAPTED from a working branch's lib/A/Prog/pf_a10b_b2.v (a sub-lane of a B10b sub-lane, 861a42d8f0c4: the
   cut's facts across a bcmp call, the premises of aj_bcmp_at at a role-word call) and from the B10b segment lane's image-B
   JOIN piece lib/B/Prog/pf_seg_B10b_j.v (961c19ce3f65: b10j_geo, the keep lemmas, the pf_fi form), re-derived on
   image B's frame: B's real frame is 352 bytes (s1 in [sp0 - 368, sp0 - 352]), STK 12832, pf_fi's registers
   sp / gp / tp / s0 / s1 / s4, c in slot 0xc8, cur in slot 0xc0, val in slot 0x70, low = F + 0x280 in s7.
   What the file gives:
   - b10c_geo: the numbers at a cut (b10j_geo's, under this lane's prefix);
   - b10c_kept: a reader kept outside bcmp's window [s1 - 2 ESTACK, s1) (abcmp_realizes's havoc window at sp = s1);
     every object a B10b cut names lies outside it: below alloc_ceiling (the class-5 frame and its shadow, the
     heap blocks, the image) or in the real frame at and above s1 (the 29 spill slots, the 13 saved registers);
   - b10c_move: INV_INTENT carried to a state with the same layout and state, a journal at the new memory, the
     reader kept outside the window and the registers of b10c_RL unchanged (a plain run that stores nothing, or a
     bcmp call: every register of b10c_RL is callee-saved); b10c_to_rolev / b10c_to_bad: INV_ROLEV / INV_BAD from
     INV_INTENT and the role value;
   - b10c_bcmp_pre: every premise of YCbq.aj_bcmp_at for x = low, y = the literal of a role word, n = its length
     plus one, at sp = s1;
   - b10c_bcmp: the bcmp call step at the trampoline (Section hypothesis ABCMP, pf_pieces.v's form): INV_INTENT
     at the return, the callee-saved registers kept, and a0 = 0 exactly when strcmp (r_low val 0 64) w = 0
     (pf_seg_B10b_f.b10b_cmp_lit). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic, registers and small tools (pf_seg_B10b_j.v) ---------- *)
Lemma b10c_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b10c_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b10c_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b10c_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma b10c_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b10c_bvr2 : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Ltac b10c_in := cbn [In app]; repeat first [left; reflexivity | right].
(* the registers a B10b cut names: pf_fi's sp / gp / tp / s0 / s1 / s4, PF_RL's s2 / s5 / s10, PF_RM's s9 / s6,
   and s7 = low (INV_INTENT); all callee-saved *)
Definition b10c_RL : list Z := [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 23].
Lemma b10c_RL_cs : forall r, In r b10c_RL -> acallee_saved r.
Proof. intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr. unfold acallee_saved. lia. Qed.
Lemma b10c_rg_same : forall rX rX' L, (forall r v, In (r, v) L -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L H HL. unfold pf_rg in *. rewrite Forall_forall in *. intros [r v0] Hin. cbn [fst snd] in *.
rewrite (H r v0 Hin). exact (HL (r, v0) Hin).
Qed.
(* the k first role words are not low's string *)
Definition b10c_ne (val : list Z) (k : nat) : Prop :=
  forall j wj, (j < k)%nat -> nth_error PB10_WORDS j = Some wj -> strcmp (r_low val 0 64) wj <> 0.
Lemma b10c_ne0 : forall val, b10c_ne val 0.
Proof. intros val j wj Hj. lia. Qed.
Lemma b10c_ne_step : forall val k w, nth_error PB10_WORDS k = Some w -> b10c_ne val k ->
  strcmp (r_low val 0 64) w <> 0 -> b10c_ne val (S k).
Proof.
intros val k w Hk H Hw j wj Hj Hn. destruct (Nat.eq_dec j k) as [-> | Hne].
- rewrite Hk in Hn. injection Hn as <-. exact Hw.
- apply (H j wj); [lia | exact Hn].
Qed.
Lemma b10c_ne_all : forall val, b10c_ne val 5 -> forall w, In w PB10_WORDS -> strcmp (r_low val 0 64) w <> 0.
Proof.
intros val H w Hw. destruct (In_nth_error _ _ Hw) as (k & Hk).
assert (Hk5 : (k < length PB10_WORDS)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
change (length PB10_WORDS) with 5%nat in Hk5. exact (H k w Hk5 Hk).
Qed.
(* the five role words are literals of parse_file's module, at most 6 bytes long (pf_a10b_b2.v b2_words) *)
Lemma b10c_words : forall w, In w PB10_WORDS -> In w PARSE_FILE_LITS /\ (length w <= 6)%nat.
Proof.
intros w Hw. unfold PB10_WORDS in Hw.
destruct Hw as [<- | [<- | [<- | [<- | [<- | []]]]]];
  (split; [unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In];
           repeat first [left; reflexivity | right]
          | apply Nat.leb_le; vm_compute; reflexivity]).
Qed.
(* a present byte of a byte list / a C string (pf_a10b_b2.v) *)
Lemma b10c_bytes_some : forall (rd : reader) a bs x, sa_bytes rd a bs -> a <= x < a + Z.of_nat (length bs) ->
  rd x <> None.
Proof.
intros rd a bs x H Hx. specialize (H (Z.to_nat (x - a)) ltac:(lia)).
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia. rewrite H. discriminate.
Qed.
Lemma b10c_zs_some : forall (rd : reader) a l x, sa_zs rd a l -> a <= x < a + Z.of_nat (length l) -> rd x <> None.
Proof.
intros rd a l x H Hx. specialize (H (Z.to_nat (x - a)) ltac:(lia)).
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia. rewrite H. discriminate.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Lemma b10c_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ---------- the geometry at a cut (pf_seg_B10b_j.v b10j_geo) ---------- *)
Definition b10c_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b10c_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b10c_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
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
pose proof (b10c_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b10c_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b10c_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b10c_F8 : forall v pos, b10c_geoP v pos -> pf_F v pos mod 8 = 0.
Proof.
intros v pos (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.

(* ---------- the window bcmp may write, and the reader kept outside it ---------- *)
Definition b10c_Wr (v : pfv) (a : Z) : Prop := pf_s1 v - 2 * ESTACK <= a < pf_s1 v.
Definition b10c_kept (v : pfv) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ b10c_Wr v a -> rd' a = rd a.
Lemma b10c_kept_trans : forall v rd1 rd2 rd3, b10c_kept v rd1 rd2 -> b10c_kept v rd2 rd3 -> b10c_kept v rd1 rd3.
Proof. intros v rd1 rd2 rd3 K1 K2 a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn). Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b10c_geoP v pos.
Lemma b10c_lo_nw : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ b10c_Wr v a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
unfold b10c_Wr, ESTACK. lia.
Qed.
Section r.
Variables rd rd' : reader.
Hypothesis K : b10c_kept v rd rd'.
Lemma b10c_k_lo : forall x, 0 <= x < alloc_ceiling -> rd' x = rd x.
Proof. intros x Hx. destruct (b10c_lo_nw x Hx) as (H0 & H1). exact (K x H0 H1). Qed.
Lemma b10c_k_hi : forall x, pf_s1 v <= x < 2 ^ 64 -> rd' x = rd x.
Proof.
intros x Hx. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
apply K; [lia|]. unfold b10c_Wr. lia.
Qed.
Lemma b10c_k_zs : forall p l, 0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l H0 H1 H i Hi. rewrite (b10c_k_lo (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma b10c_k_bytes : forall p l, 0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l H0 H1 H i Hi. rewrite (b10c_k_lo (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma b10c_k_rdword_lo : forall a, 0 <= a -> a + 8 <= alloc_ceiling -> rdword rd' a = rdword rd a.
Proof. intros a H0 H1. apply rdword_ext. intros k Hk. apply b10c_k_lo. lia. Qed.
Lemma b10c_k_rdword_hi : forall a, pf_s1 v <= a -> a + 8 <= 2 ^ 64 -> rdword rd' a = rdword rd a.
Proof. intros a H0 H1. apply rdword_ext. intros k Hk. apply b10c_k_hi. lia. Qed.
Lemma b10c_k_tail : forall e, 0 <= e < alloc_ceiling -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e He H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
pose proof ASAN_CEIL_range as (_ & HM). unfold ASAN_CEIL in HM.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
rewrite (b10c_k_lo x) by lia. exact (H x Hx).
Qed.
Lemma b10c_k_hull : forall q n, 0 <= q -> q + n <= alloc_ceiling -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. rewrite (b10c_k_lo s); [exact (H s Hs)|].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b10c_k_str : forall p s, 0 <= p -> p + Z.of_nat (length s) + 1 <= alloc_ceiling -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s H0 H1 [[Hz Hn] Ht].
split; [split; [|exact Hn] | exact (b10c_k_tail (p + Z.of_nat (length s)) ltac:(lia) Ht)].
apply (b10c_k_zs p (s ++ [0])); [lia | rewrite length_app; cbn [length]; lia | exact Hz].
Qed.
Lemma b10c_k_addr : forall q n, 0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n H0 H1 (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
split; [|intros Hn; exact (b10c_k_hull _ _ H0 H1 Hn (A4 Hn))].
intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b10c_k_lo (SHADOW_OFF + x / 8)); [exact Hs|].
pose proof asan_consts as (C1 & _). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le x 8 ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.
Lemma b10c_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
pose proof (pa_img_range (a + Z.of_nat (length s)) (proj1 (Hi (a + Z.of_nat (length s)) ltac:(lia)))) as He.
pose proof asan_consts as (C1 & _).
apply (b10c_k_str a s); [lia | unfold kImgEnd in *; lia | exact Hs].
Qed.
Lemma b10c_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b10c_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
assert (Hr : forall k, 0 <= k < 8 -> 0x10000 <= pin_spec.row_addr cat i + k < kImgEnd).
{ intros k Hk. apply pa_img_range. apply (proj1 (Hi (pin_spec.row_addr cat i + k) ltac:(unfold pin_spec.row_addr,
    pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia))). }
pose proof (Hr 0 ltac:(lia)) as Hr0. pose proof (Hr 7 ltac:(lia)) as Hr7. pose proof asan_consts as (C1 & _).
rewrite (b10c_k_rdword_lo (pin_spec.row_addr cat i)); [exact Htp | lia | unfold kImgEnd in *; lia].
Qed.
Lemma b10c_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b10c_k_lo a); [exact (H a Hro Ho He)|].
pose proof asan_consts as (C1 & _).
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg). unfold kImgEnd in *. lia.
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in *. lia.
Qed.
Lemma b10c_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2). pose proof asan_consts as (C1 & _).
split; [rewrite (b10c_k_rdword_lo gotwA); [exact G1 | unfold gotwA; lia | unfold gotwA; lia]|].
exists g. rewrite (b10c_k_rdword_lo guardA); [exact G2 | unfold guardA; lia | unfold guardA; lia].
Qed.
(* the real frame: slots at s1 + off, the saved registers at sp0 - 8 - 8 j *)
Lemma b10c_k_sl : forall L, (forall ov, In ov L -> 0 <= fst ov <= 0xd8) -> pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros L HL H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (HL ov Hov) as Ho. pose proof G as (S1 & S2 & S3 & S4 & _).
rewrite (b10c_k_rdword_hi (pf_s1 v + fst ov)); [exact (H ov Hov) | lia | lia].
Qed.
Lemma b10c_k_saved : forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros regs H j r Hj.
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof G as (S1 & S2 & S3 & S4 & _).
rewrite (b10c_k_rdword_hi (pf_sp0 v - 8 - 8 * Z.of_nat j)); [exact (H j r Hj) | lia | lia].
Qed.
(* the class-5 frame: its flag word, cur_name, buf, low, its 144 shadow cells *)
Lemma b10c_k_flag : forall x, rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros x H. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). change (fs_frame_bytes 5) with 2048 in *.
rewrite (b10c_k_rdword_lo (pf_F v pos + 2048 - 8)); [exact H | lia | lia].
Qed.
Lemma b10c_k_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros nm (f & Hb & Henc). exists f. split; [|exact Henc].
pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). destruct Henc as [Hl _].
apply (b10c_k_bytes _ f); [unfold PF_O_CN; lia | rewrite Hl; unfold PF_O_CN; lia | exact Hb].
Qed.
Lemma b10c_k_fsh : forall sc, pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros sc H i Hi. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). pose proof asan_consts as (C1 & _).
rewrite (b10c_k_lo (pf_SH v pos + i)); [exact (H i Hi)|].
pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (pf_F v pos) 8 ltac:(lia)).
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.
Lemma b10c_k_buf : forall p s, pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s [Hb1 Hb2] H. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). unfold PF_O_BUF in *.
apply (b10c_k_str p s); [lia | lia | exact H].
Qed.
Lemma b10c_k_low : forall LB : list byte, length LB = 64%nat ->
  sa_bytes rd (pf_F v pos + PF_O_LOW) LB -> sa_bytes rd' (pf_F v pos + PF_O_LOW) LB.
Proof.
intros LB HL H. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _).
apply (b10c_k_bytes _ LB); [unfold PF_O_LOW; lia | rewrite HL; unfold PF_O_LOW; lia | exact H].
Qed.
End r.
End k.

(* a range inside a live heap block lies below alloc_ceiling *)
Lemma b10c_heap_lo : forall lyc Sc (Wc : world SEGS) memc mdc q n x,
  AR SEGS B lyc Sc Wc memc mdc -> sa_heap B lyc Sc q n -> q <= x < q + n -> 0 <= x < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc q n x HAR (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
Qed.

(* ---------- the cut's facts carried to a kept reader ---------- *)
Lemma b10c_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b10c_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc ->
  b10c_kept v rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : 0 <= p_t v /\ p_t v + pf_len v <= alloc_ceiling).
{ unfold pf_len. pose proof (b10c_heap_lo lyc Sc Wc memc mdc _ _ (p_t v) HAR H3 ltac:(unfold pf_len; lia)).
  pose proof (b10c_heap_lo lyc Sc Wc memc mdc _ _ (p_t v + Z.of_nat (length (p_s v))) HAR H3
    ltac:(unfold pf_len; lia)). lia. }
assert (Hc : 0 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling).
{ pose proof (b10c_heap_lo lyc Sc Wc memc mdc _ _ (p_c v) HAR H5 ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
  pose proof (b10c_heap_lo lyc Sc Wc memc mdc _ _ (p_c v + seg_spec.SEG_C_SIZE - 1) HAR H5
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)). lia. }
split; [apply (b10c_k_str v pos HG rd rd' K); [lia | unfold pf_len in Ht; lia | exact H1]|].
split; [exact (b10c_k_addr v pos HG rd rd' K (p_t v) (pf_len v) ltac:(lia) ltac:(lia) H2)|]. split; [exact H3|].
split; [exact (b10c_k_addr v pos HG rd rd' K (p_c v) seg_spec.SEG_C_SIZE ltac:(lia) ltac:(lia) H4)|]. split; [exact H5|].
split; [exact (b10c_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (b10c_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (b10c_k_rod v pos HG rd rd' K H8) | exact (b10c_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma b10c_keep_st : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf cur nm k,
  b10c_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  b10c_kept v rd rd' -> pf_st v pos rd cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf cur nm k HG HAR Hh K (HRC & HCUR & HNM & HCNT & HC0).
split.
{ destruct HRC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
  intros i Hi. destruct Henc as [Hl _].
  rewrite (b10c_k_lo v pos HG rd rd' K (p_c v + Z.of_nat i)); [exact (Hb i Hi)|].
  apply (b10c_heap_lo lyc Sc Wc memc mdc _ _ _ HAR Hh). lia. }
split; [exact HCUR|]. split; [exact (b10c_k_nm v pos HG rd rd' K nm HNM)|]. split; [exact HCNT|].
pose proof HG as (S1 & S2 & S3 & S4 & _).
rewrite (b10c_k_rdword_hi v pos HG rd rd' K (pf_s1 v + 0xc0)); [exact HC0 | lia | lia].
Qed.

(* ---------- pf_base and INV_INTENT at a new state ---------- *)
Lemma b10c_base_move : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  b10c_kept v (rdW Wc memc) (rdW Wc memc') ->
  (forall r, In r b10c_RL -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc HB HJ' K HR.
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10c_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
destruct HFI as (_ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
  split; [exact (b10c_k_saved v pos HG _ _ K _ HSAV)|].
  split; [exact (b10c_k_flag v pos HG _ _ K _ HFLAG)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [apply (b10c_k_sl v pos HG _ _ K); [intros ov [<- | []]; cbn [fst]; lia | exact HC8]|].
  apply (b10c_rg_same rX rX' _); [|exact HRG0].
  intros r v0 Hin0. apply HR. cbn [In] in Hin0.
  repeat (destruct Hin0 as [Hq | Hin0]; [injection Hq as Hq1 Hq2; subst r; unfold b10c_RL; b10c_in |]).
  destruct Hin0. }
split; [exact (b10c_keep_obj v pos lyc Sc Wc memc mdc _ _ HG HAR K HOBJ)|].
split; [exact (b10c_k_sl v pos HG _ _ K _ (b10c_PF_SL_offs v pos) HSL) | exact (b10c_k_fsh v pos HG _ _ K sc HFSH)].
Qed.
Lemma b10c_move : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc',
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  b10c_kept v (rdW Wc memc) (rdW Wc memc') ->
  (forall r, In r b10c_RL -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  INV_INTENT B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc' HI HJ' K HR.
destruct HI as (HB & HMID & HST & HVS & HVB & (LB & HL & HLB & HLF) & HSL70 & HRG).
pose proof HB as (HCX & HFI & HOBJ & _).
destruct (b10c_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [exact (b10c_base_move v pos lyc Sc Wc rX memc mdc rX' memc' mdc' PF_SC_LOW HB HJ' K HR)|].
split; [exact HMID|].
split; [exact (b10c_keep_st v pos lyc Sc Wc memc mdc _ _ cf (Some gi) nm _ HG HAR HC5 K HST)|].
split; [exact (b10c_k_buf v pos HG _ _ K vp val HVB HVS)|].
split; [exact HVB|].
split; [exists LB; split; [exact HL|]; split; [exact (b10c_k_low v pos HG _ _ K LB HL HLB) | exact HLF]|].
split; [apply (b10c_k_sl v pos HG _ _ K); [intros ov [<- | []]; cbn [fst]; lia | exact HSL70]|].
apply (b10c_rg_same rX rX' _); [|exact HRG].
intros r v0 Hin0. apply HR. unfold PF_RL, PF_RM in Hin0. cbn [In app] in Hin0.
repeat (destruct Hin0 as [Hq | Hin0]; [injection Hq as Hq1 Hq2; subst r; unfold b10c_RL; b10c_in |]).
destruct Hin0.
Qed.
(* ROLEV and BAD from INTENT's facts at the same state *)
Lemma b10c_to_rolev : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  getr rX (Z_to_bv 5 19) = w64 r -> role_intent_parse (r_low val 0 64) = Some r ->
  INV_ROLEV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r HI H19 Hr.
destruct HI as (HB & HMID & HST & _ & _ & _ & _ & HRG).
split; [exact HB|]. split; [exact HMID|]. split; [exact HST|]. split; [exact Hr|].
unfold pf_rg in *. rewrite !Forall_app in *. destruct HRG as (H1 & H2 & _).
split; [exact H1|]. split; [exact H2|]. apply Forall_cons; [cbn [fst snd]; exact H19 | apply Forall_nil].
Qed.
Lemma b10c_to_bad : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  role_intent_parse (r_low val 0 64) = None ->
  INV_BAD B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI Hr.
destruct HI as (HB & HMID & HST & HVS & HVB & _ & HSL70 & HRG).
split; [exact HB|]. split; [exact HMID|]. split; [exact HST|]. split; [exact HVS|]. split; [exact HVB|].
split; [exact HSL70|]. split; [exact Hr|].
unfold pf_rg in *. rewrite !Forall_app in *. destruct HRG as (H1 & H2 & _). split; [exact H1 | exact H2].
Qed.

(* ---------- the premises of YCbq.aj_bcmp_at at a role-word call (pf_a10b_b2.v b_bcmp_pre) ---------- *)
Lemma b10c_bcmp_pre : forall v pos lyc Sc Wc rX memc mdc (LB : list byte) (regsT : bvmap 5 word) (w : list Z),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW ->
  length LB = 64%nat -> sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB ->
  In w PB10_WORDS -> spZ regsT = pf_s1 v ->
  0 <= pf_F v pos + PF_O_LOW /\ pf_F v pos + PF_O_LOW + Z.of_nat (S (length w)) <= 2 ^ 63 /\
  0 <= seg_litA_rc w /\ seg_litA_rc w + Z.of_nat (S (length w)) <= 2 ^ 63 /\
  (pf_s1 v - pf_sp0 v) mod 16 = 0 /\ pf_s1 v - pf_sp0 v <= 0 /\
  2 * ESTACK - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file /\
  src_ok SEGS Wc regsT memc (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  src_ok SEGS Wc regsT memc (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  (forall a, pf_F v pos + PF_O_LOW <= a < pf_F v pos + PF_O_LOW + Z.of_nat (S (length w)) ->
     ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - 2 * ESTACK <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v))) /\
  (forall a, seg_litA_rc w <= a < seg_litA_rc w + Z.of_nat (S (length w)) ->
     ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - 2 * ESTACK <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v))) /\
  amem_range (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  amem_range (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  (0 < Z.of_nat (S (length w)) -> shadow_hull_vis (rdW Wc memc) (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w)))) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  (0 < Z.of_nat (S (length w)) -> shadow_hull_vis (rdW Wc memc) (seg_litA_rc w) (Z.of_nat (S (length w)))) /\
  sa_str (rdW Wc memc) (seg_litA_rc w) w.
Proof.
intros v pos lyc Sc Wc rX memc mdc LB regsT w HB HL HLB Hw Hsp.
destruct HB as (HCX & HFI & HOBJ & _ & HFSH).
destruct (b10c_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
destruct (b10c_words w Hw) as (HwL & Hw6).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & LI & _).
destruct (LI w HwL) as (Hy0 & Hys & Hyp & _ & Hyi).
destruct (Hyp lyc Sc Wc memc mdc HAR) as (P0 & P1 & P2 & P3 & P4).
pose proof (b10c_F8 v pos G) as HF8.
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
assert (Hs16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by (apply b10c_m16; [exact S6 | exact S3]).
assert (Hyimg : forall a, seg_litA_rc w <= a < seg_litA_rc w + (Z.of_nat (length w) + 1) -> a < kImgEnd)
  by (intros a Ha; exact (proj2 (pa_img_range a (proj1 (Hyi a Ha))))).
assert (HSH80 : rdW Wc memc (pf_SH v pos + 80) = Some 0) by (rewrite (HFSH 80 ltac:(lia)); reflexivity).
replace (Z.of_nat (S (length w))) with (Z.of_nat (length w) + 1) by lia.
unfold PF_O_LOW in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact P1|].
split; [exact Hs16|]. split; [lia|]. split; [rewrite SPF; unfold ESTACK; lia|].
split.
{ unfold src_ok. intros a Ha. split.
  - apply (b10c_bytes_some _ _ LB a HLB). rewrite HL. change (Z.of_nat 64) with 64. lia.
  - rewrite Hsp. unfold ESTACK. lia. }
split.
{ unfold src_ok. intros a Ha. split.
  - destruct Hys as ((Hz & _) & _). apply (b10c_zs_some _ _ _ _ Hz). rewrite length_app. cbn [length]. lia.
  - rewrite Hsp. pose proof (Hyimg a Ha). unfold kImgEnd, ESTACK in *. lia. }
split; [intros a Ha; unfold ESTACK; lia|].
split; [intros a Ha; pose proof (Hyimg a Ha); unfold kImgEnd, ESTACK in *; lia|].
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
split; [exact P2|].
split.
{ intros z Hz. exists 0. split; [|left; reflexivity].
  replace z with (pf_F v pos + (z - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (z - pf_F v pos) HF8).
  replace ((z - pf_F v pos) / 8) with 80 by (apply Z.div_unique with (r := z - pf_F v pos - 640); lia).
  exact HSH80. }
split.
{ intros Hn0.
  exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memc mdc 5 pos (pf_F v pos + 640)
    (Z.of_nat (length w) + 1) HAR Hin ltac:(rewrite EF; lia)
    ltac:(rewrite EF; change (fs_frame_bytes 5) with 2048; lia) Hn0). }
split; [exact P3|]. split; [exact P4 | exact Hys].
Qed.

(* ---------- the bcmp call step at the trampoline ---------- *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_bcmp).
Lemma b10c_bcmp : forall n v pos lyc Sc Wc rT memT mdT cf nm o ln d gi vp val (w : list Z) (retk : Z) Q,
  INV_INTENT B n v pos lyc Sc Wc rT memT mdT cf nm o ln d gi vp val ->
  In w PB10_WORDS ->
  getr rT (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW) ->
  getr rT (Z_to_bv 5 11) = w64 (seg_litA_rc w) ->
  getr rT (Z_to_bv 5 12) = w64 (Z.of_nat (S (length w))) ->
  getr rT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     aregs_preserved rT rX2 ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) w = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + retk) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rT memT mdT) Q.
Proof.
intros n v pos lyc Sc Wc rT memT mdT cf nm o ln d gi vp val w retk Q HI Hw R10 R11 R12 R1 Hrk Hrk2 Kc.
pose proof HI as (HB & _ & _ & _ & _ & (LB & HL & HLB & HLF) & _).
pose proof HB as (HCX & HFI & _).
destruct (b10c_geo v pos lyc Sc Wc rT memT mdT HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof asan_consts as (C1 & _).
destruct (b10c_words w Hw) as (_ & Hw6).
assert (Rsp : spZ rT = pf_s1 v).
{ unfold spZ. match goal with |- context [getr rT ?r] =>
    rewrite (b10c_bvr rT r 2 _ eq_refl (b10c_rg rT _ 2 _ HRG0 ltac:(b10c_in))) end.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Gsp : spZ rT = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by lia.
assert (G10 : getr rT 10 = w64 (pf_F v pos + PF_O_LOW)) by (apply (b10c_bvr _ _ 10); [reflexivity | exact R10]).
assert (G11 : getr rT 11 = w64 (seg_litA_rc w)) by (apply (b10c_bvr _ _ 11); [reflexivity | exact R11]).
assert (G12 : getr rT 12 = w64 (Z.of_nat (S (length w)))) by (apply (b10c_bvr _ _ 12); [reflexivity | exact R12]).
assert (G1 : getr rT 1 = Z_to_bv 64 (BASE + retk)) by (apply (b10c_bvr _ _ 1); [reflexivity | exact R1]).
assert (G3 : getr rT 3 = w64 (as_gp B)) by (apply (b10c_bvr _ _ 3); [reflexivity | exact (b10c_rg rT _ 3 _ HRG0 ltac:(b10c_in))]).
assert (G4 : getr rT 4 = w64 (as_tp B)) by (apply (b10c_bvr _ _ 4); [reflexivity | exact (b10c_rg rT _ 4 _ HRG0 ltac:(b10c_in))]).
destruct (b10c_bcmp_pre v pos lyc Sc Wc rT memT mdT LB rT w HB HL HLB Hw Rsp)
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & HYS).
unfold cfg_at.
eapply SRr_bind.
{ exact (aj_bcmp_at SEGS B LAWS pa_segs_low (pa_sigma SS___interceptor_trampoline_bcmp) (ABCMP fx) Wc rT memT
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v)
    [(5, pos)] lyc Sc mdT 0 (pf_F v pos + PF_O_LOW) (seg_litA_rc w) (Z.of_nat (S (length w))) (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + retk)) HJ G10 G11 G12 ltac:(lia) P1 P2 P3 P4 Gsp P5 P6 P7 G3 G4 G1
    (ret_ok_codeptr_v retk Hrk Hrk2) P8 P9 P10 P11 P12 P13 P14 P15 P16 P17). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v0 & -> & HJ2 & HP & Hres & Hcmp & Hfr & Hpres2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + retk) regs2 mem2 md2).
assert (K2 : b10c_kept v (rdW Wc memT) (rdW Wc mem2)).
{ intros a Ha Hn. apply (Hfr a Ha). intros Hq. apply Hn. unfold b10c_Wr. lia. }
assert (HR2 : forall r, In r b10c_RL -> getr regs2 (Z_to_bv 5 r) = getr rT (Z_to_bv 5 r))
  by (intros r Hr; exact (HP r (b10c_RL_cs r Hr))).
apply (Kc regs2 mem2 md2).
- exact (b10c_move n v pos lyc Sc Wc rT memT mdT cf nm o ln d gi vp val regs2 mem2 md2 HI HJ2 K2 HR2).
- exact HP.
- lazymatch type of Hres with getr _ ?r = _ => pose proof (b10c_bvr2 regs2 r 10 v0 eq_refl Hres) as E10 end.
  rewrite E10.
  rewrite <- (b10b_cmp_lit (rdW Wc memT) (pf_F v pos + PF_O_LOW) (seg_litA_rc w) LB (r_low val 0 64) w HL HLB HLF
    (b10b_low_nulfree val 0 64) HYS (b10b_words_nulfree w Hw)).
  exact Hcmp.
Qed.
End x.
End d.
