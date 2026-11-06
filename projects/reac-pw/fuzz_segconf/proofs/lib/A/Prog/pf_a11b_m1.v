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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 530 of its 580 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the kit of the MISS piece of segment A11b of
   reac_segconf_parse_file's walk (MISS 0x885a8 -> KLOOP 0x8865c; lib/A/Prog/pf_a11b_m.v proves the segment
   piece pfm_miss_ok from it). Part of segment A11b's proof, by the G3 walk owner, 2026-10-30.

   WHAT THE PIECE WRITES (pfm_Wr): the walk's own stack window below s1 + 0x20 (slot 0x18 at 0x885a8, and the
   16-byte window of reac_box_catalogue below s1), the frame's shadow cells 0x64..0x81 and 0x8a (the 31
   `sb zero, X(s11)` at 0x885ac..0x88624: known[240] and ntok come into scope) and the 8 bytes of ntok at
   F + 0x450 (`sd zero, 0(s3)` at 0x8862c, then the callee's store of 11).
   The keep lemmas below are lib/A/Prog/pf_a5_k.v's (segment A5's proof, base 385fd095481f) restated over pfm_Wr, with
   their proofs; the stack-protector cells and the read-only window are kept because they lie in the image
   range [0x10000, kImgEnd), which holds no frame byte (pfm_img_far, from AR's ledger, pa_img_cover and
   al_client_img, as lib/A/Prog/pf_a2_g.v's pa2_geo), so no SSPX and no VRO hypothesis is taken.
   pfm_move is pf_a5_k.v's a5_move over pfm_Wr, with the frame's shadow at the new state as a premise, so the
   scope may change (PF_SC_L146 at MISS, PF_SC_KN after the 31 stores).
   The closed call-site lemma of VERIFY rule 1j-bis, reac_box_catalogue_site_ok, is here: from the cut state at
   0x88634 (pf_base at known's scope PF_SC_KN, a0 = F + 0x450) it gives every premise of
   reac_box_catalogue_contract but afn_pre (which PaNoChain.cl_callS_wide builds).
   The two symbolic seeds: pfm_seed1 at MISS (the plain executor: the run stores into the shadow band), with
   the slot region on s1 (slot 0x18 written, slot 0x70 read: the extra atom 32 = F + 0x450), two shadow regions
   on s11 (cells 0x64..0x81 and 0x8a, empty chunk lists) and the ntok region on atom 32; pfm_seed2 at the
   catalogue's return 0x88638, ntok read-only on s3 (= 11, the callee's post). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  reac_box_catalogue_c pf_pieces pf_a5_k pf_a11b_d pf_a11b_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= small facts ======================= *)
Lemma pfm_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma pfm_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pfm_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pfm_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pfm_bvr' : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma pfm_hull_rng : forall q n s, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64.
Proof.
intros q n s H0 H1 Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma pfm_div8 : forall x q, 8 * q <= x < 8 * q + 8 -> x / 8 = q.
Proof. intros x q H. symmetry. apply Z.div_unique with (r := x - 8 * q); lia. Qed.
Ltac pfm_in := solve [cbn [In app]; repeat first [left; reflexivity | right]].

(* the cells known's scope writes: 0x64..0x81 and 0x8a *)
Definition pfm_wcell (i : Z) : bool := ((0x64 <=? i) && (i <? 0x82)) || (i =? 0x8a).
Lemma pfm_wcell_spec : forall i, pfm_wcell i = true <-> (0x64 <= i < 0x82 \/ i = 0x8a).
Proof.
intros i. unfold pfm_wcell. rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, Z.eqb_eq. tauto.
Qed.
(* known's scope against low146's, cell by cell (pf_pieces.v's pf_shb) *)
Lemma pfm_shb_kn : forall i, 0 <= i < 144 ->
  (if pfm_wcell i then pf_shb PF_SC_KN i =? 0 else pf_shb PF_SC_KN i =? pf_shb PF_SC_L146 i) = true.
Proof.
intros i Hi.
apply (pfm_zrange (fun i => if pfm_wcell i then pf_shb PF_SC_KN i =? 0 else pf_shb PF_SC_KN i =? pf_shb PF_SC_L146 i)
  0 144); [vm_compute; reflexivity | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ======================= the write set ======================= *)
Definition pfm_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v + 0x20) \/
  (pf_SH v pos + 0x64 <= a < pf_SH v pos + 0x82) \/ a = pf_SH v pos + 0x8a \/
  (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8).
(* a byte below alloc_ceiling, outside the frame and outside the shadow band, is not one (pf_a5_k.v's a5_out) *)
Lemma pfm_out : forall v pos a, a5_G v pos -> a < alloc_ceiling -> ~ (pf_F v pos <= a < pf_F v pos + 2048) ->
  ~ (kLowMemEnd <= a < kHighShadowEnd) -> ~ pfm_Wr v pos a.
Proof.
intros v pos a G Hc Hf Hs W. pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold pfm_Wr, PF_O_NTOK in W. rewrite SPF in G1, W.
destruct W as [W | [W | [W | W]]]; lia.
Qed.
(* a byte of the frame other than ntok's *)
Lemma pfm_frame_out : forall v pos a, a5_G v pos -> pf_F v pos <= a < pf_F v pos + 2048 ->
  ~ (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8) -> 0 <= a < 2 ^ 64 /\ ~ pfm_Wr v pos a.
Proof.
intros v pos a G Ha Hn. pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
split; [lia|]. unfold pfm_Wr, PF_O_NTOK in *. rewrite SPF in G1 |- *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; lia.
Qed.
(* a cell of the frame's shadow other than the 31 known's scope writes *)
Lemma pfm_cell_out : forall v pos i, a5_G v pos -> 0 <= i < 256 -> ~ (0x64 <= i < 0x82 \/ i = 0x8a) ->
  0 <= pf_SH v pos + i < 2 ^ 64 /\ ~ pfm_Wr v pos (pf_SH v pos + i).
Proof.
intros v pos i G Hi Hn. pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold kLowMemEnd, kHighShadowEnd in *.
split; [lia|]. unfold pfm_Wr, PF_O_NTOK. rewrite SPF in G1 |- *.
intros [W | [W | [W | W]]]; [lia | apply Hn; lia | apply Hn; lia | lia].
Qed.
(* the stack slots s1 + 0x20 .. s1 + 0xc0 and the saved registers *)
Lemma pfm_stack_out : forall v pos a, a5_G v pos -> pf_s1 v + 0x20 <= a < pf_sp0 v ->
  0 <= a < 2 ^ 64 /\ ~ pfm_Wr v pos a.
Proof.
intros v pos a G Ha. pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold kLowMemEnd, kHighShadowEnd in *.
split; [lia|]. unfold pfm_Wr, PF_O_NTOK. rewrite SPF in G1 |- *.
intros [W | [W | [W | W]]]; lia.
Qed.

(* ======================= pf_shb cells after known's scope ======================= *)
Lemma pfm_fsh_kn : forall v pos (rd rd' : reader), a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rd' a = rd a) ->
  (forall i, 0x64 <= i < 0x82 \/ i = 0x8a -> rd' (pf_SH v pos + i) = Some 0) ->
  pf_fsh rd (pf_SH v pos) PF_SC_L146 -> pf_fsh rd' (pf_SH v pos) PF_SC_KN.
Proof.
intros v pos rd rd' G HK HW H i Hi. pose proof (pfm_shb_kn i Hi) as Hb.
destruct (pfm_wcell i) eqn:Ew; apply Z.eqb_eq in Hb; rewrite Hb.
- apply HW. apply pfm_wcell_spec. exact Ew.
- assert (Hn : ~ (0x64 <= i < 0x82 \/ i = 0x8a)) by (rewrite <- pfm_wcell_spec, Ew; discriminate).
  destruct (pfm_cell_out v pos i G ltac:(lia) Hn) as (H0 & H1).
  rewrite (HK _ H0 H1). exact (H i Hi).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the image range holds no frame byte (lib/A/Prog/pf_a2_g.v's pa2_geo, last clause) *)
Lemma pfm_img_far : forall lyc Sc (Wc : world SEGS) memc mdc pos a, AR SEGS B lyc Sc Wc memc mdc ->
  In (5, pos) (frames Sc) -> 0x10000 <= a < kImgEnd -> ~ (frame_addr lyc 5 pos <= a < frame_addr lyc 5 pos + 2048).
Proof.
intros lyc Sc Wc memc mdc pos a HAR Hin Ha Hf.
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma pfm_low_out : forall v pos lyc Sc (Wc : world SEGS) memc mdc a, a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc ->
  In (5, pos) (frames Sc) -> lyc = p_ly v -> 0x10000 <= a < kImgEnd -> 0 <= a < 2 ^ 64 /\ ~ pfm_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Ha. subst lyc.
pose proof (pfm_img_far _ _ _ _ _ pos a HAR Hin Ha) as Hf. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hf.
pose proof asan_consts as (C1 & _).
split; [unfold kImgEnd in Ha; lia|].
apply (pfm_out v pos a G); [unfold kImgEnd in Ha; lia | exact Hf | unfold kImgEnd, kLowMemEnd in *; lia].
Qed.

(* ======================= what the piece keeps (pf_a5_k.v's lemmas over pfm_Wr) ======================= *)
Lemma pfm_heap_out : forall v pos lyc Sc Wc memc mdc b m a,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ pfm_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc b m a G HAR Hin Hly Hb Ha. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
apply (pfm_out v pos a G); [lia | lia |].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
Lemma pfm_heap_shadow_out : forall v pos lyc Sc Wc memc mdc b m x,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ pfm_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF.
assert (MF : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, G9.
unfold pfm_Wr, PF_O_NTOK. rewrite SPF in *. rewrite G10. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
intros [W | [W | [W | W]]]; lia.
Qed.
Lemma pfm_heap_tail_out : forall v pos lyc Sc Wc memc mdc b m e x,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= e < b + req_size m -> e < x < e - e mod 8 + 8 -> ~ pfm_Wr v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m e x G HAR Hin Hly Hb He Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof (alloc_ceiling_value) as (_ & AC4).
pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as DA.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & G8 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF.
apply (pfm_out v pos x G).
- lia.
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
Lemma pfm_img_out : forall v pos lyc Sc Wc memc mdc a,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  in_img SEGS a -> ~ pfm_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Hi.
pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
exact (proj2 (pfm_low_out v pos lyc Sc Wc memc mdc a G HAR Hin Hly ltac:(unfold kImgEnd; lia))).
Qed.

(* the keep premise every lemma below takes: rd' agrees with the state's reader off pfm_Wr *)
Section k.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (Wc' : world SEGS) (memc' : word -> option byte).
#[local] Notation rd' := (rdW Wc' memc').
Hypothesis G : a5_G v pos.
Hypothesis HAR : AR SEGS B lyc Sc Wc memc mdc.
Hypothesis Hin : In (5, pos) (frames Sc).
Hypothesis Hly : lyc = p_ly v.
Hypothesis HK : forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rd' a = rdW Wc memc a.
Hypothesis HV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rd' a <> None.

Lemma pfm_keep_addr : forall q n, sa_heap B lyc Sc q n -> sa_addr (rdW Wc memc) q n -> sa_addr rd' q n.
Proof.
intros q n (b & m & Hb & H1 & H2) (A0 & A1 & A2 & A3 & A4).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs | |].
  + pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia.
  + exact (pfm_heap_shadow_out v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb ltac:(lia)).
- intros Hn s Hs. apply HV; [exact (pfm_hull_rng q n s A0 A1 Hn Hs) | exact (A4 Hn s Hs)].
Qed.
Lemma pfm_keep_hstr : forall q s, sa_heap B lyc Sc q (Z.of_nat (length s) + 1) -> sa_str (rdW Wc memc) q s ->
  sa_str rd' q s.
Proof.
intros q s (b & m & Hb & H1 & H2) ((Hz & Hn) & Ht).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |].
  refine (pfm_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). lia.
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht x Hx) | lia |].
  exact (pfm_heap_tail_out v pos lyc Sc Wc memc mdc b m (q + Z.of_nat (length s)) x G HAR Hin Hly Hb ltac:(lia) Hx).
Qed.
Lemma pfm_keep_lit : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
rewrite HK; [exact (Hz i Hi') | lia | exact (pfm_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Himg)].
Qed.
Lemma pfm_keep_low_word : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword rd' a = rdword (rdW Wc memc) a.
Proof.
intros a H1 H2. apply rdword_ext. intros k Hk.
destruct (pfm_low_out v pos lyc Sc Wc memc mdc (a + k) G HAR Hin Hly ltac:(lia)) as (H0 & Hn).
exact (HK _ H0 Hn).
Qed.
Lemma pfm_keep_cat : sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B rd' catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pfm_keep_lit tp _ Hl)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite pfm_keep_low_word; [exact Htp | |]; unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA, kImgEnd; lia.
Qed.
Lemma pfm_keep_rod : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ Hi) as Hrg. unfold kImgEnd in *. lia.
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia. }
destruct (pfm_low_out v pos lyc Sc Wc memc mdc a G HAR Hin Hly Hlow) as (H0 & Hn).
rewrite (HK _ H0 Hn). exact (HR a Hro Ho He).
Qed.
Lemma pfm_keep_ssp : sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
split; [rewrite pfm_keep_low_word; [exact G1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite pfm_keep_low_word; [exact G2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
Lemma pfm_keep_obj : pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof.
intros (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (pfm_keep_hstr _ _ T3 T1)|]. split; [exact (pfm_keep_addr _ _ T3 T2)|]. split; [exact T3|].
split; [exact (pfm_keep_addr _ _ C2 C1)|]. split; [exact C2|]. split; [exact (pfm_keep_cat CA)|].
split; [intros x Hx; exact (pfm_keep_lit _ _ (LI x Hx))|]. split; [exact (pfm_keep_rod RO) | exact (pfm_keep_ssp SS)].
Qed.
(* c's bytes and cur_name *)
Lemma pfm_keep_st : forall cf cur nm k, sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros cf cur nm k (b & m & Hb & H1 & H2) ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (AC1 & _).
split; [|split; [exact HC|split; [|exact HN]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  refine (pfm_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). unfold seg_spec.SEG_C_SIZE in *. lia.
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  destruct (pfm_frame_out v pos (pf_F v pos + PF_O_CN + Z.of_nat i) G ltac:(unfold PF_O_CN; lia)
    ltac:(unfold PF_O_CN, PF_O_NTOK; lia)) as (H0 & Hn).
  rewrite (HK _ H0 Hn). exact (Hf i Hi).
Qed.
(* a C string in buf (the value of the key line) *)
Lemma pfm_keep_bstr : forall p s, pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str (rdW Wc memc) p s -> sa_str rd' p s.
Proof.
intros p s Hb ((Hz & Hn) & Ht). unfold pf_inb, PF_O_BUF in Hb.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof asan_consts as (AC1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  destruct (pfm_frame_out v pos (p + Z.of_nat i) G ltac:(lia) ltac:(unfold PF_O_NTOK; lia)) as (H0 & Hn').
  rewrite (HK _ H0 Hn'). exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  apply HV; [lia | exact (Ht x Hx)].
Qed.
End k.

(* the stack slots, the saved registers, the flag word *)
Lemma pfm_keep_sl : forall v pos (rd rd' : reader) (L : list (Z * Z)), a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rd' a = rd a) ->
  Forall (fun ov => 0x20 <= fst ov <= 0xb8) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' L G HK HL H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov. specialize (H _ Hov). specialize (HL _ Hov).
cbn [fst snd] in *. rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk.
destruct (pfm_stack_out v pos (pf_s1 v + off + k) G ltac:(lia)) as (H0 & Hn). exact (HK _ H0 Hn).
Qed.
Lemma pfm_SL_rng : forall v pos, Forall (fun ov => 0x20 <= fst ov <= 0xb8) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. Qed.
Lemma pfm_keep_saved : forall v pos (rd rd' : reader) regs, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs G HK H j r Hj.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite rdword_ext with (rd := rd); [exact (H j r Hj)|]. intros k Hk.
destruct (pfm_stack_out v pos (pf_sp0 v - 8 - 8 * Z.of_nat j + k) G ltac:(lia)) as (H0 & Hn). exact (HK _ H0 Hn).
Qed.
Lemma pfm_keep_flag : forall v pos (rd rd' : reader) x, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos rd rd' x G HK H.
change (fs_frame_bytes 5) with 2048 in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk.
destruct (pfm_frame_out v pos (pf_F v pos + 2048 - 8 + k) G ltac:(lia) ltac:(unfold PF_O_NTOK; lia)) as (H0 & Hn).
exact (HK _ H0 Hn).
Qed.

(* ======================= the cut state after a step ======================= *)
(* pf_a5_k.v's a5_move over pfm_Wr: the frame's shadow at the new state is a premise, so the scope may change *)
Lemma pfm_move : forall v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B v) -> sa_frm0 ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm HK HV HRG HFRM HFSH.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & _ & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply a5_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (pfm_keep_saved v pos _ _ _ G HK HSV)|].
  split; [exact (pfm_keep_flag v pos _ _ _ G HK HFL)|].
  split; [exact HFRM | exact HRG]. }
split.
{ pose proof (pfm_keep_obj v pos lyc Sc Wc memc mdc Wc' memc' G HAR Hin Hly HK HV HOBJ)
    as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (pfm_keep_sl v pos _ _ _ G HK (pfm_SL_rng v pos) HSL) | exact HFSH].
Qed.

(* ======================= the call site 0x88634 (VERIFY rule 1j-bis) ======================= *)
(* reac_box_catalogue (count pointer a0 = s3 = F + 0x450, &ntok): from the cut state at the jal (known and ntok
   in scope, PF_SC_KN, so ntok's shadow cell 0x8a is 0), every premise of reac_box_catalogue_contract but
   afn_pre: the count pointer and its bounds, its alignment, its addressability (one granule, shadow 0, the
   frame's shadow word mapped) and where it lies (sa_dst's first arm: the caller's own class-5 frame), and the
   event budget (the walk spent none). *)
Lemma reac_box_catalogue_site_ok : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KN ->
  getr rX 10 = w64 (pf_F v pos + PF_O_NTOK) ->
  getr rX 10 = w64 (pf_F v pos + PF_O_NTOK) /\ 0 <= pf_F v pos + PF_O_NTOK < 2 ^ 64 /\
  (pf_F v pos + PF_O_NTOK = 0 \/
   ((pf_F v pos + PF_O_NTOK) mod 8 = 0 /\ sa_addr (rdW Wc memc) (pf_F v pos + PF_O_NTOK) 8 /\
    sa_dst SEGS B lyc Sc Wc memc rX (pf_F v pos + PF_O_NTOK) 8)) /\
  st_nev Sc + EV_reac_box_catalogue <= EV_MAX.
Proof.
intros v pos lyc Sc Wc rX memc mdc HB H10.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & _).
destruct HB as (HCX & HFI & _ & _ & HFSH).
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
destruct HFI as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (MF : pf_F v pos mod 8 = 0).
{ pose proof G8 as G8'. apply Z.mod_divide in G8'; [|lia]. destruct G8' as [k Hk]. rewrite Hk.
  replace (k * 32) with ((4 * k) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite MF, Z.add_0_r in DF.
set (c := pf_F v pos + PF_O_NTOK) in *.
assert (Ec : c = 8 * (pf_F v pos / 8 + 0x8a)) by (subst c; unfold PF_O_NTOK; lia).
assert (Hsh : forall x, c <= x < c + 8 -> shadow_of_addr SHADOW_OFF x = pf_SH v pos + 0x8a).
{ intros x Hx. unfold shadow_of_addr. rewrite G10.
  assert (x / 8 = pf_F v pos / 8 + 0x8a) by (apply pfm_div8; lia). lia. }
assert (Hcell : rdW Wc memc (pf_SH v pos + 0x8a) = Some 0).
{ rewrite (HFSH 0x8a ltac:(lia)). vm_compute. reflexivity. }
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF c 8).
{ intros x Hx. exists 0. split; [rewrite (Hsh x Hx); exact Hcell | left; reflexivity]. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
split; [exact H10|]. split; [subst c; unfold PF_O_NTOK; lia|].
split.
- right. split; [rewrite Ec; rewrite Z.mul_comm; apply Z_mod_mult|].
  split.
  + split; [subst c; unfold PF_O_NTOK; lia|]. split; [subst c; unfold PF_O_NTOK; lia|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; subst c; unfold PF_O_NTOK; lia|].
    split; [exact HRA|].
    intros _ s Hs. apply (aview_some_of_apresent SEGS).
    unfold shadow_addr in Hs.
    assert (E1 : c / 8 = pf_F v pos / 8 + 0x8a) by (apply pfm_div8; lia).
    assert (E2 : (c + 8 - 1) / 8 = pf_F v pos / 8 + 0x8a) by (apply pfm_div8; lia).
    rewrite E1, E2 in Hs. replace (SHADOW_OFF + (pf_F v pos / 8 + 0x8a)) with (pf_SH v pos + 0x8a) in Hs by lia.
    pose proof (Z.div_mod (pf_SH v pos + 0x8a) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (pf_SH v pos + 0x8a) 8 ltac:(lia)).
    replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia. apply Hshp. lia.
  + left. split; [|exact HRA]. exists 5, pos. split; [exact Hin|]. split; [lia|]. subst lyc.
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
    subst c. unfold PF_O_NTOK. lia.
- unfold EV_reac_box_catalogue. unfold EV_reac_segconf_parse_file in HEV. lia.
Qed.

(* ======================= the two symbolic seeds ======================= *)
(* at MISS (0x885a8): the slot region on s1 (slot 0x18 written, slot 0x70 = F + 0x450 read as the extra atom 32),
   the shadow cells 0x64..0x81 and 0x8a on s11 (written), ntok on atom 32 (written) *)
Definition pfm_ss1 : sstate := mkSS PF_MISS sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x18 0x78 0x18 0x20 [YP09.mkChunk 0x70 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 27%nat) 0x64 0x82 0x64 0x82 [];
   YP09.mkRegion (Some 27%nat) 0x8a 0x8b 0x8a 0x8b [];
   YP09.mkRegion (Some 32%nat) 0 8 0 8 []] None (mkFacts [] [] []).
Definition pfm_E1 (v : pfv) (pos : Z) (rX : bvmap 5 word) : env := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)]).
Lemma pfm_seed1 : forall v pos lyc Sc Wc rX memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> pf_rg rX [(27, pf_SH v pos)] ->
  st_ok_pi SEGS VAL (pfm_E1 v pos rX) pfm_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_MISS)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB H27.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFR.
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct HB as (_ & HFI & _ & HSL & _).
destruct HFI as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite SPF in Hpres, G1.
assert (W70 : rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some (pf_F v pos + PF_O_NTOK)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL. exact (HSL (0x70, pf_F v pos + PF_O_NTOK) ltac:(unfold PF_SL; pfm_in)). }
set (E := pfm_E1 v pos rX).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; unfold pfm_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (pf_F v pos + PF_O_NTOK))
  by (subst E; unfold pfm_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 9 _ HFR); unfold a5_FI; pfm_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)) by (apply (a5_rg_get rX _ 27 _ H27); pfm_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (HSH0 : 0 <= pf_SH v pos < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in G11, G12; lia).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; exact HSH0).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold PF_O_NTOK; lia).
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
rewrite restrict_mkst_fx. unfold pfm_ss1. apply pa_entry_st_ok_full.
- subst E. unfold pfm_E1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x70 8 (SOff 32 0) (pf_F v pos + PF_O_NTOK)).
      -- apply pfm_den_off with (k := 0) in E32; [rewrite Z.add_0_r in E32; exact E32 | unfold PF_O_NTOK; lia].
      -- unfold PF_O_NTOK. lia.
      -- lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W70).
  + rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hshp. lia.
  + rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hshp. lia.
  + rewrite U32. split; [unfold PF_O_NTOK; lia|]. split; [unfold PF_O_NTOK; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hfp. unfold PF_O_NTOK. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27, U32.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold PF_O_NTOK.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I].
Qed.

(* at the catalogue's return (0x88638): ntok, read-only on s3 = F + 0x450, holds 11 *)
Definition pfm_ss2 : sstate := mkSS PF_KRET sr_atoms
  [YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))]] None (mkFacts [] [] []).
Lemma pfm_val_of_sa_val : forall H mem a n x, sa_val (aview SEGS H mem) a n x -> val_mem SEGS (mrestrict H mem) a n x.
Proof.
intros H mem a n x Hv k Hk. destruct (aview_byte SEGS H mem (a + Z.of_nat k) _ (Hv k Hk)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b). f_equal. symmetry. exact Hbv.
Qed.
Lemma pfm_seed2 : forall (W : world SEGS) (regs : bvmap 5 word) mem c,
  getr regs (Z_to_bv 5 19) = w64 c -> 0 <= c -> c + 8 <= 2 ^ 64 -> sa_val (rdW W mem) c 8 11 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) pfm_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PF_KRET)) mem (seg_rom SEGS))).
Proof.
intros W regs mem c R19 Hc0 Hc8 Hv.
assert (U19 : bv_unsigned (ew (Eimg (Ereg regs [])) 19) = c)
  by (rewrite (ew_Eimg_Ereg_nat regs [] 19 (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold pfm_ss2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ c 0 8 (SLit 11) 11); [reflexivity | lia | lia |].
  rewrite Z.add_0_r. exact (pfm_val_of_sa_val _ _ _ _ _ Hv).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.

(* ======================= the cut KLOOP at pass 0 ======================= *)
(* the registers at 0x8865c: pf_fi's, s2, s11, PF_RM, then the five 0x88638..0x88658 set *)
Definition pfm_R3 (v : pfv) (pos : Z) (o : nat) (ln : Z) : list (Z * Z) :=
  a5_FI B v ++ [(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln ++
  [(19, 1); (25, 0); (20, SHADOW_OFF + catA / 8); (23, catA); (12, 240)].
(* INV_KLOOP at ti = 0 from INV_MISS and what the piece did: the journal at the new state, the reader kept off
   pfm_Wr (and every mapped byte mapped), the 31 cells now 0, slot 0x18 = vp, ntok = 11 *)
Lemma pfm_assemble : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val S3 (W3 : world SEGS) rX3 mem3 md3,
  INV_MISS B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc S3 W3 mem3 md3 0 ->
  (exists f, S3 = set_fs f Sc) -> Permutation (ablocks B lyc S3) (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rdW W3 mem3 a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW W3 mem3 a <> None) ->
  sa_frm0 ->
  pf_rg rX3 (pfm_R3 v pos o ln) ->
  (forall i, 0x64 <= i < 0x82 \/ i = 0x8a -> rdW W3 mem3 (pf_SH v pos + i) = Some 0) ->
  rdword (rdW W3 mem3) (pf_s1 v + 0x18) = Some vp ->
  sa_val (rdW W3 mem3) (pf_F v pos + PF_O_NTOK) 8 11 ->
  INV_KLOOP B n v pos lyc S3 W3 rX3 mem3 md3 cf nm o ln d gi vp val 0.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val S3 W3 rX3 mem3 md3
  HI HJ3 HS3 HP3 K M HFRM HRG3 HW HW18 HV11.
destruct HI as (HB & HMID & HST & HSTR & HINB & HBT & HSL & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
assert (HC : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (RF : pf_rg rX3 (a5_FI B v)).
{ apply (a5_rg_incl rX3 (pfm_R3 v pos o ln)); [|exact HRG3]. intros x Hx. unfold pfm_R3. apply in_or_app. left. exact Hx. }
split; [exact (pfm_move v pos lyc Sc Wc rX memc mdc PF_SC_L146 S3 W3 rX3 mem3 md3 PF_SC_KN HB HJ3 HS3 HP3 K M RF HFRM
  (pfm_fsh_kn v pos _ _ G K HW HFSH))|].
split; [exact HMID|].
split; [eapply pfm_keep_st; eassumption|].
split; [eapply pfm_keep_bstr; eassumption|].
split; [exact HINB|].
split; [lia|].
split; [exact I|].
split; [exact HV11|].
split.
- unfold pf_sl. apply Forall_cons; [exact HW18|].
  pose proof (pfm_keep_sl v pos _ _ [(0xb0, seg_spec.rseg_addr (p_c v) gi)] G K
    ltac:(apply Forall_cons; [cbn [fst]; lia | apply Forall_nil]) HSL) as H.
  exact H.
- rewrite pf_kn_0. replace (pin_spec.row_addr catA 0) with catA by (unfold pin_spec.row_addr; lia).
  change (Z.of_nat 0 + 1) with 1.
  apply (a5_rg_incl rX3 (pfm_R3 v pos o ln)); [|exact HRG3].
  intros x Hx. unfold pfm_R3, a5_FI, PF_RM in *. cbn [In app] in Hx |- *. tauto.
Qed.

End e.
End f.
End d.
