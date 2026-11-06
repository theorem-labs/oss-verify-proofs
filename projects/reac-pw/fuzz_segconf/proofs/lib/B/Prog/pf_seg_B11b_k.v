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
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the kit of segment B11b of
   reac_segconf_parse_file (the B11b segment lane of the image-B G3 walk owner, 2026-10-30). proves no function (kind: transport lemmas).
   ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a5_k.v (commit 385fd095481f, the
   image-A A5 segment lane) and lib/A/Prog/pf_a2_g.v (the image-A A2 segment lane): the same transport, with image B's frame (s1 = (sp0 - 0x160) & -32,
   STK_reac_segconf_parse_file = 12832) and B11b's write set in place of A5's.
   - the geometry of a cut state (pb11_geo), the bytes a B11b step may write (pb11_Wrx), what a step that keeps every
     other byte carries over (the pb11_keep lemmas), and the rebuild of pf_base after a step (pb11_move);
   - the frame shadow after B11b's 31 scope-in stores (PF_SC_L146 -> PF_SC_KNOWN), the register lists, the frame
     chain at a call (the prologue's record on afn_pre's chain), the read-only view.
   B11b WRITES: the callees' windows below s1 (reac_box_catalogue 16 bytes, snprintf CMD_SNP_K = 8192; inside parse
   file's own window [sp0 - 12832, s1)); slots s1 + 0x60 .. 0x70 (0x88b00 / 0x88b08); known[240] at F + 0x320
   (snprintf) and ntok at F + 0x450 (0x88ad0 and reac_box_catalogue); the shadow cells SH + 0x64 .. 0x81 and
   SH + 0x8a (0x88a50 - 0x88ac8). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B11b_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= small arithmetic ======================= *)
Lemma pb11_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma pb11_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.
Lemma pb11_mod32_down : forall x, 0 <= x -> (x - x mod 32) mod 32 = 0 /\ x - 32 < x - x mod 32 <= x.
Proof.
intros x Hx. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M. pose proof (Z.div_mod x 32 ltac:(lia)) as D.
split; [|lia]. replace (x - x mod 32) with ((x / 32) * 32) by lia. apply Z_mod_mult.
Qed.
Lemma pb11_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.

(* ======================= the register lists ======================= *)
Lemma pb11_rg_get : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Lemma pb11_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Lemma pb11_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Lemma pb11_rg_incl : forall rX L1 L2, incl L2 L1 -> pf_rg rX L1 -> pf_rg rX L2.
Proof. intros rX L1 L2 Hi H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin. exact (H rv (Hi rv Hin)). Qed.
(* ======================= the frame's shadow before and after the 31 scope-in stores ======================= *)
(* the cells B11b writes: known's 30 (0x64 .. 0x81) and ntok's (0x8a) *)
Definition pb11_kcell (i : Z) : Prop := (100 <= i < 130) \/ i = 138.
Lemma pb11_shb_out : forall i, 0 <= i < 144 -> ~ pb11_kcell i -> pf_shb PF_SC_KNOWN i = pf_shb PF_SC_L146 i.
Proof.
intros i Hi Hn. unfold pb11_kcell in Hn.
assert (H : forall j, 0 <= j < 144 -> (100 <=? j) && (j <? 130) || (j =? 138) = false ->
  pf_shb PF_SC_KNOWN j =? pf_shb PF_SC_L146 j = true).
{ intros j Hj. revert j Hj.
  assert (G : forallb (fun j => ((100 <=? j) && (j <? 130) || (j =? 138)) || (pf_shb PF_SC_KNOWN j =? pf_shb PF_SC_L146 j))
    (map Z.of_nat (seq 0 144)) = true) by (vm_compute; reflexivity).
  intros j Hj Hf. rewrite forallb_forall in G. specialize (G j). rewrite Hf in G. apply G.
  apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia]. }
apply Z.eqb_eq. apply H; [exact Hi|].
destruct (100 <=? i) eqn:E1; destruct (i <? 130) eqn:E2; destruct (i =? 138) eqn:E3; cbn; try reflexivity;
  exfalso; apply Hn; first [right; apply Z.eqb_eq; exact E3 | left; apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia].
Qed.
Lemma pb11_shb_in : forall i, pb11_kcell i -> pf_shb PF_SC_KNOWN i = 0.
Proof.
intros i [Hi | ->]; [|reflexivity].
apply Z.eqb_eq. revert i Hi. apply (pb11_zrange (fun i => pf_shb PF_SC_KNOWN i =? 0) 100 30). vm_compute. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma pb11_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof. intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma pb11_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof. intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Definition pb11_FI (B : asyms) (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Lemma pb11_FI_cs : forall B v, Forall (fun rv => acallee_saved (fst rv)) (pb11_FI B v).
Proof. intros B v. unfold pb11_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.

(* the numbers every cut state has (pb11_geo): the entry sp0 and s1, the class-5 frame F (2048 bytes, 32-aligned, in
   the application range, off the image) and its shadow SH (256 cells, in the shadow band) *)
Definition pb11_G (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + STK_reac_segconf_parse_file <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 384 < pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  in_app (pf_F v pos) 2048 /\ pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\
  kLowMemEnd <= pf_SH v pos /\ pf_SH v pos + 256 <= kHighShadowEnd /\
  (pf_F v pos + 2048 <= 0x10000 \/ kImgEnd <= pf_F v pos).
(* the bytes a B11b step may write: the callees' windows and parse_file's own below s1; slots 0x60 .. 0x70 (sl);
   known[240] and ntok (kno); the 31 shadow cells of known and ntok (shw) *)
Definition pb11_Wrx (v : pfv) (pos : Z) (sl kno shw : bool) (a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (sl = true /\ pf_s1 v + 0x60 <= a < pf_s1 v + 0x70) \/
  (kno = true /\ (pf_F v pos + PF_O_KNOWN <= a < pf_F v pos + PF_O_KNOWN + 240 \/
                  pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8)) \/
  (shw = true /\ exists i, pb11_kcell i /\ a = pf_SH v pos + i).
Lemma pb11_Wrx_mono : forall v pos sl kno shw a, pb11_Wrx v pos sl kno shw a -> pb11_Wrx v pos true true true a.
Proof.
intros v pos sl kno shw a [H | [(_ & H) | [(_ & H) | (_ & H)]]]; unfold pb11_Wrx;
  [left | right; left | right; right; left | right; right; right]; auto.
Qed.
(* a byte below alloc_ceiling, outside the frame and outside the shadow band, is none of them *)
Lemma pb11_out : forall v pos a, pb11_G v pos -> a < alloc_ceiling -> ~ (pf_F v pos <= a < pf_F v pos + 2048) ->
  ~ (kLowMemEnd <= a < kHighShadowEnd) -> ~ pb11_Wrx v pos true true true a.
Proof.
intros v pos a G Hc Hf Hs W. pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK in W. rewrite SPF in G1, W.
destruct W as [W | [W | [W | W]]].
- lia.
- destruct W as [_ W]. lia.
- destruct W as [_ W]. lia.
- destruct W as [_ (i & Hi & ->)]. unfold pb11_kcell in Hi. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma pb11_fi_regs : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_rg rX (pb11_FI B v).
Proof. intros v pos lyc Sc Wc rX memc mdc sc (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma pb11_geo : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\ In (5, pos) (frames Sc) /\ pb11_G v pos /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & _).
destruct HFI as (HJ & Hly & _).
destruct HCX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
subst lyc.
destruct (al_frames _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & Hfb & Hsh).
destruct (frames_bounds SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (frm_off_imgP B (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as Hoff.
change (fs_frame_bytes 5) with 2048 in *. change (2048 / 8) with 256 in Hsh.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *. rewrite SPF in *.
split; [exact HAR|]. split; [reflexivity|]. split; [exact Hin|].
split.
- unfold pb11_G. rewrite SPF.
  pose proof (pb11_mod32_down (pf_sp0 v - 0x160) ltac:(lia)) as (M1 & M2).
  assert (Hs1 : pf_s1 v = pf_sp0 v - 0x160 - (pf_sp0 v - 0x160) mod 32) by reflexivity.
  assert (ESH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
  pose proof Happ as Happ0.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  assert (Hq0 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : (pf_F v pos + 2048) / 8 = pf_F v pos / 8 + 256).
  { replace (pf_F v pos + 2048) with (pf_F v pos + 256 * 8) by lia. apply Z.div_add. lia. }
  assert (Hq3 : (pf_F v pos + 2048) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (Hq4 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in Hq4.
  unfold off_img in Hoff.
  rewrite ESH. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF, kImgEnd.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [rewrite Hs1; lia|].
  split; [rewrite Hs1; exact M1|]. split; [lia|]. split; [lia|]. split; [exact H32|].
  split; [exact Happ0|]. split; [reflexivity|]. split; [lia|]. split; lia.
- split; [exact (fun a Ha => proj1 (Hfb a Ha))|]. intros i Hi. exact (proj1 (Hsh i Hi)).
Qed.

(* ======================= what a B11b step keeps ======================= *)
Lemma pb11_heap_out : forall v pos lyc Sc Wc memc mdc b m a,
  pb11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ pb11_Wrx v pos true true true a.
Proof.
intros v pos lyc Sc Wc memc mdc b m a G HAR Hin Hly Hb Ha. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
apply (pb11_out v pos a G); [lia | lia |].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
(* the shadow cell of a heap byte *)
Lemma pb11_heap_shadow_out : forall v pos lyc Sc Wc memc mdc b m x,
  pb11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ pb11_Wrx v pos true true true (SHADOW_OFF + x / 8).
Proof.
intros v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF.
assert (MF : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, G9.
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. rewrite G10. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
intros [W | [W | [W | W]]].
- lia.
- destruct W as [_ W]. lia.
- destruct W as [_ W]. lia.
- destruct W as [_ (i & Hi & Ha)]. unfold pb11_kcell in Hi. lia.
Qed.
(* a byte after a heap string's NUL in the NUL's granule *)
Lemma pb11_heap_tail_out : forall v pos lyc Sc Wc memc mdc b m e x,
  pb11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= e < b + req_size m -> e < x < e - e mod 8 + 8 -> ~ pb11_Wrx v pos true true true x.
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
apply (pb11_out v pos x G).
- lia.
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
(* an image byte *)
Lemma pb11_img_out : forall v pos lyc Sc Wc memc mdc a,
  pb11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  in_img SEGS a -> ~ pb11_Wrx v pos true true true a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Hi. subst lyc.
pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
pose proof (frm_img SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos a HAR Hin) as Hf.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hf. change (fs_frame_bytes 5) with 2048 in Hf.
pose proof asan_consts as (C1 & _).
apply (pb11_out v pos a G); [lia | intros Ha; exact (Hf Ha Hi) | unfold kLowMemEnd; lia].
Qed.
(* an address of the image's range [0x10000, kImgEnd) (the stack-protector cells) *)
Lemma pb11_imgrange_out : forall v pos a, pb11_G v pos -> 0x10000 <= a < kImgEnd -> ~ pb11_Wrx v pos true true true a.
Proof.
intros v pos a G Ha. pose proof asan_consts as (C1 & _).
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13).
apply (pb11_out v pos a G); [unfold kImgEnd in *; lia | unfold kImgEnd in *; lia | unfold kLowMemEnd, kImgEnd in *; lia].
Qed.
Lemma pb11_ro_img_range : forall a, in_roP SEGS RLO_A RHI_A a -> 0x10000 <= a < kImgEnd.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr].
- pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as H. exact H.
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.

(* the keep premise every lemma below takes: rd' agrees with the state's reader off the B11b writes *)
Section k.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (Wc' : world SEGS) (memc' : word -> option byte).
#[local] Notation rd' := (rdW Wc' memc').
Hypothesis G : pb11_G v pos.
Hypothesis HAR : AR SEGS B lyc Sc Wc memc mdc.
Hypothesis Hin : In (5, pos) (frames Sc).
Hypothesis Hly : lyc = p_ly v.
Hypothesis HK : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rd' a = rdW Wc memc a.
Hypothesis HV : forall a, rdW Wc memc a <> None -> rd' a <> None.

Lemma pb11_keep_addr : forall q n, sa_heap B lyc Sc q n -> sa_addr (rdW Wc memc) q n -> sa_addr rd' q n.
Proof.
intros q n (b & m & Hb & H1 & H2) (A0 & A1 & A2 & A3 & A4).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs | |].
  + pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia.
  + exact (pb11_heap_shadow_out v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb ltac:(lia)).
- intros Hn s Hs. apply HV. exact (A4 Hn s Hs).
Qed.
Lemma pb11_keep_hstr : forall q s, sa_heap B lyc Sc q (Z.of_nat (length s) + 1) -> sa_str (rdW Wc memc) q s ->
  sa_str rd' q s.
Proof.
intros q s (b & m & Hb & H1 & H2) ((Hz & Hn) & Ht).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |].
  refine (pb11_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). lia.
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht x Hx) | lia |].
  exact (pb11_heap_tail_out v pos lyc Sc Wc memc mdc b m (q + Z.of_nat (length s)) x G HAR Hin Hly Hb ltac:(lia) Hx).
Qed.
Lemma pb11_keep_lit : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
rewrite HK; [exact (Hz i Hi') | lia | exact (pb11_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Himg)].
Qed.
Lemma pb11_keep_img_word : forall a, (forall k, 0 <= k < 8 -> in_img SEGS (a + k)) -> rdword rd' a = rdword (rdW Wc memc) a.
Proof.
intros a Hi. apply rdword_ext. intros k Hk. pose proof (pa_img_range _ (Hi k Hk)) as Hrg. unfold kImgEnd in Hrg.
apply HK; [lia | exact (pb11_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly (Hi k Hk))].
Qed.
Lemma pb11_keep_cat : sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B rd' catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb11_keep_lit tp _ Hl)].
rewrite pb11_keep_img_word; [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)). unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma pb11_keep_rod : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros HR a Hro Ho He. pose proof (pb11_ro_img_range a Hro) as Hrg.
rewrite HK; [exact (HR a Hro Ho He) | unfold kImgEnd in Hrg; lia | exact (pb11_imgrange_out v pos a G Hrg)].
Qed.
Lemma pb11_keep_ssp : sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> rdword rd' a = rdword (rdW Wc memc) a).
{ intros a Ha. apply rdword_ext. intros k Hk. apply HK; [unfold kImgEnd in Ha; lia|].
  apply (pb11_imgrange_out v pos (a + k) G). lia. }
split; [rewrite (Ho gotwA); [exact G1 | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (Ho guardA); [exact G2 | unfold guardA, kImgEnd; lia].
Qed.
Lemma pb11_keep_obj : pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof.
intros (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (pb11_keep_hstr _ _ T3 T1)|]. split; [exact (pb11_keep_addr _ _ T3 T2)|]. split; [exact T3|].
split; [exact (pb11_keep_addr _ _ C2 C1)|]. split; [exact C2|]. split; [exact (pb11_keep_cat CA)|].
split; [intros x Hx; exact (pb11_keep_lit _ _ (LI x Hx))|]. split; [exact (pb11_keep_rod RO) | exact (pb11_keep_ssp SS)].
Qed.
(* c's bytes, cur_name and slot 0xc0 *)
Lemma pb11_keep_st : forall cf cur nm k, sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros cf cur nm k (b & m & Hb & H1 & H2) ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN & HS).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (AC1 & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _).
split; [|split; [exact HC|split; [|split; [exact HN|]]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  refine (pb11_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). unfold seg_spec.SEG_C_SIZE in *. lia.
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK, PF_O_CN. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. unfold pb11_kcell in Hj. lia.
- rewrite rdword_ext with (rd := rdW Wc memc); [exact HS|]. intros i Hi.
  apply HK; [lia|]. unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. unfold pb11_kcell in Hj. lia.
Qed.
(* a string in buf (val) *)
Lemma pb11_keep_buf_str : forall p s, pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str (rdW Wc memc) p s -> sa_str rd' p s.
Proof.
intros p s Hb ((Hz & Hn) & Ht).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (AC1 & _).
unfold pf_inb, PF_O_BUF in Hb.
assert (KB : forall x, pf_F v pos + 0x40 <= x < pf_F v pos + 0x248 -> rd' x = rdW Wc memc x).
{ intros x Hx. apply HK; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. unfold pb11_kcell in Hj. lia. }
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite KB by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite KB by lia. exact (Ht x Hx).
Qed.
End k.

(* the stack slots, the saved registers, the flag word and the frame's shadow, kept by a step that writes only
   pb11_Wrx bytes (each with the narrowest write set it needs) *)
Lemma pb11_keep_sl : forall v pos (rd rd' : reader) kno shw, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true kno shw a -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' kno shw G HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
assert (KW : forall off, (0 <= off <= 0x58 \/ 0x78 <= off <= 0xd8) ->
  rdword rd' (pf_s1 v + off) = rdword rd (pf_s1 v + off)).
{ intros off Hoff. apply rdword_ext. intros k Hk. apply HK; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. unfold pb11_kcell in Hj. lia. }
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov. specialize (H _ Hov). cbn [fst snd] in *.
assert (Hoff : 0 <= off <= 0x58 \/ 0x78 <= off <= 0xd8).
{ unfold PF_SL in Hov. cbn [In] in Hov.
  repeat (let Hq := fresh "Hq" in destruct Hov as [Hq | Hov]; [injection Hq as <- _; lia |]). destruct Hov. }
rewrite (KW off Hoff). exact H.
Qed.
Lemma pb11_keep_slots : forall v pos (rd rd' : reader) sl kno shw L, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos sl kno shw a -> rd' a = rd a) ->
  Forall (fun ov => (sl = false /\ 0 <= fst ov <= 0xd8) \/ 0 <= fst ov <= 0x58 \/ 0x70 <= fst ov <= 0xd8) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' sl kno shw L G HK HL H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov. specialize (H _ Hov). specialize (HL _ Hov).
cbn [fst snd] in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; [lia | | destruct W as [_ W]; lia |].
- destruct W as [Hsl W]. destruct HL as [[Hf _] | HL]; [rewrite Hf in Hsl; discriminate Hsl | lia].
- destruct W as [_ (j & Hj & Ha)]. unfold pb11_kcell in Hj. lia.
Qed.
Lemma pb11_keep_saved : forall v pos (rd rd' : reader) regs, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs G HK H j r Hj.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite rdword_ext with (rd := rd); [exact (H j r Hj)|]. intros k Hk. apply HK; [lia|].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
destruct W as [_ (i & Hi & Ha)]. unfold pb11_kcell in Hi. lia.
Qed.
Lemma pb11_keep_flag : forall v pos (rd rd' : reader) x, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos rd rd' x G HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (fs_frame_bytes 5) with 2048 in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
destruct W as [_ (i & Hi & Ha)]. unfold pb11_kcell in Hi. lia.
Qed.
Lemma pb11_keep_fsh : forall v pos (rd rd' : reader) sl kno sc, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos sl kno false a -> rd' a = rd a) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sl kno sc G HK H i Hi.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite HK; [exact (H i Hi) | unfold kHighShadowEnd in G12; lia |].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia | destruct W as [W _]; discriminate W].
Qed.
(* the 31 scope-in stores: the frame's shadow goes from PF_SC_L146 to PF_SC_KNOWN *)
Lemma pb11_fill_fsh : forall v pos (rd rd' : reader) sl kno, pb11_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos sl kno true a -> rd' a = rd a) ->
  (forall i, pb11_kcell i -> rd' (pf_SH v pos + i) = Some 0) ->
  pf_fsh rd (pf_SH v pos) PF_SC_L146 -> pf_fsh rd' (pf_SH v pos) PF_SC_KNOWN.
Proof.
intros v pos rd rd' sl kno G HK HF H i Hi.
destruct (Z.eq_dec i 138) as [E | E]; [rewrite (HF i (or_intror E)), (pb11_shb_in i (or_intror E)); reflexivity|].
destruct (Z_le_gt_dec 100 i) as [E1 | E1]; [destruct (Z_lt_ge_dec i 130) as [E2 | E2]|].
- rewrite (HF i (or_introl (conj E1 E2))), (pb11_shb_in i (or_introl (conj E1 E2))). reflexivity.
- assert (Hn : ~ pb11_kcell i) by (unfold pb11_kcell; lia).
  rewrite (pb11_shb_out i Hi Hn).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite HK; [exact (H i Hi) | unfold kHighShadowEnd in G12; lia |].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. apply Hn. replace i with j by lia. exact Hj.
- assert (Hn : ~ pb11_kcell i) by (unfold pb11_kcell; lia).
  rewrite (pb11_shb_out i Hi Hn).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite HK; [exact (H i Hi) | unfold kHighShadowEnd in G12; lia |].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | destruct W as [_ W]; lia |].
  destruct W as [_ (j & Hj & Ha)]. apply Hn. replace i with j by lia. exact Hj.
Qed.

(* ======================= the cut state after a step ======================= *)
(* pf_base after a step that kept every byte off pb11_Wrx (and every visible byte visible), with the journal it
   returned at the same layout, the frame state changed at most (set_fs), the live blocks permuted; the step may
   end at another FP state f1 (a call through snprintf or a program callee), whose rounding mode is 0 *)
Lemma pb11_move : forall (f1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (pb11_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  sa_frm0 (fx := f1) ->
  pf_base (fx := f1) B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros f1 v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm HK HV HRG HFSH HFRM1.
pose proof (pb11_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & _ & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply pb11_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (pb11_keep_saved v pos _ _ _ G HK HSV)|].
  split; [exact (pb11_keep_flag v pos _ _ _ G HK HFL)|].
  split; [exact HFRM1|]. split; [exact HTF|].
  split; [|exact HRG].
  apply (pb11_keep_slots v pos _ _ true true true _ G HK); [|exact HC8].
  repeat constructor; cbn [fst]; lia. }
split.
{ pose proof (pb11_keep_obj v pos lyc Sc Wc memc mdc Wc' memc' G HAR Hin Hly HK HV HOBJ)
    as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (pb11_keep_sl v pos _ _ true true G HK HSL) | exact HFSH].
Qed.

(* ======================= the text, the read-only view, the frame chain ======================= *)
Lemma pb11_textF : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ~ In 0 (p_s v) /\ (length (p_s v) <= 65535)%nat /\ sa_str (rdW Wc memc) (p_t v) (p_s v) /\
  sa_addr (rdW Wc memc) (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & HOBJ & _).
destruct HOBJ as (HSTR & HADDR & HHEAP & _ & HC & _).
destruct HFI as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HLS) & _).
split; [exact (proj2 (proj1 HSTR))|]. split; [exact HLS|]. auto.
Qed.
Lemma pb11_rom : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
intros a (sg & Hsg & Hw & Hr) Ho He. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* the frame chain at a call from B11b (s0 = sp0, the frame pointer): the prologue's record (ra at sp0 - 8, the
   entry s0 at sp0 - 16, pf_saved) on afn_pre's chain, which the journal keeps above sp0 *)
Lemma pb11_chain : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof (pb11_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & _).
destruct HFI as (HJ & _ & _ & _ & HSV & _).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [rewrite SPF in G1; lia | rewrite SPF; lia |].
    intros Hf. apply pb11_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. rewrite SPF in G1. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + rewrite SPF in G1. lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
End e.
End f.
End d.
