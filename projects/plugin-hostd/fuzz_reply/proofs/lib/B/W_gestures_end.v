(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's gestures_end,
   a NEW walk over lib/B/W_listing.v after lib/A/W_gestures_end.v (a working branch 8cdde8f679f), in the form of the
   cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop lemma from the loop head, a test lemma, the stretch
   over the loop), lib/A/AC8h.v (free call sites) and lib/A/ACh2.v (an internal call).  pb_gestures_end runs the entry
   at 0x82618 to the `blez` at 0x8267c and hands the state to the cut points of lib/B/W_gse_cut.v, Section hypotheses
   GSE_TAIL (nheld <= 0, at 0x82754 with no key) and GSE_LOOP (0 < nheld, at the loop head 0x82694 with i = 0).
   B's frame (80) saves ra and s0..s8; s4 = s1 >> 3 is set before the `blez`; the loop head has s5 = 0 (8i), s6 = 0 (i),
   s7 = s4 + SB, s8 = (s0 & 7) + 3 = 3.  B's UBSan entry traps (to `unimp` at 0x827b0; UBSan is trap mode in this pin),
   `beqz a0` (0x82644, s null) and `andi a1,a0,7; bnez a1` (0x82648-0x8264c, s misaligned), are decided NOT TAKEN by the
   runner inside the entry run from the entry state's fact on atom 10 (a0 = SA: 4096 <= SA, SA mod 8 = 0; gse_entry's
   gse_facts), which gse_entry proves from 4096 <= TB <= SA (the table block) and SA mod 8 = 0 (gse_spec).
   The walk is proved over any allocator relation ARx (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)) as
   pb_gestures_end_x : gse_spec_x, with the cut points' generic forms GSE_LOOP_X / GSE_TAIL_X; pb_gestures_end, the AR
   statement, is re-derived from it at ARi0 (Section cAR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_frame W_gse_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_kit_xb W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ byte lists *)
Lemma gse_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Lemma gse_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, gse_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Definition A_gestures_end : Z := AF_fr_gestures_end.
Definition A_gestures_endP : Z := BASE + A_gestures_end.
Definition A_gse_test : Z := AF_fr_gestures_end + 0x64.   (* 0x8267c: blez a1, 82754 *)
(* ---- THE GENERIC WALK (route (b), step 3): gestures_end over any allocator relation ARx with its laws, stated as
   W_contract_x.gse_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation),
   HP0 (no hidden head in any ARx state: W_journal_x's range_addressable_of_block_hp0_x), IMGC / BLKN (W_kit_xb.v
   Section g, for blk_off_imgB_x); the free rules and the two cut points are their generic forms. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
(* the free rules in their caller-context form (a Theorem Labs lane's 21:20Z ruling), over one context list per allocator
   entry; the entry walk itself calls no allocator, so this Section names no free site (gse_free_x takes the caller's
   context as a premise, discharged at each site by the loop and the tail) *)
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* the two cut points (W_gse_cut.v, FROZEN), in their generic form: the loop from its head, and the stretch after the
   loop *)
Hypothesis GSE_LOOP_X : gse_loop_at_x B PST ARx MT RP MMAX RG (BASE + A_gse_loop).
Hypothesis GSE_TAIL_X : gse_tail_at_x B PST ARx MT RP MMAX RG (BASE + A_gse_tail).
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the journal helpers below at a world relation R.  ajournal_gx_x SEGS B PST ARx ->
   ajournal_gx_xR SEGS B PST ARx R, SRr SEGS -> SRrG SEGS R, the kit's journal lemmas -> their _xR twins (the call
   step is W_journal_x.v gx_callS_xR's text with this file's K).  The strict helpers below are these at wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* W_gesture_end.v's gx_callS (W4Gesture): a call to a program function over ajournal_gx_x, the callee's contract
   applied at its entry and its journal composed into the caller's (W_journal_x.v ajournal_gx_sub_x). *)
Lemma gse_callS_xR : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR SEGS B PST ARx R G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee.
  pose proof HJ as HJin. apply ajournal_gx_inner_xR in HJin. destruct HJin as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJi);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HPr & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HPr | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans);
[exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* W_gesture_end.v's ajgx_keep_img / ajgx_keep_high / fp_spares_blocks / ablocks_nodup (W4Gesture), over
   ajournal_gx_x.  An image byte is kept when it is also off PST (the journal's image clause, YCbqG.ajournal_x). *)
Lemma gse_keep_img_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Hi Ho He Hq Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hq Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma gse_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* A block present at both ends of a journal and outside its footprint keeps its bytes. *)
Lemma gse_keep_blk_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i,
gx_ok SEGS B G -> ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
exact (blk_img_x SEGS B ARx LAWS ly' S' Hp' W' mem' md' p n (p + i) HAR0 H2 ltac:(lia) Hi').
Qed.
End wR.
(* the strict texts are the R sections' at R := wle (route R's rule: one walk text): each R premise at wle is the
   strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* ------------------------------------------------------------------ journal helpers *)
(* W_gesture_end.v's gx_callS (W4Gesture): a call to a program function over ajournal_gx_x, the callee's contract
   applied at its entry and its journal composed into the caller's (W_journal_x.v ajournal_gx_sub_x). *)
Lemma gse_callS_x : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x SEGS B PST ARx G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof. eapply (gse_callS_xR (@wle SEGS)); wle_inst. Qed.
(* W_gesture_end.v's ajgx_keep_img / ajgx_keep_high / fp_spares_blocks / ablocks_nodup (W4Gesture), over
   ajournal_gx_x.  An image byte is kept when it is also off PST (the journal's image clause, YCbqG.ajournal_x). *)
Lemma gse_keep_img_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof. eapply (gse_keep_img_xR (@wle SEGS)); wle_inst. Qed.
Lemma gse_keep_high_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof. eapply (gse_keep_high_xR (@wle SEGS)); wle_inst. Qed.
(* A block present at both ends of a journal and outside its footprint keeps its bytes. *)
Lemma gse_keep_blk_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i,
gx_ok SEGS B G -> ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof. eapply (gse_keep_blk_xR (@wle SEGS)); wle_inst. Qed.
Lemma gse_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma gse_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR. destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hpw Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* ------------------------------------------------------------------ free, over ajournal_gx_x *)
Lemma gse_not_owned_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): free (hp) at a world relation R, over the R free rules (W_journal_x.v Section hc:
   afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX_AFREE R), whose call-boundary premise RO comes from the
   journal's ARx at the call state (RO_ARx; part 3c took memnorm out of the free rules).  The strict gse_free_x below
   is it at wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :237 gse_free_x *)
Lemma gse_free_xR : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch (kr : nat),
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (gse_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCTX HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
unfold gse_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRrG_mono.
  { exact (AFREEN_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HRO HCTX HRM HCNT MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & _ & HK & HM & HRM2 & HE & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a []]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (gse_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gse_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | exact Hpa].
- assert (Hin : In (hp, kh) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  eapply SRrG_mono.
  { apply (AFREE_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k hp kh o raw ch kr HJi Hin H10 Hsp Hal
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HRO HCTX HRM HCNT); [intros _ i Hi; exact (HFP Hnz i Hi) | exact MOK]. }
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & _ & HK & HM & HRM2 & HE
    & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|].
  split; [rewrite E2; apply Permutation_sym; apply (@Permutation_cons_app_inv _ l l1 l2 (hp, kh)); rewrite <- E1;
    apply Permutation_sym; exact HP|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a Ha; split; [exact Hnz | exact Ha]]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (gse_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gse_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hpa].
  intros Hr. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memT mdc hp kh a (proj1 HJi) Hin ltac:(lia) Hi).
Qed.
End wR.
(* free (hp): gse_free_xR at R := wle, RO := True; the R free rules at wle are the strict AFREE / AFREEN
   (W_journal_x.v afree_cf_rule_c_xR_of_x / afree_null_cf_rule_c_xR_of_x). *)
Lemma gse_free_x : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch (kr : nat),
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (gse_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
eapply (gse_free_xR (@wle SEGS)) with (RO := fun _ => True);
  first [ wle_inst | (intros; exact I) | (apply afree_cf_rule_c_xR_of_x; exact AFREE)
  | (apply afree_null_cf_rule_c_xR_of_x; exact AFREEN) ].
Qed.

(* ------------------------------------------------------------------ bytes kept, writability, presence *)
Lemma gse_le_garr8 : forall m a n z, val_mem SEGS m a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS m a (bzs (Z_to_le_bytes n z)).
Proof.
intros m a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, gse_nth_le_bytes by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma gse_garr8_kept : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
Lemma gse_vm_kept : forall H H' (m m' : word -> option byte) a n v, val_mem SEGS (mrestrict H m) a n v ->
(forall b, a <= b < a + Z.of_nat n -> aview SEGS H' m' b = aview SEGS H m b) -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply (val_mem_kept SEGS H H' m m' a n v); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
(* A byte a reader sees, off the read-only segments, is writable: either a present byte, or a byte of a writable
   segment's file image (wview and memory_read find the same segment). *)
Lemma gse_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
Lemma gse_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma gse_view_garr8 : forall H (m : word -> option byte) a l k, garr8 SEGS (mrestrict H m) a l -> 0 <= k < Z.of_nat (length l) ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a l k Hg Hk. destruct (Hg (Z.to_nat k) ltac:(lia)) as [Hv _].
pose proof (gse_view_some H m (a + Z.of_nat (Z.to_nat k)) 1 _ 0 Hv ltac:(lia)) as R. rewrite Z.add_0_r in R.
replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia. exact R.
Qed.
(* abyte_kept from the view alone, for a byte seen before and off the read-only segments *)
Lemma gse_abyte_kept : forall (W W' : world SEGS) m m' a, 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> aview SEGS (w_H W) m a <> None -> ~ in_rom SEGS a ->
abyte_kept W m W' m' a.
Proof.
intros W W' m m' a Ha He Hs Hr. split; [exact He|]. intros _. unfold arm.
destruct (aview SEGS (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (gse_writable_view (w_H W') m' a v Ha He Hr).
Qed.
Lemma gse_apres_trans : forall W m W1 m1 W2 m2, apres_kept B W m W1 m1 -> apres_kept B W1 m1 W2 m2 -> apres_kept B W m W2 m2.
Proof. intros W m W1 m1 W2 m2 H1 H2 a Hi Ho He Hp. apply H2; [exact Hi | exact Ho | exact He | apply H1; assumption]. Qed.
Lemma gse_apres_grows : forall W m m2, mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m2) -> apres_kept B W m W m2.
Proof. intros W m m2 Hg a _ _ _ Hp. exact (apresent_grows (w_H W) m m2 a Hg Hp). Qed.
Lemma gse_apres_refl : forall W m, apres_kept B W m W m.
Proof. intros W m a _ _ _ Hp. exact Hp. Qed.

(* ------------------------------------------------------------------ the held keys (kblks, key_ok: W_gse_cut.v) *)
Lemma gse_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* held[i] = key_addr (nth i keys): the i-th 8-byte word of the held array *)
Lemma gse_key_ptr : forall m hp ks i k, garr8 SEGS m hp (bzs (key_ptrs ks)) -> nth_error ks i = Some k ->
0 <= key_addr k < 2 ^ 64 -> val_mem SEGS m (hp + 8 * Z.of_nat i) 8 (key_addr k).
Proof.
intros m hp ks i k Hg Hn Hk.
destruct (nth_error_split ks i Hn) as (l1 & l2 & -> & Hl1).
unfold key_ptrs in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold bzs in Hg. rewrite !map_app in Hg. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
fold (key_ptrs l1) in Hg. rewrite length_map, gse_key_ptrs_len, Hl1 in Hg.
replace (hp + 8 * Z.of_nat i) with (hp + Z.of_nat (8 * i)) by lia.
apply gse_garr8_le; [|lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.
(* the 56 bytes of a source_t: the 40 before held, held, nheld, pad2 *)
Notation le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Notation le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.
Definition epre (e : rentry) : list byte :=
le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++
le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e)).
Lemma gse_epre_len : forall e, length (re_pad1 e) = 4%nat -> length (epre e) = 40%nat.
Proof.
intros e Hp1. unfold epre. rewrite !length_app,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, Hp1. reflexivity.
Qed.
Lemma gse_entry_split : forall e,
entry_bytes e = epre e ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e.
Proof. intros e. unfold entry_bytes, epre. rewrite <- !app_assoc. reflexivity. Qed.
Lemma gse_entry_split_cleared : forall e,
entry_bytes (entry_cleared e) = epre e ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ re_pad2 e.
Proof.
intros e. unfold entry_bytes, entry_cleared, epre, re_nheld.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys length].
rewrite <- !app_assoc. reflexivity.
Qed.


(* ------------------------------------------------------------------ the entry state *)
Definition Bx : sv := SOff 34 0.
(* s's held / nheld cells: read-only here (nothing before the tail stores to s+40..52), so a run's KEEP fact covers
   every byte outside the frame *)
Definition gse_ent : YP09.region :=
YP09.mkRegion (Some 10%nat) 40 52 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 4 (SOff 33 0))].
Definition gse_regions : smem := [ stack_region GSE_FRAME; got_regionP; bcell_regionP 34; gse_ent ].
(* atom 10 (a0 = SA): af_lo 4096 decides B's UBSan trap `beqz a0` (0x82644) and af_al2 3 (SA mod 8 = 0) its trap
   `andi a1,a0,7; bnez a1` (0x82648-0x8264c) NOT TAKEN inside the entry run; with either one weakened the entry run
   stops at that trap (probe of 2026-10-29).  gse_entry proves both from 4096 <= TB <= SA and SA mod 8 = 0. *)
Definition gse_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3); (33%nat, mkAF 0 (2^26) 0);
(34%nat, mkAF SB SB 0) ] [] [].
Definition ss_gse : sstate := mkSS A_gestures_end sr_atoms gse_regions None gse_facts.
Definition gse_SH : list shent := [ mkSHE 10 40 56 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gse_extra (hp nh : Z) : list word := map (Z_to_bv 64) [hp; nh; SB].
Lemma gse_entry_x : forall W ly S Hp regs mem md ch SA TB hp nh,
afn_pre_x SEGS B ARx GSE_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 SA ->
In (TB, ATABLE) (ablocks B ly S) -> TB <= SA -> SA + AENT <= TB + ATABLE -> SA mod 8 = 0 ->
val_mem SEGS (arm W mem) (SA + 40) 8 hp -> val_mem SEGS (arm W mem) (SA + 48) 4 nh ->
0 <= hp < 2 ^ 64 -> 0 <= nh < 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (gse_extra hp nh))) ss_gse
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_gestures_endP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx gse_SH (Eimg (Ereg regs (gse_extra hp nh))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch SA TB hp nh HPRE H10 Hin HT1 HT2 HSA8 Mhp Mnh Rhp Rnh.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : GSE_STK = 16624) by reflexivity.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md TB ATABLE HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ TB ATABLE HAR Hin) as Hph_img.
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (gse_extra hp nh))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Egot : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_gse, A_gestures_endP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold gse_regions, gse_ent, stack_region, got_regionP, bcell_regionP, GSE_FRAME.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ecell) by (pose proof (pa_val_range (A_OBJ 30)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 Bx SB);
      [cbn [sv_denot Bx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat SA E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ SA 40 8 _ hp); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mhp].
      -- apply (chunk_ok_val SEGS E _ SA 48 4 _ nh); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mnh].
  + apply pairwise_disjoint_of_extents. unfold gse_regions, gse_ent, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat SA E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ecell) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
    unfold GSE_FRAME.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hpceil Hph Hph_img Hp4096 C1 C3 WS Hstk0 HcellR HgcD HgotR HT1 HT2. clear.
    unfold zone2, off_img, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img, in_app, kLowShadowBeg,
      kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [gse_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hpceil Hph Hph_img Hp4096 Hp16 Hal16 C1 C3 WS Hstk0 Rnh HT1 HT2 HSA8. clear.
    unfold SB, zone2, off_img, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img, in_app, kLowShadowBeg,
      kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gse_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E Bx 10 TB 896 SA 40 56).
  + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md TB ATABLE TB 896 HAR Hin ltac:(lia)
      ltac:(change (req_size ATABLE) with 896; lia)).
  + unfold U, Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* ------------------------------------------------------------------ the composition *)
(* the shadow address of x, as the prologue computes it (srli 3, add SB) *)
Lemma gse_shadow_w : forall x, 0 <= x < 2 ^ 60 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = w64 (x / 8 + SB).
Proof.
intros x Hx. assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SB; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. apply Z.mod_small. unfold SB. lia.
Qed.
(* s4 = s1 >> 3, set before the `blez` *)
Lemma gse_srl3_w : forall x, 0 <= x < 2 ^ 60 ->
alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = w64 (x / 8).
Proof.
intros x Hx. assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. lia.
Qed.
(* W_gesture_end.v's aout_fp_cases / aout_facts (W4Gesture) *)
Lemma gse_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) -> In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma gse_aout_blk : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
(cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S)).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd).
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* Everything gse_inv reads below the allocator's ceiling, at a memory that keeps those bytes' views and every
   present byte: the output, s's bytes, the held array, the keys, " end\0" and the ROM. *)
Lemma gse_kept_x : forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest (kr : nat) memc,
gse_pre_x B ARx MT RP MMAX RG W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
aout_at B RG ly S W memc c O mx no cap out /\
garr8 SEGS (arm W memc) SA (bzs (entry_bytes e)) /\ awr W memc SA AENT /\
garr8 SEGS (arm W memc) (re_hp e) (bzs (key_ptrs (re_keys e))) /\
Forall (key_ok W memc) (re_keys e) /\
garr8 SEGS (arm W memc) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS W memc.
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr memc
  (HPRE & H10 & Hin & HT1 & HT2 & HSA8 & HEB & HAW & HHELD & HOUT & HPERM & G5 & HROM & ROOM & MOK & _) KV KP.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as ((He0 & He1) & _ & _).
destruct HHELD as (Hp1 & Hp2 & Hnh & HHP & _ & _ & FK).
assert (BLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a < alloc_ceiling).
{ intros p n a Hb Ha. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hb) as (_ & Hp4 & Hpc & _). lia. }
assert (IMG : forall a, in_img SEGS a -> 0 <= a < alloc_ceiling).
{ intros a Ha. pose proof (pa_segs_low a Ha). lia. }
assert (KW : forall a, writable_at SEGS (arm W mem) a -> writable_at SEGS (arm W memc) a).
{ intros a Hw. exact (writable_kept (w_H W) mem memc a (KP a) Hw). }
split.
{ apply (aout_at_kept B RG ly S W mem ly S W memc c O mx no cap out HOUT).
  - intros r Hr a Ha. split; [apply KV | exact (KW a)].
    destruct (gse_aout_fp_cases cap out r Hr) as [Hc | (Hc & ->)].
    + destruct (Z_le_gt_dec (as_errno B) a) as [E1 | E1]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2 | E2]|].
      * lia.
      * exact (IMG a (proj1 (HOUTG r a Hc Ha ltac:(lia)))).
      * exact (IMG a (proj1 (HOUTG r a Hc Ha ltac:(lia)))).
    + cbn [fst snd] in Ha. destruct (gse_aout_blk _ _ _ _ _ _ _ _ _ _ HOUT) as [(Hc0 & _) | (_ & _ & Hb)]; [lia|].
      pose proof (req_size_pos cap ltac:(lia)) as [_ Hrs]. exact (BLK out cap a Hb ltac:(lia)).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0); [destruct Hb|].
    destruct Hb as [<- | []]. destruct (gse_aout_blk _ _ _ _ _ _ _ _ _ _ HOUT) as [(Hc0 & _) | (_ & _ & Hb)]; [lia | exact Hb]. }
split.
{ apply (gse_garr8_kept (w_H W) (w_H W) mem memc SA _ HEB). intros b Hb. apply KV.
  assert (LE : length (bzs (entry_bytes e)) = 56%nat).
  { unfold bzs. rewrite length_map, gse_entry_split, !length_app, (gse_epre_len e Hp1).
    rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8,
      OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4, Hp2. reflexivity. }
  rewrite LE in Hb. apply (BLK TB ATABLE b Hin). change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia. }
split; [intros i Hi; exact (KW (SA + i) (HAW i Hi))|].
split.
{ destruct HHP as [(Hz & Hk) | (Hnz & Hinb & Hkh & Hkh8 & Ghp)].
  - rewrite Hk. intros j Hj. cbn in Hj. lia.
  - apply (gse_garr8_kept (w_H W) (w_H W) mem memc (re_hp e) _ Ghp). intros b Hb. apply KV.
    unfold bzs in Hb. rewrite length_map, gse_key_ptrs_len in Hb. unfold re_nheld in Hkh.
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hrs]. apply (BLK _ _ b Hinb). lia. }
split.
{ eapply Forall_impl; [|exact FK]. intros k (Hkin & Hkg & Hknz & Hklen). unfold key_ok.
  split; [|split; [exact Hknz | exact Hklen]].
  apply (gse_garr8_kept (w_H W) (w_H W) mem memc (key_addr k) _ Hkg). intros b Hb. apply KV.
  unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hrs].
  apply (BLK _ _ b Hkin). lia. }
split.
{ apply (gse_garr8_kept (w_H W) (w_H W) mem memc _ _ G5). intros b Hb. apply KV.
  change (Z.of_nat (length (bzs END5))) with 5 in Hb. pose proof (pa_obj_img 28 ltac:(lia)) as HO.
  change (VAL A_lit_end5) with (VAL (A_OBJ 28)) in Hb. lia. }
intros a Hin'.
assert (HI : 0x10000 <= a < 0x5fc000)
  by (destruct Hin' as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
rewrite KV by lia. exact (HROM a Hin').
Qed.
(* the runs write only the 80-byte frame: every other byte is outside the regions' writable windows *)
Ltac gse_outw Usp :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gse gse_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val
stack_region got_regionP bcell_regionP gse_ent] in Hr;
rewrite ?Usp in Hr; unfold GSE_FRAME in *; lia | ]);
destruct Hin.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the entry walk at a world relation R.  gse_spec_x -> W_contract_xR.gse_spec_xR
   (R right after ARx), the two cut points -> W_gse_cut.gse_loop_at_xR / gse_tail_at_xR (GSE_LOOP_XR / GSE_TAIL_XR),
   the runs and the branch -> their SRrG forms (W_journal_x.v paj_run_to_x_xG, W_kit.v paj_branch_xR).
   pb_gestures_end_x below is it at wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GSE_LOOP_XR : gse_loop_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_loop).
Hypothesis GSE_TAIL_XR : gse_tail_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_tail).
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :630 pb_gestures_end_x *)
Theorem pb_gestures_end_xR : gse_spec_xR B PST ARx R MT RP MMAX RG A_gestures_endP.
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest HPRE H10 Hin HT1 HT2 HSA8 HEB HAW HHELD HOUT HPERM G5 HROM
  ROOM MOK kr RM CNT.
assert (HPREB : gse_pre_x B ARx MT RP MMAX RG W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr)
  by exact (conj HPRE (conj H10 (conj Hin (conj HT1 (conj HT2 (conj HSA8 (conj HEB (conj HAW (conj HHELD
    (conj HOUT (conj HPERM (conj G5 (conj HROM (conj ROOM (conj MOK (conj RM CNT)))))))))))))))).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GSE_STK = 16624) by reflexivity.
assert (HLO : alloc_ceiling + GSE_STK <= spZ regs) by lia.
assert (RSA : 4096 <= SA /\ SA + 56 <= alloc_ceiling).
{ destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md TB ATABLE HAR Hin) as (_ & Hp4 & Hpc & _).
  change (req_size ATABLE) with 896 in Hpc. clear - Hp4 Hpc HT1 HT2. unfold AENT, ATABLE in *. lia. }
pose proof HHELD as (Hp1 & Hp2 & Hnh & HHP & _ & _ & _).
(* hp and nheld, from s's bytes *)
assert (Rhp : 0 <= re_hp e < 2 ^ 64).
{ destruct HHP as [(Hz & _) | (_ & Hinb & _ & Hkh8 & _)]; [rewrite Hz; lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hinb) as (_ & Hp4 & Hpc & _).
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as [Hrs _]. lia. }
assert (Rnh : 0 <= re_nheld e < 2 ^ 26) by (unfold re_nheld in *; lia).
pose proof HEB as HEB2. rewrite gse_entry_split in HEB2. unfold bzs in HEB2. rewrite !map_app in HEB2.
apply garr8_app in HEB2 as [_ HEB2]. rewrite length_map, (gse_epre_len e Hp1) in HEB2.
apply garr8_app in HEB2 as [Ghp HEB2]. apply garr8_app in HEB2 as [Gnh _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8 in Gnh.
change (SA + Z.of_nat 40) with (SA + 40) in Ghp, Gnh. replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh by lia.
assert (Mhp : val_mem SEGS (arm W mem) (SA + 40) 8 (re_hp e)).
{ apply gse_garr8_le; [|lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes in Ghp.
  rewrite unsigned_lit_small in Ghp by lia. exact Ghp. }
assert (Mnh : val_mem SEGS (arm W mem) (SA + 48) 4 (re_nheld e)).
{ apply gse_garr8_le; [|lia].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Gnh.
  rewrite unsigned_lit_small in Gnh by lia. exact Gnh. }
clear Ghp Gnh.
destruct (gse_entry_x W ly S Hp regs mem md ch SA TB (re_hp e) (re_nheld e) HPRE H10 Hin HT1 HT2 HSA8 Mhp Mnh Rhp Rnh)
  as [HS SHOK].
assert (HJ : ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S Hp W mem md []
  ly S Hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl (G_SL B RG) 0 [] GSE_STK _ ly S Hp W regs mem md ch HPRE);
  [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (gse_extra (re_hp e) (re_nheld e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regs 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr regs 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
assert (E21 : ew E 21 = getr regs 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr regs 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)).
assert (E24 : ew E 24 = getr regs 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 (re_nheld e)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gse_extra (re_hp e) (re_nheld e))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U33 : U E (SOff 33 0) = re_nheld e) by (apply (U_atom E 33 _ E33); lia).
clear HE.
(* the frame slots and registers at a cut state reached by runs from this entry: B's prologue saves ra, s0..s8 *)
assert (SLOTS : forall (m : word -> option byte) cs lo hi wlo whi,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  (forall od n, In (YP09.mkChunk od (CVal 8 (SOff n 0))) [YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
   In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs) ->
  val_mem SEGS m (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS m (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS m (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS m (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS m (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS m (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS m (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS m (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS m (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS m (spZ regs - 80) 8 (bv_unsigned (getr regs 24))).
{ intros m cs lo hi wlo whi HRG HCS.
  assert (SLOT : forall (od : Z) (n : nat) (r : bv 5),
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) [YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
    ew E n = getr regs r -> val_mem SEGS m (spZ regs + od) 8 (bv_unsigned (getr regs r))).
  { intros od n r Hin' Hew.
    apply (slot_of_region _ _ (spZ regs) _ _ _ _ _ od (SOff n 0) (bv_unsigned (getr regs r)) HRG Usp (HCS od n Hin'));
    [cbn [sv_denot]; rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hrr; change (bv_modulus 64) with (2 ^ 64) in Hrr; lia]. }
  rewrite <- !Z.add_opp_r.
  split; [exact (SLOT (-8) 1%nat 1%bv (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror
    (or_intror (or_intror (or_introl eq_refl)))))))))) E1)|].
  split; [exact (SLOT (-16) 8%nat 8%bv
    (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) E8)|].
  split; [exact (SLOT (-24) 9%nat 9%bv
    (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) E9)|].
  split; [exact (SLOT (-32) 18%nat 18%bv
    (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) E18)|].
  split; [exact (SLOT (-40) 19%nat 19%bv
    (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) E19)|].
  split; [exact (SLOT (-48) 20%nat 20%bv (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))) E20)|].
  split; [exact (SLOT (-56) 21%nat 21%bv (or_intror (or_intror (or_intror (or_introl eq_refl)))) E21)|].
  split; [exact (SLOT (-64) 22%nat 22%bv (or_intror (or_intror (or_introl eq_refl))) E22)|].
  split; [exact (SLOT (-72) 23%nat 23%bv (or_intror (or_introl eq_refl)) E23)|].
  exact (SLOT (-80) 24%nat 24%bv (or_introl eq_refl) E24). }
unfold cfg_at. change (w64 A_gestures_endP) with (Z_to_bv 64 A_gestures_endP).
unfold A_gestures_endP, A_gestures_end.
(* 0x82618 -> 0x8267c: the prologue; the UBSan traps `beqz a0` (0x82644) and `andi a1,a0,7; bnez a1` (0x82648-0x8264c),
   both to `unimp` at 0x827b0, decided NOT TAKEN by the runner from atom 10's fact (a0 = SA, 4096 <= SA, SA mod 8 = 0:
   gse_facts, proved in gse_entry); s3 = SB (GOT slot 0x9df50 = A_OBJ 0 -> the shadow cell A_OBJ 30), s0 = s+48,
   s2 = shadow (s0), nheld's load4 check (gse_SH), a1 = nheld, s1 = s+40, s4 = s1 >> 3 *)
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_gse_test. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GSE_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha). clear - Usp Hno. gse_outw Usp. }
assert (PRES1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a).
{ intros a Hpa. lazymatch goal with
  | K1 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) |- _ => exact (apresent_grows _ _ _ a K1 Hpa) end. }
psrr_branch_tok RUNTOG BRR HS SHOK Bspan.
- (* nheld <= 0: no held key; blez to the tail *)
  assert (Hk0 : length (re_keys e) = 0%nat).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
    lazymatch type of Hc with _ <= bv_signed ?z => assert (Hz : bv_signed z = 0) by reflexivity; rewrite Hz in Hc end.
    rewrite bv_signed_small in Hc by (change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)); lia).
    change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)) in Hc. unfold re_nheld in U33. lia. }
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_gse_tail. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
  assert (KEEP : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha. assert (Hno : ~ (spZ regs - GSE_FRAME <= a < spZ regs)) by (unfold GSE_FRAME; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha64) by (clear - Usp Hno; gse_outw Usp).
    exact (KEEP1 a Ha64 Hno). }
  assert (PRES : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hpa. lazymatch goal with
    | K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (PRES1 a Hpa)) end. }
  destruct (gse_kept_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr (ms_mem ms0) HPREB KEEP PRES)
    as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (gse_extra (re_hp e) (re_nheld e))
    [3%bv; 4%bv; 25%bv; 26%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
  destruct (SLOTS _ _ _ _ _ _ HRG ltac:(intros od n Hc'; exact Hc'))
    as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24).
  eapply (GSE_TAIL_XR W ly S Hp regs mem md ch SA TB e c O mx no cap out rest W ly S Hp (ms_regs ms0) (ms_mem ms0) _ 0 out
    kr HPREB).
  rewrite Hk0. unfold gse_inv_xR. cbv zeta. cbn [firstn skipn gse_run gse_c gse_O gse_no gse_cap gse_spent fst snd].
  split; [exact HJ|].
  split; [intros a _ _ _ Hpa; exact (PRES a Hpa)|].
  split; [apply (mo_le_refl MT MTL)|].
  split; [exact MOK|].
  split; [exact RM|].
  split; [exact ROOM|].
  split; [rewrite gse_blks_split, <- app_assoc in HPERM; exact HPERM|].
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
  split; [exact K6|]. split; [exact K7|].
  split; [change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2));
    rewrite T2, Usp, unsigned_lit_small by (unfold spZ in *; lia); unfold GSE_FRAME; lia|].
  split; [exact (HK 3%bv (or_introl eq_refl))|].
  split; [exact (HK 4%bv (or_intror (or_introl eq_refl)))|].
  split; [rewrite T8, E10, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite T9, E10, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite T18, E10, E34, unsigned_lit_small by lia; apply gse_shadow_w; lia|].
  split; [rewrite T19, E34; reflexivity|].
  split; [rewrite T20, E10, unsigned_lit_small by lia; apply gse_srl3_w; lia|].
  split.
  { intros rr Hrr. apply HK.
    assert (Hr3 : rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
    clear - Hr3. destruct Hr3 as [-> | [-> | ->]]; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]. }
  split; [exact S1|]. split; [exact S8|]. split; [exact S9|]. split; [exact S18|]. split; [exact S19|].
  split; [exact S20|]. split; [exact S21|]. split; [exact S22|]. split; [exact S23 | exact S24].
- (* 0 < nheld: the loop head with i = 0 *)
  assert (Hk1 : (0 < length (re_keys e))%nat).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
    lazymatch type of Hc with bv_signed ?z < _ => assert (Hz : bv_signed z = 0) by reflexivity; rewrite Hz in Hc end.
    rewrite bv_signed_small in Hc by (change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)); lia).
    change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)) in Hc. unfold re_nheld in U33. lia. }
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_gse_loop. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
  assert (KEEP : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha. assert (Hno : ~ (spZ regs - GSE_FRAME <= a < spZ regs)) by (unfold GSE_FRAME; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha64) by (clear - Usp Hno; gse_outw Usp).
    exact (KEEP1 a Ha64 Hno). }
  assert (PRES : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hpa. lazymatch goal with
    | K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (PRES1 a Hpa)) end. }
  destruct (gse_kept_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr (ms_mem ms0) HPREB KEEP PRES)
    as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (gse_extra (re_hp e) (re_nheld e))
    [3%bv; 4%bv; 25%bv; 26%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
  destruct (SLOTS _ _ _ _ _ _ HRG ltac:(intros od n Hc'; exact Hc'))
    as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24).
  eapply (GSE_LOOP_XR W ly S Hp regs mem md ch SA TB e c O mx no cap out rest 0%nat W ly S Hp (ms_regs ms0) (ms_mem ms0) _ 0
    out kr HPREB Hk1).
  + unfold gse_inv_xR. cbv zeta. cbn [firstn skipn gse_run gse_c gse_O gse_no gse_cap gse_spent fst snd].
    split; [exact HJ|].
    split; [intros a _ _ _ Hpa; exact (PRES a Hpa)|].
    split; [apply (mo_le_refl MT MTL)|].
    split; [exact MOK|].
    split; [exact RM|].
    split; [exact ROOM|].
    split; [rewrite gse_blks_split, <- app_assoc in HPERM; exact HPERM|].
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
    split; [exact K6|]. split; [exact K7|].
    split; [change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2));
      rewrite T2, Usp, unsigned_lit_small by (unfold spZ in *; lia); unfold GSE_FRAME; lia|].
    split; [exact (HK 3%bv (or_introl eq_refl))|].
    split; [exact (HK 4%bv (or_intror (or_introl eq_refl)))|].
    split; [rewrite T8, E10, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T9, E10, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T18, E10, E34, unsigned_lit_small by lia; apply gse_shadow_w; lia|].
    split; [rewrite T19, E34; reflexivity|].
    split; [rewrite T20, E10, unsigned_lit_small by lia; apply gse_srl3_w; lia|].
    split.
    { intros rr Hrr. apply HK.
      assert (Hr3 : rr = 25 \/ rr = 26 \/ rr = 27) by (clear - Hrr; lia).
      clear - Hr3. destruct Hr3 as [-> | [-> | ->]]; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]. }
    split; [exact S1|]. split; [exact S8|]. split; [exact S9|]. split; [exact S18|]. split; [exact S19|].
    split; [exact S20|]. split; [exact S21|]. split; [exact S22|]. split; [exact S23 | exact S24].
  + (* s5 = 8i = 0 *) rewrite T21. reflexivity.
  + (* s6 = i = 0 *) rewrite T22. reflexivity.
  + (* s7 = s4 + s3 = shadow (s1) *) rewrite T23, E10, E34, unsigned_lit_small by lia. apply gse_shadow_w. lia.
  + (* s8 = (s0 & 7) + 3 = 3: the runner folds s0 & 7 = (SA + 48) & 7 to 0 from atom 10's alignment *)
    rewrite T24. reflexivity.
Qed.
End wR.
Theorem pb_gestures_end_x : gse_spec_x B PST ARx MT RP MMAX RG A_gestures_endP.
Proof. eapply (pb_gestures_end_xR (@wle SEGS)); wle_inst. Qed.
End c.

(* ---- THE AR JOURNAL HELPERS, kept under their AR names for the files that cite them (image A's W_rig_top.v cites
   gse_callS / gse_keep_img / gse_pres / gse_keep_high / gse_nodup at `B LAWS` / `B`; A's e954f0c83e4 keeps them, and
   so does this twin for the B port of that walk).  The ARx conversion above proves their _x twins (gse_callS_x ..);
   these five are the AR statements and proofs of the B AR walk (e43cf0c7bef's lib/B/W_gestures_end.v), word for
   word, over the AR journal and AR_laws. ---- *)
Section ark.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma gse_callS : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx SEGS B G 0 [] STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + k1) /\
 ajournal_gx SEGS B G 0 [] STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k regsc STK1 o ch1 HJi); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
Lemma gse_keep_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma gse_pres : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
Lemma gse_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma gse_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hp Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
End ark.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_gestures_end's statement is the AR
   walk's, byte-identical, now a corollary of pb_gestures_end_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [].  Its Section takes LX0 (the laws at ARi0) in place of LAWS: the instance builds it once,
   W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The spec bridge is W_contract_x.gse_spec_x_AR0, the cut
   points' W_gse_cut.gse_loop_at_x_of_AR0 / gse_tail_at_x_of_AR0; HP0 at ARi0 is ARi0_hp0; IMGC / BLKN are
   W_kit_x.AR_imgc / AR_blkn. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis GSE_LOOP : gse_loop_at B MT MMAX RG (BASE + A_gse_loop).
Hypothesis GSE_TAIL : gse_tail_at B MT MMAX RG (BASE + A_gse_tail).
Theorem pb_gestures_end : gse_spec B MT MMAX RG A_gestures_endP.
Proof.
apply gse_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (gse_loop_at_x_of_AR0 B MT MMAX RG _ GSE_LOOP) as GSE_LOOP_X.
pose proof (gse_tail_at_x_of_AR0 B MT MMAX RG _ GSE_TAIL) as GSE_TAIL_X.
eapply (pb_gestures_end_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG); eassumption.
Qed.
End cAR.
End b.
End a.
