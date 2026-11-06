(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_copy on the ASan+UBSan build of plugin-hostd/fuzz_command
   (image fuzz_command.asan-ubsan, entry 0x89c34, 177 instructions), proving trec_calls_copy_spec
   (lib/B/Prog/rec_calls_copy_c.v), ported from the ASan walk lib/A/Prog/rec_calls_copy.v (same shape: the symbolic
   executor over the position-abstract listing CmdPaLib.v, the seven inline shadow checks removed by the shadow entries
   of each cut point PaShadow.v, the outer loop by induction on the calls left with the call index a number in each
   run, the inner loop by induction on the arguments left).
   What differs from the A walk (B-PREP.md, rec_calls_copy): A's `jal xstrdup` is inlined here as three call steps of
   the inner body, the strlen wrapper at 0x89da8 (aj_art_at with the statement's ASTRLEN), the program call of xmalloc
   at 0x89db4 (cl_callS with the statement's HXMALLOC, its call target by HSIG) and `__asan_memcpy` at 0x89dc4
   (aj_intrin_atS with the statement's AMEMCPY), each runtime hypothesis taken at the walk's own FP state (none of
   them changes it); the 160-byte frame and the B cut points (outer head 0x89cc4, inner head 0x89d7c, latch 0x89e14,
   epilogue 0x89e90; lib/B/Prog/rec_calls_copy_s1.v). The six UBSan trap branches (all to the unimp at 0x89ed0) are
   decided by the runs themselves: 0x89cc8 from the concrete call index of each outer run (i <= 1 < 16), 0x89cfc,
   0x89d0c and 0x89d14 from dst >= 4096 and the two predicate slots 8(sp) = 16(sp) = 1 (dst mod 8 = 0, dst <> 0; the
   entry's values of them are computed at the outer head), 0x89d7c and 0x89dc8 from the facts on ~cursor (s0) and
   ~(dst[i].args) (s5) against 8a <= 40 (the inner state's facts).
   xmalloc's frame chain: s0 holds ~(&g_rec.calls[i].args) at the call, 7 mod 8, so achain's empty case gives it
   (the statement's own remark; YCbq.v:264-265). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdBase CmdRep CmdObj CmdAddr CmdGlob xmalloc_c rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_copy_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PRcc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.
Lemma rcc_nodup_r : forall (l1 l2 : list Z), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
intros l1 l2 H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. revert l2 H.
induction l1 as [|y l1 IH]; intros l2 H; [exact H|].
cbn [app] in H. apply List.NoDup_cons_iff in H. exact (IH l2 (proj2 H)).
Qed.
Lemma rcc_nodup_snoc : forall (l : list Z) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
intros l x H Hn. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
induction l as [|y l IH]; cbn [app]; [constructor; [intros [] | constructor]|].
apply List.NoDup_cons_iff in H as [Hy Hd]. constructor.
- intros Hin. apply in_app_or in Hin as [Hin | [<- | []]]; [exact (Hy Hin)|]. apply Hn. left. reflexivity.
- apply IH; [exact Hd|]. intros Hin. apply Hn. right. exact Hin.
Qed.
(* `not` of a 64-bit value *)
Lemma rcc_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
assert (Hb : forall n, 64 <= n -> Z.testbit x n = false).
{ intros n Hn. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
rewrite Z.sub_nocarry_ldiff.
- apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
  + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  + rewrite Z.ones_spec_high, Hb by lia. reflexivity.
- apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
  + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  + rewrite Hb by lia. reflexivity.
Qed.
(* the denotations of the register and slot shapes the runs produce *)
Lemma rcc_den_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.
(* the two UBSan predicate slots the entry stores: 16(sp) = (dst != 0), 8(sp) = (dst & 7 == 0) & (dst != 0) *)
Lemma rcc_den_c16 : forall E cv, ew E 10 = Z_to_bv 64 cv -> 0 < cv < 2 ^ 64 ->
 sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) = Z_to_bv 64 1.
Proof.
intros E cv H Hc. apply rcc_den_of_U. rewrite U_SAlu, U_SLit, U_SOff, H, unsigned_lit_small, Z.add_0_r by lia.
cbn [zalu_raw]. rewrite (zcanon_small cv) by lia. change (zcanon 0) with 0.
destruct (Z.ltb_spec 0 cv); [reflexivity | lia].
Qed.
Lemma rcc_den_c8 : forall E cv, ew E 10 = Z_to_bv 64 cv -> 0 < cv < 2 ^ 64 -> cv mod 8 = 0 ->
 sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 10 0))) = Z_to_bv 64 1.
Proof.
intros E cv H Hc H8. apply rcc_den_of_U. rewrite !U_SAlu, !U_SLit, !U_SOff, H, unsigned_lit_small, Z.add_0_r by lia.
cbn [zalu_raw]. rewrite (zcanon_small cv) by lia.
change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite H8.
destruct (Z.ltb_spec (zcanon 0) cv) as [_|Hn]; [|change (zcanon 0) with 0 in Hn; lia].
vm_compute. reflexivity.
Qed.
(* s0 and s5 at the inner head: not (v + c) *)
Lemma rcc_den_not : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
 sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = Z_to_bv 64 (NOTW (v + c)).
Proof.
intros E n v c H H0 Hc H1. apply rcc_den_of_U. rewrite U_SAlu, U_SLit, U_SOff, H, unsigned_lit_small by lia.
cbn [zalu_raw]. rewrite (zcanon_small (v + c)) by lia. change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite rcc_lxor_ones64 by lia. apply zcanon_small. unfold NOTW. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses (rec_calls_copy_c.v, Section e): the program callee xmalloc and the two runtime
   entries of the inlined xstrdup, each at every FP state (pass 4b); the walk keeps the FP state (no callee changes
   it), so it takes each at its own fx; and the bridge from the image's addresses to the listing's atoms *)
Hypothesis HXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis HVAL : cmd_val_objs.
(* the per-binary record (CmdRecFacts.v): the shadow GOT and cell and the strlen/malloc entries (TL), the image's
   symbols (HB: g_rec and record.spill are program statics), the image facts (IMG), the meter laws (MTL, to chain
   the xmalloc calls' meters) and the call target of xmalloc (HSIG) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HSIG : cmd_sig_prog.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a := cif_prog_img _ _ IMG.
Let cif_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a :=
  fun a H => proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG a H).
(* a block's word tail, for a byte below the request (the block's request size is at least the request) *)
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p k e, AR SEGS B ly S W mem md ->
In (p, k) (ablocks B ly S) -> p <= e < p + k -> atail_vis SEGS W mem e :=
  fun ly S W mem md p k e HAR Hin He => cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p k e HAR Hin
    (conj (proj1 He) (Z.lt_le_trans _ _ _ (proj2 He) (proj1 (Z.add_le_mono_l _ _ p) (crf_req_size_ge k)))).
Let errno_low := pal_env B TL.
(* the walk's runners *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* the meter and the live bytes of one argument: one xmalloc of |s| + 1 bytes *)
Definition LIVE_ARG (x : list byte) : Z := Z.of_nat (length x) + 1.
Definition XM_ARG (x : list byte) : Z := XM_XMALLOC MT (Z.of_nat (length x) + 1).
Lemma rcc_xm_arg_nonneg : forall x, 0 <= XM_ARG x.
Proof. intros x. unfold XM_ARG, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. Qed.

(* g_rec and record.spill are program statics: no runtime entry owns them, and they are not errno *)
Lemma rcc_pg : forall a, inFP cmd_PG a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha.
assert (HP : Exists (in_zr a) (as_prog_static B)).
{ rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
  destruct Ha as (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
  - apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
destruct (prog_static_sep B a (ts_ok B HB) HP) as (H1 & H2 & _). auto.
Qed.
(* a live block lies in application memory below alloc_ceiling *)
Lemma rcc_blk_rng : forall lyc Sc (Wc : world SEGS) memc mdc pn, AR SEGS B lyc Sc Wc memc mdc -> In pn (ablocks B lyc Sc) ->
4096 <= fst pn /\ fst pn + snd pn <= alloc_ceiling /\ 0 <= snd pn.
Proof.
intros lyc Sc Wc memc mdc [p n] HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
pose proof (req_size_pos n (proj1 Hm)) as [_ Hq]. cbn [fst snd]. lia.
Qed.

(* ---------- one call of rec_calls_copy ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (dst : Z) (R : rstate) (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B REC_CALLS_COPY_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 dst.
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HLEN : (length (r_calls R) <= 2)%nat.
Hypothesis HOBJ : afobj SEGS B ly S W mem dst (CALL_SIZE * Z.of_nat (length (r_calls R))).
Hypothesis HEV : st_nev S + EV_REC_CALLS_COPY R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_REC_CALLS_COPY R <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_REC_CALLS_COPY MT R).
#[local] Notation STK := REC_CALLS_COPY_STK.
#[local] Notation NC := (length (r_calls R)).
#[local] Notation FP := [(dst, dst + CALL_SIZE * Z.of_nat (length (r_calls R)))].

(* the statement's post-condition *)
Definition rcc_Q : world SEGS -> config -> Prop :=
apost_base SEGS B STK FP regs ly S W mem md (EV_REC_CALLS_COPY R)
(fun ly' S' W' regs' mem' md' => exists qs : list (list (Z * Z)),
 getr regs' 10 = w64 (Z.of_nat (length (r_calls R))) /\
 length qs = length (r_calls R) /\
 (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
   acall_at (ablocks B ly' S') (rdW W' mem') (dst + CALL_SIZE * Z.of_nat i) c P /\
   forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1) /\
 Permutation (ablocks B ly' S') (ablocks B ly S ++ concat qs) /\
 NoDup (map fst (concat qs)) /\
 (forall pn q, In pn (concat qs) -> In q (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q) (snd q)) /\
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 rec_repA B ly' S' (rdW W' mem') R O /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_COPY R /\
 mo_le MT S S' (XM_REC_CALLS_COPY MT R)).

(* the stack and the copy table *)
Lemma rcc_geo : spZ regs mod 16 = 0 /\ alloc_ceiling + STK <= spZ regs <= 2 ^ 47 /\
4096 <= dst /\ dst + CALL_SIZE * Z.of_nat NC <= alloc_ceiling /\ dst mod 8 = 0 /\
exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= dst /\ dst + CALL_SIZE * Z.of_nat NC <= frame_addr ly cid pos + fs_frame_bytes cid /\
in_app (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOBJ as ((cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2) & Hd8 & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
assert (Hn0 : 0 <= CALL_SIZE * Z.of_nat NC) by (unfold CALL_SIZE; lia).
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hd8|].
exists cid, pos. split; [exact Hfin|]. split; [exact Hcid|]. split; [exact Hfal|]. split; [exact Hf1|].
split; [exact Hf2 | exact Hfapp].
Qed.

(* at a later state of the walk (its journal from the entry, the blocks only grown): the blocks that were live are
   kept, so is the recorder, and the read-only bytes *)
Lemma rcc_now : forall lyc Sc Wc memc mdc k bln,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
Permutation (ablocks B lyc Sc) (ablocks B ly S ++ bln) ->
(forall p n x, In (p, n) (ablocks B ly S) -> 0 <= x < n -> rdW Wc memc (p + x) = rdW W mem (p + x)) /\
rec_repA B lyc Sc (rdW Wc memc) R O /\ arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros lyc Sc Wc memc mdc k bln HJ HPm.
pose proof HPRE as (HAR & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & F3 & F4 & Hgone & _).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2 & Hfapp).
assert (HinS : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyc Sc))
  by (intros pn H; eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact H]).
assert (HFPa : forall a, inFP FP a -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)
  by (intros a (r & [<- | []] & Ha); cbn [fst snd] in Ha; lia).
assert (HSP : ~ YI16.sink_open_fp FP)
  by (apply sink_closed_pos; apply Forall_cons; [cbn [fst]; lia | apply Forall_nil]).
assert (KB : forall p n x, In (p, n) (ablocks B ly S) -> 0 <= x < n -> rdW Wc memc (p + x) = rdW W mem (p + x)).
{ intros p n x Hin Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos n ltac:(lia)) as [Hq1 Hq2].
  apply (F2 p n x Hin (HinS _ Hin)); [lia|].
  intros Hf. apply HFPa in Hf.
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n cid pos HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW Wc memc a = rdW W mem a).
{ intros a Hi Ho He. apply F3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [exact HSP|].
  intros Hf. apply HFPa in Hf. exact (frm_img SEGS B LAWS ly S W mem md cid pos a HAR Hfin Hf Hi). }
split; [exact KB|]. split.
- apply (rcc_rep_grow B ly S lyc Sc (rdW W mem) (rdW Wc memc) R O HREP); [| exact HinS | exact KB].
  intros a Ha.
  assert (HPG : inFP cmd_PG a).
  { destruct Ha as [Ha | Ha].
    - exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
    - exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]. }
  destruct (rcc_pg a HPG) as [Ho He]. exact (KI a (cif_prog_img a HPG) Ho He).
- intros a Hro Ho He. rewrite (KI a (cif_ro_img a Hro) Ho He). exact (HROD a Hro Ho He).
Qed.

(* ---------- the cut points ---------- *)
(* the thirteen registers the prologue saved *)
Definition rcc_saves (rd : reader) : Prop :=
forall j r, nth_error rcc_saved j = Some r ->
aval_mem rd (spZ regs - 160 + 152 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the frame's words: &g_rec, the two UBSan predicates of dst, dst, the two copies of the cursor of call i *)
Definition rcc_slots (rd : reader) (i : nat) : Prop :=
aval_mem rd (spZ regs - 160) 8 A_G_REC /\ aval_mem rd (spZ regs - 160 + 8) 8 1 /\
aval_mem rd (spZ regs - 160 + 16) 8 1 /\ aval_mem rd (spZ regs - 160 + 24) 8 dst /\
aval_mem rd (spZ regs - 160 + 40) 8 (A_G_REC + 24 + 56 * Z.of_nat i) /\
aval_mem rd (spZ regs - 160 + 48) 8 (A_G_REC + 24 + 56 * Z.of_nat i).
(* the call index, spilled by the outer head *)
Definition rcc_islot (rd : reader) (i : nat) : Prop := aval_mem rd (spZ regs - 160 + 32) 8 (Z.of_nat i).
(* the journal from the entry, the copies made so far (xs, in the blocks bln), the frame, sp, gp and tp *)
Definition rcc_cut (xs : list (list byte)) (bln : list (Z * Z)) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs1 : bvmap 5 word) : Prop :=
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= Z.of_nat (length xs) /\
Permutation (ablocks B lyc Sc) (ablocks B ly S ++ bln) /\
NoDup (map fst bln) /\ Forall (fun pn => 1 <= snd pn) bln /\
(forall pn q, In pn bln -> In q (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q) (snd q)) /\
blocks_bytes Sc <= blocks_bytes S + zsum LIVE_ARG xs /\
mo_le MT S Sc (zsum XM_ARG xs) /\
rcc_saves (rdW Wc memc) /\
getr regs1 2 = w64 (spZ regs - 160) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4.
(* the copy table: slots 0 .. i-1 hold the calls, their arguments in the blocks of qs *)
Definition rcc_tab (rd : reader) (bl : list (Z * Z)) (i : nat) (qs : list (list (Z * Z))) : Prop :=
length qs = i /\
forall j c P, nth_error (r_calls R) j = Some c -> nth_error qs j = Some P ->
acall_at bl rd (dst + CALL_SIZE * Z.of_nat j) c P /\
(forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1).
(* slot i during its copy: the two scalar fields, and its first a arguments in the blocks Pa *)
Definition rcc_part (rd : reader) (bl : list (Z * Z)) (i : nat) (c : rcall) (a : nat) (Pa : list (Z * Z)) : Prop :=
length Pa = a /\
aval_mem rd (dst + CALL_SIZE * Z.of_nat i) 4 (fst c) /\
aval_mem rd (dst + CALL_SIZE * Z.of_nat i + 4) 4 (Z.of_nat (length (snd c))) /\
forall j s pn, nth_error (snd c) j = Some s -> nth_error Pa j = Some pn ->
aval_mem rd (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat j) 8 (fst pn) /\
fst pn <> 0 /\ In pn bl /\ snd pn = Z.of_nat (length s) + 1 /\ astr_atR rd (fst pn) s.
(* the epilogue 0x89e90: every call copied, a1 = the call count *)
Definition rcc_RT (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
rcc_cut (PRcc.rcc_args (r_calls R)) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) NC qs /\ getr regs1 11 = w64 (Z.of_nat NC).
(* the outer loop head 0x89cc4, about to copy call i: a2 = &g_rec, a4 = i, s8 = the shadow base, s10 = s11 = the
   copy's argument array *)
Definition rcc_OH (i : nat) (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
(i < NC)%nat /\
rcc_cut (PRcc.rcc_args (firstn i (r_calls R))) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) i qs /\ rcc_slots (rdW Wc memc) i /\
getr regs1 12 = w64 A_G_REC /\ getr regs1 14 = w64 (Z.of_nat i) /\ getr regs1 24 = w64 SB /\
getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i) /\ getr regs1 27 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the outer latch 0x89e14, call i copied *)
Definition rcc_LT (i : nat) (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
(i < NC)%nat /\
rcc_cut (PRcc.rcc_args (firstn (Datatypes.S i) (r_calls R))) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) (Datatypes.S i) qs /\ rcc_slots (rdW Wc memc) i /\ rcc_islot (rdW Wc memc) i /\
getr regs1 24 = w64 SB /\
getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i) /\ getr regs1 27 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the inner loop head 0x89d7c, about to copy argument a of call i (= c): s0 = ~cursor, s1 = &dst[i].nargs,
   s5 = ~(dst[i].args), s6 = a, s7 = 8a, s9 = the shadow cell of s1 *)
Definition rcc_IH (i a : nat) (c : rcall) (qs : list (list (Z * Z))) (Pa : list (Z * Z)) lyc Sc Wc memc mdc k regs1 : Prop :=
nth_error (r_calls R) i = Some c /\ (a < length (snd c))%nat /\
rcc_cut (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) (concat qs ++ Pa) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) i qs /\ rcc_part (rdW Wc memc) (ablocks B lyc Sc) i c a Pa /\
rcc_slots (rdW Wc memc) i /\ rcc_islot (rdW Wc memc) i /\
getr regs1 8 = w64 (NOTW (A_G_REC + 24 + 56 * Z.of_nat i)) /\ getr regs1 9 = w64 (dst + (4 + 56 * Z.of_nat i)) /\
getr regs1 21 = w64 (NOTW (dst + 8 + 56 * Z.of_nat i)) /\
getr regs1 22 = w64 (Z.of_nat a) /\ getr regs1 23 = w64 (8 * Z.of_nat a) /\ getr regs1 24 = w64 SB /\
getr regs1 25 = w64 (SB + (dst + (4 + 56 * Z.of_nat i)) / 8) /\
getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i) /\ getr regs1 27 = w64 (dst + 8 + 56 * Z.of_nat i).

(* the table facts at a later reader: their bytes kept *)
Lemma rcc_tab_keep : forall (rd rd' : reader) bl bl' i qs,
rcc_tab rd bl i qs ->
(forall x, dst <= x < dst + CALL_SIZE * Z.of_nat i -> rd' x = rd x) ->
(forall pn, In pn (concat qs) -> In pn bl -> In pn bl' /\ forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
rcc_tab rd' bl' i qs.
Proof.
intros rd rd' bl bl' i qs (Hlen & HT) K KB. split; [exact Hlen|].
intros j c P Hc HP. destruct (HT j c P Hc HP) as [Hcall Hsz]. split; [|exact Hsz].
assert (Hj : (j < i)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite HP; discriminate).
apply (rcc_call_keep bl bl' rd rd' _ c P Hcall).
- intros x Hx. apply K. unfold CALL_SIZE in *. lia.
- intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
Qed.
Lemma rcc_part_keep : forall (rd rd' : reader) bl bl' i c a Pa,
rcc_part rd bl i c a Pa ->
(forall x, dst + CALL_SIZE * Z.of_nat i <= x < dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a -> rd' x = rd x) ->
(forall pn, In pn Pa -> In pn bl -> In pn bl' /\ forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
rcc_part rd' bl' i c a Pa.
Proof.
intros rd rd' bl bl' i c a Pa (Hlen & Hfn & Hna & HA) K KB.
split; [exact Hlen|].
split; [apply (rcc_aval_keep rd _ _ _ _ Hfn); intros j Hj; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ Hna); intros j Hj; apply K; lia|].
intros j s pn Hs Hp. destruct (HA j s pn Hs Hp) as (Hv & H0 & Hin & Hsz & Hstr).
assert (Hj : (j < a)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hp; discriminate).
destruct (KB pn (nth_error_In _ _ Hp) Hin) as [Hin' Kp].
split; [apply (rcc_aval_keep rd _ _ _ _ Hv); intros x Hx; apply K; lia|].
split; [exact H0|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (rcc_str_keep rd _ _ _ Hstr). intros x Hx. apply Kp. lia.
Qed.
(* an 8-byte word read back from a symbolic region, any value *)
Lemma rcc_chunk_gen : forall E H (m : word -> option byte) (nb : nat) b lo hi wlo whi cs off e v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
bv_unsigned (ew E nb) = b -> In (YP09.mkChunk off (CVal 8 e)) cs -> bv_unsigned (sv_denot E e) = v ->
aval_mem (aview SEGS H m) (b + off) 8 v.
Proof.
intros E H m nb b lo hi wlo whi cs off e v HR Hb Hin Hv.
pose proof (field_of_region_any E _ nb b cs lo hi wlo whi off 8%N e HR Hb Hin ltac:(cbn; lia)) as Hm.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite Hv in Hm, Hr. change (8 * Z.of_N 8) with 64 in Hm. rewrite Z.mod_small in Hm by lia. change (N.to_nat 8) with 8%nat in Hm.
apply (rcc_aval_of_val H m (b + off) 8 v); [change (8 * Z.of_nat 8) with 64; lia | exact Hm].
Qed.
(* a 4-byte field read back from a symbolic region *)
Lemma rcc_chunk_val4 : forall E H (m : word -> option byte) (nb : nat) b lo hi wlo whi cs off (n : nat) c v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
bv_unsigned (ew E nb) = b ->
In (YP09.mkChunk off (CVal 4 (SOff n c))) cs ->
bv_unsigned (ew E n) + c = v -> 0 <= v < 2 ^ 32 ->
aval_mem (aview SEGS H m) (b + off) 4 v.
Proof.
intros E H m nb b lo hi wlo whi cs off n c v HR Hb Hin Hv Hr.
pose proof (field_of_region_any E _ nb b cs lo hi wlo whi off 4%N (SOff n c) HR Hb Hin ltac:(cbn; lia)) as Hm.
cbn [sv_denot] in Hm. rewrite Hv in Hm. rewrite unsigned_lit_small in Hm by lia.
change (8 * Z.of_N 4) with 32 in Hm. rewrite Z.mod_small in Hm by lia. change (N.to_nat 4) with 4%nat in Hm.
apply (rcc_aval_of_val H m (b + off) 4 v); [change (8 * Z.of_nat 4) with 32; lia | exact Hm].
Qed.
Lemma rcc_den_atom : forall E (n : nat) c, bv_unsigned (sv_denot E (SOff n c)) = (bv_unsigned (ew E n) + c) mod 2 ^ 64.
Proof. intros E n c. cbn [sv_denot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma rcc_den_val : forall E (n : nat) c v, bv_unsigned (ew E n) + c = v -> 0 <= v < 2 ^ 64 ->
bv_unsigned (sv_denot E (SOff n c)) = v.
Proof. intros E n c v Hv Hr. rewrite rcc_den_atom, Hv. apply Z.mod_small. exact Hr. Qed.
(* the frame's words, read back from the frame region at sp - 160 *)
Lemma rcc_slots_of : forall E H (m : word -> option byte) wlo whi cs i e0 e8 e16 e24 e40 e48,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 160 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 160 ->
In (YP09.mkChunk 0 (CVal 8 e0)) cs -> bv_unsigned (sv_denot E e0) = A_G_REC ->
In (YP09.mkChunk 8 (CVal 8 e8)) cs -> bv_unsigned (sv_denot E e8) = 1 ->
In (YP09.mkChunk 16 (CVal 8 e16)) cs -> bv_unsigned (sv_denot E e16) = 1 ->
In (YP09.mkChunk 24 (CVal 8 e24)) cs -> bv_unsigned (sv_denot E e24) = dst ->
In (YP09.mkChunk 40 (CVal 8 e40)) cs -> bv_unsigned (sv_denot E e40) = A_G_REC + 24 + 56 * Z.of_nat i ->
In (YP09.mkChunk 48 (CVal 8 e48)) cs -> bv_unsigned (sv_denot E e48) = A_G_REC + 24 + 56 * Z.of_nat i ->
rcc_slots (aview SEGS H m) i.
Proof.
intros E H m wlo whi cs i e0 e8 e16 e24 e40 e48 HR Hb C0 V0 C8 V8 C16 V16 C24 V24 C40 V40 C48 V48.
split; [rewrite <- (Z.add_0_r (spZ regs - 160)); exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 0 e0 A_G_REC HR Hb C0 V0)|].
split; [exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 8 e8 1 HR Hb C8 V8)|].
split; [exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 16 e16 1 HR Hb C16 V16)|].
split; [exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 24 e24 dst HR Hb C24 V24)|].
split; [exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 40 e40 _ HR Hb C40 V40)|].
exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 48 e48 _ HR Hb C48 V48).
Qed.
Lemma rcc_islot_of : forall E H (m : word -> option byte) wlo whi cs i e,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 160 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 160 ->
In (YP09.mkChunk 32 (CVal 8 e)) cs -> bv_unsigned (sv_denot E e) = Z.of_nat i ->
rcc_islot (aview SEGS H m) i.
Proof. intros E H m wlo whi cs i e HR Hb C V. exact (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs 32 e _ HR Hb C V). Qed.
Lemma rcc_saves_get : forall E H (m : word -> option byte) wlo whi cs,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 160 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 160 ->
(forall j, (j < 13)%nat -> ew E (42 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0))) ->
(forall j, (j < 13)%nat -> In (rcc_sav j) cs) ->
rcc_saves (aview SEGS H m).
Proof.
intros E H m wlo whi cs HR Hb Esv Cs j r Hj.
assert (Hj13 : (j < length rcc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length rcc_saved] in Hj13.
assert (Hr : r = nth j rcc_saved 0) by (symmetry; apply nth_error_nth; exact Hj). subst r.
replace (spZ regs - 160 + 152 - 8 * Z.of_nat j) with (spZ regs - 160 + (152 - 8 * Z.of_nat j)) by lia.
apply (rcc_chunk_gen E H m 2 _ 0 160 wlo whi cs (152 - 8 * Z.of_nat j) (SOff (42 + j) 0) _ HR Hb (Cs j Hj13)).
apply rcc_den_val; [rewrite (Esv j Hj13); lia | apply bv_unsigned_in_range].
Qed.
Lemma rcc_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma rcc_blt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia.
rewrite !rcc_swrap_small by lia. reflexivity.
Qed.
Lemma rcc_bge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia.
rewrite !rcc_swrap_small by lia. reflexivity.
Qed.
(* After a symbolic run the model is `with_vm_backing (m_vm_lazy md) mat md`; naming it (and forgetting the body)
   keeps the next run from nesting two copies of it. *)
Ltac clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* the bytes a run keeps: every byte outside its regions' windows *)
Ltac rcc_keep HFr K Zs :=
  lazymatch type of HFr with frame_of ?Ex _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  let T := eval cbv beta in (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m2 a = aview SEGS H m1 a) in
  assert (K : T)
  by (intros a0 Ha0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr); [| exact Ha0 | exact Hn0];
      intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta; lia|]);
      destruct Hin) end.
(* ---------- seeds ---------- *)
Lemma rcc_seed : forall E (regs1 : bvmap 5 word) pc sregs rs G SH (Wc : world SEGS) memc,
regs_ok E sregs regs1 -> regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict (w_H Wc) memc)) rs ->
pairwise_disjoint E rs -> facts_ok E G -> Forall (shent_ok SEGS rcc_Bx E (mrestrict (w_H Wc) memc)) SH ->
st_ok_pi SEGS VAL E (mkSS pc sregs rs None G) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS rcc_Bx SH E (mrestrict (w_H Wc) memc).
Proof. intros. split; [|assumption]. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; assumption. Qed.

(* ---------- the epilogue: 0x89e90 .. 0x89ecc, ra and s0..s11 restored, a0 := a1, ret ---------- *)
Lemma rcc_ret : forall qs lyc Sc Wc memc mdc k regs1,
rcc_RT qs lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_RET)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros qs lyc Sc Wc memc mdc k regs1 ((HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & R11).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
assert (Hnc : 0 <= Z.of_nat NC <= 2) by lia.
assert (HE2 : bv_unsigned (ew (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) 2) = spZ regs - 160).
{ rewrite (rcc_EE regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0 2%nat 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. lia. }
destruct (rcc_seed (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) regs1 RCC_RET rcc_regs_r [rcc_stkr] rcc_facts_r [] Wc memc
  (rcc_regs_r_ok regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0 R11 Hnc)
  ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [|apply Forall_nil];
        exact (rcc_stkr_ok regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0 Wc memc (spZ regs - 160) R2
          ltac:(lia) ltac:(lia) HSV))
  ltac:(apply pairwise_disjoint_of_extents; cbn [map zpairwise_disjoint zall_disjoint]; repeat split)
  ltac:(apply (rcc_facts_r_ok regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0 (spZ regs - 160) HE2);
        [ lia | replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16 ])
  ltac:(apply Forall_nil)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0))
  by (unfold rcc_E; apply Eimg_env).
pose proof (rcc_Esav regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as Esv.
pose proof (rcc_E38 regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as E38.
pose proof (rcc_EE regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as EE.
remember (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk sp0 fp b0 bc f0 lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia | apply awr_ok_nil]. }
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN end.
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rcc_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyc, Sc, r, m, d end.
split.
{ rewrite F1. change 42%nat with (42 + 0)%nat. rewrite (Esv 0%nat ltac:(lia)). cbn [nth rcc_saved].
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  unfold EV_REC_CALLS_COPY, EV_XMALLOC, ev_args. rewrite rcc_ev_len. lia. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot].
  1: { rewrite HE2. replace (spZ regs - 160 + 160) with (spZ regs) by lia.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). unfold spZ. apply Z_to_bv_bv_unsigned. }
  1: { rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (Z_to_bv 5 3) eq_refl).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3. }
  1: { rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (Z_to_bv 5 4) eq_refl).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4. }
  all: rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?n = getr _ _ =>
      let j := eval compute in (n - 42)%nat in change n with (42 + j)%nat; rewrite (Esv j ltac:(lia)); reflexivity end. }
destruct (rcc_now lyc Sc Wc _ _ k (concat qs) HJ HPm) as (KB & HREPc & _).
exists qs.
split; [rewrite F10, E38; reflexivity|].
split; [exact (proj1 HTAB)|].
split.
{ apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B lyc Sc) NC qs HTAB).
  - intros x Hx. apply UN; [unfold CALL_SIZE in *; lia | tauto].
  - intros pn _ Hb. split; [exact Hb|]. intros j Hj.
    destruct (rcc_blk_rng _ _ _ _ _ pn (proj1 HJ) Hb) as (Hp4 & Hpc & Hn0). apply UN; [lia | tauto]. }
split; [exact HPm|]. split; [exact HND|]. split; [exact HAP|]. split; [exact KB|]. split; [exact HREPc|].
split; [unfold LIVE_REC_CALLS_COPY; exact HBB | exact HMLE].
Qed.

(* a register of a symbolic state, its value left as the denotation of its symbolic form *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* the copy table is apart from g_rec: a frame is never in the image, and g_rec is *)
Lemma rcc_dst_grec : forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> ~ (A_G_REC <= x < A_G_REC + 960).
Proof.
intros x Hx Hg.
pose proof HPRE as (HAR & _).
pose proof rcc_geo as (_ & _ & _ & _ & _ & cid & pos & Hfin & _ & _ & Hf1 & Hf2 & _).
apply (frm_img SEGS B LAWS ly S W mem md cid pos x HAR Hfin ltac:(lia)).
apply cif_prog_img. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.
(* a write into the copy table: a footprint byte in a frame of the caller (awr_byte's frames-of-S clause) *)
Lemma rcc_awr_dst : forall lyc Sc Wc memc mdc k a,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
dst <= a < dst + CALL_SIZE * Z.of_nat NC ->
awr_byte SEGS B STK (spZ regs) FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a.
Proof.
intros lyc Sc Wc memc mdc k a HJ Ha.
pose proof HPRE as (HAR & _).
pose proof HJ as (_ & Hly & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
pose proof rcc_geo as (_ & _ & _ & _ & _ & cid & pos & Hfin & _ & _ & Hf1 & Hf2 & _).
right; right; right; right. unfold awr_prog_or_caller. right; right. split.
- exists (dst, dst + CALL_SIZE * Z.of_nat NC). split; [left; reflexivity | cbn [fst snd]; lia].
- exists cid, pos. split; [exact Hfin|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa. lia.
Qed.
(* a block live at a later state of the walk lies below alloc_ceiling and apart from the copy table *)
Lemma rcc_blk_dst : forall lyc Sc Wc memc mdc k pn,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
In pn (ablocks B lyc Sc) ->
4096 <= fst pn /\ fst pn + snd pn <= alloc_ceiling /\ 0 <= snd pn /\
(fst pn + snd pn <= dst \/ dst + CALL_SIZE * Z.of_nat NC <= fst pn).
Proof.
intros lyc Sc Wc memc mdc k [p n] HJ Hin.
pose proof HPRE as (HAR & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
pose proof rcc_geo as (_ & _ & _ & _ & _ & cid & pos & Hfin & _ & _ & Hf1 & Hf2 & _).
assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
pose proof (req_size_pos n (proj1 Hm)) as [_ Hq].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n cid pos HARc Hin Hfinc) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. rewrite Efa in Hd. lia.
Qed.
(* the write rules of the walk's runs: the frame, read-only regions, the copy table *)
Ltac rcc_awr Usp WS HJ :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk sp0 fp b0 bc f0 lyx own) end;
  repeat first
  [ apply (awr_ok_cons_ro SEGS B); [cbn; lia|]
  | eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := -160);
    [reflexivity | rewrite Usp; lia | cbn; rewrite WS; lia | cbn; lia |]
  | eapply awr_ok_cons_gen;
    [reflexivity | eassumption | cbn [YP09.r_wlo YP09.r_whi]; intros ax Hax; eapply rcc_awr_dst;
     [exact HJ | unfold CALL_SIZE in *; lia] |] ];
  apply awr_ok_nil.
(* a shadow-check entry, for any environment whose atom 32 is the shadow base *)
Lemma rcc_shent_any : forall E (m : nat) q lo hi (W' : world SEGS) mem',
bv_unsigned (ew E 32) = SB -> bv_unsigned (ew E m) = q -> lo <= hi ->
range_addressable (rdW W' mem') SHADOW_OFF (q + lo) (hi - lo) ->
(forall x, q + lo <= x < q + hi -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
shent_ok SEGS rcc_Bx E (mrestrict (w_H W') mem') (mkSHE m lo hi).
Proof.
intros E m q lo hi W' mem' E32 Hq Hlh Hra Hap.
assert (HBx : U E rcc_Bx = SHADOW_OFF)
  by (unfold U, rcc_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia); reflexivity).
assert (Hm : U E (SOff m 0) = q) by (unfold U; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hq).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hm.
split; [rewrite <- (aview_rd_of SEGS); exact Hra|].
intros x Hx. apply Hap. revert Hx. replace (Z.min lo hi) with lo by lia. replace (Z.max lo hi) with hi by lia. exact (fun h => h).
Qed.
(* the copy table's shadow at a later state: kept from the entry (afobj) *)
Lemma rcc_tab_ra : forall lyc Sc Wc memc mdc k,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
range_addressable (rdW Wc memc) SHADOW_OFF dst (CALL_SIZE * Z.of_nat NC) /\
(forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
Proof.
intros lyc Sc Wc memc mdc k HJ.
pose proof HPRE as (HAR & _).
pose proof rcc_geo as (_ & _ & _ & _ & _ & cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2 & Hfapp).
assert (Happ : forall x, frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid -> x < kLowShadowBeg \/ kHighShadowEnd <= x)
  by (intros x Hx; pose proof asan_consts as (_ & C2 & C3 & _); unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
split.
- apply (range_addressable_entry_frame SEGS B LAWS STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k cid pos dst
    (CALL_SIZE * Z.of_nat NC) HJ Hfin Hcid Hf1 Hf2 Hfal); [| exact HAR | exact (proj2 (proj2 HOBJ))].
  intros x (r & [<- | []] & Hx). cbn [fst snd] in Hx. apply Happ. lia.
- intros x Hx. pose proof (Happ x ltac:(lia)) as Hb. unfold kLowShadowBeg, SHADOW_OFF in *.
  pose proof asan_consts as (_ & C2 & _). lia.
Qed.
Lemma rcc_perm_snoc : forall (l1 l2 l3 : list (Z * Z)) x, Permutation l2 l3 -> Permutation l1 (x :: l2) -> Permutation l1 (l3 ++ [x]).
Proof.
intros l1 l2 l3 x H23 H1. eapply Permutation_trans; [exact H1|]. eapply Permutation_trans; [apply Permutation_cons_append|].
apply Permutation_app_tail. exact H23.
Qed.
(* the source call i and its argument a, at a state where the recorder holds *)
Lemma rcc_src_call : forall lyc Sc (rd : reader) i c, rec_repA B lyc Sc rd R O -> nth_error (r_calls R) i = Some c ->
0 <= fst c < REC_FN_COUNT /\ (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros lyc Sc rd i c (Q & HA & _) Hc.
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hc; discriminate).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
destruct (C4 i c P Hc HP) as [(Hfn & Hn6 & _) HL]. auto.
Qed.
Lemma rcc_src_arg : forall lyc Sc (rd : reader) i c a, rec_repA B lyc Sc rd R O ->
nth_error (r_calls R) i = Some c -> (a < length (snd c))%nat ->
exists s sa sn, nth_error (snd c) a = Some s /\
aval_mem rd (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) 8 sa /\
sa <> 0 /\ In (sa, sn) (ablocks B lyc Sc) /\ Z.of_nat (length s) + 1 <= sn /\ Z.of_nat (length s) <= LMAX /\
astr_atR rd sa s.
Proof.
intros lyc Sc rd i c a (Q & HA & _) Hc Ha.
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hc; discriminate).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
destruct (C4 i c P Hc HP) as [(Hfn & Hn6 & HlP & _ & _ & _ & Hargs) HL].
destruct (nth_error (snd c) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (nth_error P a) as [[sa sn]|] eqn:Hp; [|apply nth_error_None in Hp; lia].
destruct (Hargs a s (sa, sn) Hs Hp) as (Hv & H0 & Hin & Hsz & Hstr).
pose proof (proj1 (Forall_forall _ _) HL s (nth_error_In _ _ Hs)) as HsL.
exists s, sa, sn. cbn [fst snd] in *.
split; [reflexivity|].
split; [replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  with (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a)
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS; lia); exact Hv|].
split; [exact H0|]. split; [exact Hin|]. split; [lia|]. split; [exact HsL | exact Hstr].
Qed.
(* slot i, once its last argument is copied, holds call i *)
Lemma rcc_slot_of_part : forall rd bl i c Pa, rcc_part rd bl i c (length (snd c)) Pa ->
0 <= fst c < REC_FN_COUNT -> (length (snd c) <= 6)%nat -> Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c) ->
NoDup (map fst Pa) ->
acall_at bl rd (dst + CALL_SIZE * Z.of_nat i) c Pa /\
(forall a s pn, nth_error (snd c) a = Some s -> nth_error Pa a = Some pn -> snd pn = Z.of_nat (length s) + 1).
Proof.
intros rd bl i c Pa (Hlen & Hfn & Hna & HA) Hf H6 HL HND.
split.
- unfold acall_at. split; [exact Hf|]. split; [exact H6|]. split; [exact Hlen|].
  split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact Hfn|].
  split; [unfold CALL_OFF_NARGS; exact Hna|].
  split; [exact HND|].
  intros j s pn Hs Hp. destruct (HA j s pn Hs Hp) as (Hv & H0 & Hin & Hsz & Hstr).
  pose proof (proj1 (Forall_forall _ _) HL s (nth_error_In _ _ Hs)) as HsL.
  split; [unfold CALL_OFF_ARGS; exact Hv|]. split; [exact H0|]. split; [exact Hin|].
  split; [unfold LMAX in *; lia | exact Hstr].
- intros j s pn Hs Hp. destruct (HA j s pn Hs Hp) as (_ & _ & _ & Hsz & _). exact Hsz.
Qed.
Lemma rcc_tab_snoc : forall rd bl i qs c P, rcc_tab rd bl i qs -> nth_error (r_calls R) i = Some c ->
acall_at bl rd (dst + CALL_SIZE * Z.of_nat i) c P /\
(forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1) ->
rcc_tab rd bl (Datatypes.S i) (qs ++ [P]).
Proof.
intros rd bl i qs c P (Hlen & HT) Hc HSl. split; [rewrite length_app, Hlen; cbn [length]; lia|].
intros j c' P' Hc' HP'. destruct (Nat.lt_ge_cases j i) as [Hj|Hj].
- rewrite nth_error_app1 in HP' by lia. exact (HT j c' P' Hc' HP').
- rewrite nth_error_app2 in HP' by lia. rewrite Hlen in HP'.
  destruct (j - i)%nat as [|t] eqn:Ejt; cbn in HP'; [|destruct t; discriminate].
  injection HP' as <-. assert (j = i) by lia. subst j. rewrite Hc in Hc'. injection Hc' as <-. exact HSl.
Qed.
Lemma rcc_part_snoc : forall rd bl i c a Pa s pn, rcc_part rd bl i c a Pa -> nth_error (snd c) a = Some s ->
aval_mem rd (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a) 8 (fst pn) -> fst pn <> 0 -> In pn bl ->
snd pn = Z.of_nat (length s) + 1 -> astr_atR rd (fst pn) s ->
rcc_part rd bl i c (Datatypes.S a) (Pa ++ [pn]).
Proof.
intros rd bl i c a Pa s pn (Hlen & Hfn & Hna & HA) Hs Hv H0 Hin Hsz Hstr.
split; [rewrite length_app, Hlen; cbn [length]; lia|]. split; [exact Hfn|]. split; [exact Hna|].
intros j s' pn' Hs' Hp'. destruct (Nat.lt_ge_cases j a) as [Hj|Hj].
- rewrite nth_error_app1 in Hp' by lia. exact (HA j s' pn' Hs' Hp').
- rewrite nth_error_app2 in Hp' by lia. rewrite Hlen in Hp'.
  destruct (j - a)%nat as [|t] eqn:Ejt; cbn in Hp'; [|destruct t; discriminate].
  injection Hp' as <-. assert (j = a) by lia. subst j. rewrite Hs in Hs'. injection Hs' as <-.
  split; [exact Hv|]. split; [exact H0|]. split; [exact Hin|]. split; [exact Hsz | exact Hstr].
Qed.
(* a 64-bit literal equation, once its operands are numbers *)
Ltac rcc_w64 := unfold w64; rewrite ?unsigned_lit_small by (unfold A_G_REC, SB, CALL_SIZE in *; lia); f_equal; lia.
(* two non-empty ranges with no common address are apart *)
Lemma rcc_iv_of_ne : forall lo1 hi1 lo2 hi2,
lo1 < hi1 -> lo2 < hi2 -> (forall a, lo1 <= a < hi1 -> lo2 <= a < hi2 -> False) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof.
intros lo1 hi1 lo2 hi2 H1 H2 H.
destruct (Z_le_gt_dec hi1 lo2) as [|Hg1]; [left; lia|].
destruct (Z_le_gt_dec hi2 lo1) as [|Hg2]; [right; lia|].
exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.

(* ---------- the outer latch: 0x89e14 .. 0x89e44, then the outer head or (via 0x89e48) the epilogue ---------- *)
Lemma rcc_latch : forall i qs lyc Sc Wc memc mdc k regs1,
(forall memc' mdc' regs1', rcc_OH (Datatypes.S i) qs lyc Sc Wc memc' mdc' k regs1' ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_OUTER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
rcc_LT i qs lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_LATCH)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i qs lyc Sc Wc memc mdc k regs1 OHK
  (Hi & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HSL & HIS & R24 & R26 & R27).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct (rcc_now lyc Sc Wc memc mdc k (concat qs) HJ HPm) as (_ & HREPc & _).
assert (HNC : aval_mem (rdW Wc memc) (A_G_REC + 8) 4 (Z.of_nat NC)).
{ destruct HREPc as (Q & (_ & _ & _ & (_ & _ & HN & _) & _) & _). exact HN. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
assert (Hwr : forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 160 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
set (G0 := A_G_REC + 24 + 56 * Z.of_nat i).
pose proof (rcc_E285' regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i) HVAL) as E285.
pose proof (rcc_E33 regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E33.
pose proof (rcc_E32 regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E32.
pose proof (rcc_E36 regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E36.
pose proof (rcc_E38 regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E38.
pose proof (rcc_E41 regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E41.
pose proof (rcc_Esav regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as Esv.
pose proof (rcc_EE regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i))) by (unfold rcc_E; apply Eimg_env).
assert (HSK : region_ok SEGS (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) (mrestrict (w_H Wc) memc) rcc_stkl).
{ apply (rcc_stkl_ok regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i) HVAL Wc memc (spZ regs - 160) R2);
    [lia | lia | unfold CALL_SIZE in *; lia | lia | unfold G0, A_G_REC; lia | exact Hwr | | exact HIS].
  destruct HSL as (F0 & F8 & F16 & F24 & F40 & F48). exact (conj F0 (conj F8 (conj F16 (conj F24 (conj F40 (conj F48 HSV)))))). }
assert (HNR : region_ok SEGS (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) (mrestrict (w_H Wc) memc) rcc_nc)
  by (apply (rcc_nc_ok regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i) HVAL Wc memc); [lia | exact HNC]).
assert (HRS : regs_ok (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) sr_atoms regs1) by (unfold rcc_E; apply regs_ok_Eimg_Ereg).
assert (HFL : facts_ok (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) rcc_facts_l).
{ apply (rcc_facts_l_ok regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i) HVAL (spZ regs - 160));
  [ rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia
  | lia | replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
  | unfold G0; lia | unfold G0; replace (A_G_REC + 24 + 56 * Z.of_nat i) with (A_G_REC + (3 + 7 * Z.of_nat i) * 8) by lia;
    rewrite Z_mod_plus_full; reflexivity
  | lia | lia ]. }
remember (rcc_E regs1 regs dst 0 0 G0 0 (Z.of_nat NC) 0 0 (Z.of_nat i)) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 160) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E36u : bv_unsigned (ew E 36) = G0) by (rewrite E36; apply unsigned_lit_small; unfold G0, A_G_REC; lia).
assert (E38u : bv_unsigned (ew E 38) = Z.of_nat NC) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E41u : bv_unsigned (ew E 41) = Z.of_nat i) by (rewrite E41; apply unsigned_lit_small; lia).
assert (E26u : bv_unsigned (ew E 26) = dst + 8 + 56 * Z.of_nat i)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E27u : bv_unsigned (ew E 27) = dst + 8 + 56 * Z.of_nat i)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
destruct (rcc_seed E regs1 RCC_LATCH sr_atoms [rcc_stkl; rcc_nc] rcc_facts_l [] Wc memc) as [HS SHOK].
{ exact HRS. }
{ vm_compute. reflexivity. }
{ apply Forall_cons; [exact HSK | apply Forall_cons; [exact HNR | apply Forall_nil]]. }
{ apply pairwise_disjoint_of_extents. unfold rcc_stkl, rcc_nc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 44) with 285%nat.
  rewrite Usp, E285u. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC. repeat split; lia. }
{ exact HFL. }
{ apply Forall_nil. }
clear HSK HNR HRS HFL.
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ rcc_awr Usp WS HJ. }
rcc_keep HFr K1 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
- (* i + 1 < nc: back to the outer head *)
  assert (HSi : (Datatypes.S i < NC)%nat).
  { cbn [sv_denot] in Hc. rewrite E41u, E38u, Z.add_0_r in Hc. rewrite rcc_blt in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_OUTER.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (12%bv : bv 5) Q12.
  prreg HS (14%bv : bv 5) Q14. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) rcc_nc) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  apply OHK.
  split; [exact HSi|].
  split.
  { split; [exact HJ|]. split; [exact Hk|]. split; [exact HPm|]. split; [exact HND|]. split; [exact H1|].
    split; [exact HAP|]. split; [exact HBB|]. split; [exact HMLE|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3|].
    rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4. }
  split.
  { apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B lyc Sc) (Datatypes.S i) qs HTAB).
    - intros x Hx. rewrite K2, K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - intros pn _ Hb. split; [exact Hb|]. intros j Hj.
      destruct (rcc_blk_rng _ _ _ _ _ pn (proj1 HJ) Hb) as (Hp4 & Hpc & Hn0). rewrite K2, K1 by lia. reflexivity. }
  split.
  { apply (rcc_slots_of E _ _ _ _ _ (Datatypes.S i) (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 36 56) (SOff 36 56) HRg Usp);
    [ cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
    | cbn; tauto | reflexivity | cbn; tauto | reflexivity
    | cbn; tauto | apply rcc_den_val; [rewrite E33u; lia | unfold CALL_SIZE in *; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u; unfold G0; lia | unfold A_G_REC; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u; unfold G0; lia | unfold A_G_REC; lia] ]. }
  split; [rewrite Q12, E285; reflexivity|].
  split; [rewrite Q14, E41u; unfold w64; f_equal; lia|].
  split; [rewrite Q24, (EE 24%nat 24%bv eq_refl); exact R24|].
  split; [rewrite Q26, E26u; unfold w64; f_equal; lia|].
  rewrite Q27, E27u; unfold w64; f_equal; lia.
- (* the last call: on to the epilogue *)
  assert (HSi : Datatypes.S i = NC).
  { cbn [sv_denot] in Hc. rewrite E41u, E38u, Z.add_0_r in Hc. rewrite rcc_blt in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_RET.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (11%bv : bv 5) Q11.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) rcc_nc) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  rewrite HSi, firstn_all in Hk, HBB, HMLE. rewrite HSi in HTAB.
  apply (rcc_ret qs lyc Sc Wc _ _ k _).
  split.
  { split; [exact HJ|]. split; [exact Hk|]. split; [exact HPm|]. split; [exact HND|]. split; [exact H1|].
    split; [exact HAP|]. split; [exact HBB|]. split; [exact HMLE|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3|].
    rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4. }
  split.
  { apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B lyc Sc) NC qs HTAB).
    - intros x Hx. rewrite K2, K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - intros pn _ Hb. split; [exact Hb|]. intros j Hj.
      destruct (rcc_blk_rng _ _ _ _ _ pn (proj1 HJ) Hb) as (Hp4 & Hpc & Hn0). rewrite K2, K1 by lia. reflexivity. }
  rewrite Q11, E38. reflexivity.
Qed.

(* ---------- the outer body: 0x89cc4 .. 0x89d60 (call i's two scalar fields into slot i), then the inner head
   0x89d7c or, for a call with no argument, the latch 0x89e14 ---------- *)
(* the source call's two scalar fields, at a state where the recorder holds *)
Lemma rcc_src_fields : forall lyc Sc (rd : reader) i c, rec_repA B lyc Sc rd R O -> nth_error (r_calls R) i = Some c ->
aval_mem rd (A_G_REC + 16 + 56 * Z.of_nat i) 4 (fst c) /\ aval_mem rd (A_G_REC + 20 + 56 * Z.of_nat i) 4 (Z.of_nat (length (snd c))).
Proof.
intros lyc Sc rd i c (Q & HA & _) Hc.
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hc; discriminate).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
destruct (C4 i c P Hc HP) as [(_ & _ & _ & Hb0 & Hb1 & _) _].
split.
- replace (A_G_REC + 16 + 56 * Z.of_nat i) with (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_FN)
    by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia). exact Hb0.
- replace (A_G_REC + 20 + 56 * Z.of_nat i) with (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS)
    by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia). exact Hb1.
Qed.
(* the state after the outer body: the journal, the bytes kept (all but the frame and slot i's two fields), the
   frame, slot i's fields, and the registers the latch and the inner head read *)
Definition rcc_OB (i : nat) (na fn : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(k : Z) (regs1 : bvmap 5 word) (memc' : word -> option byte) (mdc' : Model) (regs1' : bvmap 5 word) : Prop :=
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc' mdc' k /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat i <= x < dst + 56 * Z.of_nat i + 8) ->
  rdW Wc memc' x = rdW Wc memc x) /\
rcc_saves (rdW Wc memc') /\ rcc_slots (rdW Wc memc') i /\ rcc_islot (rdW Wc memc') i /\
aval_mem (rdW Wc memc') (dst + 56 * Z.of_nat i) 4 fn /\ aval_mem (rdW Wc memc') (dst + 56 * Z.of_nat i + 4) 4 na /\
getr regs1' 2 = getr regs1 2 /\ getr regs1' 3 = getr regs1 3 /\ getr regs1' 4 = getr regs1 4 /\
getr regs1' 24 = w64 SB /\
getr regs1' 26 = w64 (dst + 8 + 56 * Z.of_nat i) /\ getr regs1' 27 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the outer body's runs, for each of the (at most two) calls: the call index is a number in each run *)
Lemma rcc_ob_run : forall i, (i < 2)%nat -> forall E lyc Sc Wc memc mdc k regs1 na fn,
(i < NC)%nat -> img_env VAL A_LIM E ->
bv_unsigned (ew E 2) = spZ regs - 160 -> ew E 32 = Z_to_bv 64 SB -> ew E 33 = Z_to_bv 64 dst -> bv_unsigned (ew E 33) = dst ->
ew E 285 = Z_to_bv 64 A_G_REC -> bv_unsigned (ew E 285) = A_G_REC -> bv_unsigned (ew E 37) = na -> bv_unsigned (ew E 39) = fn ->
0 <= na <= 6 -> 0 <= fn < 2 ^ 31 ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) ->
(forall j, (j < 13)%nat -> ew E (42 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0))) ->
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
st_ok_pi SEGS VAL E (mkSS RCC_OUTER (rcc_regs_o (Z.of_nat i)) [rcc_stk (Z.of_nat i); rcc_src (Z.of_nat i); rcc_dst0 (Z.of_nat i)]
  None rcc_facts) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS))) ->
sh_ok SEGS rcc_Bx (rcc_SH_o (Z.of_nat i)) E (mrestrict (w_H Wc) memc) ->
(forall memc' mdc' regs1', rcc_OB i na fn lyc Sc Wc memc k regs1 memc' mdc' regs1' -> na <= 0 ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
(forall memc' mdc' regs1', rcc_OB i na fn lyc Sc Wc memc k regs1 memc' mdc' regs1' -> 0 < na ->
  getr regs1' 8 = w64 (NOTW (A_G_REC + 24 + 56 * Z.of_nat i)) -> getr regs1' 9 = w64 (dst + (4 + 56 * Z.of_nat i)) ->
  getr regs1' 21 = w64 (NOTW (dst + 8 + 56 * Z.of_nat i)) -> getr regs1' 22 = w64 0 -> getr regs1' 23 = w64 0 ->
  getr regs1' 25 = w64 (SB + (dst + (4 + 56 * Z.of_nat i)) / 8) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_INNER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i Hi2 E lyc Sc Wc memc mdc k regs1 na fn Hi HEI Usp E32 E33 E33u E285 E285u E37u E39u Hna Hfn EE Esv HJ HS SHOK LTC IHC.
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct i as [|[|i]]; [| | lia].
- (* call 0 *)
  paj_run_tok RUN HS HJ SHOK rcc_Bspan.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K1 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
  clear HF HFr HG. clear_md.
  psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
  + (* no argument: on to the latch 0x89e14 *)
    assert (Hnz : na <= 0).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_LATCH.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (24%bv : bv 5) Q24.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply LTC; [|exact Hnz].
    split; [exact HJ|].
    split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [apply (rcc_slots_of E _ _ _ _ _ 0%nat (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 285 24) (SOff 285 24) HRg Usp);
      [ cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | reflexivity | cbn; tauto | reflexivity
      | cbn; tauto | apply rcc_den_val; [rewrite E33u; lia | unfold CALL_SIZE in *; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia] ]|].
    split; [apply (rcc_islot_of E _ _ _ _ _ 0%nat (SLit 0) HRg Usp); [cbn; tauto | reflexivity]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat) with (dst + 0) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 0 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat + 4) with (dst + 4) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 4 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24, E32; reflexivity|].
    split; [rewrite Q26, E33u; rcc_w64|].
    rewrite Q27, E33u; rcc_w64.
  + (* an argument: on to the inner head 0x89d7c *)
    assert (Hnz : 0 < na).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_INNER.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (24%bv : bv 5) Q24.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg_raw HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg_raw HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg_raw HS (25%bv : bv 5) Q25.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply IHC.
    { split; [exact HJ|].
    split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [apply (rcc_slots_of E _ _ _ _ _ 0%nat (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 285 24) (SOff 285 24) HRg Usp);
      [ cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | reflexivity | cbn; tauto | reflexivity
      | cbn; tauto | apply rcc_den_val; [rewrite E33u; lia | unfold CALL_SIZE in *; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia] ]|].
    split; [apply (rcc_islot_of E _ _ _ _ _ 0%nat (SLit 0) HRg Usp); [cbn; tauto | reflexivity]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat) with (dst + 0) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 0 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat + 4) with (dst + 4) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 4 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24, E32; reflexivity|].
    split; [rewrite Q26, E33u; rcc_w64|].
    rewrite Q27, E33u; rcc_w64. }
    { exact Hnz. }
    { rewrite Q8, (rcc_den_not E 285 A_G_REC 24 E285 ltac:(unfold A_G_REC; lia) ltac:(lia) ltac:(unfold A_G_REC; lia)).
      replace (A_G_REC + 24 + 56 * Z.of_nat 0%nat) with (A_G_REC + 24) by lia. reflexivity. }
    { rewrite Q9, E33u; rcc_w64. }
    { rewrite Q21, (rcc_den_not E 33 dst 8 E33 ltac:(lia) ltac:(lia) ltac:(unfold CALL_SIZE in *; lia)).
      replace (dst + 8 + 56 * Z.of_nat 0%nat) with (dst + 8) by lia. reflexivity. }
    { rewrite Q22; reflexivity. }
    { rewrite Q23; reflexivity. }
    { rewrite Q25, (denot_shx E 33 32 4 dst SB E33 E32 ltac:(lia) ltac:(lia) ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold SB; lia)).
      replace (dst + (4 + 56 * Z.of_nat 0%nat)) with (dst + 4) by lia. reflexivity. }
- (* call 1 *)
  paj_run_tok RUN HS HJ SHOK rcc_Bspan.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K1 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
  clear HF HFr HG. clear_md.
  psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
  + (* no argument: on to the latch 0x89e14 *)
    assert (Hnz : na <= 0).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_LATCH.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (24%bv : bv 5) Q24.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply LTC; [|exact Hnz].
    split; [exact HJ|].
    split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [apply (rcc_slots_of E _ _ _ _ _ 1%nat (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 285 80) (SOff 285 80) HRg Usp);
      [ cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | reflexivity | cbn; tauto | reflexivity
      | cbn; tauto | apply rcc_den_val; [rewrite E33u; lia | unfold CALL_SIZE in *; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia] ]|].
    split; [apply (rcc_islot_of E _ _ _ _ _ 1%nat (SLit 1) HRg Usp); [cbn; tauto | reflexivity]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat) with (dst + 56) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 56 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat + 4) with (dst + 60) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 60 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24, E32; reflexivity|].
    split; [rewrite Q26, E33u; rcc_w64|].
    rewrite Q27, E33u; rcc_w64.
  + (* an argument: on to the inner head 0x89d7c *)
    assert (Hnz : 0 < na).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_INNER.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (24%bv : bv 5) Q24.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg_raw HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg_raw HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg_raw HS (25%bv : bv 5) Q25.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply IHC.
    { split; [exact HJ|].
    split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
    split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [apply (rcc_slots_of E _ _ _ _ _ 1%nat (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 285 80) (SOff 285 80) HRg Usp);
      [ cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | reflexivity | cbn; tauto | reflexivity
      | cbn; tauto | apply rcc_den_val; [rewrite E33u; lia | unfold CALL_SIZE in *; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]
      | cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia] ]|].
    split; [apply (rcc_islot_of E _ _ _ _ _ 1%nat (SLit 1) HRg Usp); [cbn; tauto | reflexivity]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat) with (dst + 56) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 56 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat + 4) with (dst + 60) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 60 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24, E32; reflexivity|].
    split; [rewrite Q26, E33u; rcc_w64|].
    rewrite Q27, E33u; rcc_w64. }
    { exact Hnz. }
    { rewrite Q8, (rcc_den_not E 285 A_G_REC 80 E285 ltac:(unfold A_G_REC; lia) ltac:(lia) ltac:(unfold A_G_REC; lia)).
      replace (A_G_REC + 24 + 56 * Z.of_nat 1%nat) with (A_G_REC + 80) by lia. reflexivity. }
    { rewrite Q9, E33u; rcc_w64. }
    { rewrite Q21, (rcc_den_not E 33 dst 64 E33 ltac:(lia) ltac:(lia) ltac:(unfold CALL_SIZE in *; lia)).
      replace (dst + 8 + 56 * Z.of_nat 1%nat) with (dst + 64) by lia. reflexivity. }
    { rewrite Q22; reflexivity. }
    { rewrite Q23; reflexivity. }
    { rewrite Q25, (denot_shx E 33 32 60 dst SB E33 E32 ltac:(lia) ltac:(lia) ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold SB; lia)).
      replace (dst + (4 + 56 * Z.of_nat 1%nat)) with (dst + 60) by lia. reflexivity. }
Qed.
Lemma rcc_outer_body : forall i qs lyc Sc Wc memc mdc k regs1,
(forall c lyc' Sc' Wc' memc' mdc' k' regs1', rcc_IH i 0 c qs [] lyc' Sc' Wc' memc' mdc' k' regs1' ->
  SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_INNER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
(forall qs' lyc' Sc' Wc' memc' mdc' k' regs1', rcc_LT i qs' lyc' Sc' Wc' memc' mdc' k' regs1' ->
  SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
rcc_OH i qs lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i qs lyc Sc Wc memc mdc k regs1 IHK LTK
  (Hi & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HSL & R12 & R14 & R24 & R26 & R27).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2 & Hfapp).
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct (nth_error (r_calls R) i) as [c|] eqn:Hci; [|apply nth_error_None in Hci; lia].
destruct (rcc_now lyc Sc Wc memc mdc k (concat qs) HJ HPm) as (_ & HREPc & _).
destruct (rcc_src_call lyc Sc (rdW Wc memc) i c HREPc Hci) as (Hfn & Hn6 & HLMAX).
destruct (rcc_src_fields lyc Sc (rdW Wc memc) i c HREPc Hci) as (Ffn & Fna).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARc Hfinc) as (_ & _ & Hfp & _).
assert (Hi2 : (i < 2)%nat) by lia.
assert (Hwr : forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 160 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
assert (HwrD : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H Wc) memc) (dst + 56 * Z.of_nat i + o)).
{ intros o Ho. apply (apresent_writable SEGS).
  apply (proj1 (Hfp (dst + 56 * Z.of_nat i + o) ltac:(rewrite Efa; unfold CALL_SIZE in *; lia))). }
destruct (rcc_tab_ra lyc Sc Wc memc mdc k HJ) as (HRAt & HBDt).
set (na := Z.of_nat (length (snd c))).
pose proof (rcc_E285' regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 HVAL) as E285.
pose proof (rcc_E32 regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as E32.
pose proof (rcc_E33 regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as E33.
pose proof (rcc_E37 regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as E37.
pose proof (rcc_E39 regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as E39.
pose proof (rcc_Esav regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as Esv.
pose proof (rcc_EE regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0)) by (unfold rcc_E; apply Eimg_env).
destruct (rcc_seed (rcc_E regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0)
  regs1 RCC_OUTER (rcc_regs_o (Z.of_nat i)) [rcc_stk (Z.of_nat i); rcc_src (Z.of_nat i); rcc_dst0 (Z.of_nat i)] rcc_facts
  (rcc_SH_o (Z.of_nat i)) Wc memc) as [HS SHOK].
{ apply (rcc_regs_o_ok regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 HVAL (Z.of_nat i) R12 R14 R24 R26 R27); unfold CALL_SIZE in *; lia. }
{ destruct i as [|[|i]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_stk_ok regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 HVAL Wc memc (Z.of_nat i) (spZ regs - 160) R2);
    [lia | lia | lia | lia | unfold CALL_SIZE in *; lia | exact Hwr |].
    destruct HSL as (F0 & F8 & F16 & F24 & F40 & F48). exact (conj F0 (conj F8 (conj F16 (conj F24 (conj F40 (conj F48 HSV)))))).
  - apply (rcc_src_ok regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 HVAL Wc memc (Z.of_nat i));
    [lia | lia | unfold REC_FN_COUNT in *; lia | unfold na; lia | exact Ffn | exact Fna].
  - apply (rcc_dst0_ok regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 Wc memc (Z.of_nat i)); [lia | lia | unfold CALL_SIZE in *; lia | exact HwrD]. }
{ apply pairwise_disjoint_of_extents. unfold rcc_stk, rcc_src, rcc_dst0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 44) with 285%nat.
  rewrite (EE 2%nat 2%bv eq_refl), R2, E285, E33.
  unfold w64. rewrite !unsigned_lit_small by (unfold A_G_REC, CALL_SIZE in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (rcc_dst_grec dst ltac:(unfold CALL_SIZE in *; lia)) as HAp0.
  assert (HDG : dst + CALL_SIZE * Z.of_nat NC <= A_G_REC \/ A_G_REC + 960 <= dst).
  { apply (rcc_iv_of_ne dst (dst + CALL_SIZE * Z.of_nat NC) A_G_REC (A_G_REC + 960)); [unfold CALL_SIZE; lia | unfold A_G_REC; lia |].
    intros x Hx1 Hx2. exact (rcc_dst_grec x Hx1 Hx2). }
  unfold A_G_REC, CALL_SIZE in *. repeat split; lia. }
{ apply (rcc_facts_ok regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0 HVAL (spZ regs - 160));
  [ rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia
  | lia | replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
  | unfold CALL_SIZE in *; lia | exact Hd8 | unfold na; lia | lia | unfold REC_FN_COUNT in *; lia ]. }
{ unfold rcc_SH_o. repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_shent_any _ 285%nat A_G_REC (16 + 56 * Z.of_nat i) (72 + 56 * Z.of_nat i) Wc memc);
    [ rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia | lia
    | apply (range_addressable_sub _ _ A_G_REC REC_SIZE);
      [exact (cmd_cf_grec SEGS B LAWS HB lyc Sc Wc memc _ HARc) | unfold A_G_REC in *; lia | unfold A_G_REC, REC_SIZE in *; lia]
    | intros x Hx; unfold A_G_REC, SHADOW_OFF in *; lia ].
  - apply (rcc_shent_any _ 33%nat dst (56 * Z.of_nat i) (56 * Z.of_nat i + 56) Wc memc);
    [ rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia | lia
    | apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia]
    | intros x Hx; apply HBDt; unfold CALL_SIZE in *; lia ]. }
remember (rcc_E regs1 regs dst 0 0 0 na (Z.of_nat NC) (fst c) 0 0) as E eqn:HE. clear HE.
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E37u : bv_unsigned (ew E 37) = na) by (rewrite E37; apply unsigned_lit_small; unfold na; lia).
assert (E39u : bv_unsigned (ew E 39) = fst c) by (rewrite E39; apply unsigned_lit_small; unfold REC_FN_COUNT in *; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 160) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
apply (rcc_ob_run i Hi2 E lyc Sc Wc memc mdc k regs1 na (fst c) Hi HEI Usp E32 E33 E33u E285 E285u E37u E39u
  ltac:(unfold na; lia) ltac:(unfold REC_FN_COUNT in *; lia) EE Esv HJ HS SHOK).
- (* no argument: slot i holds call i with no argument blocks *)
  intros memc' mdc' regs1' (HJ' & K & HSV' & HSL' & HIS' & Ffn' & Fna' & Q2 & Q3 & Q4 & Q24 & Q26 & Q27) Hn0.
  assert (Hc0 : snd c = []) by (destruct (snd c); [reflexivity | unfold na in Hn0; cbn [length] in Hn0; lia]).
  apply (LTK (qs ++ [[]]) lyc Sc Wc memc' mdc' k regs1').
  split; [exact Hi|].
  split.
  { rewrite (rcc_args_firstn_S (r_calls R) i c Hci), Hc0, app_nil_r, concat_app. cbn [concat]. rewrite !app_nil_r.
    split; [exact HJ'|]. split; [exact Hk|]. split; [exact HPm|]. split; [exact HND|]. split; [exact H1|].
    split; [exact HAP|]. split; [exact HBB|]. split; [exact HMLE|]. split; [exact HSV'|].
    split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. rewrite Q4; exact R4. }
  split.
  { apply (rcc_tab_snoc _ _ i qs c []).
    - apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B lyc Sc) i qs HTAB).
      + intros x Hx. apply K; unfold CALL_SIZE in *; lia.
      + intros pn _ Hb. split; [exact Hb|]. intros j Hj.
        destruct (rcc_blk_dst lyc Sc Wc memc mdc k pn HJ Hb) as (Hq4 & Hqc & _ & Hqd).
        apply K; unfold CALL_SIZE in *; lia.
    - exact Hci.
    - apply (rcc_slot_of_part _ _ i c []); [| exact Hfn | exact Hn6 | exact HLMAX | constructor].
      split; [rewrite Hc0; reflexivity|].
      split; [unfold CALL_SIZE; exact Ffn'|]. split; [unfold CALL_SIZE; exact Fna'|].
      intros j s pn _ Hp. destruct j; cbn in Hp; discriminate Hp. }
  split; [exact HSL'|]. split; [exact HIS'|].
  split; [exact Q24|]. split; [exact Q26|]. exact Q27.
- (* arguments: on to the inner loop at argument 0 *)
  intros memc' mdc' regs1' (HJ' & K & HSV' & HSL' & HIS' & Ffn' & Fna' & Q2 & Q3 & Q4 & Q24 & Q26 & Q27) Hn0
    Q8 Q9 Q21 Q22 Q23 Q25.
  apply (IHK c lyc Sc Wc memc' mdc' k regs1').
  split; [exact Hci|]. split; [unfold na in Hn0; lia|].
  split.
  { cbn [firstn]. rewrite !app_nil_r.
    split; [exact HJ'|]. split; [exact Hk|]. split; [exact HPm|]. split; [exact HND|]. split; [exact H1|].
    split; [exact HAP|]. split; [exact HBB|]. split; [exact HMLE|]. split; [exact HSV'|].
    split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. rewrite Q4; exact R4. }
  split.
  { apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B lyc Sc) i qs HTAB).
    - intros x Hx. apply K; unfold CALL_SIZE in *; lia.
    - intros pn _ Hb. split; [exact Hb|]. intros j Hj.
      destruct (rcc_blk_dst lyc Sc Wc memc mdc k pn HJ Hb) as (Hq4 & Hqc & _ & Hqd).
      apply K; unfold CALL_SIZE in *; lia. }
  split.
  { split; [reflexivity|].
    split; [unfold CALL_SIZE; exact Ffn'|]. split; [unfold CALL_SIZE; exact Fna'|].
    intros j s pn _ Hp. destruct j; cbn in Hp; discriminate Hp. }
  split; [exact HSL'|]. split; [exact HIS'|].
  split; [exact Q8|]. split; [exact Q9|]. split; [exact Q21|].
  split; [exact Q22|]. split; [exact Q23|]. split; [exact Q24|].
  split; [exact Q25|]. split; [exact Q26|]. exact Q27.
Qed.

(* ---------- the inner loop's helpers ---------- *)
Ltac rcc_side := first [unfold CALL_SIZE in *; lia | tauto].
(* a disjunctive fact kept out of lia's sight (lia splits on every disjunction in the context) *)
Definition rcc_or (P Q : Prop) : Prop := P \/ Q.
Lemma rcc_astr_some : forall (rd : reader) p x a, astr_atR rd p x -> p <= a < p + (Z.of_nat (length x) + 1) -> rd a <> None.
Proof.
intros rd p x a [Hb _] Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite Hb; [discriminate|]. rewrite length_app; cbn; lia.
Qed.
Lemma rcc_astr_move : forall (rd rd' : reader) s p x,
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (s + i)) -> astr_atR rd s x -> astr_atR rd' p x.
Proof.
intros rd rd' s p x Hm [Hb Hz]. split; [|exact Hz]. intros i Hi. rewrite Hm; [apply Hb; exact Hi|]. rewrite length_app in Hi; cbn in Hi; lia.
Qed.
(* every byte of the copy table is present at a later state of the walk (a frame of the caller) *)
Lemma rcc_tab_pres : forall lyc Sc Wc memc mdc k,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> apresent (w_H Wc) memc x.
Proof.
intros lyc Sc Wc memc mdc k HJ x Hx.
pose proof HPRE as (HAR & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
pose proof rcc_geo as (_ & _ & _ & _ & _ & cid & pos & Hfin & _ & _ & Hf1 & Hf2 & _).
assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARc Hfinc) as (_ & _ & Hfp & _).
apply (proj1 (Hfp x ltac:(rewrite Efa; lia))).
Qed.
(* the shadow entries of the inner loop after its first call: the copy table's slot i (around s1) and the copy's
   argument slot, at any later state of the walk *)
Lemma rcc_sha_ok : forall E lyc Sc Wc memc mdc k i a,
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
(i < NC)%nat -> (a < 6)%nat ->
bv_unsigned (ew E 32) = SB -> bv_unsigned (ew E 9) = dst + (4 + 56 * Z.of_nat i) ->
bv_unsigned (ew E 35) = dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a ->
sh_ok SEGS rcc_Bx rcc_SHa E (mrestrict (w_H Wc) memc).
Proof.
intros E lyc Sc Wc memc mdc k i a HJ Hi Ha E32u E9u E35u.
destruct (rcc_tab_ra lyc Sc Wc memc mdc k HJ) as (HRAt & HBDt).
repeat apply Forall_cons; try apply Forall_nil.
- apply (rcc_shent_any _ 9%nat (dst + (4 + 56 * Z.of_nat i)) (-4) 52 Wc memc); [exact E32u | exact E9u | lia | |].
  + apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia].
  + intros x Hx. apply HBDt. unfold CALL_SIZE in *. lia.
- apply (rcc_shent_any _ 35%nat (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) 0 8 Wc memc); [exact E32u | exact E35u | lia | |].
  + rewrite Z.add_0_r. replace (8 - 0) with 8 by lia.
    apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia].
  + intros x Hx. apply HBDt. unfold CALL_SIZE in *. lia.
Qed.

(* ---------- the inner loop's body: 0x89d7c .. 0x89dfc; the inlined xstrdup at 0x89da8 (strlen), 0x89db4 (xmalloc),
   0x89dc4 (__asan_memcpy) ---------- *)
Lemma rcc_inner_step : forall i a c qs Pa lyc Sc Wc memc mdc k regs1,
(forall qs' lyc' Sc' Wc' memc' mdc' k' regs1', rcc_LT i qs' lyc' Sc' Wc' memc' mdc' k' regs1' ->
  SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
((Datatypes.S a < length (snd c))%nat -> forall Pa' lyc' Sc' Wc' memc' mdc' k' regs1',
  rcc_IH i (Datatypes.S a) c qs Pa' lyc' Sc' Wc' memc' mdc' k' regs1' ->
  SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_INNER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
rcc_IH i a c qs Pa lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_INNER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i a c qs Pa lyc Sc Wc memc mdc k regs1 LTK NXT
  (Hc & Ha & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HPART & HSL & HIS
   & R8 & R9 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2 & Hfapp).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. assert (HXS : XMALLOC_STK = 16400) by reflexivity.
assert (Hi : (i < NC)%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
destruct (rcc_now lyc Sc Wc memc mdc k (concat qs ++ Pa) HJ HPm) as (KBe & HREPc & HRODc).
destruct (rcc_src_call lyc Sc (rdW Wc memc) i c HREPc Hc) as (Hfn & Hn6 & HLMAX).
destruct (rcc_src_arg lyc Sc (rdW Wc memc) i c a HREPc Hc Ha) as (s & sa & sn & Hs & HVsa & Hsa0 & Hsain & Hsn & HsL & Hstr).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpresc & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
assert (Ha6 : (a < 6)%nat) by lia.
assert (HNA : aval_mem (rdW Wc memc) (dst + (4 + 56 * Z.of_nat i)) 4 (Z.of_nat (length (snd c)))).
{ destruct HPART as (_ & _ & Hna & _). replace (dst + (4 + 56 * Z.of_nat i)) with (dst + CALL_SIZE * Z.of_nat i + 4)
    by (unfold CALL_SIZE; lia). exact Hna. }
destruct (rcc_blk_dst lyc Sc Wc memc mdc k (sa, sn) HJ Hsain) as (Hsa4 & Hsac & Hsn0 & Hsad).
cbn [fst snd] in Hsa4, Hsac, Hsn0, Hsad.
assert (HSAD : rcc_or (sa + sn <= dst) (dst + CALL_SIZE * Z.of_nat NC <= sa)) by exact Hsad. clear Hsad.
remember (A_G_REC + 24 + 56 * Z.of_nat i) as G0 eqn:EG0 in *.
remember (G0 + 8 * Z.of_nat a) as GA eqn:EGA in *.
remember (dst + 8 + 56 * Z.of_nat i) as D0 eqn:ED0 in *.
remember (D0 + 8 * Z.of_nat a) as DA eqn:EDA in *.
remember (dst + (4 + 56 * Z.of_nat i)) as X eqn:EX in *.
remember (Z.of_nat (length s) + 1) as n eqn:En in *.
remember (Z.of_nat (length (snd c))) as na eqn:Ena in *.
assert (Hna6 : 0 <= na <= 6) by lia.
assert (Hn1 : 1 <= n <= LMAX + 1) by lia.
assert (HwrD : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H Wc) memc) (DA + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply (rcc_tab_pres lyc Sc Wc memc mdc k HJ). unfold CALL_SIZE in *; lia. }
assert (Hwr : forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 160 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
destruct (rcc_tab_ra lyc Sc Wc memc mdc k HJ) as (HRAt & HBDt).
assert (HRAg : range_addressable (rdW Wc memc) SHADOW_OFF GA 8).
{ apply (range_addressable_sub _ _ A_G_REC REC_SIZE);
  [exact (cmd_cf_grec SEGS B LAWS HB lyc Sc Wc memc _ HARc) | unfold A_G_REC in *; lia | unfold A_G_REC, REC_SIZE in *; lia]. }
assert (HBDg : forall x, GA <= x < GA + 8 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))
  by (intros x Hx; unfold A_G_REC, SHADOW_OFF in *; lia).
assert (HG08 : G0 mod 8 = 0).
{ rewrite EG0. replace (A_G_REC + 24 + 56 * Z.of_nat i) with (A_G_REC + (3 + 7 * Z.of_nat i) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
assert (HD08 : D0 mod 8 = 0).
{ rewrite ED0. replace (dst + 8 + 56 * Z.of_nat i) with (dst + (1 + 7 * Z.of_nat i) * 8) by lia.
  rewrite Z_mod_plus_full. exact Hd8. }
assert (HX4 : X mod 4 = 0).
{ rewrite EX. destruct (proj1 (Z.mod_divide dst 8 ltac:(lia)) Hd8) as [q Hq].
  replace (dst + (4 + 56 * Z.of_nat i)) with (q * 2 * 4 + (1 + 14 * Z.of_nat i) * 4) by lia.
  rewrite Z.add_comm, Z_mod_plus_full. apply Z_mod_mult. }
pose proof (rcc_E285' regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) HVAL) as E285.
pose proof (rcc_E32 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E32.
pose proof (rcc_E33 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E33.
pose proof (rcc_E34 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E34.
pose proof (rcc_E35 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E35.
pose proof (rcc_E36 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E36.
pose proof (rcc_E37 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E37.
pose proof (rcc_E40 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E40.
pose proof (rcc_E41 regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E41.
pose proof (rcc_Esav regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as Esv.
pose proof (rcc_EE regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)))
  by (unfold rcc_E; apply Eimg_env).
destruct (rcc_seed (rcc_E regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i))
  regs1 RCC_INNER rcc_regs_i [rcc_stkl; rcc_dsti; rcc_ga; rcc_da] rcc_facts_i rcc_SHi Wc memc) as [HS SHOK].
{ apply (rcc_regs_i_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) X R9 R24 R25).
  unfold CALL_SIZE in *; lia. }
{ vm_compute. reflexivity. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_stkl_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) HVAL Wc memc (spZ regs - 160) R2);
    [lia | lia | unfold CALL_SIZE in *; lia | lia | unfold A_G_REC in *; lia | exact Hwr | | exact HIS].
    destruct HSL as (F0 & F8 & F16 & F24 & F40 & F48). subst G0.
    exact (conj F0 (conj F8 (conj F16 (conj F24 (conj F40 (conj F48 HSV)))))).
  - apply (rcc_dsti_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) Wc memc X R9);
    [unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | lia | exact HNA].
  - apply (rcc_ga_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) Wc memc);
    [unfold A_G_REC in *; lia | unfold A_G_REC in *; lia | lia | exact HVsa].
  - apply (rcc_da_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) Wc memc);
    [unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | exact HwrD]. }
{ assert (HDG : dst + CALL_SIZE * Z.of_nat NC <= A_G_REC \/ A_G_REC + 960 <= dst).
  { apply (rcc_iv_of_ne dst (dst + CALL_SIZE * Z.of_nat NC) A_G_REC (A_G_REC + 960)); [unfold CALL_SIZE; lia | unfold A_G_REC; lia |].
    intros x Hx1 Hx2. exact (rcc_dst_grec x Hx1 Hx2). }
  apply pairwise_disjoint_of_extents. unfold rcc_stkl, rcc_dsti, rcc_ga, rcc_da, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (EE 2%nat 2%bv eq_refl), R2, (EE 9%nat 9%bv eq_refl), R9, E34, E35.
  unfold w64. rewrite !unsigned_lit_small by (unfold A_G_REC, CALL_SIZE in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, CALL_SIZE in *. repeat split; lia. }
{ apply (rcc_facts_i_ok regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i) HVAL (spZ regs - 160) X G0 (Z.of_nat a) D0);
  [ rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia
  | lia | replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
  | exact R8 | exact R9 | exact R21 | exact R22 | exact R23 | exact R26 | exact R27
  | lia | exact HG08 | reflexivity | exact EGA | unfold CALL_SIZE in *; lia | exact HX4
  | lia | unfold CALL_SIZE in *; lia | exact HD08 | exact EDA | lia | lia | lia ]. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_shent_any _ 9%nat X (-4) 52 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia
    | lia
    | apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia]
    | intros x Hx; apply HBDt; unfold CALL_SIZE in *; lia].
  - apply (rcc_shent_any _ 34%nat GA 0 8 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E34; apply unsigned_lit_small; unfold A_G_REC in *; lia | lia
    | rewrite Z.add_0_r; replace (8 - 0) with 8 by lia; exact HRAg
    | intros x Hx; apply HBDg; lia].
  - apply (rcc_shent_any _ 35%nat DA 0 8 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E35; apply unsigned_lit_small; unfold CALL_SIZE in *; lia | lia
    | rewrite Z.add_0_r; replace (8 - 0) with 8 by lia;
      apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia]
    | intros x Hx; apply HBDt; unfold CALL_SIZE in *; lia]. }
remember (rcc_E regs1 regs dst GA DA G0 na (Z.of_nat NC) (fst c) sa (Z.of_nat i)) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 160)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E35u : bv_unsigned (ew E 35) = DA) by (rewrite E35; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E36u : bv_unsigned (ew E 36) = G0) by (rewrite E36; apply unsigned_lit_small; unfold A_G_REC in *; lia).
assert (E41u : bv_unsigned (ew E 41) = Z.of_nat i) by (rewrite E41; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E9u : bv_unsigned (ew E 9) = X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
(* ---- 0x89d7c .. 0x89da8: the wrap check (decided), the source slot's check, its word, the strlen call ---- *)
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ rcc_awr Usp WS HJ. }
rcc_keep HFr K1 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
clear HF HFr HG. clear_md.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ => set (rT0 := rT) in *; set (mT0 := mT) in *; set (dT0 := dT) in * end.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ mT0 dT0 _ |- _ => rename HJx into HJT end.
assert (HspT : spZ rT0 = spZ regs + -160) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (P3' : getr rT0 3 = w64 (as_gp B)).
{ rewrite P3, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3. exact Hgp. }
assert (P4' : getr rT0 4 = w64 (as_tp B)).
{ rewrite P4, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4. exact Htp. }
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 sa) by (rewrite P10, E40; reflexivity).
destruct (rcc_now lyc Sc Wc mT0 dT0 k (concat qs ++ Pa) HJT HPm) as (_ & _ & HRODT).
assert (HstrT : astr_atR (rdW Wc mT0) sa s).
{ unfold rcc_or in HSAD. apply (rcc_str_keep (rdW Wc memc)); [exact Hstr|]. intros x Hx. rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity. }
assert (HTAIL : atail_vis SEGS Wc mT0 (sa + astr_len s))
  by (unfold astr_len; exact (cmd_heap_tail_vis lyc Sc Wc mT0 dT0 sa sn (sa + Z.of_nat (length s)) (proj1 HJT) Hsain ltac:(lia))).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
    Wc rT0 mT0 STK (spZ regs) FP ly S W mem md [] lyc Sc dT0 k (-160) (getr rT0 1) _ HJT HspT eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite Hes, WS; lia) eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx lyc Sc Wc rT0 mT0 dT0 sa s).
  - exact (ecall_pre_stk_at SEGS B ESTACK STK (spZ regs) FP ly S W mem md [] lyc Sc Wc mT0 dT0 k rT0 (-160) HJT HspT eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite Hes, WS; lia) HraT P3' P4').
  - exact P10'.
  - lia.
  - apply astr_atR_view. exact HstrT.
  - apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc rT0 mT0 dT0 sa sn sa (astr_len s + 1) (proj1 HJT) Hsain);
    [lia | unfold astr_len; lia | unfold astr_len; lia | rewrite HspT, Hes; lia].
  - exact HTAIL.
  - exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI Wc mT0 HRODT). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
rewrite P1.
jafter_call_keep_pi HS 56%nat regs2 (mrestrict (w_H Wc) mem2) HP2 [0; 1; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  repeat apply Forall_cons; [| | | apply Forall_nil];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros x Hx.
  - rewrite Usp in Hx. apply (mbyte_of_aview SEGS). apply HK2; [lia | rewrite Hes; lia | tauto].
  - intros _. rewrite Usp in Hx. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia.
  - rewrite E9u in Hx. apply (mbyte_of_aview SEGS). apply HK2; [unfold CALL_SIZE in *; lia | rewrite Hes; unfold CALL_SIZE in *; lia | tauto].
  - lia.
  - rewrite E35u in Hx. apply (mbyte_of_aview SEGS). apply HK2; [unfold CALL_SIZE in *; lia | rewrite Hes; unfold CALL_SIZE in *; lia | tauto].
  - intros _. rewrite E35u in Hx. apply (apresent_writable SEGS). apply (rcc_tab_pres lyc Sc Wc mem2 md2 k HJ2).
    unfold CALL_SIZE in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 56 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEIq2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 56)%nat -> ew E2 n = ew E n) by (intros n0 Hn0; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn0).
assert (OLDH2 : forall n, (76 <= n)%nat -> ew E2 n = ew E n)
  by (intros n0 Hn0; rewrite HE2; apply ew_havoc_above; cbn [length map CLOB]; lia).
assert (E60 : ew E2 60 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs - 160) by (rewrite OLD2 by lia; exact Usp).
assert (E9u2 : bv_unsigned (ew E2 9) = X) by (rewrite OLD2 by lia; exact E9u).
assert (E35u2 : bv_unsigned (ew E2 35) = DA) by (rewrite OLD2 by lia; exact E35u).
assert (E32u2 : bv_unsigned (ew E2 32) = SB) by (rewrite OLD2 by lia; exact E32u).
assert (SHOK2 : sh_ok SEGS rcc_Bx rcc_SHa E2 (mrestrict (w_H Wc) mem2)).
{ apply (rcc_sha_ok E2 lyc Sc Wc mem2 md2 k i a HJ2 Hi Ha6 E32u2); [rewrite E9u2; exact EX | rewrite E35u2; lia]. }
(* ---- 0x89dac .. 0x89db4: n = |s| + 1, the xmalloc call ---- *)
paj_run_tok RUN HS HJ2 SHOK2 rcc_Bspan.
{ rcc_awr Usp2 WS HJ2. }
rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
clear HF HFr HG. clear_md.
pmkst HS.
prreg HS (1%bv : bv 5) P1x. prreg HS (2%bv : bv 5) P2x. prreg HS (3%bv : bv 5) P3x. prreg HS (4%bv : bv 5) P4x.
prreg HS (8%bv : bv 5) P8x. prreg HS (10%bv : bv 5) P10x.
rewrite (HSIG CS_xmalloc ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_xmalloc) with (BASE + AF_xmalloc) by (unfold cmd_af, AF_xmalloc; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ => set (rT1 := rT) in *; set (mT1 := mT) in *; set (dT1 := dT) in * end.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ mT1 dT1 _ |- _ => rename HJx into HJT1 end.
assert (HspT1 : spZ rT1 = spZ regs + -160) by (unfold spZ at 1; rewrite P2x, Usp2; lia).
assert (P3x' : getr rT1 3 = w64 (as_gp B)).
{ rewrite P3x, OLD2, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3. exact Hgp. }
assert (P4x' : getr rT1 4 = w64 (as_tp B)).
{ rewrite P4x, OLD2, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4. exact Htp. }
assert (HraT1 : YK0s.ret_ok (getr rT1 1)) by (rewrite P1x; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T1 : 4096 <= bv_unsigned (getr rT1 1)) by (rewrite P1x; rewrite unsigned_lit_small; lia).
assert (P10x' : getr rT1 10 = w64 n).
{ rewrite P10x, E60, Ha02. unfold astr_len, w64. rewrite unsigned_lit_small by (unfold LMAX in *; lia). f_equal. lia. }
(* xmalloc's frame chain: s0 holds ~cursor, 7 mod 8, achain's empty case *)
assert (Hs0 : achain lyc (rdW Wc mT1) (spZ regs + -160) (s0Z rT1) []).
{ left. split; [|reflexivity]. right; right. unfold s0Z. rewrite P8x, OLD2, (EE 8%nat 8%bv eq_refl), R8 by lia.
  unfold w64, NOTW. rewrite unsigned_lit_small by (unfold A_G_REC in *; lia).
  destruct (proj1 (Z.mod_divide G0 8 ltac:(lia)) HG08) as [q Hq]. rewrite Hq.
  replace (2 ^ 64 - 1 - q * 8) with (7 + (2 ^ 61 - 1 - q) * 8) by lia. rewrite Z_mod_plus_full.
  intros Hc7. vm_compute in Hc7. discriminate Hc7. }
assert (HEVc : st_nev Sc + EV_XMALLOC <= EV_MAX).
{ assert (HLENa : Z.of_nat (length (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))) + 1 <= ev_args R).
  { unfold ev_args. rewrite rcc_ev_len. rewrite (rcc_args_at (r_calls R) i c a s Hc Hs). rewrite !length_app. cbn [length]. lia. }
  unfold EV_XMALLOC. unfold EV_REC_CALLS_COPY, EV_XMALLOC in HEV. lia. }
pose proof (rcc_args_at (r_calls R) i c a s Hc Hs) as HSPL.
pose proof (zsum_nonneg LIVE_ARG (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))
  ltac:(intros x; unfold LIVE_ARG; lia)) as Hz1.
pose proof (zsum_nonneg XM_ARG (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))
  rcc_xm_arg_nonneg) as Hz2.
assert (HSUMl : LIVE_REC_CALLS_COPY R = zsum LIVE_ARG (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))
  + LIVE_ARG s + zsum LIVE_ARG (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))).
{ unfold LIVE_REC_CALLS_COPY.
  change (fold_right (fun x acc => Z.of_nat (length x) + 1 + acc) 0 (PRcc.rcc_args (r_calls R)))
    with (zsum LIVE_ARG (PRcc.rcc_args (r_calls R))).
  rewrite HSPL at 1. rewrite zsum_app, zsum_cons. lia. }
assert (HSUMm : XM_REC_CALLS_COPY MT R = zsum XM_ARG (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))
  + XM_ARG s + zsum XM_ARG (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))).
{ unfold XM_REC_CALLS_COPY.
  change (fold_right (fun x acc => XM_XMALLOC MT (Z.of_nat (length x) + 1) + acc) 0 (PRcc.rcc_args (r_calls R)))
    with (zsum XM_ARG (PRcc.rcc_args (r_calls R))).
  rewrite HSPL at 1. rewrite zsum_app, zsum_cons. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_XMALLOC n <= LIVE_MAX) by (unfold LIVE_XMALLOC, LIVE_ARG in *; lia).
assert (HMOKc : mo_ok MT Sc (XM_XMALLOC MT n)).
{ apply (mok_station MT S Sc (XM_REC_CALLS_COPY MT R)
    (zsum XM_ARG (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))) (XM_XMALLOC MT n) MTL HMOK HMLE);
  [unfold XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia | unfold XM_ARG at 2 in HSUMm; rewrite <- En in HSUMm; lia]. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc rT1 mT1 _ STK (spZ regs) FP ly S W mem md [] lyc Sc dT1 k XMALLOC_STK [] EV_XMALLOC
    (-160) (getr rT1 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
      getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
      Permutation (ablocks B ly2 S2) ((p, LIVE_XMALLOC n) :: ablocks B lyc Sc) /\
      Forall (fun qk => iv_apart p (LIVE_XMALLOC n) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
      in_blockA (ablocks B ly2 S2) p (LIVE_XMALLOC n) /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_XMALLOC n /\
      mo_le MT Sc S2 (XM_XMALLOC MT n)));
  [ exact HJT1
  | exact HspT1 | reflexivity | lia | rewrite HXS; lia | rewrite WS, HXS; lia
  | exact P3x' | exact P4x' | reflexivity | exact HraT1 | exact Hra4T1 | exact Hs0
  | | intros x Hx; exfalso; exact (inFP_nil x Hx) ].
  intros HPRE1.
  exact (HXMALLOC fx lyc Sc Wc rT1 mT1 dT1 [] n HPRE1 P10x' ltac:(unfold MALLOC_MAX, LMAX in *; lia) HEVc HLIVEc HMOKc). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & pnew & Ha03 & Hp4096 & HPm3 & HAPn
  & HINBn & HBB3 & MLE3).
assert (HLX : LIVE_XMALLOC n = n) by (unfold LIVE_XMALLOC; lia).
rewrite HLX in HPm3, HAPn, HINBn, HBB3.
rewrite P1x.
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR Hly3) as (_ & Efa3 & _).
jafter_call_keep_pi HS 76%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp2 | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia
    | intros x _; apply inFP_nil].
  - eapply (region_kept_frame_sub (segs := SEGS) B _ _ _ _ lyc Sc Wc mT1 dT1 ly3 S3 W3 mem3 md3 _ 9%nat X);
    [exact HJc3 | exact E9u2 | exact Hfinc | rewrite Efa; unfold CALL_SIZE in *; lia | rewrite Efa; unfold CALL_SIZE in *; lia
    | intros x _; apply inFP_nil | cbn; intros x Hx; lia].
  - eapply (region_kept_frame_sub (segs := SEGS) B _ _ _ _ lyc Sc Wc mT1 dT1 ly3 S3 W3 mem3 md3 _ 35%nat DA);
    [exact HJc3 | exact E35u2 | exact Hfinc | rewrite Efa; unfold CALL_SIZE in *; lia | rewrite Efa; unfold CALL_SIZE in *; lia
    | intros x _; apply inFP_nil |].
    cbn [YP09.r_wlo YP09.r_whi]. intros x Hx. apply (rcc_tab_pres ly3 S3 W3 mem3 md3 (k + EV_XMALLOC) HJ3). unfold CALL_SIZE in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 76 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEIq3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEIq2 | cbv; lia]).
assert (OLD3 : forall n, (n < 76)%nat -> ew E3 n = ew E2 n) by (intros n0 Hn0; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn0).
assert (OLDH3 : forall n, (96 <= n)%nat -> ew E3 n = ew E2 n)
  by (intros n0 Hn0; rewrite HE3; apply ew_havoc_above; cbn [length map CLOB]; lia).
assert (E80 : ew E3 80 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs - 160) by (rewrite OLD3 by lia; exact Usp2).
assert (E9u3 : bv_unsigned (ew E3 9) = X) by (rewrite OLD3 by lia; exact E9u2).
assert (E35u3 : bv_unsigned (ew E3 35) = DA) by (rewrite OLD3 by lia; exact E35u2).
assert (E32u3 : bv_unsigned (ew E3 32) = SB) by (rewrite OLD3 by lia; exact E32u2).
assert (SHOK3 : sh_ok SEGS rcc_Bx rcc_SHa E3 (mrestrict (w_H W3) mem3)).
{ apply (rcc_sha_ok E3 ly3 S3 W3 mem3 md3 (k + EV_XMALLOC) i a HJ3 Hi Ha6 E32u3); [rewrite E9u3; exact EX | rewrite E35u3; lia]. }
assert (Hpnin : In (pnew, n) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | left; reflexivity]).
destruct (rcc_blk_dst ly3 S3 W3 mem3 md3 (k + EV_XMALLOC) (pnew, n) HJ3 Hpnin) as (Hpn4 & Hpnc & _ & Hpnd).
cbn [fst snd] in Hpn4, Hpnc, Hpnd.
assert (HPND : rcc_or (pnew + n <= dst) (dst + CALL_SIZE * Z.of_nat NC <= pnew)) by exact Hpnd. clear Hpnd.
assert (Hsain3 : In (sa, sn) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hsain]).
(* xmalloc kept the copy table (a frame of the caller) and every block that was live *)
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
assert (KT3 : forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> rdW W3 mem3 x = rdW Wc mT1 x).
{ intros x Hx. apply (G4 cid pos x Hfinc); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa; unfold CALL_SIZE in *; lia | apply inFP_nil]. }
assert (KB3 : forall pn j, In pn (ablocks B lyc Sc) -> 0 <= j < snd pn -> rdW W3 mem3 (fst pn + j) = rdW Wc mT1 (fst pn + j)).
{ intros [p m] j Hb Hj. cbn [fst snd] in *.
  assert (Hb3 : In (p, m) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HARc Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hq].
  apply (G2 p m j Hb Hb3); [lia | apply inFP_nil]. }
(* ---- 0x89db8 .. 0x89dc4: the copy's address, the source, n, the __asan_memcpy call ---- *)
paj_run_tok RUN HS HJ3 SHOK3 rcc_Bspan.
{ rcc_awr Usp3 WS HJ3. }
rcc_keep HFr K3 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
clear HF HFr HG. clear_md.
pmkst HS.
prreg HS (1%bv : bv 5) P1m. prreg HS (2%bv : bv 5) P2m. prreg HS (3%bv : bv 5) P3m. prreg HS (4%bv : bv 5) P4m.
prreg HS (10%bv : bv 5) P10m. prreg HS (11%bv : bv 5) P11m. prreg HS (12%bv : bv 5) P12m.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ => set (rT2 := rT) in *; set (mT2 := mT) in *; set (dT2 := dT) in * end.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ mT2 dT2 _ |- _ => rename HJx into HJT2 end.
assert (HspT2 : spZ rT2 = spZ regs + -160) by (unfold spZ at 1; rewrite P2m, Usp3; lia).
assert (Ra0 : getr rT2 10 = w64 pnew) by (rewrite P10m, E80; exact Ha03).
assert (Ra1 : getr rT2 11 = w64 sa) by (rewrite P11m, OLD3, OLD2, E40 by lia; reflexivity).
assert (Ra2 : getr rT2 12 = w64 n).
{ rewrite P12m, OLD3, E60, Ha02 by lia. unfold astr_len, w64. rewrite unsigned_lit_small by (unfold LMAX in *; lia). f_equal. lia. }
assert (HstrT2 : astr_atR (rdW W3 mT2) sa s).
{ unfold rcc_or in HSAD. apply (rcc_str_keep (rdW Wc memc)); [exact Hstr|]. intros j Hj.
  rewrite K3 by rcc_side.
  change (sa + j) with (fst (sa, sn) + j).
  rewrite (KB3 (sa, sn) j Hsain ltac:(cbn [snd]; lia)). cbn [fst].
  rewrite K2 by rcc_side. rewrite HK2 by rcc_side. rewrite K1 by rcc_side. reflexivity. }
assert (HAR3' : AR SEGS B ly3 S3 W3 mT2 dT2) by exact (proj1 HJT2).
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W3 rT2 mT2 STK (spZ regs) FP ly S W mem md []
    ly3 S3 dT2 (k + EV_XMALLOC) pnew sa n (-160) (getr rT2 1) HJT2).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - unfold LMAX in *. lia.
  - lia.
  - lia.
  - exact HspT2.
  - reflexivity.
  - lia.
  - rewrite Hes, WS. lia.
  - rewrite P3m, OLD3, OLD2, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia.
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3. exact Hgp.
  - rewrite P4m, OLD3, OLD2, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia.
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4. exact Htp.
  - reflexivity.
  - rewrite P1m. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros x Hx. split; [|lia].
    right; right; left. exists pnew, n. split; [exact Hpnin|]. split; [|pose proof (crf_req_size_ge n); lia].
    intros Hin0. pose proof (proj1 (Forall_forall _ _) HAPn (pnew, n)
      ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact Hin0])) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
  - intros x Hx _ _. apply (apresent_writable SEGS).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ pnew n HAR3' Hpnin) as (_ & _ & _ & _ & Hbp & _).
    pose proof (crf_req_size_ge n). exact (proj1 (Hbp x ltac:(lia))).
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 pnew n); [exact HAR3' | exact Hpnin | lia | pose proof (crf_req_size_ge n); lia].
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 pnew n); [exact HAR3' | exact Hpnin | lia | pose proof (crf_req_size_ge n); lia].
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 pnew n); [exact HAR3' | exact Hpnin | lia | pose proof (crf_req_size_ge n); lia | lia].
  - pose proof (crf_req_size_ge sn) as Hrsn.
    assert (Hsdisj : pnew + n <= sa \/ sa + n <= pnew).
    { pose proof (proj1 (Forall_forall _ _) HAPn (sa, sn) Hsain) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
    split; [lia|]. split; [lia|]. split.
    { intros x Hx. split; [exact (rcc_astr_some _ sa s x HstrT2 ltac:(lia)) | rewrite HspT2, Hes; lia]. }
    split; [exact Hsdisj|].
    split; [apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 sa sn); [exact HAR3' | exact Hsain3 | lia | lia]|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 sa sn); [exact HAR3' | exact Hsain3 | lia | lia]|].
    intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mT2 dT2 sa sn); [exact HAR3' | exact Hsain3 | lia | lia | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
cbv beta iota in Heff.
rewrite P1m.
jafter_call_keep_pi HS 96%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0; 1; 2]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ unfold rcc_or in HPND. cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - apply (region_kept_aview (segs := SEGS) E3 (w_H W3) mT2 mem4 2 (spZ regs - 160)); [exact Usp3 | | exact Hpres4].
    intros x Hx. apply Hfr4; lia.
  - apply (region_kept_aview (segs := SEGS) E3 (w_H W3) mT2 mem4 9 X); [exact E9u3 | | exact Hpres4].
    intros x Hx. apply Hfr4; unfold CALL_SIZE in *; lia.
  - apply (region_kept_aview (segs := SEGS) E3 (w_H W3) mT2 mem4 35 DA); [exact E35u3 | | exact Hpres4].
    intros x Hx. apply Hfr4; unfold CALL_SIZE in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 96 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEIq4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEIq3 | cbv; lia]).
assert (OLD4 : forall n, (n < 96)%nat -> ew E4 n = ew E3 n) by (intros n0 Hn0; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn0).
assert (OLDH4 : forall n, (116 <= n)%nat -> ew E4 n = ew E3 n)
  by (intros n0 Hn0; rewrite HE4; apply ew_havoc_above; cbn [length map CLOB]; lia).
clear HE4.
assert (OLDA : forall n, (n < 56)%nat -> ew E4 n = ew E n) by (intros n0 Hn0; rewrite OLD4, OLD3, OLD2 by lia; reflexivity).
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs - 160) by (rewrite OLDA by lia; exact Usp).
assert (E9u4 : bv_unsigned (ew E4 9) = X) by (rewrite OLDA by lia; exact E9u).
assert (E35u4 : bv_unsigned (ew E4 35) = DA) by (rewrite OLDA by lia; exact E35u).
assert (E32u4 : bv_unsigned (ew E4 32) = SB) by (rewrite OLDA by lia; exact E32u).
assert (E33u4 : bv_unsigned (ew E4 33) = dst) by (rewrite OLDA by lia; exact E33u).
assert (E36u4 : bv_unsigned (ew E4 36) = G0) by (rewrite OLDA by lia; exact E36u).
assert (E41u4 : bv_unsigned (ew E4 41) = Z.of_nat i) by (rewrite OLDA by lia; exact E41u).
assert (E285u4 : bv_unsigned (ew E4 285) = A_G_REC) by (rewrite OLDH4, OLDH3, OLDH2 by lia; exact E285u).
assert (E80u4 : bv_unsigned (ew E4 80) = pnew) by (rewrite OLD4, E80, Ha03 by lia; unfold w64; apply unsigned_lit_small; lia).
assert (Esv4 : forall j, (j < 13)%nat -> ew E4 (42 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0)))
  by (intros j Hj; rewrite OLDA by lia; exact (Esv j Hj)).
assert (SHOK4 : sh_ok SEGS rcc_Bx rcc_SHa E4 (mrestrict (w_H W3) mem4)).
{ apply (rcc_sha_ok E4 ly3 S3 W3 mem4 md4 (k + EV_XMALLOC) i a HJ4 Hi Ha6 E32u4); [rewrite E9u4; exact EX | rewrite E35u4; lia]. }
(* the copy holds s, and the source is kept *)
assert (HSTRn : astr_atR (rdW W3 mem4) pnew s).
{ apply (rcc_astr_move (rdW W3 mT2) _ sa); [|exact HstrT2]. intros j Hj. rewrite <- En in Hj. exact (Heff j Hj). }
(* ---- 0x89dc8 .. 0x89dfc: the wrap check (decided), the copy's slot check, the store, the nargs reload, the
   back-edge ---- *)
paj_run_tok RUN HS HJ4 SHOK4 rcc_Bspan.
{ rcc_awr Usp4 WS HJ4. }
rcc_keep HFr K4 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
clear HF HFr HG. clear_md.
(* everything the inner step read before its first call, kept to its end but for the frame and the copy's slot *)
assert (KT : forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> ~ (DA <= x < DA + 8) ->
  forall mm, (forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 160 <= y < spZ regs \/ DA <= y < DA + 8) -> rdW W3 mm y = rdW W3 mem4 y) ->
  rdW W3 mm x = rdW Wc memc x).
{ unfold rcc_or in HPND. intros x Hx Hnx mm Kmm.
  rewrite Kmm by (unfold CALL_SIZE in *; lia).
  rewrite Hfr4 by (unfold CALL_SIZE in *; lia).
  rewrite K3 by (unfold CALL_SIZE in *; lia).
  rewrite (KT3 x Hx). rewrite K2 by (unfold CALL_SIZE in *; lia).
  rewrite HK2 by rcc_side.
  rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity. }
assert (KB : forall pn j, In pn (ablocks B lyc Sc) -> 0 <= j < snd pn ->
  forall mm, (forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 160 <= y < spZ regs \/ DA <= y < DA + 8) -> rdW W3 mm y = rdW W3 mem4 y) ->
  rdW W3 mm (fst pn + j) = rdW Wc memc (fst pn + j)).
{ intros pn j Hb Hj mm Kmm.
  destruct (rcc_blk_dst lyc Sc Wc mT0 dT0 k pn HJT Hb) as (Hq4 & Hqc & _ & Hqd).
  assert (Hpq : fst pn + snd pn <= pnew \/ pnew + n <= fst pn).
  { pose proof (proj1 (Forall_forall _ _) HAPn pn Hb) as Hap. unfold iv_apart in Hap. lia. }
  rewrite Kmm by (unfold CALL_SIZE in *; lia).
  rewrite Hfr4 by (unfold CALL_SIZE in *; lia).
  rewrite K3 by (unfold CALL_SIZE in *; lia).
  rewrite (KB3 pn j Hb Hj). rewrite K2 by (unfold CALL_SIZE in *; lia).
  rewrite HK2 by rcc_side.
  rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity. }
assert (HPmn : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ (concat qs ++ Pa) ++ [(pnew, n)])).
{ rewrite app_assoc. apply (rcc_perm_snoc _ (ablocks B lyc Sc) _ _ HPm HPm3). }
assert (HFR : forall q, In q (ablocks B ly S ++ concat qs ++ Pa) -> iv_apart pnew n (fst q) (snd q)).
{ intros q Hq. apply (proj1 (Forall_forall _ _) HAPn). eapply Permutation_in; [apply Permutation_sym; exact HPm | exact Hq]. }
assert (HNDn : NoDup (map fst ((concat qs ++ Pa) ++ [(pnew, n)]))).
{ rewrite map_app. cbn [map]. apply rcc_nodup_snoc; [exact HND|].
  intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hqin). cbn [fst] in Hq. subst q.
  pose proof (HFR (pnew, m) ltac:(apply in_or_app; right; exact Hqin)) as Hap. cbn [fst snd] in Hap.
  pose proof (proj1 (Forall_forall _ _) H1 (pnew, m) Hqin) as Hm1. cbn [snd] in Hm1.
  unfold iv_apart in Hap. lia. }
assert (H1n : Forall (fun pn => 1 <= snd pn) ((concat qs ++ Pa) ++ [(pnew, n)])).
{ apply Forall_app. split; [exact H1 | apply Forall_cons; [cbn [snd]; lia | apply Forall_nil]]. }
assert (HAPn' : forall pn q, In pn ((concat qs ++ Pa) ++ [(pnew, n)]) -> In q (ablocks B ly S) ->
  iv_apart (fst pn) (snd pn) (fst q) (snd q)).
{ intros pn q Hpn Hq. apply in_app_or in Hpn as [Hpn | [<- | []]]; [exact (HAP pn q Hpn Hq)|].
  cbn [fst snd]. exact (HFR q ltac:(apply in_or_app; left; exact Hq)). }
assert (HBBn : blocks_bytes S3 <= blocks_bytes S + zsum LIVE_ARG ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])).
{ rewrite zsum_app, zsum_one. unfold LIVE_ARG at 2. lia. }
assert (HMLEn : mo_le MT S S3 (zsum XM_ARG ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s]))).
{ rewrite zsum_app, zsum_one. unfold XM_ARG at 2. rewrite <- En. exact (mle_station MT S Sc S3 _ _ MTL HMLE MLE3). }
assert (Hkn : 0 <= k + EV_XMALLOC <= Z.of_nat (length ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])))
  by (rewrite length_app; cbn [length]; unfold EV_XMALLOC; lia).
assert (HARGn : PRcc.rcc_args (firstn i (r_calls R)) ++ firstn (Datatypes.S a) (snd c)
  = (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])
  by (rewrite (rcc_firstn_S (snd c) a s Hs), app_assoc; reflexivity).
psrr_branch_tok RUN BR HS SHOK4 rcc_Bspan.
- (* another argument: back to 0x89d7c *)
  assert (HaS : (Datatypes.S a < length (snd c))%nat).
  { cbn [sv_denot] in Hc0. rewrite !OLDA in Hc0 by lia.
    rewrite (EE 22%nat 22%bv eq_refl), R22, E37 in Hc0. unfold w64 in Hc0.
    rewrite !unsigned_lit_small in Hc0 by lia.
    rewrite rcc_blt in Hc0 by lia. apply Z.ltb_lt in Hc0. lia. }
  clear Hc0.
  paj_run_to_tok RUNTO HS HJ4 SHOK4 rcc_Bspan RCC_INNER.
  { rcc_awr Usp4 WS HJ4. }
  rcc_keep HFr K5 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
  clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg_raw HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E4 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg;
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E4 ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
    cbn [ms_mem restrict mkst] in HRd end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
    assert (Kmm : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 160 <= y < spZ regs \/ DA <= y < DA + 8) -> rdW W3 mm y = rdW W3 mem4 y)
      by (intros y Hy Hny; rewrite K5, K4 by first [exact Hy | exact Hny]; reflexivity) end.
  apply (NXT HaS (Pa ++ [(pnew, n)]) ly3 S3 W3 _ _ (k + EV_XMALLOC)).
  split; [exact Hc|]. split; [exact HaS|].
  split.
  { split; [exact HJ4|]. rewrite HARGn.
    split; [exact Hkn|]. split; [rewrite (app_assoc (concat qs)); exact HPmn|].
    split; [rewrite (app_assoc (concat qs)); exact HNDn|].
    split; [rewrite (app_assoc (concat qs)); exact H1n|]. split; [rewrite (app_assoc (concat qs)); exact HAPn'|].
    split; [exact HBBn|]. split; [exact HMLEn|].
    split; [apply (rcc_saves_get E4 _ _ _ _ _ HRg Usp4 Esv4); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, OLDA, (EE 2%nat 2%bv eq_refl) by lia; exact R2|].
    split; [rewrite Q3, OLDA, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia;
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3|].
    rewrite Q4, OLDA, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia;
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4. }
  split.
  { apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly3 S3) i qs HTAB).
    - intros x Hx. apply (KT x ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold CALL_SIZE in *; lia) _ Kmm).
    - intros pn Hpn Hb. split.
      + eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hb].
      + intros j Hj. exact (KB pn j Hb Hj _ Kmm). }
  split.
  { apply (rcc_part_snoc _ _ i c a Pa s (pnew, n)); [| exact Hs | | cbn [fst]; lia | exact Hpnin | cbn [snd]; exact En |].
    - apply (rcc_part_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly3 S3) i c a Pa HPART).
      + intros x Hx. apply (KT x ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold CALL_SIZE in *; lia) _ Kmm).
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hb].
        * intros j Hj. exact (KB pn j Hb Hj _ Kmm).
    - cbn [fst]. replace (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a) with (DA + 0) by (unfold CALL_SIZE; lia).
      apply (rcc_chunk_gen E4 _ _ 35%nat _ _ _ _ _ _ 0 (SOff 80 0) pnew HRd E35u4); [cbn; tauto|].
      apply rcc_den_val; [rewrite E80u4; lia | lia].
    - cbn [fst]. apply (rcc_str_keep (rdW W3 mem4)); [exact HSTRn|].
      unfold rcc_or in HPND. intros x Hx. rewrite Kmm by (unfold CALL_SIZE in *; lia). reflexivity. }
  split.
  { apply (rcc_slots_of E4 _ _ _ _ _ i (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 36 0) (SOff 36 0) HRg Usp4);
    [ cbn; tauto | apply rcc_den_val; [rewrite E285u4; lia | unfold A_G_REC; lia]
    | cbn; tauto | reflexivity | cbn; tauto | reflexivity
    | cbn; tauto | apply rcc_den_val; [rewrite E33u4; lia | unfold CALL_SIZE in *; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u4; lia | unfold A_G_REC in *; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u4; lia | unfold A_G_REC in *; lia] ]. }
  split.
  { apply (rcc_islot_of E4 _ _ _ _ _ i (SOff 41 0) HRg Usp4); [cbn; tauto|].
    apply rcc_den_val; [rewrite E41u4; lia | lia]. }
  subst G0 D0 X.
  split; [rewrite Q8, OLDA, (EE 8%nat 8%bv eq_refl) by lia; exact R8|].
  split; [rewrite Q9, OLDA, (EE 9%nat 9%bv eq_refl) by lia; exact R9|].
  split; [rewrite Q21, OLDA, (EE 21%nat 21%bv eq_refl) by lia; exact R21|].
  split; [rewrite Q22, OLDA, (EE 22%nat 22%bv eq_refl), R22 by lia; rcc_w64|].
  split; [rewrite Q23, OLDA, (EE 23%nat 23%bv eq_refl), R23 by lia; rcc_w64|].
  split; [rewrite Q24, OLDA, E32 by lia; reflexivity|].
  split.
  { rewrite Q25. assert (E9w : ew E4 9 = Z_to_bv 64 (dst + (4 + 56 * Z.of_nat i)))
      by (rewrite OLDA, (EE 9%nat 9%bv eq_refl) by lia; exact R9).
    assert (E32w : ew E4 32 = Z_to_bv 64 SB) by (rewrite OLDA by lia; exact E32).
    rewrite (denot_shx E4 9 32 0 (dst + (4 + 56 * Z.of_nat i)) SB E9w E32w ltac:(lia) ltac:(lia) ltac:(unfold CALL_SIZE in *; lia)
      ltac:(unfold SB; lia)).
    rewrite Z.add_0_r. reflexivity. }
  split; [rewrite Q26, OLDA, (EE 26%nat 26%bv eq_refl) by lia; exact R26|].
  rewrite Q27, OLDA, (EE 27%nat 27%bv eq_refl) by lia; exact R27.
- (* the last argument: on to the latch 0x89e14 *)
  assert (HaS : Datatypes.S a = length (snd c)).
  { cbn [sv_denot] in Hc0. rewrite !OLDA in Hc0 by lia.
    rewrite (EE 22%nat 22%bv eq_refl), R22, E37 in Hc0. unfold w64 in Hc0.
    rewrite !unsigned_lit_small in Hc0 by lia.
    rewrite rcc_blt in Hc0 by lia. apply Z.ltb_ge in Hc0. lia. }
  clear Hc0.
  paj_run_to_tok RUNTO HS HJ4 SHOK4 rcc_Bspan RCC_LATCH.
  { rcc_awr Usp4 WS HJ4. }
  rcc_keep HFr K5 (fun x => spZ regs - 160 <= x < spZ regs \/ DA <= x < DA + 8).
  clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E4 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg;
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E4 ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
    cbn [ms_mem restrict mkst] in HRd end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
    assert (Kmm : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 160 <= y < spZ regs \/ DA <= y < DA + 8) -> rdW W3 mm y = rdW W3 mem4 y)
      by (intros y Hy Hny; rewrite K5, K4 by first [exact Hy | exact Hny]; reflexivity) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
  assert (HPARTn : rcc_part (rdW W3 mm) (ablocks B ly3 S3) i c (Datatypes.S a) (Pa ++ [(pnew, n)])) end.
  { apply (rcc_part_snoc _ _ i c a Pa s (pnew, n)); [| exact Hs | | cbn [fst]; lia | exact Hpnin | cbn [snd]; exact En |].
    - apply (rcc_part_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly3 S3) i c a Pa HPART).
      + intros x Hx. apply (KT x ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold CALL_SIZE in *; lia) _ Kmm).
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hb].
        * intros j Hj. exact (KB pn j Hb Hj _ Kmm).
    - cbn [fst]. replace (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a) with (DA + 0) by (unfold CALL_SIZE; lia).
      apply (rcc_chunk_gen E4 _ _ 35%nat _ _ _ _ _ _ 0 (SOff 80 0) pnew HRd E35u4); [cbn; tauto|].
      apply rcc_den_val; [rewrite E80u4; lia | lia].
    - cbn [fst]. apply (rcc_str_keep (rdW W3 mem4)); [exact HSTRn|].
      unfold rcc_or in HPND. intros x Hx. rewrite Kmm by (unfold CALL_SIZE in *; lia). reflexivity. }
  rewrite HaS in HPARTn.
  apply (LTK (qs ++ [Pa ++ [(pnew, n)]]) ly3 S3 W3 _ _ (k + EV_XMALLOC)).
  split; [exact Hi|].
  split.
  { split; [exact HJ4|]. rewrite (rcc_args_firstn_S (r_calls R) i c Hc).
    assert (HEQ : PRcc.rcc_args (firstn i (r_calls R)) ++ snd c
      = (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])
      by (rewrite <- HARGn, HaS, firstn_all; reflexivity).
    rewrite HEQ. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
    split; [exact Hkn|]. split; [rewrite (app_assoc (concat qs)); exact HPmn|].
    split; [rewrite (app_assoc (concat qs)); exact HNDn|].
    split; [rewrite (app_assoc (concat qs)); exact H1n|]. split; [rewrite (app_assoc (concat qs)); exact HAPn'|].
    split; [exact HBBn|]. split; [exact HMLEn|].
    split; [apply (rcc_saves_get E4 _ _ _ _ _ HRg Usp4 Esv4); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, OLDA, (EE 2%nat 2%bv eq_refl) by lia; exact R2|].
    split; [rewrite Q3, OLDA, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia;
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3|].
    rewrite Q4, OLDA, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia;
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4. }
  split.
  { apply (rcc_tab_snoc _ _ i qs c (Pa ++ [(pnew, n)])).
    - apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly3 S3) i qs HTAB).
      + intros x Hx. apply (KT x ltac:(unfold CALL_SIZE in *; lia) ltac:(unfold CALL_SIZE in *; lia) _ Kmm).
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm3 | right; exact Hb].
        * intros j Hj. exact (KB pn j Hb Hj _ Kmm).
    - exact Hc.
    - apply (rcc_slot_of_part _ _ i c _ HPARTn Hfn Hn6 HLMAX).
      rewrite map_app. cbn [map]. apply rcc_nodup_snoc.
      + rewrite map_app in HND. exact (rcc_nodup_r _ _ HND).
      + intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hqin). cbn [fst] in Hq. subst q.
        pose proof (HFR (pnew, m) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hqin)) as Hap.
        cbn [fst snd] in Hap.
        pose proof (proj1 (Forall_forall _ _) H1 (pnew, m) ltac:(apply in_or_app; right; exact Hqin)) as Hm1.
        cbn [snd] in Hm1. unfold iv_apart in Hap. lia. }
  split.
  { apply (rcc_slots_of E4 _ _ _ _ _ i (SOff 285 0) (SLit 1) (SLit 1) (SOff 33 0) (SOff 36 0) (SOff 36 0) HRg Usp4);
    [ cbn; tauto | apply rcc_den_val; [rewrite E285u4; lia | unfold A_G_REC; lia]
    | cbn; tauto | reflexivity | cbn; tauto | reflexivity
    | cbn; tauto | apply rcc_den_val; [rewrite E33u4; lia | unfold CALL_SIZE in *; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u4; lia | unfold A_G_REC in *; lia]
    | cbn; tauto | apply rcc_den_val; [rewrite E36u4; lia | unfold A_G_REC in *; lia] ]. }
  split.
  { apply (rcc_islot_of E4 _ _ _ _ _ i (SOff 41 0) HRg Usp4); [cbn; tauto|].
    apply rcc_den_val; [rewrite E41u4; lia | lia]. }
  subst D0.
  split; [rewrite Q24, OLDA, E32 by lia; reflexivity|].
  split; [rewrite Q26, OLDA, (EE 26%nat 26%bv eq_refl) by lia; exact R26|].
  rewrite Q27, OLDA, (EE 27%nat 27%bv eq_refl) by lia; exact R27.
Qed.

(* ---------- the loops: the inner by induction on the arguments left, the outer on the calls left ---------- *)
Lemma rcc_inner : forall i c qs,
(forall qs' lyc' Sc' Wc' memc' mdc' k' regs1', rcc_LT i qs' lyc' Sc' Wc' memc' mdc' k' regs1' ->
  SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
forall n a Pa lyc Sc Wc memc mdc k regs1, (length (snd c) - a = n)%nat ->
rcc_IH i a c qs Pa lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_INNER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i c qs LTK n. induction n as [|n IH]; intros a Pa lyc Sc Wc memc mdc k regs1 Hn HIH.
- exfalso. destruct HIH as (_ & Ha & _). lia.
- apply (rcc_inner_step i a c qs Pa lyc Sc Wc memc mdc k regs1 LTK); [|exact HIH].
  intros HaS Pa' lyc' Sc' Wc' memc' mdc' k' regs1' HIH'.
  exact (IH (Datatypes.S a) Pa' lyc' Sc' Wc' memc' mdc' k' regs1' ltac:(lia) HIH').
Qed.
Lemma rcc_outer : forall n i qs lyc Sc Wc memc mdc k regs1, (NC - i = n)%nat ->
rcc_OH i qs lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intro n. induction n as [|n IH]; intros i qs lyc Sc Wc memc mdc k regs1 Hn HOH.
- exfalso. destruct HOH as (Hi & _). lia.
- assert (LTK : forall qs' lyc' Sc' Wc' memc' mdc' k' regs1', rcc_LT i qs' lyc' Sc' Wc' memc' mdc' k' regs1' ->
    SRr SEGS Wc' (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q).
  { intros qs' lyc' Sc' Wc' memc' mdc' k' regs1' HLT.
    apply (rcc_latch i qs' lyc' Sc' Wc' memc' mdc' k' regs1'); [|exact HLT].
    intros memc'' mdc'' regs1'' HOH'.
    exact (IH (Datatypes.S i) qs' lyc' Sc' Wc' memc'' mdc'' k' regs1'' ltac:(lia) HOH'). }
  apply (rcc_outer_body i qs lyc Sc Wc memc mdc k regs1); [| exact LTK | exact HOH].
  intros c lyc' Sc' Wc' memc' mdc' k' regs1' HIH.
  exact (rcc_inner i c qs LTK (length (snd c) - 0) 0 [] lyc' Sc' Wc' memc' mdc' k' regs1' eq_refl HIH).
Qed.

(* ---------- the entry: 0x89c34 .. 0x89c7c (the prologue, dst into 24(sp), g_rec.ncalls), then the outer head (via
   the two UBSan predicates of dst into 8(sp) and 16(sp), the shadow base, the two copies of the cursor) or the
   epilogue ---------- *)
Lemma rcc_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_copy) regs mem md) rcc_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
pose proof (rcc_seed0 B TL HVAL W regs mem ly S md R O dst (Z.of_nat NC) HAR Hstk Hpres HREP eq_refl HLEN) as HS.
pose proof (ajournal_init SEGS B STK FP ly S W regs mem md ch HPRE) as HJ.
assert (SHOK : sh_ok SEGS rcc_Bx [] (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) (mrestrict (w_H W) mem))
  by apply Forall_nil.
pose proof (rcc_E285' regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0 HVAL) as E285.
pose proof (rcc_E32 regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as E32.
pose proof (rcc_E38 regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as E38.
pose proof (rcc_EE regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0)) by (unfold rcc_E; apply Eimg_env).
remember (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 0) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E10 : ew E 10 = Z_to_bv 64 dst) by (rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity).
assert (E10u : bv_unsigned (ew E 10) = dst) by (rewrite E10; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E38u : bv_unsigned (ew E 38) = Z.of_nat NC) by (rewrite E38; apply unsigned_lit_small; lia).
(* the frame the prologue wrote: the thirteen saved registers *)
assert (HSAVES : forall cs mm, region_ok SEGS E (mrestrict (w_H W) mm) (YP09.mkRegion (Some 2%nat) (-160) 0 (-160) 0 cs) ->
  (forall j, (j < 13)%nat -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j rcc_saved 0)) 0))) cs) ->
  rcc_saves (rdW W mm)).
{ intros cs mm HRg Hin j r Hj.
  assert (Hj13 : (j < length rcc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length rcc_saved] in Hj13.
  assert (Hr : r = nth j rcc_saved 0) by (symmetry; apply nth_error_nth; exact Hj). subst r.
  replace (spZ regs - 160 + 152 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-8 - 8 * Z.of_nat j) (SOff (Z.to_nat (nth j rcc_saved 0)) 0) _ HRg Usp (Hin j Hj13)).
  apply rcc_den_val; [|apply bv_unsigned_in_range].
  rewrite Z.add_0_r, (EE (Z.to_nat (nth j rcc_saved 0)) (Z_to_bv 5 (nth j rcc_saved 0))); [reflexivity|].
  do 13 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
unfold cfg_at. change (w64 (BASE + AF_rec_calls_copy)) with (Z_to_bv 64 (BASE + AF_rec_calls_copy)).
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ awr_ok_tac. exact Usp. }
rcc_keep HFr K1 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
- (* no call: on to the epilogue *)
  assert (HN0 : NC = 0%nat).
  { cbn [sv_denot] in Hc. rewrite E38u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_RET.
  { awr_ok_tac. exact Usp. }
  rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (11%bv : bv 5) Q11.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  apply (rcc_ret [] ly S W _ _ 0 _).
  split.
  { split; [exact HJ|]. split; [lia|]. split; [cbn [concat]; rewrite app_nil_r; apply Permutation_refl|].
    split; [constructor|]. split; [constructor|]. split; [intros pn q Hpn; cbn in Hpn; contradiction|].
    split; [pose proof (zsum_nonneg LIVE_ARG (PRcc.rcc_args (r_calls R)) ltac:(intros x; unfold LIVE_ARG; lia)); lia|].
    split; [apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)); apply zsum_nonneg; exact rcc_xm_arg_nonneg|].
    split; [apply (HSAVES _ _ HRg); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, Usp; rcc_w64|]. split; [rewrite Q3; apply EE; reflexivity|]. rewrite Q4; apply EE; reflexivity. }
  split.
  { split; [cbn [length]; lia|]. intros j c P _ HP. destruct j; cbn in HP; discriminate HP. }
  rewrite Q11, E38. reflexivity.
- (* calls: on to the outer head with call 0 *)
  assert (HN1 : (0 < NC)%nat).
  { cbn [sv_denot] in Hc. rewrite E38u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
    apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_OUTER.
  { awr_ok_tac. exact Usp. }
  rcc_keep HFr K2 (fun x => spZ regs - 160 <= x < spZ regs). clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (12%bv : bv 5) Q12.
  prreg HS (14%bv : bv 5) Q14. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  apply (rcc_outer (NC - 0) 0 [] ly S W _ _ 0 _ eq_refl).
  split; [exact HN1|].
  split.
  { split; [exact HJ|]. split; [lia|]. split; [cbn [concat]; rewrite app_nil_r; apply Permutation_refl|].
    split; [constructor|]. split; [constructor|]. split; [intros pn q Hpn; cbn in Hpn; contradiction|].
    split; [pose proof (zsum_nonneg LIVE_ARG (PRcc.rcc_args (firstn 0 (r_calls R))) ltac:(intros x; unfold LIVE_ARG; lia)); lia|].
    split; [apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)); apply zsum_nonneg; exact rcc_xm_arg_nonneg|].
    split; [apply (HSAVES _ _ HRg); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, Usp; rcc_w64|]. split; [rewrite Q3; apply EE; reflexivity|]. rewrite Q4; apply EE; reflexivity. }
  split.
  { split; [reflexivity|]. intros j c P _ HP. destruct j; cbn in HP; discriminate HP. }
  split.
  { split; [replace (spZ regs - 160) with (spZ regs + -160) by lia;
      apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-160) (SOff 285 0) A_G_REC HRg Usp);
      [cbn; tauto | apply rcc_den_val; [rewrite E285u; lia | unfold A_G_REC; lia]]|].
    split; [replace (spZ regs - 160 + 8) with (spZ regs + -152) by lia;
      apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-152) (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 10 0))) 1 HRg Usp); [cbn; tauto|];
      rewrite (rcc_den_c8 E dst E10 ltac:(unfold CALL_SIZE in *; lia) Hd8); reflexivity|].
    split; [replace (spZ regs - 160 + 16) with (spZ regs + -144) by lia;
      apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-144) (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) 1 HRg Usp); [cbn; tauto|];
      rewrite (rcc_den_c16 E dst E10 ltac:(unfold CALL_SIZE in *; lia)); reflexivity|].
    split; [replace (spZ regs - 160 + 24) with (spZ regs + -136) by lia;
      apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-136) (SOff 10 0) dst HRg Usp);
      [cbn; tauto | apply rcc_den_val; [rewrite E10u; lia | unfold CALL_SIZE in *; lia]]|].
    split; [replace (spZ regs - 160 + 40) with (spZ regs + -120) by lia;
      apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-120) (SOff 285 24) _ HRg Usp);
      [cbn; tauto | apply rcc_den_val; [rewrite E285u; cbn [Z.of_nat]; lia | unfold A_G_REC; lia]]|].
    replace (spZ regs - 160 + 48) with (spZ regs + -112) by lia.
    apply (rcc_chunk_gen E _ _ 2%nat _ _ _ _ _ _ (-112) (SOff 285 24) _ HRg Usp);
    [cbn; tauto | apply rcc_den_val; [rewrite E285u; cbn [Z.of_nat]; lia | unfold A_G_REC; lia]]. }
  split; [rewrite Q12, E285; reflexivity|].
  split; [rewrite Q14; reflexivity|].
  split; [rewrite Q24, E32; reflexivity|].
  split; [rewrite Q26, E10u; rcc_w64|].
  rewrite Q27, E10u; rcc_w64.
Qed.
End w.
(* the contract *)
Theorem trec_calls_copy_spec_holds : trec_calls_copy_spec B MT.
Proof.
intros ly S W regs mem md ch dst R O HPRE HROD H10 HREP HLEN HOBJ HEV HLIVE HMOK.
exact (rcc_entry ly S W regs mem md ch dst R O HPRE HROD H10 HREP HLEN HOBJ HEV HLIVE HMOK).
Qed.
End e.
End f.
End d.
