(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its numbers changed; 1747 of its 1873 lines of code are new or changed and 1365 lines of the source are left out. *)
(* The program walk of rec_calls_copy on the ASan build of plugin-hostd/fuzz_command (entry 0x896bc, 146 instructions),
   proving trec_calls_copy_spec (lib/A/Prog/rec_calls_copy_c.v) in the shape of cgif_file_fuzzer's walks: the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the seven inline shadow checks removed by the
   shadow entries of each cut point (PaShadow.v), and the xstrdup call through cl_callS (PaCall.v) with xstrdup's
   contract, the statement's HXSTRDUP.
   The walk is cut at the outer loop head (0x89730), the inner loop head (0x897c4), the outer latch (0x89824) and the
   epilogue (0x8989c); each piece is re-seeded from the concrete state there (lib/A/Prog/rec_calls_copy_s1.v), the
   inner loop is proved by induction on the arguments left and the outer loop by induction on the calls left (the
   outer index is concrete in each run: at most 2 calls).
   Section hypotheses besides the statement's own HXSTRDUP and HVAL: TL (the shadow GOT and cell, CmdPaLib.v), HB
   (the image's symbols: g_rec and record.spill are program statics), IMG (the image facts), MTL (the meter laws, to
   chain the xstrdup calls' meters) and HSIG (cmd_sig_prog, CmdObj.v: the call target of xstrdup). From HB and IMG,
   CmdRecFacts.v gives the per-binary facts the walk uses: cif_prog_img (g_rec is in the image), cmd_cf_grec (g_rec's
   shadow marks it usable), cmd_ro_prog_apart (the read-only bytes are in the image: xstrdup's arodata_okP is carried
   across the walk) and cmd_heap_tail_vis (the readable word tail after a heap string: xstrdup's atail_vis for each
   argument string). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdBase CmdRep CmdObj CmdAddr CmdGlob xstrdup_c rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_copy_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
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
(* the statement's own hypotheses *)
Hypothesis HXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis HVAL : cmd_val_objs.
(* the per-binary record (CmdRecFacts.v) *)
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
(* the walk's runners *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

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
(* the thirteen registers the prologue saved, and the frame's four words: g_rec, dst and the two cursors *)
Definition rcc_saves (rd : reader) : Prop :=
forall j r, nth_error rcc_saved j = Some r ->
aval_mem rd (spZ regs - 144 + 136 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition rcc_slots (rd : reader) (i : nat) : Prop :=
aval_mem rd (spZ regs - 144 + 8) 8 A_G_REC /\ aval_mem rd (spZ regs - 144 + 16) 8 dst /\
aval_mem rd (spZ regs - 144 + 24) 8 (A_G_REC + 24 + 56 * Z.of_nat i) /\
aval_mem rd (spZ regs - 144 + 32) 8 (dst + 8 + 56 * Z.of_nat i).
(* the journal from the entry, the copies made so far (xs, in the blocks bln), the frame, sp, gp and tp *)
Definition rcc_cut (xs : list (list byte)) (bln : list (Z * Z)) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs1 : bvmap 5 word) : Prop :=
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= Z.of_nat (length xs) /\
Permutation (ablocks B lyc Sc) (ablocks B ly S ++ bln) /\
NoDup (map fst bln) /\ Forall (fun pn => 1 <= snd pn) bln /\
(forall pn q, In pn bln -> In q (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q) (snd q)) /\
blocks_bytes Sc <= blocks_bytes S + zsum LIVE_XSTRDUP xs /\
mo_le MT S Sc (zsum (XM_XSTRDUP MT) xs) /\
rcc_saves (rdW Wc memc) /\
getr regs1 2 = w64 (spZ regs - 144) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4.
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
(* the epilogue 0x8989c: every call copied, a1 = the call count *)
Definition rcc_RT (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
rcc_cut (PRcc.rcc_args (r_calls R)) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) NC qs /\ getr regs1 11 = w64 (Z.of_nat NC).
(* the outer loop head 0x89730, about to copy call i *)
Definition rcc_OH (i : nat) (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
(i < NC)%nat /\
rcc_cut (PRcc.rcc_args (firstn i (r_calls R))) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) i qs /\ rcc_slots (rdW Wc memc) i /\
getr regs1 14 = w64 A_G_REC /\ getr regs1 20 = w64 SB /\ getr regs1 21 = w64 (Z.of_nat i) /\
getr regs1 25 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) /\ getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the outer latch 0x89824, call i copied *)
Definition rcc_LT (i : nat) (qs : list (list (Z * Z))) lyc Sc Wc memc mdc k regs1 : Prop :=
(i < NC)%nat /\
rcc_cut (PRcc.rcc_args (firstn (Datatypes.S i) (r_calls R))) (concat qs) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) (Datatypes.S i) qs /\ rcc_slots (rdW Wc memc) i /\
getr regs1 20 = w64 SB /\ getr regs1 21 = w64 (Z.of_nat i) /\
getr regs1 25 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) /\ getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the inner loop head 0x897c4, about to copy argument a of call i (= c) *)
Definition rcc_IH (i a : nat) (c : rcall) (qs : list (list (Z * Z))) (Pa : list (Z * Z)) lyc Sc Wc memc mdc k regs1 : Prop :=
nth_error (r_calls R) i = Some c /\ (a < length (snd c))%nat /\
rcc_cut (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) (concat qs ++ Pa) lyc Sc Wc memc mdc k regs1 /\
rcc_tab (rdW Wc memc) (ablocks B lyc Sc) i qs /\ rcc_part (rdW Wc memc) (ablocks B lyc Sc) i c a Pa /\
rcc_slots (rdW Wc memc) i /\
getr regs1 8 = w64 (Z.of_nat a) /\ getr regs1 9 = w64 (dst + (4 + 56 * Z.of_nat i)) /\
getr regs1 18 = w64 (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) /\
getr regs1 19 = w64 (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) /\ getr regs1 20 = w64 SB /\
getr regs1 21 = w64 (Z.of_nat i) /\
getr regs1 22 = w64 (SB + (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) / 8) /\
getr regs1 23 = w64 (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) /\
getr regs1 24 = w64 (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) /\
getr regs1 25 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) /\ getr regs1 26 = w64 (dst + 8 + 56 * Z.of_nat i) /\
getr regs1 27 = w64 (SB + (dst + (4 + 56 * Z.of_nat i)) / 8).

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
(* the frame's words, read back from a symbolic stack region at sp - 144 *)
Lemma rcc_chunk_val : forall E H (m : word -> option byte) wlo whi cs off (n : nat) c v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 144 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 144 ->
In (YP09.mkChunk off (CVal 8 (SOff n c))) cs ->
bv_unsigned (ew E n) + c = v -> 0 <= v < 2 ^ 64 ->
aval_mem (aview SEGS H m) (spZ regs - 144 + off) 8 v.
Proof.
intros E H m wlo whi cs off n c v HR Hb Hin Hv Hr.
pose proof (field_of_region_any E _ 2%nat (spZ regs - 144) cs 0 144 wlo whi off 8%N (SOff n c) HR Hb Hin
  ltac:(cbn; lia)) as Hm.
cbn [sv_denot] in Hm. rewrite Hv in Hm. rewrite unsigned_lit_small in Hm by lia.
change (8 * Z.of_N 8) with 64 in Hm. rewrite Z.mod_small in Hm by lia. change (N.to_nat 8) with 8%nat in Hm.
apply (rcc_aval_of_val H m (spZ regs - 144 + off) 8 v); [change (8 * Z.of_nat 8) with 64; lia | exact Hm].
Qed.
Lemma rcc_slots_get : forall E H (m : word -> option byte) wlo whi cs i,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 144 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 144 -> bv_unsigned (ew E 285) = A_G_REC -> bv_unsigned (ew E 33) = dst ->
(i <= 2)%nat -> 4096 <= dst -> dst + 8 + 56 * Z.of_nat i < 2 ^ 64 ->
In (YP09.mkChunk 8 (CVal 8 (SOff 285 0))) cs -> In (YP09.mkChunk 16 (CVal 8 (SOff 33 0))) cs ->
In (YP09.mkChunk 24 (CVal 8 (SOff 285 (24 + 56 * Z.of_nat i)))) cs ->
In (YP09.mkChunk 32 (CVal 8 (SOff 33 (8 + 56 * Z.of_nat i)))) cs ->
rcc_slots (aview SEGS H m) i.
Proof.
intros E H m wlo whi cs i HR Hb E285 E33 Hi Hd0 Hd1 C8 C16 C24 C32.
split; [apply (rcc_chunk_val E H m wlo whi cs 8 285 0); [exact HR | exact Hb | exact C8 | rewrite E285; lia | unfold A_G_REC; lia]|].
split; [apply (rcc_chunk_val E H m wlo whi cs 16 33 0); [exact HR | exact Hb | exact C16 | rewrite E33; lia | lia]|].
split; [apply (rcc_chunk_val E H m wlo whi cs 24 285 (24 + 56 * Z.of_nat i));
  [exact HR | exact Hb | exact C24 | rewrite E285; lia | unfold A_G_REC; lia]|].
apply (rcc_chunk_val E H m wlo whi cs 32 33 (8 + 56 * Z.of_nat i)); [exact HR | exact Hb | exact C32 | rewrite E33; lia | lia].
Qed.
Lemma rcc_saves_get : forall E H (m : word -> option byte) wlo whi cs,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 144 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 144 ->
(forall j, (j < 13)%nat -> ew E (41 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0))) ->
(forall j, (j < 13)%nat -> In (rcc_sav j) cs) ->
rcc_saves (aview SEGS H m).
Proof.
intros E H m wlo whi cs HR Hb Esv Cs j r Hj.
assert (Hj13 : (j < length rcc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length rcc_saved] in Hj13.
assert (Hr : r = nth j rcc_saved 0) by (symmetry; apply nth_error_nth; exact Hj). subst r.
replace (spZ regs - 144 + 136 - 8 * Z.of_nat j) with (spZ regs - 144 + (136 - 8 * Z.of_nat j)) by lia.
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))) as HR64.
change (bv_modulus 64) with (2 ^ 64) in HR64.
apply (rcc_chunk_val E H m wlo whi cs (136 - 8 * Z.of_nat j) (41 + j) 0); [exact HR | exact Hb | exact (Cs j Hj13) | | lia].
rewrite (Esv j Hj13). lia.
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

(* ---------- the epilogue: 0x8989c .. 0x898d8, ra and s0..s11 restored, a0 := a1, ret ---------- *)
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
assert (HE2 : bv_unsigned (ew (rcc_E regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0) 2) = spZ regs - 144).
{ rewrite (rcc_EE regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0 2%nat 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. lia. }
destruct (rcc_seed_mid regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0 RCC_RET rcc_regs_r [rcc_stkr] [] Wc memc
  (rcc_regs_r_ok regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0 R11 Hnc)
  ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [|apply Forall_nil];
        exact (rcc_stkr_ok regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0 Wc memc (spZ regs - 144) R2
          ltac:(lia) ltac:(lia) HSV))
  ltac:(apply pairwise_disjoint_of_extents; cbn [map zpairwise_disjoint zall_disjoint]; repeat split)
  ltac:(apply (rcc_facts_ok regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0 HVAL (spZ regs - 144) HE2);
        [ lia | replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
        | unfold CALL_SIZE in *; lia | exact Hd8 | unfold A_G_REC; lia | unfold A_G_REC; reflexivity
        | unfold CALL_SIZE in *; lia | exact Hd8 | lia | lia | lia | lia ])
  ltac:(apply Forall_nil)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0))
  by (unfold rcc_E; apply Eimg_env).
pose proof (rcc_Esav regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0) as Esv.
pose proof (rcc_E38 regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0) as E38.
pose proof (rcc_EE regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0) as EE.
remember (rcc_E regs1 regs dst (A_G_REC + 24) dst 0 0 (Z.of_nat NC) 0 0) as E eqn:HE. clear HE.
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
{ rewrite F1. change 41%nat with (41 + 0)%nat. rewrite (Esv 0%nat ltac:(lia)). cbn [nth rcc_saved].
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  unfold EV_REC_CALLS_COPY, EV_XSTRDUP, ev_args. rewrite rcc_ev_len. lia. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot].
  1: { rewrite HE2. replace (spZ regs - 144 + 144) with (spZ regs) by lia.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). unfold spZ. apply Z_to_bv_bv_unsigned. }
  1: { rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (Z_to_bv 5 3) eq_refl).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3. }
  1: { rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (Z_to_bv 5 4) eq_refl).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4. }
  all: rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?n = getr _ _ =>
      let j := eval compute in (n - 41)%nat in change n with (41 + j)%nat; rewrite (Esv j ltac:(lia)); reflexivity end. }
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

(* ---------- seeds ---------- *)
Lemma rcc_seed : forall E (regs1 : bvmap 5 word) pc sregs rs G SH (Wc : world SEGS) memc,
regs_ok E sregs regs1 -> regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict (w_H Wc) memc)) rs ->
pairwise_disjoint E rs -> facts_ok E G -> Forall (shent_ok SEGS rcc_Bx E (mrestrict (w_H Wc) memc)) SH ->
st_ok_pi SEGS VAL E (mkSS pc sregs rs None G) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS rcc_Bx SH E (mrestrict (w_H Wc) memc).
Proof. intros. split; [|assumption]. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; assumption. Qed.
(* the frame as the latch and the inner loop see it *)
Lemma rcc_stkl_ok : forall regs1 GA DA aI na nc fn sa (Wc : world SEGS) memc GS DS,
getr regs1 2 = w64 (spZ regs - 144) -> getr regs1 25 = w64 GS -> getr regs1 26 = w64 DS ->
0 <= GS < 2 ^ 64 -> 0 <= DS < 2 ^ 64 ->
(forall o, 0 <= o < 144 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 144 + o)) ->
rcc_frame (rdW Wc memc) (spZ regs - 144) dst GS DS regs ->
region_ok SEGS (rcc_E regs1 regs dst GA DA aI na nc fn sa) (mrestrict (w_H Wc) memc) rcc_stkl.
Proof.
intros regs1 GA DA aI na nc fn sa Wc memc GS DS R2 R25 R26 HG HD Hwr (F8 & F16 & F24 & F32 & FS).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
assert (E2 : bv_unsigned (ew (rcc_E regs1 regs dst GA DA aI na nc fn sa) 2) = spZ regs - 144)
  by (rewrite (rcc_EE regs1 regs dst GA DA aI na nc fn sa 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
unfold rcc_stkl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [exact Hwr|].
apply Forall_app. split.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 144) 8 8 (SOff (A_OBJ 44) 0) A_G_REC);
    [cbn [sv_denot]; rewrite (rcc_E285 regs1 regs dst GA DA aI na nc fn sa HVAL), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold A_G_REC; zside | zside | apply rcc_val_of_aval; exact F8].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 144) 16 8 (SOff 33 0) dst);
    [cbn [sv_denot]; rewrite (rcc_E33 regs1 regs dst GA DA aI na nc fn sa), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold CALL_SIZE in *; zside | zside | apply rcc_val_of_aval; exact F16].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 144) 24 8 (SOff 25 0) GS);
    [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (rcc_EE regs1 regs dst GA DA aI na nc fn sa 25%nat 25%bv eq_refl), R25;
     reflexivity | zside | zside | apply rcc_val_of_aval; exact F24].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 144) 32 8 (SOff 26 0) DS);
    [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (rcc_EE regs1 regs dst GA DA aI na nc fn sa 26%nat 26%bv eq_refl), R26;
     reflexivity | zside | zside | apply rcc_val_of_aval; exact F32].
- apply Forall_map. apply Forall_forall. intros j Hj.
  assert (Hj13 : (j < 13)%nat) by (apply in_seq in Hj; lia).
  assert (Hnth : nth_error rcc_saved j = Some (nth j rcc_saved 0))
    by (apply nth_error_nth'; unfold rcc_saved; cbn [length]; lia).
  unfold rcc_sav.
  apply (chunk_ok_val SEGS _ _ (spZ regs - 144) (136 - 8 * Z.of_nat j) 8 (SOff (41 + j) 0)
    (bv_unsigned (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))));
  [cbn [sv_denot]; rewrite (rcc_Esav regs1 regs dst GA DA aI na nc fn sa j Hj13), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))) as HR;
    change (bv_modulus 64) with (2 ^ 64) in HR; zside
  | zside | ].
  replace (spZ regs - 144 + (136 - 8 * Z.of_nat j)) with (spZ regs - 144 + 136 - 8 * Z.of_nat j) by lia.
  apply rcc_val_of_aval. exact (FS j (nth j rcc_saved 0) Hnth).
Qed.
(* the frame's words read back after a run: the two cursors are any atom plus an offset *)
Lemma rcc_slots_of : forall E H (m : word -> option byte) wlo whi cs i (n24 n32 : nat) c24 c32,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) 0 144 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs - 144 -> bv_unsigned (ew E 285) = A_G_REC -> bv_unsigned (ew E 33) = dst ->
(i <= 2)%nat -> 4096 <= dst -> dst + 8 + 56 * Z.of_nat i < 2 ^ 64 ->
In (YP09.mkChunk 8 (CVal 8 (SOff 285 0))) cs -> In (YP09.mkChunk 16 (CVal 8 (SOff 33 0))) cs ->
In (YP09.mkChunk 24 (CVal 8 (SOff n24 c24))) cs -> bv_unsigned (ew E n24) + c24 = A_G_REC + 24 + 56 * Z.of_nat i ->
In (YP09.mkChunk 32 (CVal 8 (SOff n32 c32))) cs -> bv_unsigned (ew E n32) + c32 = dst + 8 + 56 * Z.of_nat i ->
rcc_slots (aview SEGS H m) i.
Proof.
intros E H m wlo whi cs i n24 n32 c24 c32 HR Hb E285 E33 Hi Hd0 Hd1 C8 C16 C24 V24 C32 V32.
split; [apply (rcc_chunk_val E H m wlo whi cs 8 285 0); [exact HR | exact Hb | exact C8 | rewrite E285; lia | unfold A_G_REC; lia]|].
split; [apply (rcc_chunk_val E H m wlo whi cs 16 33 0); [exact HR | exact Hb | exact C16 | rewrite E33; lia | lia]|].
split; [apply (rcc_chunk_val E H m wlo whi cs 24 n24 c24); [exact HR | exact Hb | exact C24 | exact V24 | unfold A_G_REC; lia]|].
apply (rcc_chunk_val E H m wlo whi cs 32 n32 c32); [exact HR | exact Hb | exact C32 | exact V32 | lia].
Qed.
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
(* a block live at a later state of the walk lies below alloc_ceiling and apart from the copy table: the table is in
   a frame of the caller, and no live block meets a live frame *)
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
  | eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := -144);
    [reflexivity | rewrite Usp; lia | cbn; rewrite WS; lia | cbn; lia |]
  | eapply awr_ok_cons_gen;
    [reflexivity | eassumption | cbn [YP09.r_wlo YP09.r_whi]; intros ax Hax; eapply rcc_awr_dst;
     [exact HJ | unfold CALL_SIZE in *; lia] |] ];
  apply awr_ok_nil.

(* ---------- the inner loop's helpers ---------- *)
Lemma zsum_cons : forall f x l, zsum f (x :: l) = f x + zsum f l.
Proof. reflexivity. Qed.
Lemma rcc_chunk_val' : forall E H (m : word -> option byte) (nb : nat) b lo hi wlo whi cs off (n : nat) c v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
bv_unsigned (ew E nb) = b ->
In (YP09.mkChunk off (CVal 8 (SOff n c))) cs ->
bv_unsigned (ew E n) + c = v -> 0 <= v < 2 ^ 64 ->
aval_mem (aview SEGS H m) (b + off) 8 v.
Proof.
intros E H m nb b lo hi wlo whi cs off n c v HR Hb Hin Hv Hr.
pose proof (field_of_region_any E _ nb b cs lo hi wlo whi off 8%N (SOff n c) HR Hb Hin ltac:(cbn; lia)) as Hm.
cbn [sv_denot] in Hm. rewrite Hv in Hm. rewrite unsigned_lit_small in Hm by lia.
change (8 * Z.of_N 8) with 64 in Hm. rewrite Z.mod_small in Hm by lia. change (N.to_nat 8) with 8%nat in Hm.
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
(* the shadow-cell sums the walk's registers hold, once their atoms are numbers *)
Lemma rcc_alu_shx : forall (E0 : env) x sb, 0 <= x < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 sb) = Z_to_bv 64 (sb + x / 8).
Proof.
intros E0 x sb Hx Hsb.
change (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 sb))
  with (sv_denot E0 (SAlu ALU_ADD (SAlu ALU_SRL (SLit x) (SLit 3)) (SLit sb))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 (SAlu ALU_ADD (SAlu ALU_SRL (SLit x) (SLit 3)) (SLit sb)))). f_equal.
change (U E0 (SAlu ALU_ADD (SAlu ALU_SRL (SLit x) (SLit 3)) (SLit sb)) = sb + x / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. unfold U. cbn [sv_denot].
rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (x / 8)) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma rcc_alu_shx' : forall (E0 : env) x sb, 0 <= x < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
alu64 ALU_ADD (Z_to_bv 64 sb) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) = Z_to_bv 64 (sb + x / 8).
Proof.
intros E0 x sb Hx Hsb.
change (alu64 ALU_ADD (Z_to_bv 64 sb) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)))
  with (sv_denot E0 (SAlu ALU_ADD (SLit sb) (SAlu ALU_SRL (SLit x) (SLit 3)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 (SAlu ALU_ADD (SLit sb) (SAlu ALU_SRL (SLit x) (SLit 3))))). f_equal.
change (U E0 (SAlu ALU_ADD (SLit sb) (SAlu ALU_SRL (SLit x) (SLit 3))) = sb + x / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. unfold U. cbn [sv_denot].
rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (x / 8)) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma rcc_alu_add : forall (E0 : env) x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros E0 x y Hx Hy Hxy.
change (alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y)) with (sv_denot E0 (SAlu ALU_ADD (SLit x) (SLit y))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 (SAlu ALU_ADD (SLit x) (SLit y)))). f_equal.
change (U E0 (SAlu ALU_ADD (SLit x) (SLit y)) = x + y).
rewrite U_SAlu. cbn [zalu_raw]. unfold U. cbn [sv_denot]. rewrite !unsigned_lit_small by lia.
rewrite zcanon_small by lia. reflexivity.
Qed.
(* a 64-bit literal equation, once its operands are numbers *)
Ltac rcc_w64 := unfold w64; rewrite ?unsigned_lit_small by (unfold A_G_REC, SB, CALL_SIZE in *; lia); f_equal; lia.
Lemma rcc_perm_snoc : forall (l1 l2 l3 : list (Z * Z)) x, Permutation l2 l3 -> Permutation l1 (x :: l2) -> Permutation l1 (l3 ++ [x]).
Proof.
intros l1 l2 l3 x H23 H1. eapply Permutation_trans; [exact H1|]. eapply Permutation_trans; [apply Permutation_cons_append|].
apply Permutation_app_tail. exact H23.
Qed.
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

(* ---------- the inner loop's body: 0x897c4 .. 0x8980c, the xstrdup call at 0x897d0 ---------- *)
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
  (Hc & Ha & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HPART & HSL
   & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2 & Hfapp).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hi : (i < NC)%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
destruct (rcc_now lyc Sc Wc memc mdc k (concat qs ++ Pa) HJ HPm) as (KBe & HREPc & HRODc).
destruct (rcc_src_call lyc Sc (rdW Wc memc) i c HREPc Hc) as (Hfn & Hn6 & HLMAX).
destruct (rcc_src_arg lyc Sc (rdW Wc memc) i c a HREPc Hc Ha) as (s & sa & sn & Hs & HVsa & Hsa0 & Hsain & Hsn & HsL & Hstr).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpresc & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARc Hfinc) as (_ & _ & Hfp & _).
assert (Ha6 : (a < 6)%nat) by lia.
assert (HwrD : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H Wc) memc) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + o)).
{ intros o Ho. apply (apresent_writable SEGS).
  apply (proj1 (Hfp (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + o) ltac:(rewrite Efa; unfold CALL_SIZE in *; lia))). }
assert (Hwr : forall o, 0 <= o < 144 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 144 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
destruct (rcc_tab_ra lyc Sc Wc memc mdc k HJ) as (HRAt & HBDt).
assert (HRAg : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) 8).
{ apply (range_addressable_sub _ _ A_G_REC REC_SIZE);
  [exact (cmd_cf_grec SEGS B LAWS HB lyc Sc Wc memc _ HARc) | unfold A_G_REC in *; lia | unfold A_G_REC, REC_SIZE in *; lia]. }
assert (HBDg : forall x, A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a <= x < A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a + 8 ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) by (intros x Hx; unfold A_G_REC, SHADOW_OFF in *; lia).
assert (HG8 : (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) mod 8 = 0).
{ replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) with (A_G_REC + (3 + 7 * Z.of_nat i + Z.of_nat a) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
assert (HD8 : (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) mod 8 = 0).
{ replace (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) with (dst + (1 + 7 * Z.of_nat i + Z.of_nat a) * 8) by lia.
  rewrite Z_mod_plus_full. exact Hd8. }
assert (HX4 : (dst + (4 + 56 * Z.of_nat i)) mod 4 = 0).
{ destruct (proj1 (Z.mod_divide dst 8 ltac:(lia)) Hd8) as [q Hq].
  replace (dst + (4 + 56 * Z.of_nat i)) with (q * 2 * 4 + (1 + 14 * Z.of_nat i) * 4) by lia.
  rewrite Z.add_comm, Z_mod_plus_full. apply Z_mod_mult. }
assert (HNA : aval_mem (rdW Wc memc) (dst + (4 + 56 * Z.of_nat i)) 4 (Z.of_nat (length (snd c)))).
{ destruct HPART as (_ & _ & Hna & _). replace (dst + (4 + 56 * Z.of_nat i)) with (dst + CALL_SIZE * Z.of_nat i + 4)
    by (unfold CALL_SIZE; lia). exact Hna. }
destruct (rcc_blk_dst lyc Sc Wc memc mdc k (sa, sn) HJ Hsain) as (Hsa4 & Hsac & Hsn0 & Hsad).
cbn [fst snd] in Hsa4, Hsac, Hsn0, Hsad.
pose proof (rcc_E285' regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa HVAL) as E285.
pose proof (rcc_E32 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E32.
pose proof (rcc_E33 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E33.
pose proof (rcc_E34 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E34.
pose proof (rcc_E35 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E35.
pose proof (rcc_E37 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E37.
pose proof (rcc_E40 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E40.
pose proof (rcc_Esav regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as Esv.
pose proof (rcc_EE regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa))
  by (unfold rcc_E; apply Eimg_env).
destruct (rcc_seed (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa)
  regs1 RCC_INNER rcc_regs_i2 [rcc_stkl; rcc_dsti; rcc_ga; rcc_da] rcc_facts_i rcc_SHi Wc memc) as [HS SHOK].
{ apply (rcc_regs_i2_ok regs1 regs dst _ _ _ _ _ _ _ (dst + (4 + 56 * Z.of_nat i)) R9 R18 R19 R20 R22 R23 R24 R27);
  [unfold CALL_SIZE in *; lia | unfold A_G_REC in *; lia | unfold CALL_SIZE in *; lia]. }
{ vm_compute. reflexivity. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_stkl_ok regs1 _ _ _ _ _ _ _ Wc memc (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i)
      R2 R25 R26); [unfold A_G_REC; lia | unfold CALL_SIZE in *; lia | exact Hwr |].
    destruct HSL as (F8 & F16 & F24 & F32). exact (conj F8 (conj F16 (conj F24 (conj F32 HSV)))).
  - apply (rcc_dsti_ok regs1 regs dst _ _ _ _ _ _ _ Wc memc (dst + (4 + 56 * Z.of_nat i)) R9);
    [unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | lia | exact HNA].
  - apply (rcc_ga_ok regs1 regs dst _ _ _ _ _ _ _ Wc memc);
    [unfold A_G_REC; lia | unfold A_G_REC; lia | lia | exact HVsa].
  - apply (rcc_da_ok regs1 regs dst _ _ _ _ _ _ _ Wc memc);
    [unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | exact HwrD]. }
{ apply pairwise_disjoint_of_extents. unfold rcc_stkl, rcc_dsti, rcc_ga, rcc_da, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (EE 2%nat 2%bv eq_refl), R2, (EE 9%nat 9%bv eq_refl), R9, E34, E35.
  unfold w64. rewrite !unsigned_lit_small by (unfold A_G_REC, CALL_SIZE in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (rcc_dst_grec (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) ltac:(unfold CALL_SIZE in *; lia)) as HAp.
  unfold A_G_REC, CALL_SIZE in *. repeat split; lia. }
{ apply (rcc_facts_i_ok regs1 regs dst _ _ _ _ _ _ _ HVAL (spZ regs - 144) (dst + (4 + 56 * Z.of_nat i)));
  [ rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia
  | lia | replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
  | exact R9 | unfold CALL_SIZE in *; lia | exact HX4 | unfold A_G_REC; lia | exact HG8
  | unfold CALL_SIZE in *; lia | exact HD8 | lia ]. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_shent_any _ 9%nat (dst + (4 + 56 * Z.of_nat i)) (-4) 52 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia
    | lia
    | apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia]
    | intros x Hx; apply HBDt; unfold CALL_SIZE in *; lia].
  - apply (rcc_shent_any _ 34%nat (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) 0 8 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E34; apply unsigned_lit_small; unfold A_G_REC; lia | lia
    | rewrite Z.add_0_r; replace (8 - 0) with 8 by lia; exact HRAg
    | intros x Hx; apply HBDg; lia].
  - apply (rcc_shent_any _ 35%nat (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) 0 8 Wc memc);
    [rewrite E32; apply unsigned_lit_small; unfold SB; lia
    | rewrite E35; apply unsigned_lit_small; unfold CALL_SIZE in *; lia | lia
    | rewrite Z.add_0_r; replace (8 - 0) with 8 by lia;
      apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia]
    | intros x Hx; apply HBDt; unfold CALL_SIZE in *; lia]. }
remember (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  (Z.of_nat a) (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) sa) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E35u : bv_unsigned (ew E 35) = dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)
  by (rewrite E35; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E9u : bv_unsigned (ew E 9) = dst + (4 + 56 * Z.of_nat i))
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
(* 0x897c4 .. 0x897d0: the source slot's check, its word, the call *)
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ rcc_awr Usp WS HJ. }
rcc_keep HFr K1 (fun x => spZ regs - 144 <= x < spZ regs \/
  dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a <= x < dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 8).
clear HF HFr HG. clear_md.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
rewrite (HSIG CS_xstrdup ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_xstrdup) with (BASE + AF_xstrdup) by (unfold cmd_af, AF_xstrdup; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ => set (rT0 := rT) in *; set (mT0 := mT) in *; set (dT0 := dT) in * end.
assert (HspT : spZ rT0 = spZ regs - 144) by (unfold spZ at 1; rewrite P2, Usp; reflexivity).
assert (P3' : getr rT0 3 = w64 (as_gp B)).
{ rewrite P3, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3. exact Hgp. }
assert (P4' : getr rT0 4 = w64 (as_tp B)).
{ rewrite P4, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4. exact Htp. }
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr rT0 1)).
{ rewrite P1. rewrite unsigned_lit_small; lia. }
assert (P10' : getr rT0 10 = w64 sa) by (rewrite P10, E40; reflexivity).
assert (Hs0 : achain lyc (rdW Wc mT0) (spZ regs - 144) (s0Z rT0) []).
{ unfold achain. left. split; [|reflexivity]. left. unfold s0Z. rewrite P8, (EE 8%nat 8%bv eq_refl), R8.
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ mT0 dT0 _ |- _ => rename HJx into HJT end.
destruct (rcc_now lyc Sc Wc mT0 dT0 k (concat qs ++ Pa) HJT HPm) as (_ & _ & HRODT).
assert (HstrT : astr_atR (rdW Wc mT0) sa s).
{ apply (rcc_str_keep (rdW Wc memc)); [exact Hstr|]. intros x Hx. rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity. }
assert (HSRC : astr_argA B lyc Sc (rdW Wc mT0) (in_roP SEGS RLO RHI) [] sa (Some s) \/
  (astr_atR (rdW Wc mT0) sa s /\ Z.of_nat (length s) + 1 <= LMAX + 1 /\
   afobj SEGS B lyc Sc Wc mT0 sa (Z.of_nat (length s) + 1))).
{ left. cbn [astr_argA]. split; [exact Hsa0|]. split; [exact HstrT|]. split; [unfold LMAX in *; lia|].
  left. split; [exists sa, sn; split; [exact Hsain | lia] | apply Forall_nil]. }
(* the word tail after the string: the block's, by the record (cmd_heap_tail_vis) at the call's state *)
assert (HTAIL : atail_vis SEGS Wc mT0 (sa + Z.of_nat (length s)))
  by exact (cmd_heap_tail_vis lyc Sc Wc mT0 dT0 sa sn (sa + Z.of_nat (length s)) (proj1 HJT) Hsain ltac:(lia)).
pose proof (rcc_args_at (r_calls R) i c a s Hc Hs) as HSPL.
pose proof (zsum_nonneg LIVE_XSTRDUP (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))
  ltac:(intros x; unfold LIVE_XSTRDUP; lia)) as Hz1.
pose proof (zsum_nonneg (XM_XSTRDUP MT) (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))
  ltac:(intros x; unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia)) as Hz2.
assert (HSUMl : LIVE_REC_CALLS_COPY R = zsum LIVE_XSTRDUP (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))
  + LIVE_XSTRDUP s + zsum LIVE_XSTRDUP (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))).
{ unfold LIVE_REC_CALLS_COPY.
  change (fold_right (fun x acc => LIVE_XSTRDUP x + acc) 0 (PRcc.rcc_args (r_calls R)))
    with (zsum LIVE_XSTRDUP (PRcc.rcc_args (r_calls R))).
  rewrite HSPL at 1. rewrite zsum_app, zsum_cons. lia. }
assert (HSUMm : XM_REC_CALLS_COPY MT R = zsum (XM_XSTRDUP MT) (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))
  + XM_XSTRDUP MT s + zsum (XM_XSTRDUP MT) (skipn (Datatypes.S a) (snd c) ++ PRcc.rcc_args (skipn (Datatypes.S i) (r_calls R)))).
{ unfold XM_REC_CALLS_COPY.
  change (fold_right (fun x acc => XM_XSTRDUP MT x + acc) 0 (PRcc.rcc_args (r_calls R)))
    with (zsum (XM_XSTRDUP MT) (PRcc.rcc_args (r_calls R))).
  rewrite HSPL at 1. rewrite zsum_app, zsum_cons. lia. }
assert (HLENa : Z.of_nat (length (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))) + 1 <= ev_args R).
{ unfold ev_args. rewrite rcc_ev_len. rewrite HSPL. rewrite !length_app. cbn [length]. lia. }
assert (HEVc : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ unfold EV_XSTRDUP. unfold EV_REC_CALLS_COPY, EV_XSTRDUP in HEV. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_XSTRDUP s <= LIVE_MAX) by lia.
assert (HMOKc : mo_ok MT Sc (XM_XSTRDUP MT s)).
{ apply (mok_station MT S Sc (XM_REC_CALLS_COPY MT R)
    (zsum (XM_XSTRDUP MT) (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c))) (XM_XSTRDUP MT s) MTL HMOK HMLE);
  [unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia | lia]. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc rT0 mT0 _ STK (spZ regs) FP ly S W mem md [] lyc Sc dT0 k XSTRDUP_STK [] EV_XSTRDUP
    (-144) (getr rT0 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
      getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
      Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP s) :: ablocks B lyc Sc) /\
      Forall (fun qk => iv_apart p (LIVE_XSTRDUP s) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
      in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP s) /\
      astr_atR (rdW W2 mem2) p s /\ astr_atR (rdW W2 mem2) sa s /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP s /\
      mo_le MT Sc S2 (XM_XSTRDUP MT s)));
  [ exact HJT
  | exact HspT | reflexivity | lia | unfold XSTRDUP_STK, ASTACK; lia | rewrite WS; unfold XSTRDUP_STK, ASTACK; lia
  | exact P3' | exact P4' | reflexivity | exact HraT | exact Hra4T | exact Hs0
  | | intros x Hx; exfalso; exact (inFP_nil x Hx) ].
  intros HPRE1.
  exact (HXSTRDUP fx lyc Sc Wc rT0 mT0 dT0 [] sa s HPRE1 HRODT P10' HSRC HTAIL HEVc HLIVEc HMOKc). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & pnew & Ha02 & Hp4096 & HPm2 & HAPn
  & HINBn & HSTRn & HSTRs & HBB2 & MLE2).
rewrite P1.
jafter_call_keep_pi HS 56%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia
    | intros x _; apply inFP_nil].
  - eapply (region_kept_frame_sub (segs := SEGS) B _ _ _ _ lyc Sc Wc mT0 dT0 ly2 S2 W2 mem2 md2 _ 9%nat (dst + (4 + 56 * Z.of_nat i)));
    [exact HJc2 | exact E9u | exact Hfinc | rewrite Efa; unfold CALL_SIZE in *; lia | rewrite Efa; unfold CALL_SIZE in *; lia
    | intros x _; apply inFP_nil | cbn; intros x Hx; lia].
  - eapply (region_kept_frame_sub (segs := SEGS) B _ _ _ _ lyc Sc Wc mT0 dT0 ly2 S2 W2 mem2 md2 _ 35%nat
      (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a));
    [exact HJc2 | exact E35u | exact Hfinc | rewrite Efa; unfold CALL_SIZE in *; lia | rewrite Efa; unfold CALL_SIZE in *; lia
    | intros x _; apply inFP_nil |].
    cbn [YP09.r_wlo YP09.r_whi]. intros x Hx.
    pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
    destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (_ & Efa2 & _).
    assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & Hfp2 & _).
    apply (proj1 (Hfp2 x ltac:(rewrite Efa2; unfold CALL_SIZE in *; lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 56 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 56)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (OLDH : forall n, (76 <= n)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2; apply ew_havoc_above; cbn [length map CLOB]; lia).
assert (E60 : ew E2 60 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs - 144) by (rewrite OLD2 by lia; exact Usp).
assert (E9u2 : bv_unsigned (ew E2 9) = dst + (4 + 56 * Z.of_nat i)) by (rewrite OLD2 by lia; exact E9u).
assert (E35u2 : bv_unsigned (ew E2 35) = dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) by (rewrite OLD2 by lia; exact E35u).
assert (E33u2 : bv_unsigned (ew E2 33) = dst) by (rewrite OLD2 by lia; exact E33u).
assert (E285u2 : bv_unsigned (ew E2 285) = A_G_REC) by (rewrite OLDH by lia; exact E285u).
assert (E32u2 : bv_unsigned (ew E2 32) = SB) by (rewrite OLD2 by lia; rewrite E32; apply unsigned_lit_small; unfold SB; lia).
destruct (rcc_tab_ra ly2 S2 W2 mem2 md2 (k + EV_XSTRDUP) HJ2) as (HRAt2 & HBDt2).
assert (SHOK2 : sh_ok SEGS rcc_Bx rcc_SHa E2 (mrestrict (w_H W2) mem2)).
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_shent_any _ 9%nat (dst + (4 + 56 * Z.of_nat i)) (-4) 52 W2 mem2); [exact E32u2 | exact E9u2 | lia | |].
    + apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt2 | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia].
    + intros x Hx. apply HBDt2. unfold CALL_SIZE in *. lia.
  - apply (rcc_shent_any _ 35%nat (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) 0 8 W2 mem2); [exact E32u2 | exact E35u2 | lia | |].
    + rewrite Z.add_0_r. replace (8 - 0) with 8 by lia.
      apply (range_addressable_sub _ _ dst (CALL_SIZE * Z.of_nat NC)); [exact HRAt2 | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia].
    + intros x Hx. apply HBDt2. unfold CALL_SIZE in *. lia. }
(* 0x897d4 .. 0x8980c: the copy's slot check, the store, the nargs reload, the back-edge *)
paj_run_tok RUN HS HJ2 SHOK2 rcc_Bspan.
{ rcc_awr Usp2 WS HJ2. }
rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs \/
  dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a <= x < dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 8).
clear HF HFr HG. clear_md.
assert (Hpnin : In (pnew, LIVE_XSTRDUP s) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm2 | left; reflexivity]).
destruct (rcc_blk_dst ly2 S2 W2 _ _ (k + EV_XSTRDUP) (pnew, LIVE_XSTRDUP s) HJ2 Hpnin) as (Hpn4 & Hpnc & _ & Hpnd).
cbn [fst snd] in Hpn4, Hpnc, Hpnd.
(* xstrdup kept the copy table (a frame of the caller) and every block that was live *)
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
assert (KT : forall x, dst <= x < dst + CALL_SIZE * Z.of_nat NC -> rdW W2 mem2 x = rdW Wc mT0 x).
{ intros x Hx. apply (G4 cid pos x Hfinc); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa; unfold CALL_SIZE in *; lia | apply inFP_nil]. }
assert (KBk : forall pn j, In pn (ablocks B lyc Sc) -> 0 <= j < snd pn -> rdW W2 mem2 (fst pn + j) = rdW Wc mT0 (fst pn + j)).
{ intros [p n] j Hb Hj. cbn [fst snd] in *.
  assert (Hb2 : In (p, n) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm2 | right; exact Hb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [_ Hq].
  apply (G2 p n j Hb Hb2); [lia | apply inFP_nil]. }
assert (HPmn : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ (concat qs ++ Pa) ++ [(pnew, LIVE_XSTRDUP s)])).
{ rewrite app_assoc. apply (rcc_perm_snoc _ (ablocks B lyc Sc) _ _ HPm HPm2). }
assert (HFR : forall q, In q (ablocks B ly S ++ concat qs ++ Pa) -> iv_apart pnew (LIVE_XSTRDUP s) (fst q) (snd q)).
{ intros q Hq. apply (proj1 (Forall_forall _ _) HAPn). eapply Permutation_in; [apply Permutation_sym; exact HPm | exact Hq]. }
assert (HNDn : NoDup (map fst ((concat qs ++ Pa) ++ [(pnew, LIVE_XSTRDUP s)]))).
{ rewrite map_app. cbn [map]. apply rcc_nodup_snoc; [exact HND|].
  intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hqin). cbn [fst] in Hq. subst q.
  pose proof (HFR (pnew, m) ltac:(apply in_or_app; right; exact Hqin)) as Hap. cbn [fst snd] in Hap.
  pose proof (proj1 (Forall_forall _ _) H1 (pnew, m) Hqin) as Hm1. cbn [snd] in Hm1.
  unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (H1n : Forall (fun pn => 1 <= snd pn) ((concat qs ++ Pa) ++ [(pnew, LIVE_XSTRDUP s)])).
{ apply Forall_app. split; [exact H1 | apply Forall_cons; [cbn [snd]; unfold LIVE_XSTRDUP; lia | apply Forall_nil]]. }
assert (HAPn' : forall pn q, In pn ((concat qs ++ Pa) ++ [(pnew, LIVE_XSTRDUP s)]) -> In q (ablocks B ly S) ->
  iv_apart (fst pn) (snd pn) (fst q) (snd q)).
{ intros pn q Hpn Hq. apply in_app_or in Hpn as [Hpn | [<- | []]]; [exact (HAP pn q Hpn Hq)|].
  cbn [fst snd]. exact (HFR q ltac:(apply in_or_app; left; exact Hq)). }
assert (HBBn : blocks_bytes S2 <= blocks_bytes S +
  zsum LIVE_XSTRDUP ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])).
{ rewrite zsum_app, zsum_one. lia. }
assert (HMLEn : mo_le MT S S2 (zsum (XM_XSTRDUP MT) ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s]))).
{ rewrite zsum_app, zsum_one. exact (mle_station MT S Sc S2 _ _ MTL HMLE MLE2). }
assert (Hkn : 0 <= k + EV_XSTRDUP <= Z.of_nat (length ((PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])))
  by (rewrite length_app; cbn [length]; unfold EV_XSTRDUP; lia).
assert (HARGn : PRcc.rcc_args (firstn i (r_calls R)) ++ firstn (Datatypes.S a) (snd c)
  = (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])
  by (rewrite (rcc_firstn_S (snd c) a s Hs), app_assoc; reflexivity).
psrr_branch_tok RUN BR HS SHOK2 rcc_Bspan.
- (* another argument: back to 0x897c4 *)
  assert (HaS : (Datatypes.S a < length (snd c))%nat).
  { cbn [sv_denot] in Hc0. rewrite !OLD2 in Hc0 by lia.
    rewrite (EE 8%nat 8%bv eq_refl), R8, E37 in Hc0. unfold w64 in Hc0.
    rewrite !unsigned_lit_small in Hc0 by lia. rewrite ?Z.add_0_r in Hc0.
    rewrite rcc_blt in Hc0 by lia. apply Z.ltb_lt in Hc0. lia. }
  clear Hc0.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 rcc_Bspan RCC_INNER.
  { rcc_awr Usp2 WS HJ2. }
  rcc_keep HFr K3 (fun x => spZ regs - 144 <= x < spZ regs \/
    dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a <= x < dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 8).
  clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg;
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
    cbn [ms_mem restrict mkst] in HRd end.
  apply (NXT HaS (Pa ++ [(pnew, LIVE_XSTRDUP s)]) ly2 S2 W2 _ _ (k + EV_XSTRDUP)).
  split; [exact Hc|]. split; [exact HaS|].
  split.
  { split; [exact HJ2|]. rewrite HARGn.
    split; [exact Hkn|]. split; [rewrite (app_assoc (concat qs)); exact HPmn|].
    split; [rewrite (app_assoc (concat qs)); exact HNDn|].
    split; [rewrite (app_assoc (concat qs)); exact H1n|]. split; [rewrite (app_assoc (concat qs)); exact HAPn'|].
    split; [exact HBBn|]. split; [exact HMLEn|].
    split; [apply (rcc_saves_get E2 _ _ _ _ _ HRg Usp2);
      [intros j Hj; rewrite OLD2 by lia; exact (Esv j Hj) | intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia]|].
    split; [rewrite Q2, OLD2, (EE 2%nat 2%bv eq_refl) by lia; exact R2|].
    split; [rewrite Q3, OLD2, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia;
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3|].
    rewrite Q4, OLD2, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia;
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4. }
  split.
  { apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly2 S2) i qs HTAB).
    - intros x Hx. rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
      rewrite (KT x ltac:(unfold CALL_SIZE in *; lia)).
      rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - intros pn Hpn Hb. split.
      + eapply Permutation_in; [apply Permutation_sym; exact HPm2 | right; exact Hb].
      + intros j Hj. destruct (rcc_blk_dst lyc Sc Wc _ _ k pn HJT Hb) as (Hq4 & Hqc & _ & Hqd).
        rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
        rewrite (KBk pn j Hb Hj).
        rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity. }
  split.
  { apply (rcc_part_snoc _ _ i c a Pa s (pnew, LIVE_XSTRDUP s)); [| exact Hs | | cbn [fst]; lia | exact Hpnin
    | cbn [snd]; reflexivity |].
    - apply (rcc_part_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly2 S2) i c a Pa HPART).
      + intros x Hx. rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
        rewrite (KT x ltac:(unfold CALL_SIZE in *; lia)).
        rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm2 | right; exact Hb].
        * intros j Hj. destruct (rcc_blk_dst lyc Sc Wc _ _ k pn HJT Hb) as (Hq4 & Hqc & _ & Hqd).
          rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
          rewrite (KBk pn j Hb Hj).
          rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - cbn [fst]. replace (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a)
        with (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 0) by (unfold CALL_SIZE; lia).
      apply (rcc_chunk_val' E2 _ _ 35%nat _ _ _ _ _ _ 0 60%nat 0 pnew HRd E35u2);
      [cbn; tauto | rewrite E60, Ha02; unfold w64; rewrite unsigned_lit_small by lia; lia | lia].
    - cbn [fst]. apply (rcc_str_keep (rdW W2 mem2)); [exact HSTRn|].
      intros x Hx. rewrite K3, K2 by (unfold LIVE_XSTRDUP, CALL_SIZE in *; lia). reflexivity. }
  split.
  { apply (rcc_slots_of E2 _ _ _ _ _ i 25%nat 26%nat 0 0 HRg Usp2 E285u2 E33u2);
    [lia | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto
    | rewrite OLD2, (EE 25%nat 25%bv eq_refl), R25 by lia; unfold w64; rewrite unsigned_lit_small by (unfold A_G_REC; lia); lia
    | cbn; tauto
    | rewrite OLD2, (EE 26%nat 26%bv eq_refl), R26 by lia; unfold w64; rewrite unsigned_lit_small by (unfold CALL_SIZE in *; lia); lia]. }
  split; [rewrite Q8, OLD2, (EE 8%nat 8%bv eq_refl), R8 by lia; rcc_w64|].
  split; [rewrite Q9, OLD2, (EE 9%nat 9%bv eq_refl) by lia; exact R9|].
  split; [rewrite Q18, OLD2, E34 by lia; rcc_w64|].
  split; [rewrite Q19, OLD2, E35 by lia; rcc_w64|].
  split; [rewrite Q20, OLD2, E32 by lia; reflexivity|].
  split; [rewrite Q21, OLD2, (EE 21%nat 21%bv eq_refl) by lia; exact R21|].
  split.
  { rewrite Q22, ?OLD2 by lia. rewrite ?E34, ?E32. unfold w64.
    rewrite (rcc_alu_shx E) by (unfold A_G_REC, SB in *; lia).
    assert (Hg8 : 0 <= (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a) / 8 <= A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a)
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold A_G_REC; lia).
    rewrite (rcc_alu_add E) by (unfold A_G_REC, SB in *; lia). f_equal.
    replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat (Datatypes.S a))
      with (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat a + 1 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  split; [rewrite Q23, OLD2, E35 by lia; rcc_w64|].
  split; [rewrite Q24, OLD2, E34 by lia; rcc_w64|].
  split; [rewrite Q25, OLD2, (EE 25%nat 25%bv eq_refl) by lia; exact R25|].
  split; [rewrite Q26, OLD2, (EE 26%nat 26%bv eq_refl) by lia; exact R26|].
  rewrite Q27, ?OLD2 by lia. rewrite (EE 9%nat 9%bv eq_refl), R9, E32. unfold w64.
  rewrite (rcc_alu_shx E) by (unfold CALL_SIZE, SB in *; lia). reflexivity.
- (* the last argument: on to the latch 0x89824 *)
  assert (HaS : Datatypes.S a = length (snd c)).
  { cbn [sv_denot] in Hc0. rewrite !OLD2 in Hc0 by lia.
    rewrite (EE 8%nat 8%bv eq_refl), R8, E37 in Hc0. unfold w64 in Hc0.
    rewrite !unsigned_lit_small in Hc0 by lia. rewrite ?Z.add_0_r in Hc0.
    rewrite rcc_blt in Hc0 by lia. apply Z.ltb_ge in Hc0. lia. }
  clear Hc0.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 rcc_Bspan RCC_LATCH.
  { rcc_awr Usp2 WS HJ2. }
  rcc_keep HFr K3 (fun x => spZ regs - 144 <= x < spZ regs \/
    dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a <= x < dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 8).
  clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg;
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
    cbn [ms_mem restrict mkst] in HRd end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
  assert (HPARTn : rcc_part (rdW W2 mm) (ablocks B ly2 S2) i c (Datatypes.S a) (Pa ++ [(pnew, LIVE_XSTRDUP s)])) end.
  { apply (rcc_part_snoc _ _ i c a Pa s (pnew, LIVE_XSTRDUP s)); [| exact Hs | | cbn [fst]; lia | exact Hpnin
    | cbn [snd]; reflexivity |].
    - apply (rcc_part_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly2 S2) i c a Pa HPART).
      + intros x Hx. rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
        rewrite (KT x ltac:(unfold CALL_SIZE in *; lia)).
        rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm2 | right; exact Hb].
        * intros j Hj. destruct (rcc_blk_dst lyc Sc Wc _ _ k pn HJT Hb) as (Hq4 & Hqc & _ & Hqd).
          rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
          rewrite (KBk pn j Hb Hj).
          rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - cbn [fst]. replace (dst + CALL_SIZE * Z.of_nat i + 8 + 8 * Z.of_nat a)
        with (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a + 0) by (unfold CALL_SIZE; lia).
      apply (rcc_chunk_val' E2 _ _ 35%nat _ _ _ _ _ _ 0 60%nat 0 pnew HRd E35u2);
      [cbn; tauto | rewrite E60, Ha02; unfold w64; rewrite unsigned_lit_small by lia; lia | lia].
    - cbn [fst]. apply (rcc_str_keep (rdW W2 mem2)); [exact HSTRn|].
      intros x Hx. rewrite K3, K2 by (unfold LIVE_XSTRDUP, CALL_SIZE in *; lia). reflexivity. }
  rewrite HaS in HPARTn.
  apply (LTK (qs ++ [Pa ++ [(pnew, LIVE_XSTRDUP s)]]) ly2 S2 W2 _ _ (k + EV_XSTRDUP)).
  split; [exact Hi|].
  split.
  { split; [exact HJ2|]. rewrite (rcc_args_firstn_S (r_calls R) i c Hc).
    assert (HEQ : PRcc.rcc_args (firstn i (r_calls R)) ++ snd c
      = (PRcc.rcc_args (firstn i (r_calls R)) ++ firstn a (snd c)) ++ [s])
      by (rewrite <- HARGn, HaS, firstn_all; reflexivity).
    rewrite HEQ. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
    split; [exact Hkn|]. split; [rewrite (app_assoc (concat qs)); exact HPmn|].
    split; [rewrite (app_assoc (concat qs)); exact HNDn|].
    split; [rewrite (app_assoc (concat qs)); exact H1n|]. split; [rewrite (app_assoc (concat qs)); exact HAPn'|].
    split; [exact HBBn|]. split; [exact HMLEn|].
    split; [apply (rcc_saves_get E2 _ _ _ _ _ HRg Usp2);
      [intros j Hj; rewrite OLD2 by lia; exact (Esv j Hj) | intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia]|].
    split; [rewrite Q2, OLD2, (EE 2%nat 2%bv eq_refl) by lia; exact R2|].
    split; [rewrite Q3, OLD2, (EE 3%nat (Z_to_bv 5 3) eq_refl) by lia;
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3|].
    rewrite Q4, OLD2, (EE 4%nat (Z_to_bv 5 4) eq_refl) by lia;
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4. }
  split.
  { apply (rcc_tab_snoc _ _ i qs c (Pa ++ [(pnew, LIVE_XSTRDUP s)])).
    - apply (rcc_tab_keep (rdW Wc memc) _ (ablocks B lyc Sc) (ablocks B ly2 S2) i qs HTAB).
      + intros x Hx. rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
        rewrite (KT x ltac:(unfold CALL_SIZE in *; lia)).
        rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
      + intros pn Hpn Hb. split.
        * eapply Permutation_in; [apply Permutation_sym; exact HPm2 | right; exact Hb].
        * intros j Hj. destruct (rcc_blk_dst lyc Sc Wc _ _ k pn HJT Hb) as (Hq4 & Hqc & _ & Hqd).
          rewrite K3, K2 by (unfold CALL_SIZE in *; lia).
          rewrite (KBk pn j Hb Hj).
          rewrite K1 by (unfold CALL_SIZE in *; lia). reflexivity.
    - exact Hc.
    - apply (rcc_slot_of_part _ _ i c _ HPARTn Hfn Hn6 HLMAX).
      rewrite map_app. cbn [map]. apply rcc_nodup_snoc.
      + rewrite map_app in HND. exact (rcc_nodup_r _ _ HND).
      + intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hqin). cbn [fst] in Hq. subst q.
        pose proof (HFR (pnew, m) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hqin)) as Hap.
        cbn [fst snd] in Hap.
        pose proof (proj1 (Forall_forall _ _) H1 (pnew, m) ltac:(apply in_or_app; right; exact Hqin)) as Hm1.
        cbn [snd] in Hm1. unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
  split.
  { apply (rcc_slots_of E2 _ _ _ _ _ i 25%nat 26%nat 0 0 HRg Usp2 E285u2 E33u2);
    [lia | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto
    | rewrite OLD2, (EE 25%nat 25%bv eq_refl), R25 by lia; unfold w64; rewrite unsigned_lit_small by (unfold A_G_REC; lia); lia
    | cbn; tauto
    | rewrite OLD2, (EE 26%nat 26%bv eq_refl), R26 by lia; unfold w64; rewrite unsigned_lit_small by (unfold CALL_SIZE in *; lia); lia]. }
  split; [rewrite Q20, OLD2, E32 by lia; reflexivity|].
  split; [rewrite Q21, OLD2, (EE 21%nat 21%bv eq_refl) by lia; exact R21|].
  split; [rewrite Q25, OLD2, (EE 25%nat 25%bv eq_refl) by lia; exact R25|].
  rewrite Q26, OLD2, (EE 26%nat 26%bv eq_refl) by lia; exact R26.
Qed.

(* ---------- the outer latch: 0x89824 .. 0x89850, then the outer head or (via 0x89854) the epilogue ---------- *)
Lemma rcc_latch : forall i qs lyc Sc Wc memc mdc k regs1,
(forall memc' mdc' regs1', rcc_OH (Datatypes.S i) qs lyc Sc Wc memc' mdc' k regs1' ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_OUTER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
rcc_LT i qs lyc Sc Wc memc mdc k regs1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_LATCH)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i qs lyc Sc Wc memc mdc k regs1 OHK
  (Hi & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HSL & R20 & R21 & R25 & R26).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct (rcc_now lyc Sc Wc memc mdc k (concat qs) HJ HPm) as (_ & HREPc & _).
assert (HNC : aval_mem (rdW Wc memc) (A_G_REC + 8) 4 (Z.of_nat NC)).
{ destruct HREPc as (Q & (_ & _ & _ & (_ & _ & HN & _) & _) & _). exact HN. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
assert (Hwr : forall o, 0 <= o < 144 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 144 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
pose proof (rcc_E285' regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 HVAL) as E285.
pose proof (rcc_E33 regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E33.
pose proof (rcc_E32 regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E32.
pose proof (rcc_E38 regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E38.
pose proof (rcc_Esav regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as Esv.
pose proof (rcc_EE regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0)) by (unfold rcc_E; apply Eimg_env).
assert (HSK : region_ok SEGS (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) (mrestrict (w_H Wc) memc) rcc_stkl).
{ apply (rcc_stkl_ok regs1 0 0 0 0 (Z.of_nat NC) 0 0 Wc memc (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i)
    R2 R25 R26); [unfold A_G_REC; lia | unfold CALL_SIZE in *; lia | exact Hwr |].
  destruct HSL as (F8 & F16 & F24 & F32). exact (conj F8 (conj F16 (conj F24 (conj F32 HSV)))). }
assert (HNR : region_ok SEGS (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) (mrestrict (w_H Wc) memc) rcc_nc)
  by (apply (rcc_nc_ok regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0 HVAL Wc memc); [lia | exact HNC]).
assert (HRS : regs_ok (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) sr_atoms regs1) by (unfold rcc_E; apply regs_ok_Eimg_Ereg).
remember (rcc_E regs1 regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E38u : bv_unsigned (ew E 38) = Z.of_nat NC) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E21u : bv_unsigned (ew E 21) = Z.of_nat i) by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (E25u : bv_unsigned (ew E 25) = A_G_REC + 24 + 56 * Z.of_nat i)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E26u : bv_unsigned (ew E 26) = dst + 8 + 56 * Z.of_nat i)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
destruct (rcc_seed E regs1 RCC_LATCH sr_atoms [rcc_stkl; rcc_nc] rcc_facts_l [] Wc memc) as [HS SHOK].
{ exact HRS. }
{ vm_compute. reflexivity. }
{ apply Forall_cons; [exact HSK | apply Forall_cons; [exact HNR | apply Forall_nil]]. }
{ apply pairwise_disjoint_of_extents. unfold rcc_stkl, rcc_nc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 44) with 285%nat.
  rewrite Usp, E285u. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC. repeat split; lia. }
{ split; [|split; exact I]. cbn [rcc_facts_l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  change (A_OBJ 44) with 285%nat.
  rewrite Usp, E32, E38, E285, !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold A_G_REC.
  assert (Hm16 : (spZ regs - 144) mod 16 = 0)
    by (replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
  repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hm16 | lia | reflexivity]. }
{ apply Forall_nil. }
clear HSK HNR HRS.
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ rcc_awr Usp WS HJ. }
rcc_keep HFr K1 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
- (* i + 1 < nc: back to the outer head *)
  assert (HSi : (Datatypes.S i < NC)%nat).
  { cbn [sv_denot] in Hc. rewrite E21u, E38u, Z.add_0_r in Hc. rewrite rcc_blt in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_OUTER.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (14%bv : bv 5) Q14.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
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
  { apply (rcc_slots_of E _ _ _ _ _ (Datatypes.S i) 25 26 56 56 HRg Usp E285u E33u);
      [lia | lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto | rewrite E25u; lia | cbn; tauto | rewrite E26u; lia]. }
  split; [rewrite Q14, E285; reflexivity|].
  split; [rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite Q21, E21u; unfold w64; f_equal; lia|].
  split; [rewrite Q25, E25u; unfold w64; f_equal; lia|].
  rewrite Q26, E26u; unfold w64; f_equal; lia.
- (* the last call: on to the epilogue *)
  assert (HSi : Datatypes.S i = NC).
  { cbn [sv_denot] in Hc. rewrite E21u, E38u, Z.add_0_r in Hc. rewrite rcc_blt in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_RET.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG.
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

(* ---------- the outer body: 0x89730 .. 0x897a4 (call i's two scalar fields into slot i), then the inner head 0x897c4
   or, for a call with no argument, the latch 0x89824 ---------- *)
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
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat i <= x < dst + 56 * Z.of_nat i + 8) ->
  rdW Wc memc' x = rdW Wc memc x) /\
rcc_saves (rdW Wc memc') /\ rcc_slots (rdW Wc memc') i /\
aval_mem (rdW Wc memc') (dst + 56 * Z.of_nat i) 4 fn /\ aval_mem (rdW Wc memc') (dst + 56 * Z.of_nat i + 4) 4 na /\
getr regs1' 2 = getr regs1 2 /\ getr regs1' 3 = getr regs1 3 /\ getr regs1' 4 = getr regs1 4 /\
getr regs1' 20 = w64 SB /\ getr regs1' 21 = w64 (Z.of_nat i) /\
getr regs1' 25 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) /\ getr regs1' 26 = w64 (dst + 8 + 56 * Z.of_nat i).
(* the outer body's runs, for each of the (at most two) calls: the call index is a number in each run *)
Lemma rcc_ob_run : forall i, (i < 2)%nat -> forall E lyc Sc Wc memc mdc k regs1 na fn,
(i < NC)%nat -> img_env VAL A_LIM E ->
bv_unsigned (ew E 2) = spZ regs - 144 -> ew E 32 = Z_to_bv 64 SB -> bv_unsigned (ew E 33) = dst ->
bv_unsigned (ew E 285) = A_G_REC -> bv_unsigned (ew E 37) = na -> bv_unsigned (ew E 39) = fn ->
0 <= na <= 6 -> 0 <= fn < 2 ^ 31 ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) ->
(forall j, (j < 13)%nat -> ew E (41 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0))) ->
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] lyc Sc Wc memc mdc k ->
st_ok_pi SEGS VAL E (mkSS RCC_OUTER (rcc_regs_o (Z.of_nat i)) [rcc_stk (Z.of_nat i); rcc_src (Z.of_nat i); rcc_dst0 (Z.of_nat i)]
  None rcc_facts) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS))) ->
sh_ok SEGS rcc_Bx (rcc_SH_o (Z.of_nat i)) E (mrestrict (w_H Wc) memc) ->
(forall memc' mdc' regs1', rcc_OB i na fn lyc Sc Wc memc k regs1 memc' mdc' regs1' -> na <= 0 ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_LATCH)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
(forall memc' mdc' regs1', rcc_OB i na fn lyc Sc Wc memc k regs1 memc' mdc' regs1' -> 0 < na ->
  getr regs1' 8 = w64 0 -> getr regs1' 9 = w64 (dst + (4 + 56 * Z.of_nat i)) ->
  getr regs1' 18 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) -> getr regs1' 19 = w64 (dst + 8 + 56 * Z.of_nat i) ->
  getr regs1' 22 = w64 (SB + (A_G_REC + 24 + 56 * Z.of_nat i) / 8) -> getr regs1' 23 = w64 (dst + 8 + 56 * Z.of_nat i) ->
  getr regs1' 24 = w64 (A_G_REC + 24 + 56 * Z.of_nat i) -> getr regs1' 27 = w64 (SB + (dst + (4 + 56 * Z.of_nat i)) / 8) ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + RCC_INNER)) memc' (seg_rom SEGS)) mdc') rcc_Q) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCC_OUTER)) memc (seg_rom SEGS)) mdc) rcc_Q.
Proof.
intros i Hi2 E lyc Sc Wc memc mdc k regs1 na fn Hi HEI Usp E32 E33u E285u E37u E39u Hna Hfn EE Esv HJ HS SHOK LTC IHC.
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct i as [|[|i]]; [| | lia].
- (* call 0 *)
  paj_run_tok RUN HS HJ SHOK rcc_Bspan.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K1 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
  clear HF HFr HG. clear_md.
  psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
  + (* no argument: on to the latch 0x89824 *)
    assert (Hnz : na <= 0).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_LATCH.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
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
    split; [apply (rcc_slots_of E _ _ _ _ _ 0%nat 285%nat 33%nat 24 8 HRg Usp E285u E33u);
      [lia | lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto | rewrite E285u; lia | cbn; tauto
      | rewrite E33u; lia]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat) with (dst + 0) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 0 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 0%nat + 4) with (dst + 4) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 4 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q20, E32; reflexivity|].
    split; [rewrite Q21; reflexivity|].
    split; [rewrite Q25, E285u; rcc_w64|].
    rewrite Q26, E33u; rcc_w64.
  + (* an argument: on to the inner head 0x897c4 *)
    assert (Hnz : 0 < na).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_INNER.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 0%nat <= x < dst + 56 * Z.of_nat 0%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply IHC.
    {
      split; [exact HJ|].
      split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
      split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
      split; [apply (rcc_slots_of E _ _ _ _ _ 0%nat 285%nat 33%nat 24 8 HRg Usp E285u E33u);
        [lia | lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto | rewrite E285u; lia | cbn; tauto
        | rewrite E33u; lia]|].
      split; [replace (dst + 56 * Z.of_nat 0%nat) with (dst + 0) by lia;
        apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 0 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
      split; [replace (dst + 56 * Z.of_nat 0%nat + 4) with (dst + 4) by lia;
        apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 4 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
      split; [rewrite Q2; apply EE; reflexivity|].
      split; [rewrite Q3; apply EE; reflexivity|].
      split; [rewrite Q4; apply EE; reflexivity|].
      split; [rewrite Q20, E32; reflexivity|].
      split; [rewrite Q21; reflexivity|].
      split; [rewrite Q25, E285u; rcc_w64|].
      rewrite Q26, E33u; rcc_w64.
    }
    { exact Hnz. }
    { rewrite Q8; reflexivity. }
    { rewrite Q9, E33u; rcc_w64. }
    { rewrite Q18, E285u; rcc_w64. }
    { rewrite Q19, E33u; rcc_w64. }
    { rewrite Q22, E32, E285u. replace (A_G_REC + 24 + 56 * Z.of_nat 0%nat) with (A_G_REC + 24) by lia.
      unfold w64. apply (rcc_alu_shx' E); unfold A_G_REC, SB; lia. }
    { rewrite Q23, E33u; rcc_w64. }
    { rewrite Q24, E285u; rcc_w64. }
    { rewrite Q27, E33u, E32. replace (dst + (4 + 56 * Z.of_nat 0%nat)) with (dst + 4) by lia.
      unfold w64. apply (rcc_alu_shx E); unfold SB, CALL_SIZE in *; lia. }
- (* call 1 *)
  paj_run_tok RUN HS HJ SHOK rcc_Bspan.
  { rcc_awr Usp WS HJ. }
  rcc_keep HFr K1 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
  clear HF HFr HG. clear_md.
  psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
  + (* no argument: on to the latch 0x89824 *)
    assert (Hnz : na <= 0).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_LATCH.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
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
    split; [apply (rcc_slots_of E _ _ _ _ _ 1%nat 285%nat 33%nat 80 64 HRg Usp E285u E33u);
      [lia | lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto | rewrite E285u; lia | cbn; tauto
      | rewrite E33u; lia]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat) with (dst + 56) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 56 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
    split; [replace (dst + 56 * Z.of_nat 1%nat + 4) with (dst + 60) by lia;
      apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 60 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
    split; [rewrite Q2; apply EE; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|].
    split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q20, E32; reflexivity|].
    split; [rewrite Q21; reflexivity|].
    split; [rewrite Q25, E285u; rcc_w64|].
    rewrite Q26, E33u; rcc_w64.
  + (* an argument: on to the inner head 0x897c4 *)
    assert (Hnz : 0 < na).
    { cbn [sv_denot] in Hc. rewrite E37u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_INNER.
    { rcc_awr Usp WS HJ. }
    rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs \/ dst + 56 * Z.of_nat 1%nat <= x < dst + 56 * Z.of_nat 1%nat + 8).
    clear HF HFr HG. clear_md.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict mkst] in HRg;
      let r2 := eval vm_compute in (nth 2 (ss_mem ssx) rcc_da) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
      cbn [ms_mem restrict mkst] in HRd end.
    apply IHC.
    {
      split; [exact HJ|].
      split; [intros x Hx Hn; exact (eq_trans (K2 x Hx Hn) (K1 x Hx Hn))|].
      split; [apply (rcc_saves_get E _ _ _ _ _ HRg Usp Esv); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
      split; [apply (rcc_slots_of E _ _ _ _ _ 1%nat 285%nat 33%nat 80 64 HRg Usp E285u E33u);
        [lia | lia | unfold CALL_SIZE in *; lia | cbn; tauto | cbn; tauto | cbn; tauto | rewrite E285u; lia | cbn; tauto
        | rewrite E33u; lia]|].
      split; [replace (dst + 56 * Z.of_nat 1%nat) with (dst + 56) by lia;
        apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 56 39%nat 0 fn HRd E33u); [cbn; tauto | lia | lia]|].
      split; [replace (dst + 56 * Z.of_nat 1%nat + 4) with (dst + 60) by lia;
        apply (rcc_chunk_val4 E _ _ 33%nat dst _ _ _ _ _ 60 37%nat 0 na HRd E33u); [cbn; tauto | lia | lia]|].
      split; [rewrite Q2; apply EE; reflexivity|].
      split; [rewrite Q3; apply EE; reflexivity|].
      split; [rewrite Q4; apply EE; reflexivity|].
      split; [rewrite Q20, E32; reflexivity|].
      split; [rewrite Q21; reflexivity|].
      split; [rewrite Q25, E285u; rcc_w64|].
      rewrite Q26, E33u; rcc_w64.
    }
    { exact Hnz. }
    { rewrite Q8; reflexivity. }
    { rewrite Q9, E33u; rcc_w64. }
    { rewrite Q18, E285u; rcc_w64. }
    { rewrite Q19, E33u; rcc_w64. }
    { rewrite Q22, E32, E285u. replace (A_G_REC + 24 + 56 * Z.of_nat 1%nat) with (A_G_REC + 80) by lia.
      unfold w64. apply (rcc_alu_shx' E); unfold A_G_REC, SB; lia. }
    { rewrite Q23, E33u; rcc_w64. }
    { rewrite Q24, E285u; rcc_w64. }
    { rewrite Q27, E33u, E32. replace (dst + (4 + 56 * Z.of_nat 1%nat)) with (dst + 60) by lia.
      unfold w64. apply (rcc_alu_shx E); unfold SB, CALL_SIZE in *; lia. }
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
  (Hi & (HJ & Hk & HPm & HND & H1 & HAP & HBB & HMLE & HSV & R2 & R3 & R4) & HTAB & HSL & R14 & R20 & R21 & R25 & R26).
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
assert (Hwr : forall o, 0 <= o < 144 -> writable_at SEGS (mrestrict (w_H Wc) memc) (spZ regs - 144 + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpresc; rewrite WS; lia).
assert (HwrD : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H Wc) memc) (dst + 56 * Z.of_nat i + o)).
{ intros o Ho. apply (apresent_writable SEGS).
  apply (proj1 (Hfp (dst + 56 * Z.of_nat i + o) ltac:(rewrite Efa; unfold CALL_SIZE in *; lia))). }
destruct (rcc_tab_ra lyc Sc Wc memc mdc k HJ) as (HRAt & HBDt).
assert (HDG : dst + CALL_SIZE * Z.of_nat NC <= A_G_REC \/ A_G_REC + 960 <= dst).
{ apply (rcc_iv_of_ne dst (dst + CALL_SIZE * Z.of_nat NC) A_G_REC (A_G_REC + 960)); [unfold CALL_SIZE; lia | unfold A_G_REC; lia |].
  intros x Hx1 Hx2. exact (rcc_dst_grec x Hx1 Hx2). }
pose proof (rcc_E285' regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0 HVAL) as E285.
pose proof (rcc_E32 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as E32.
pose proof (rcc_E33 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as E33.
pose proof (rcc_E37 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as E37.
pose proof (rcc_E39 regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as E39.
pose proof (rcc_Esav regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as Esv.
pose proof (rcc_EE regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0
  (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) 0)) by (unfold rcc_E; apply Eimg_env).
destruct (rcc_seed (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0
  (Z.of_nat (length (snd c))) (Z.of_nat NC) (fst c) 0)
  regs1 RCC_OUTER (rcc_regs_o (Z.of_nat i)) [rcc_stk (Z.of_nat i); rcc_src (Z.of_nat i); rcc_dst0 (Z.of_nat i)] rcc_facts
  (rcc_SH_o (Z.of_nat i)) Wc memc) as [HS SHOK].
{ apply (rcc_regs_o_ok regs1 regs dst _ _ _ _ _ _ _ HVAL (Z.of_nat i) R14 R20 R21 R25 R26); unfold CALL_SIZE in *; lia. }
{ destruct i as [|[|i]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (rcc_stk_ok regs1 regs dst _ _ _ _ _ _ _ HVAL Wc memc (Z.of_nat i) (spZ regs - 144) R2);
    [lia | lia | lia | lia | unfold CALL_SIZE in *; lia | unfold CALL_SIZE in *; lia | exact Hwr |].
    destruct HSL as (F8 & F16 & F24 & F32). exact (conj F8 (conj F16 (conj F24 (conj F32 HSV)))).
  - apply (rcc_src_ok regs1 regs dst _ _ _ _ _ _ _ HVAL Wc memc (Z.of_nat i));
    [lia | lia | unfold REC_FN_COUNT in *; lia | lia | exact Ffn | exact Fna].
  - apply (rcc_dst0_ok regs1 regs dst _ _ _ _ _ _ _ Wc memc (Z.of_nat i)); [lia | lia | unfold CALL_SIZE in *; lia | exact HwrD]. }
{ apply pairwise_disjoint_of_extents. unfold rcc_stk, rcc_src, rcc_dst0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 44) with 285%nat.
  rewrite (EE 2%nat 2%bv eq_refl), R2, E285, E33.
  unfold w64. rewrite !unsigned_lit_small by (unfold A_G_REC, CALL_SIZE in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, CALL_SIZE in *. repeat split; lia. }
{ apply (rcc_facts_ok regs1 regs dst _ _ _ _ _ _ _ HVAL (spZ regs - 144));
  [ rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia
  | lia | replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
  | unfold CALL_SIZE in *; lia | exact Hd8 | unfold A_G_REC; lia
  | replace (A_G_REC + 24 + 56 * Z.of_nat i) with (A_G_REC + (3 + 7 * Z.of_nat i) * 8) by lia;
    rewrite Z_mod_plus_full; reflexivity
  | unfold CALL_SIZE in *; lia
  | replace (dst + 8 + 56 * Z.of_nat i) with (dst + (1 + 7 * Z.of_nat i) * 8) by lia; rewrite Z_mod_plus_full; exact Hd8
  | lia | lia | lia | unfold REC_FN_COUNT in *; lia ]. }
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
remember (rcc_E regs1 regs dst (A_G_REC + 24 + 56 * Z.of_nat i) (dst + 8 + 56 * Z.of_nat i) 0 (Z.of_nat (length (snd c)))
  (Z.of_nat NC) (fst c) 0) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = dst) by (rewrite E33; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E37u : bv_unsigned (ew E 37) = Z.of_nat (length (snd c))) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = fst c) by (rewrite E39; apply unsigned_lit_small; unfold REC_FN_COUNT in *; lia).
apply (rcc_ob_run i Hi2 E lyc Sc Wc memc mdc k regs1 (Z.of_nat (length (snd c))) (fst c) Hi HEI Usp E32 E33u E285u E37u E39u
  ltac:(lia) ltac:(unfold REC_FN_COUNT in *; lia) EE Esv HJ HS SHOK).
- (* no argument: slot i holds call i with no argument blocks *)
  intros memc' mdc' regs1' (HJ' & K & HSV' & HSL' & Ffn' & Fna' & Q2 & Q3 & Q4 & Q20 & Q21 & Q25 & Q26) Hn0.
  assert (Hc0 : snd c = []) by (destruct (snd c); [reflexivity | cbn [length] in Hn0; lia]).
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
  split; [exact HSL'|].
  split; [exact Q20|]. split; [exact Q21|]. split; [exact Q25|]. exact Q26.
- (* arguments: on to the inner loop at argument 0 *)
  intros memc' mdc' regs1' (HJ' & K & HSV' & HSL' & Ffn' & Fna' & Q2 & Q3 & Q4 & Q20 & Q21 & Q25 & Q26) Hn0
    Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q27.
  apply (IHK c lyc Sc Wc memc' mdc' k regs1').
  split; [exact Hci|]. split; [lia|].
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
  split; [exact HSL'|].
  split; [exact Q8|]. split; [exact Q9|].
  split; [replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat 0) with (A_G_REC + 24 + 56 * Z.of_nat i) by lia; exact Q18|].
  split; [replace (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat 0) with (dst + 8 + 56 * Z.of_nat i) by lia; exact Q19|].
  split; [exact Q20|]. split; [exact Q21|].
  split; [replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat 0) with (A_G_REC + 24 + 56 * Z.of_nat i) by lia; exact Q22|].
  split; [replace (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat 0) with (dst + 8 + 56 * Z.of_nat i) by lia; exact Q23|].
  split; [replace (A_G_REC + 24 + 56 * Z.of_nat i + 8 * Z.of_nat 0) with (A_G_REC + 24 + 56 * Z.of_nat i) by lia; exact Q24|].
  split; [exact Q25|]. split; [exact Q26|]. exact Q27.
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

(* ---------- the entry: 0x896bc .. 0x89704 (the prologue, g_rec.ncalls), then the outer head or the epilogue ---------- *)
Lemma rcc_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_copy) regs mem md) rcc_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof rcc_geo as (Hal16 & Hsp & Hd4096 & Hdceil & Hd8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
pose proof (rcc_seed0 B TL HVAL W regs mem ly S md R O dst (Z.of_nat NC) HAR Hstk Hpres HREP eq_refl HLEN) as HS.
pose proof (ajournal_init SEGS B STK FP ly S W regs mem md ch HPRE) as HJ.
assert (SHOK : sh_ok SEGS rcc_Bx [] (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0) (mrestrict (w_H W) mem))
  by apply Forall_nil.
pose proof (rcc_E285' regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0 HVAL) as E285.
pose proof (rcc_E32 regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E32.
pose proof (rcc_E38 regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E38.
pose proof (rcc_EE regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as EE.
assert (HEI : img_env VAL A_LIM (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0)) by (unfold rcc_E; apply Eimg_env).
remember (rcc_E regs regs dst 0 0 0 0 (Z.of_nat NC) 0 0) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E285u : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E10u : bv_unsigned (ew E 10) = dst)
  by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; unfold CALL_SIZE in *; lia).
assert (E38u : bv_unsigned (ew E 38) = Z.of_nat NC) by (rewrite E38; apply unsigned_lit_small; lia).
(* the frame the prologue wrote: the thirteen saved registers *)
assert (HSAVES : forall cs mm, region_ok SEGS E (mrestrict (w_H W) mm) (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 cs) ->
  (forall j, (j < 13)%nat -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j rcc_saved 0)) 0))) cs) ->
  rcc_saves (rdW W mm)).
{ intros cs mm HRg Hin j r Hj.
  assert (Hj13 : (j < length rcc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length rcc_saved] in Hj13.
  assert (Hr : r = nth j rcc_saved 0) by (symmetry; apply nth_error_nth; exact Hj). subst r.
  replace (spZ regs - 144 + 136 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))) as HR64.
  change (bv_modulus 64) with (2 ^ 64) in HR64.
  apply (rcc_chunk_val' E _ _ 2%nat _ _ _ _ _ _ (-8 - 8 * Z.of_nat j) (Z.to_nat (nth j rcc_saved 0)) 0 _ HRg Usp (Hin j Hj13));
  [|exact HR64].
  rewrite Z.add_0_r, (EE (Z.to_nat (nth j rcc_saved 0)) (Z_to_bv 5 (nth j rcc_saved 0))); [reflexivity|].
  do 13 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
unfold cfg_at. change (w64 (BASE + AF_rec_calls_copy)) with (Z_to_bv 64 (BASE + AF_rec_calls_copy)).
paj_run_tok RUN HS HJ SHOK rcc_Bspan.
{ awr_ok_tac. exact Usp. }
rcc_keep HFr K1 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG. clear_md.
psrr_branch_tok RUN BR HS SHOK rcc_Bspan.
- (* no call: on to the epilogue *)
  assert (HN0 : NC = 0%nat).
  { cbn [sv_denot] in Hc. rewrite E38u, Z.add_0_r in Hc. rewrite rcc_bge in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rcc_Bspan RCC_RET.
  { awr_ok_tac. exact Usp. }
  rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG. clear_md.
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
    split; [pose proof (zsum_nonneg LIVE_XSTRDUP (PRcc.rcc_args (r_calls R)) ltac:(intros x; unfold LIVE_XSTRDUP; lia)); lia|].
    split; [apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)); apply zsum_nonneg; intros x; unfold XM_XSTRDUP;
      apply (mo_malloc_nonneg MT MTL); lia|].
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
  rcc_keep HFr K2 (fun x => spZ regs - 144 <= x < spZ regs). clear HF HFr HG. clear_md.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (14%bv : bv 5) Q14.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) rcc_da) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  apply (rcc_outer (NC - 0) 0 [] ly S W _ _ 0 _ eq_refl).
  split; [exact HN1|].
  split.
  { split; [exact HJ|]. split; [lia|]. split; [cbn [concat]; rewrite app_nil_r; apply Permutation_refl|].
    split; [constructor|]. split; [constructor|]. split; [intros pn q Hpn; cbn in Hpn; contradiction|].
    split; [pose proof (zsum_nonneg LIVE_XSTRDUP (PRcc.rcc_args (firstn 0 (r_calls R))) ltac:(intros x; unfold LIVE_XSTRDUP; lia)); lia|].
    split; [apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)); apply zsum_nonneg; intros x; unfold XM_XSTRDUP;
      apply (mo_malloc_nonneg MT MTL); lia|].
    split; [apply (HSAVES _ _ HRg); intros j Hj; do 13 (destruct j as [|j]; [cbn; tauto|]); lia|].
    split; [rewrite Q2, Usp; rcc_w64|]. split; [rewrite Q3; apply EE; reflexivity|]. rewrite Q4; apply EE; reflexivity. }
  split.
  { split; [reflexivity|]. intros j c P _ HP. destruct j; cbn in HP; discriminate HP. }
  split.
  { split; [replace (spZ regs - 144 + 8) with (spZ regs + -136) by lia;
      apply (rcc_chunk_val' E _ _ 2%nat _ _ _ _ _ _ (-136) 285%nat 0 A_G_REC HRg Usp); [cbn; tauto | rewrite E285u; lia | unfold A_G_REC; lia]|].
    split; [replace (spZ regs - 144 + 16) with (spZ regs + -128) by lia;
      apply (rcc_chunk_val' E _ _ 2%nat _ _ _ _ _ _ (-128) 10%nat 0 dst HRg Usp); [cbn; tauto | rewrite E10u; lia | unfold CALL_SIZE in *; lia]|].
    split; [replace (spZ regs - 144 + 24) with (spZ regs + -120) by lia;
      apply (rcc_chunk_val' E _ _ 2%nat _ _ _ _ _ _ (-120) 285%nat 24 _ HRg Usp); [cbn; tauto | rewrite E285u; lia | unfold A_G_REC; lia]|].
    replace (spZ regs - 144 + 32) with (spZ regs + -112) by lia.
    apply (rcc_chunk_val' E _ _ 2%nat _ _ _ _ _ _ (-112) 10%nat 8 _ HRg Usp); [cbn; tauto | rewrite E10u; lia | unfold CALL_SIZE in *; lia]. }
  split; [rewrite Q14, E285; reflexivity|].
  split; [rewrite Q20, E32; reflexivity|].
  split; [rewrite Q21; reflexivity|].
  split; [rewrite Q25, E285u; rcc_w64|].
  rewrite Q26, E10u; rcc_w64.
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
