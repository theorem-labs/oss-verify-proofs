(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command): from
   the return of rec_shape_of (0x8b4a4) through the epilogue to the tail jump `j answer` (0x8b4c8), and answer's
   contract, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment that ends in a call, cl_callS) and
   lib/A/Prog/sup_reply_code.v (a walk whose last instruction is a tail jump). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run whose regions have no write window leaves the memory as it was *)
Lemma siv_nowin : forall E (m m' : word -> option byte),
frame_of E [siv_frame] m m' -> forall x, m' x = m x.
Proof. intros E m m' H x. apply H. intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn in Hr. lia. Qed.

Lemma siv_aview_eq : forall (H : word -> bool) (m m' : word -> option byte),
(forall x, mrestrict H m' x = mrestrict H m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' E a. unfold aview, mbyte. rewrite E. reflexivity. Qed.


Lemma siv_filter_in : forall (f : Z * Z -> bool) (l : list (Z * Z)) x, In x (filter f l) -> In x l.
Proof.
intros f l x. induction l as [|a l IH]; intros H; [exact H|].
revert H. cbn. destruct (Is_true_dec (f a)); intros H;
[destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H)].
Qed.

Lemma siv_sig : forall s, cmd_sig_prog -> In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. intros s H Hs. exact (H s Hs). Qed.

(* the registers the walk keeps between its calls: sp is the frame's, gp and tp the entry's, s0 the slot, s4 .. s11
   the entry's *)
Definition siv_regs_ok (B : asyms) (regs regs1 : bvmap 5 word) (c : Z) : Prop :=
spZ regs1 = spZ regs - 48 /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 c /\ (forall r, 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

Lemma siv_slot_ok : forall R, (length (r_calls R) <= 16)%nat -> rbs_slot_ok (siv_slot R).
Proof.
intros R H. unfold siv_slot, rbs_slot_ok. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((771818 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
apply Z_mod_mult.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the state at the return of rec_shape_of (0x8b4a4): the journal from the entry, the frame, the registers, the
   recorder with the call recorded and its two arguments added (O1 its blocks), the block facts I1 .. I4, a0 the
   reply shape's literal, the meter and the live bytes spent so far *)
Definition siv_at_tail ly S W (regs : bvmap 5 word) mem md (line : list byte) (ledger : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) memc mdc (regs1 : bvmap 5 word) (kk : Z) (Q1 : rlay) (q : Z) : Prop :=
let O1 := lay_blocks Q1 in
let x := shape_of (first_word line) in
ajournal SEGS B SUP_INSTANCE_VERB_STK (spZ regs) (siv_FP O) ly S W mem md [] lyc Sc Wc memc mdc kk /\
0 <= kk <= rec_spill_frees R + EV_ARG_LINE + EV_ARG_I /\
siv_frame_ok (mrestrict (w_H Wc) memc) (spZ regs) regs /\
siv_regs_ok B regs regs1 (siv_slot R) /\
arep_at (ablocks B lyc Sc) (rdW Wc memc) A_G_REC A_REC_SPILL
  (rec_record R REC_INSTANCE_VERB [canon line; dec ledger]) Q1 /\
(forall pn, In pn O1 -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O1) /\
getr regs1 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
(forall O0, astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) O0 q (Some x)) /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line + XM_ARG_I MT ledger) /\
blocks_bytes Sc <= blocks_bytes S + LIVE_ARG_LINE line + LIVE_ARG_I ledger.


Lemma siv_rec_repA_ext : forall ly S rd rd' R O, rec_repA B ly S rd R O -> (forall a, rd' a = rd a) ->
rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O H E. apply (rec_repA_kept B ly S rd ly S rd' R O H).
- exact (rec_repA_in B ly S rd R O H).
- intros a _. apply E. - intros a _. apply E. - intros p n0 i _ _. apply E.
Qed.

Lemma siv_arep_old : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) (lay_blocks Q)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha. unfold lay_blocks.
destruct (r_answer R) as [x|], (l_answer Q) as [[pa m]|]; try contradiction.
- exists pa. split; [exact (proj1 Ha)|]. right. exists m. apply in_app_iff. right.
  apply in_app_iff. right. apply in_app_iff. left. cbn [oblk In]. left. reflexivity.
- exists 0. split; [exact Ha | left; reflexivity].
Qed.

(* the footprint of the contract lies in the program's statics and the entry's live blocks *)
Lemma siv_FP_ok : forall ly S rd R O ly' S', rec_repA B ly S rd R O ->
forall a, inFP (siv_FP O) a -> Exists (in_zr a) recb_PG \/
  exists b n0, In (b, n0) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n0.
Proof.
intros ly S rd R O ly' S' HR a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]].
- left. apply recb_grec_in. cbn in Ha. exact Ha.
- left. apply recb_spill_in. cbn in Ha. exact Ha.
- right. destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n0 & Hpn & Hpa).
  exists p, n0. split; [apply in_or_app; left; exact (rec_repA_in B ly S rd R O HR _ Hpn) | exact Hpa].
Qed.

(* the footprint lies below the allocator's ceiling *)
Lemma siv_FP_low : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall a, inFP (siv_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O HAR HR a Ha. pose proof asan_consts as (C1 & _).
destruct (siv_FP_ok ly S rd R O ly S HR a Ha) as [HP | (b & n0 & Hb & Hba)].
- unfold recb_PG in HP. apply Exists_exists in HP as (x & Hx & Hz). unfold in_zr in Hz.
  cbn in Hx. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in Hx.
  destruct Hx as [<- | [<- | [<- | []]]]; cbn in Hz; lia.
- apply in_app_iff in Hb as [Hb | Hb];
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n0 HAR Hb) as (_ & _ & Hceil & _); lia.
Qed.


(* arodata_okP carried by a journal whose footprint is the contract's: the read-only bytes are image bytes outside
   the program's statics (cmd_ro_prog_apart) and outside every heap block *)
Lemma siv_aro_kept : ro_below_ofl SEGS RLO RHI -> (forall a, RLO <= a < RHI -> in_img SEGS a) ->
(forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG) ->
forall ly S (W : world SEGS) mem md rd R O lyc Sc (Wc : world SEGS) memc mdc STK sp0 own k,
AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
ajournal SEGS B STK sp0 (siv_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros HRO HREL HAP ly S W mem md rd R O lyc Sc Wc memc mdc STK sp0 own k HAR HR HJ HA.
apply (arodata_ok_journalP SEGS RLO RHI HREL B STK sp0 (siv_FP O) ly S W mem md own lyc Sc Wc memc mdc k HJ); [|exact HA].
intros a Hro Hfp. destruct (HAP a Hro) as [Himg HnPG].
destruct (siv_FP_ok ly S rd R O ly S HR a Hfp) as [HP | (b & n0 & Hb & Hba)]; [exact (HnPG HP)|].
apply in_app_iff in Hb as [Hb | Hb];
pose proof (blk_off_imgP (PI := PI) B ly S W mem md b n0 HAR Hb) as Hoff;
unfold off_img in Hoff; pose proof (pa_img_range a Himg); lia.
Qed.

(* the caller's frame chain above the entry sp, carried by the journal *)
Lemma siv_chain : forall STK sp0 FP ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain lyc (rdW Wc memc) sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md lyc Sc Wc memc mdc k v ch HJ HFP Hch.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly lyc); [first [exact Etop | symmetry; exact Etop]|].
apply (achain_kept ly (rdW W mem) (rdW Wc memc) sp0 v ch sp0 Hch); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hin; pose proof (HFP a Hin); lia].
Qed.

(* a string argument over another reader that agrees everywhere *)
Lemma siv_argA_ext : forall ly S (rd rd' : reader) (ro : Z -> Prop) O p x,
astr_argA B ly S rd ro O p (Some x) -> (forall a, rd' a = rd a) -> astr_argA B ly S rd' ro O p (Some x).
Proof.
intros ly S rd rd' ro O p x H E. unfold astr_argA in *. cbv zeta in *.
destruct H as (H0 & H1 & H2 & H3). split; [exact H0|]. split; [exact (rastr_kept _ _ _ _ H1 (fun i _ => E _))|].
split; [exact H2 | exact H3].
Qed.

Lemma siv_seg_tail : siv_hyps B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O lyc Sc (Wc : world SEGS) memc mdc regs1 kk Q1 q,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
siv_at_tail ly S W regs mem md line ledger R O lyc Sc Wc memc mdc regs1 kk Q1 q ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SIV_RSO_RET)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).
Proof.
intros HY ly S W regs mem md ch pl ledger line R O lyc Sc Wc memc mdc regs1 kk Q1 q CX HFRM ST.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
unfold siv_at_tail in ST. cbv zeta in ST.
destruct ST as (HJ & Hkk & HF & HR & HAREP & I1 & I2 & I3 & Q10 & Hq64 & HQARG & HMLE & HLV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct HR as (Rsp & Rgp & Rtp & R8 & Rhi).
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
assert (WA : ANSWER_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 48 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. clear - Hceil Hslo Hshi H47 Hstk0 C1 WS. lia. }
destruct HREP as (Q & HAQ & HOQ).
pose proof HAQ as (_ & _ & _ & (Hlen16 & _) & _).
set (n := Z.of_nat (length (r_calls R))) in *.
set (c := siv_slot R) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
assert (Hc : rbs_slot_ok c) by (unfold c; apply siv_slot_ok; exact Hlen16).
destruct (siv_seed_mid B HB VOBJS SIV_RSO_RET sr_atoms lyc Sc Wc memc mdc regs regs1 sp0 n c (proj1 HJ)
  Hsp46 Hal16 Hn Hc Rsp HF ltac:(unfold siv_E; apply regs_ok_Eimg_Ereg)) as [HS SHOK].
pose proof (siv_env regs regs1 n c) as HE. pose proof HE as (HEI & _).
set (E := siv_E regs regs1 n c) in *.
paj_run_tok RUN HS HJ SHOK siv_Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
(* the run wrote nothing *)
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?m2)) |- _ =>
  pose proof (siv_aview_eq (w_H Wc) memc (ms_mem m2) (siv_nowin E _ _ HFr)) as RDQ end.
(* the registers at the tail jump *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
assert (E2v : bv_unsigned (ew E 2) = sp0 - 48) by (pose proof HE as (_ & E2 & _); rewrite E2, Rsp; apply unsigned_lit_small; lia).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply siv_E_reg; exact Hk).
assert (ESV : forall j r, nth_error siv_saved j = Some r -> ew E (35 + j) = getr regs (Z_to_bv 5 r)) by (intros j r Hj; apply siv_E_saved; exact Hj).
assert (T1 : getr (ms_regs ms) 1 = getr regs 1) by (rewrite P1; exact (ESV 0%nat 1 eq_refl)).
assert (T2 : getr (ms_regs ms) 2 = getr regs 2).
{ rewrite P2, E2v. replace (sp0 - 48 + 48) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Rgp).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Rtp).
assert (T8 : getr (ms_regs ms) 8 = getr regs 8) by (rewrite P8; exact (ESV 1%nat 8 eq_refl)).
assert (T9 : getr (ms_regs ms) 9 = getr regs 9) by (rewrite P9; exact (ESV 2%nat 9 eq_refl)).
assert (T18 : getr (ms_regs ms) 18 = getr regs 18) by (rewrite P18; exact (ESV 3%nat 18 eq_refl)).
assert (T19 : getr (ms_regs ms) 19 = getr regs 19) by (rewrite P19; exact (ESV 4%nat 19 eq_refl)).
assert (T10 : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, (EE 8%nat 8%bv eq_refl); exact R8).
assert (T11 : getr (ms_regs ms) 11 = w64 q) by (rewrite P11, (EE 10%nat 10%bv eq_refl); exact Q10).
assert (Thi : forall r, 20 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  rewrite <- (Rhi r Hr).
  destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  (rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity). }
assert (HPT : aregs_preserved regs (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
  [ exact T2 | exact (eq_trans T3 (eq_sym Hgp)) | exact (eq_trans T4 (eq_sym Htp)) | exact T8 | exact T9 |].
  assert (Hr2 : r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
  destruct Hr2 as [-> | [-> | Hr2]]; [exact T18 | exact T19 | exact (Thi r Hr2)]. }
set (A2 := [canon line; dec ledger]) in *. set (R1 := rec_record R REC_INSTANCE_VERB A2) in *.
set (x := shape_of (first_word line)) in *. set (O1 := lay_blocks Q1) in *.
destruct (siv_arep_old _ _ _ _ HAREP) as (old & Hold & Hold').
assert (HrepT : rec_repA B lyc Sc (rdW Wc memc) R1 O1) by (exists Q1; split; [exact HAREP | intros pn; reflexivity]).
assert (I4 : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) by exact (rec_repA_in B lyc Sc _ R1 O1 HrepT).
assert (HrepE : rec_repA B ly S (rdW W mem) R O) by (exists Q; split; [exact HAQ | exact HOQ]).
assert (HT : snd (sup_instance_verb_m R line ledger) = snd (rec_answer R1 (REC_INSTANCE_VERB, A2) x true)) by reflexivity.
assert (Hin_ans : In CS_answer cmd_prog_syms) by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
rewrite (siv_sig CS_answer SIGP Hin_ans).
replace (cmd_af CS_answer) with AF_answer by (vm_compute; reflexivity).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (siv_aro_kept RRO RELRO ROPA ly S W mem md _ R O lyc Sc Wc (ms_mem ms) _ _ _ _ _ HAR HrepE HJ HROD).
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HARc (I4 _ Hm)) as (_ & H4096 & Hoceil & _ & _ & _ & Hk).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. pose proof alloc_ceiling_lt. lia. }
assert (Hc64 : 0 <= c < 2 ^ 64) by (destruct (rbs_slot_bounds c Hc) as [Hcb _]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (ROK lyc Sc Wc (ms_mem ms) _ HARc HRODc).
assert (HrepT' : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) R1 O1) by exact (siv_rec_repA_ext lyc Sc _ _ R1 O1 HrepT RDQ).
assert (HXa : 0 <= XM_ANSWER MT (snd (rec_answer R1 (REC_INSTANCE_VERB, A2) x true))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (rec_answer R1 (REC_INSTANCE_VERB, A2) x true))) + 1) ltac:(lia)). lia. }
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_answer)) SUP_INSTANCE_VERB_STK sp0 (siv_FP O)
    ly S W mem md [] lyc Sc _ kk ANSWER_STK _ _ 0 (getr (ms_regs ms) 1) ch _ HJ).
  - unfold spZ at 1. rewrite T2. fold (spZ regs). lia.
  - reflexivity.
  - lia.
  - rewrite WA. lia.
  - rewrite WA, WS. lia.
  - exact T3.
  - exact T4.
  - reflexivity.
  - rewrite T1. exact Hra.
  - rewrite T1. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite T8.
    exact (siv_chain _ sp0 _ ly S W mem md lyc Sc Wc (ms_mem ms) _ kk _ ch HJ (siv_FP_low ly S W mem md _ R O HAR HrepE) Hch).
  - intros HPRE1. unfold tanswer_spec in TANSWER.
    eapply (TANSWER fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ ch c q old (REC_INSTANCE_VERB, A2) x true R1 O1 HPRE1).
    + exact HFRM.
    + rewrite Hfrs. cbn [app]. exact HFR8.
    + exact HRODc.
    + exact HROc.
    + exact T10.
    + exact Hc64.
    + exact T11.
    + exact Hq64.
    + rewrite P12. reflexivity.
    + exact HrepT'.
    + exact (aval_mem_kept _ _ _ _ _ Hold (fun k _ => RDQ _)).
    + exact Hold64.
    + intros _. split; [exact (siv_argA_ext lyc Sc _ _ _ O1 q x (HQARG O1) RDQ) | exact (proj1 (shape_of_facts _))].
    + intros _ _. unfold R1, c, siv_slot, rec_record.
      destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
      * left. exists (length (r_calls R)). split; [|reflexivity].
        cbn [set_calls r_calls]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
      * right. split; reflexivity.
    + unfold EV_SUP_INSTANCE_VERB in HEV. lia.
    + rewrite <- HT. unfold LIVE_SUP_INSTANCE_VERB in HLIVE. lia.
    + apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE HXa). unfold XM_SUP_INSTANCE_VERB. rewrite HT. lia.
  - intros a (r & Hr & Har). destruct Hr as [<- | [<- | Hr]].
    + right; right; right; right; left. cbn [fst snd] in Har.
      assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_ANSWER, REC_SIZE in *; lia).
      split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Hg]|].
      split; [rewrite (RecBLemmas.recb_ts_prog_m B HB); exact (recb_grec_in a Hg) | exact (PIMG a (recb_grec_in a Hg))].
    + right; right; right; right; left. cbn [fst snd] in Har.
      assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_STATE, REC_SIZE in *; lia).
      split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Hg]|].
      split; [rewrite (RecBLemmas.recb_ts_prog_m B HB); exact (recb_grec_in a Hg) | exact (PIMG a (recb_grec_in a Hg))].
    + destruct (inFP_ablocks_fp_inv _ a (ex_intro _ r (conj Hr Har))) as (p & n0 & Hpn & Hpa).
      apply siv_filter_in in Hpn.
      destruct (I1 _ Hpn) as [HinO | Hnin].
      * right; left. split; [|exists p, n0; split; [exact (I4 _ Hpn) | exact Hpa]].
        destruct (inFP_ablocks_fp O p n0 (a - p) HinO ltac:(lia)) as (r' & Hr' & Ha').
        exists r'. split; [right; right; exact Hr' | replace a with (p + (a - p)) by lia; exact Ha'].
      * right; right; left. exists p, n0. split; [exact (I4 _ Hpn)|]. split; [exact Hnin | exact Hpa].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct Ha as (r & Hr & Har). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Har;
    [unfold A_G_REC, OFF_ANSWER in Har; lia | unfold A_G_REC, OFF_STATE in Har; lia |].
    destruct (inFP_ablocks_fp_inv _ a (ex_intro _ r (conj Hr Har))) as (p & n0 & Hpn & Hpa).
    apply siv_filter_in in Hpn.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n0 HARc (I4 _ Hpn)) as (_ & _ & Hpceil & _). lia. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJ2i & HP2 & HK2).
destruct HK2 as (p1 & p2 & O' & A10 & Ap2 & Ap12 & AN & ABL & AREP & AO & ASTR & ABB & AMLE).
unfold siv_post. rewrite T1.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly2 S2);
  [ exact Hfx
  | apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); unfold EV_SUP_INSTANCE_VERB; lia
  | exact (aregs_preserved_trans _ _ _ HPT HP2) |].
apply (siv_final B MT ly S W mem lyc Sc Wc (ms_mem ms) _ ly2 S2 W2 mem2 md2 regs2 line ledger R O O1 O' old p1 p2
  HARc (proj1 HJ2) I1 I2 I3 I4 Hold' A10 Ap2 Ap12 AN ABL AREP AO ASTR).
{ unfold LIVE_SUP_INSTANCE_VERB. rewrite HT. lia. }
apply (mle_weaken MT S S2 _ _ MTL (mle_station MT S Sc S2 _ _ MTL HMLE AMLE)).
unfold XM_SUP_INSTANCE_VERB. rewrite HT. lia.
Qed.

End e.
End f.
End d.
