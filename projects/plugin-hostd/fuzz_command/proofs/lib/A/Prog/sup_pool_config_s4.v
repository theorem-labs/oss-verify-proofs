(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths and module names changed; 169 of its 213 lines of code are new or changed and 483 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the facts sup_pool_config's ASan walk (plugin-hostd/fuzz_command) carries across its
   own stores and its callees' journals: the footprint, the writes to the slot, the program statics outside the runtime's
   owned statics, the string argument and the "(null)" default at a later state, the recorder across a callee that
   writes nothing outside its fresh blocks. In the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v's transports. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas sup_pool_config_s1 sup_pool_config_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the footprint of sup_pool_config's contract (sup_pool_config_c.v:94) *)
Definition spc_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma spc_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (spc_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.
Lemma spc_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (spc_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
Lemma spc_inFP_blk : forall O p n i, In (p, n) O -> 0 <= i < req_size n -> inFP (spc_FP O) (p + i).
Proof.
intros O p n i Hin Hi. destruct (inFP_ablocks_fp O p n i Hin Hi) as (r & Hr & Ha).
exists r. split; [right; right; exact Hr | exact Ha].
Qed.
Lemma spc_slot_in : forall c a, spc_slot_ok c -> c <= a < c + CALL_SIZE ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros c a [(H1 & H2 & _) | ->] Ha; [left | right]; unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.
Lemma spc_slot_PG : forall c a, spc_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. destruct (spc_slot_in c a Hc Ha) as [H | H]; [exact (recb_grec_in a H) | exact (recb_spill_in a H)].
Qed.
Lemma spc_slot_inFP : forall O c a, spc_slot_ok c -> c <= a < c + CALL_SIZE -> inFP (spc_FP O) a.
Proof.
intros O c a Hc Ha. destruct (spc_slot_in c a Hc Ha) as [H | H]; [exact (spc_inFP_grec O a H) | exact (spc_inFP_spill O a H)].
Qed.
(* the slot record() picks for R is a slot of the walk's kind *)
Lemma spc_slot_okR : forall R, (length (r_calls R) <= 16)%nat -> spc_slot_ok (spc_slot R).
Proof.
intros R H. unfold spc_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L | L]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE. split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((771818 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
apply Z_mod_mult.
Qed.
Lemma spc_FP_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (spc_FP O).
Proof.
intros O HO. apply sink_closed_pos. unfold spc_FP, ablocks_fp.
constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
apply Forall_map. eapply Forall_impl; [|exact HO]. intros [p n] Hp. exact Hp.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
(* the recorder walks' shared program-static and read-only facts (the record's, pending lib/A/Prog/CmdRecFacts.v) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* G2 (b): a heap string's tail word (cmd_heap_tail_vis) *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

(* a write of the walk to its slot is a footprint write to a program static (awr_byte's program-static disjunct) *)
Lemma spc_awr_slot : forall STK sp0 O bl0 blc fr0 lyc own c a,
spc_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (spc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own c a Hc Ha.
right; right; right; right. unfold awr_prog_or_caller. left.
split; [exact (spc_slot_inFP O c a Hc Ha)|].
pose proof (spc_slot_PG c a Hc Ha) as HPG.
split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.

(* g_rec, record.spill and g_quitting lie outside the runtime's owned statics and the errno cell (the record's
   tables, AF0m.v Tfib_owned_static and TFIB_ERRNO) *)
Lemma spc_prog_unowned : forall a, Exists (in_zr a) recb_PG ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a HPG. rewrite (ts_owned B HB), (ts_errno B HB).
apply Exists_exists in HPG as ([g gl] & Hg & Hag). unfold in_zr in Hag. cbn [fst snd] in Hag.
assert (Hchk : forallb (fun r => forallb (fun g => (fst r + snd r <=? fst g) || (fst g + snd g <=? fst r)) recb_PG)
  Tfib_owned_static = true) by (vm_compute; reflexivity).
split.
- intros Hown. apply Exists_exists in Hown as ([r rl] & Hr & Har). unfold in_zr in Har. cbn [fst snd] in Har.
  rewrite forallb_forall in Hchk. specialize (Hchk (r, rl) Hr). rewrite forallb_forall in Hchk.
  specialize (Hchk (g, gl) Hg). cbn [fst snd] in Hchk. apply orb_true_iff in Hchk as [H | H]; apply Z.leb_le in H; lia.
- unfold recb_PG in Hg. unfold TFIB_ERRNO.
  destruct Hg as [Hg | [Hg | [Hg | []]]]; injection Hg as <- <-; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hag; lia.
Qed.

(* a block live at a state of the walk is off the image, so apart from g_rec / record.spill and every image byte *)
Lemma spc_blk_off : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= a < p + req_size n -> ~ in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
split.
- intros Himg. pose proof (pa_img_range a Himg). lia.
- intros HPG. pose proof (cmd_prog_img a HPG) as Himg. pose proof (pa_img_range a Himg). lia.
Qed.

(* the string argument (a heap string, none of the recorder's blocks, so none record() frees) and its tail, from
   the entry to any later state of the walk *)
Lemma spc_arg_kept : forall STK sp0 O ly S W mem md own ly' S' W' mem' md' k s x,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (spc_FP O) ly S W mem md own ly' S' W' mem' md' k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
in_blockA (ablocks B ly S) s (Z.of_nat (length x) + 1) -> astr_atR (rdW W mem) s x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
Forall (fun qk => iv_apart s (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] s (Some x) /\
atail_vis SEGS W' mem' (s + Z.of_nat (length x)).
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k s x HAR HJ HO HSURV HIB HAT Hn HAP.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & KB & KI & _).
destruct HIB as (b & k0 & Hbk & Hbs & Hse).
destruct (al_blocks _ _ LAWS ly S W mem md b k0 HAR Hbk) as (_ & H4096 & _).
assert (HbO : ~ In (b, k0) O).
{ intros HbO. pose proof (proj1 (Forall_forall _ _) HAP _ HbO) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
pose proof (HSURV _ Hbk HbO) as Hbk'.
destruct (req_size_pos k0 ltac:(lia)) as [_ Hreq].
assert (KEEP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW W' mem' (s + i) = rdW W mem (s + i)).
{ intros i Hi. replace (s + i) with (b + (s + i - b)) by lia.
  apply (KB b k0 (s + i - b) Hbk Hbk'); [lia|].
  intros (r & Hr & Hra). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra.
  - destruct (spc_blk_off ly S W mem md b k0 (b + (s + i - b)) HAR Hbk ltac:(lia)) as [_ HPG].
    apply HPG. apply recb_grec_in. unfold REC_SIZE in *. lia.
  - destruct (spc_blk_off ly S W mem md b k0 (b + (s + i - b)) HAR Hbk ltac:(lia)) as [_ HPG].
    apply HPG. apply recb_spill_in. unfold SC_SIZE in *. lia.
  - destruct (inFP_ablocks_fp_inv O _ (ex_intro _ r (conj Hr Hra))) as (p & n & Hpn & Hpa).
    assert (Hne : (b, k0) <> (p, n)) by (intros E; rewrite E in HbO; exact (HbO Hpn)).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md b k0 p n HAR Hbk (HO _ Hpn) Hne) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (proj1 (Forall_forall _ _) HAP _ Hpn) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap.
    destruct (req_size_pos n ltac:(destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk); lia)) as [_ Hreqn].
    lia. }
split.
- split; [lia|]. split.
  + destruct HAT as [HB1 HB2]. split; [|exact HB2].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (KEEP (Z.of_nat i)) by lia. exact (HB1 i ltac:(rewrite length_app; cbn [length]; lia)).
  + split; [exact Hn|]. left. split; [exists b, k0; split; [exact Hbk' | lia] | constructor].
- exact (cmd_heap_tail_vis ly' S' W' mem' md' b k0 (s + Z.of_nat (length x)) HAR' Hbk' ltac:(lia)).
Qed.

(* the mid-walk regions write only the slot *)
Lemma spc_wrange_slot : forall E c cs a, base_val E (Some 34%nat) = c ->
in_wrange E [spc_frame; spc_slot_rg cs] a -> c <= a < c + CALL_SIZE.
Proof.
intros E c cs a Hc (r & Hr & Ha). destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi spc_frame spc_slot_rg] in Ha.
- lia.
- rewrite Hc in Ha. lia.
Qed.

(* a string argument and its tail survive writes to the slot only: none of its bytes or its tail word lies in g_rec
   or record.spill (the read-only arm's other facts do not read memory) *)
Lemma spc_argA_slot : forall ly S (W : world SEGS) mem mem' md c s x,
AR SEGS B ly S W mem md -> spc_slot_ok c ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW W mem' a = rdW W mem a) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] s (Some x) ->
atail_vis SEGS W mem (s + Z.of_nat (length x)) ->
astr_argA B ly S (rdW W mem') (in_roP SEGS RLO RHI) [] s (Some x) /\
atail_vis SEGS W mem' (s + Z.of_nat (length x)).
Proof.
intros ly S W mem mem' md c s x HAR Hc HK HSTR HTAIL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
assert (Hcs : A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE).
{ destruct Hc as [(H1 & H2 & _) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia. }
destruct HSTR as (Hs0 & HAT & Hn & HARM).
(* the string's bytes lie outside the slot (they are heap or read-only bytes, the slot is a program static), below
   2^47 *)
assert (Hbytes : forall i, 0 <= i < Z.of_nat (length x) + 1 -> ~ (c <= s + i < c + CALL_SIZE) /\ 0 <= s + i < 2 ^ 47).
{ intros i Hi. destruct HARM as [((b & k0 & Hbk & Hbs & Hse) & _) | (HRO & _)].
  - destruct (al_blocks _ _ LAWS ly S W mem md b k0 HAR Hbk) as (_ & H4096 & Hbc & _ & _ & _ & Hk).
    destruct (req_size_pos k0 ltac:(lia)) as [_ Hreq].
    destruct (spc_blk_off ly S W mem md b k0 (s + i) HAR Hbk ltac:(lia)) as [_ HnPG].
    split; [intros Hin; exact (HnPG (spc_slot_PG c (s + i) Hc Hin)) | lia].
  - destruct (HRO i Hi) as (Hro & _ & _). destruct (cmd_ro_prog_apart (s + i) Hro) as [Himg HnPG].
    pose proof (pa_img_range (s + i) Himg) as Hr.
    split; [intros Hin; exact (HnPG (spc_slot_PG c (s + i) Hc Hin)) | lia]. }
assert (KB : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW W mem' (s + i) = rdW W mem (s + i)).
{ intros i Hi. destruct (Hbytes i Hi) as [H1 H2]. apply HK; [lia | exact H1]. }
assert (HAT' : astr_atR (rdW W mem') s x).
{ destruct HAT as [HB1 HB2]. split; [|exact HB2].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (KB (Z.of_nat i)) by lia. exact (HB1 i ltac:(rewrite length_app; cbn [length]; lia)). }
split.
- split; [exact Hs0|]. split; [exact HAT'|]. split; [exact Hn|]. exact HARM.
- (* the tail word: it holds the terminator, which is outside the slot; the slot is a union of whole words *)
  intros a Ha. pose proof (Z.mod_pos_bound (s + Z.of_nat (length x)) 8 ltac:(lia)) as Hm.
  destruct (Hbytes (Z.of_nat (length x)) ltac:(lia)) as [He He47].
  rewrite HK; [exact (HTAIL a Ha) | lia |].
  intros Hin. apply He.
  pose proof (Z_div_mod_eq_full (s + Z.of_nat (length x)) 8) as Hd.
  assert (Hcm : c = 8 * (c / 8)) by (pose proof (Z_div_mod_eq_full c 8); lia).
  unfold CALL_SIZE in *. lia.
Qed.

End e.
End f.
End d.
