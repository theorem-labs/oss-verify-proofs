(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the segments S18, S19, S21, S22 of the walk of verbs_receive on the
   ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v): what a boundary state keeps across
   a program call whose footprint is the recorder's statics and blocks (the callee's journal, YCbq.v ajournal):
   the real stack above the callee's window, the image off the recorder statics, the walk's own blocks, the
   side-stack frame, and from them vr_frame, vr_saved, vr_spill, vr_env, the quit flag, vr_line and vr_copy. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s18_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the trimmed line fits in strndup's block (q, l+1) *)
Lemma vr_find_upto0 : forall D, match StrFun.find_byte 0 D with Some i => firstn i D | None => D end = Verbs.upto0 D.
Proof.
unfold Verbs.upto0. induction D as [|x D IH]; [reflexivity|]. cbn [StrFun.find_byte Verbs.upto].
destruct (bv_unsigned x =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 D) as [i|]; cbn [firstn]; f_equal; exact IH.
Qed.
Lemma vr_line_le_l : forall D, Z.of_nat (length (Verbs.line D)) <= StrFun.strnlen_res (Z.of_nat (length D)) D.
Proof.
intros D. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
assert (L1 : (length (Verbs.line D) <= length (Verbs.upto0 D))%nat).
{ unfold Verbs.line, Verbs.trim. rewrite length_rev. pose proof (VRR.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H.
  rewrite length_rev in H. exact H. }
pose proof (vr_find_upto0 D) as E.
destruct (StrFun.find_byte 0 D) as [i|]; rewrite <- E in L1; [rewrite length_firstn in L1|]; lia.
Qed.

(* cmd_ro_ok holds the four GOT words of cmd_got_ok (CmdRo.v RO_ptr_a7068 .. RO_ptr_a7080) *)
Lemma vr_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
assert (CV : forall a l v, abytes_atR rd a l -> length l = 8%nat ->
  (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v).
{ intros a l v HA Hl Hk k Hkk. rewrite <- (Hk k Hkk). apply HA. lia. }
split; [|split; [|split]]; (eapply CV; [eassumption | reflexivity |]);
  intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
(* the word array under a reader that agrees on the array and on the copy block (pin_set_words_s2.v's
   atoks_atA_agree) *)
Lemma vr_atoks_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (H8 & Hlen & Hp & Hw) HT HB.
split; [exact H8|]. split; [exact Hlen|]. split.
- intros i p Hi. apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)).
  assert (Hi' : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  replace (tok + 8 * Z.of_nat i + k) with (tok + (8 * Z.of_nat i + k)) by lia. apply HT. lia.
- intros i p w Hi Hw'. destruct (Hw i p w Hi Hw') as (Hs & Hl & Hc1 & Hc2).
  split; [|split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
  apply (astr_atR_agree rd rd' _ _ (cb + ncb - p) Hs); [lia|].
  intros k Hk. replace (p + k) with (cb + (p - cb + k)) by lia. apply HB. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the recorder's footprint of a recorder callee: g_rec, record.spill and the recorder's blocks *)
Definition vr_fp1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Lemma vr_notFP1 : forall O a, (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  (forall p n, In (p, n) O -> ~ (p <= a < p + req_size n)) -> ~ inFP (vr_fp1 O) a.
Proof.
intros O a H1 H2 H3 Hf. unfold vr_fp1 in Hf. apply inFP_cons in Hf as [Hf | Hf]; [lia|].
apply inFP_cons in Hf as [Hf | Hf]; [lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hpn & Hr). exact (H3 p n Hpn Hr).
Qed.
Lemma vr_fp1_closed : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (vr_fp1 O).
Proof.
intros ly S W mem md O HAR HO (r & Hr & H0). unfold vr_fp1 in Hr.
destruct Hr as [<- | [<- | Hr]]; [cbn in H0; unfold A_G_REC in H0; lia | cbn in H0; unfold A_REC_SPILL in H0; lia|].
unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in H0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & _). lia.
Qed.
(* an image byte off the recorder statics is off the footprint *)
Lemma vr_img_spared : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> 0x10000 <= a < 0x606000 ->
  (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  fp_spares (vr_fp1 O) a.
Proof.
intros ly S W mem md O a HAR HO Ha H1 H2. apply fp_spares_closed; [exact (vr_fp1_closed _ _ _ _ _ O HAR HO)|].
apply vr_notFP1; [exact H1 | exact H2|]. intros p n Hpn Hr.
pose proof (blk_off_imgP B ly S W mem md p n HAR (HO _ Hpn)) as Hoff. unfold off_img in Hoff. lia.
Qed.

Section call.
(* the callee's journal from the state at the call (lyc, Sc, W, memc) to the state at its return *)
Variables (lyc : alayout) (Sc : astate) (W W2 : world SEGS) (memc mem2 : word -> option byte) (mdc md2 : Model).
Variables (ly2 : alayout) (S2 : astate) (STK1 s1 EV1 : Z) (O : list (Z * Z)).
Hypothesis HJc : ajournal SEGS B STK1 s1 (vr_fp1 O) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1.
Hypothesis HAR : AR SEGS B lyc Sc W memc mdc.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).
Hypothesis HSTK1 : 0 <= STK1.

(* the real stack above the callee's window *)
Lemma vr_call_stack : forall a, alloc_ceiling <= a < 2 ^ 64 -> s1 <= a -> rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros a Ha Hs. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof asan_consts as (CR & _).
apply F1; [lia | lia|]. apply vr_notFP1; [unfold A_G_REC, REC_SIZE; lia | unfold A_REC_SPILL, SC_SIZE; lia|].
intros p n Hpn Hr. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.
(* an image byte that is neither the runtime's, nor errno, nor a recorder static *)
Lemma vr_call_img : forall a, in_img SEGS a -> 0x10000 <= a < 0x606000 ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  (a < A_G_REC \/ A_G_REC + REC_SIZE <= a) -> (a < A_REC_SPILL \/ A_REC_SPILL + SC_SIZE <= a) ->
  rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros a Hi Ha Ho He H1 H2. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
exact (F3 a Hi Ho He (vr_img_spared _ _ _ _ _ O a HAR HO Ha H1 H2)).
Qed.
(* a byte of a live block that is none of the recorder's and still live *)
Lemma vr_call_block : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) O ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i).
Proof using HJc HAR HO LAWS.
intros p n i H1 H2 Hn Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i H1 H2 Hi).
apply vr_notFP1.
- pose proof (blk_off_imgP B lyc Sc W memc mdc p n HAR H1) as Hoff. unfold off_img, A_G_REC, REC_SIZE in *. lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc p n HAR H1) as Hoff. unfold off_img, A_REC_SPILL, SC_SIZE in *. lia.
- intros b m Hbm Hr. assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (Hn Hbm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W memc mdc b m p n HAR (HO _ Hbm) H1 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a byte of a side-stack frame of the caller, or of its shadow *)
Lemma vr_call_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  rdW W2 mem2 a = rdW W memc a.
Proof using HJc HAR HO LAWS.
intros cid pos a Hin Hr. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin Hr).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof asan_consts as (CR & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(unfold kHighMemEnd; lia)) as Hsa.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply vr_notFP1.
- destruct Hr as [Hr|Hr]; unfold A_G_REC, REC_SIZE, kLowMemEnd in *; lia.
- destruct Hr as [Hr|Hr]; unfold A_REC_SPILL, SC_SIZE, kLowMemEnd in *; lia.
- intros b m Hbm Hb.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR (HO _ Hbm)) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b m cid pos HAR (HO _ Hbm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(unfold kHighMemEnd; lia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb).
  unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *.
  destruct Hr as [Hr|Hr]; lia.
Qed.

(* the parts of a boundary state that live in the real frame, the side-stack frame, the image, the walk's blocks *)
Lemma vr_call_vrframe : forall pos F sh, In (4, pos) (frames Sc) ->
  vr_frame lyc W memc pos F sh -> vr_frame ly2 W2 mem2 pos F sh.
Proof using HJc HAR HO LAWS.
intros pos F sh Hin (HF & Hfl & Hsh).
pose proof HJc as (_ & Hly & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly) as (_ & Efa & _).
assert (EF : ly_F ly2 = ly_F lyc) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (HB1 : fs_frame_bytes 4 = 1024) by reflexivity.
split; [rewrite Efa; exact HF|]. split.
- assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
  rewrite Efl, <- Hfl. apply rdword_ext. intros kk Hkk.
  apply (vr_call_frame 4 pos (F + 1016 + kk) Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HF, HB1. lia.
- intros i Hi. rewrite <- (Hsh i Hi). apply (vr_call_frame 4 pos _ Hin). right. unfold in_zr. cbn [fst snd].
  rewrite <- HF, HB1. change (1024 / 8) with 128. lia.
Qed.
Lemma vr_call_saved : forall e, alloc_ceiling <= s1 -> s1 + 192 <= vr_sp0 e -> vr_sp0 e <= 2 ^ 47 ->
  vr_saved e W memc -> vr_saved e W2 mem2.
Proof using HJc HAR HO LAWS.
intros e Hc Hs Ht H j r Hj k Hk.
assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length vr_saved_regs] in Hj13.
rewrite vr_call_stack by lia. exact (H j r Hj k Hk).
Qed.
Lemma vr_call_spill : forall e l, s1 = vr_s1 e -> alloc_ceiling <= s1 -> s1 + 192 <= 2 ^ 64 ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 192) l -> vr_spill e W memc l -> vr_spill e W2 mem2 l.
Proof using HJc HAR HO LAWS.
intros e l Hs Hc Ht Hl H. unfold vr_spill in *. rewrite Forall_forall in *. intros [o v] Hin. cbn [fst snd].
intros k Hk. pose proof (Hl _ Hin) as Ho. cbn [fst snd] in Ho.
rewrite vr_call_stack by lia. exact (H _ Hin k Hk).
Qed.
Lemma vr_call_quit : vr_prog_unowned B -> forall v,
  aval_mem (rdW W memc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof using HJc HAR HO LAWS.
intros PU v H k Hk.
assert (Hf : inFP cmd_PG (A_G_QUITTING + Z.of_nat k)).
{ unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. lia. }
destruct (PU _ Hf) as (Hi & Ho & He).
rewrite vr_call_img; [exact (H k Hk) | exact Hi | unfold A_G_QUITTING; lia | exact Ho | exact He
| unfold A_G_QUITTING, A_G_REC, REC_SIZE; lia | unfold A_G_QUITTING, A_REC_SPILL, SC_SIZE; lia].
Qed.
Lemma vr_call_env : vr_relro_img -> vr_pg_not_ro -> vr_ro_of_aro B -> vr_rec_cells B ->
  vr_env B W memc -> vr_env B W2 mem2.
Proof using HJc HAR HO LAWS.
intros RRO RPG ROA RECC (HRO & _ & _ & _ & _ & _).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
{ intros a Hro Ho He.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)]).
  rewrite (F3 a Hi Ho He); [exact (HRO a Hro Ho He)|].
  apply fp_spares_closed; [exact (vr_fp1_closed _ _ _ _ _ O HAR HO)|].
  apply vr_notFP1.
  - destruct (Z_lt_le_dec a A_G_REC) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_le_dec a (A_G_REC + REC_SIZE)) as [Hh|Hh]; [|right; exact Hh].
    exfalso. apply (RPG a); [|exact Hro]. unfold cmd_PG. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia.
  - destruct (Z_lt_le_dec a A_REC_SPILL) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_le_dec a (A_REC_SPILL + SC_SIZE)) as [Hh|Hh]; [|right; exact Hh].
    exfalso. apply (RPG a); [|exact Hro]. unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left.
    unfold A_REC_SPILL, SC_SIZE in *. lia.
  - intros p n Hpn Hr. exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HO _ Hpn) Hr Hi). }
pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 HRO2) as HCRO2.
destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (HFL2 & HAG2 & HEV2).
split; [exact HRO2|]. split; [exact (vr_got_of_ro _ HCRO2)|]. split; [exact HCRO2|].
split; [exact HAG2|]. split; [exact HFL2 | exact HEV2].
Qed.
Lemma vr_call_line : forall e q, vr_line B e q W memc -> In (vr_lb e q) (ablocks B lyc Sc) ->
  In (vr_lb e q) (ablocks B ly2 S2) -> ~ In (vr_lb e q) O ->
  Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) -> vr_line B e q W2 mem2.
Proof using HJc HAR HO LAWS.
intros e q [Hf Hs] H1 H2 Hn Hlen. split; [exact Hf|]. unfold vr_lb in *.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hr].
apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hs); [lia|].
intros k Hk. apply (vr_call_block q _ k H1 H2 Hn). lia.
Qed.
Lemma vr_call_copy : forall e pos F c tp, F = frame_addr lyc 4 pos -> In (4, pos) (frames Sc) ->
  vr_copy B e F c tp W memc -> In (vr_cb e c) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B ly2 S2) ->
  ~ In (vr_cb e c) O -> vr_copy B e F c tp W2 mem2.
Proof using HJc HAR HO LAWS.
intros e pos F c tp HF Hin [Hf Ht] H1 H2 Hn. split; [exact Hf|]. unfold vr_cb in *.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hr].
pose proof Ht as (_ & Hlen & _).
pose proof (Verbs.toks_length (e_D e)) as Htl.
apply (vr_atoks_agree _ _ _ _ _ _ _ Ht).
- intros k Hk. apply (vr_call_frame 4 pos _ Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HF.
  change (fs_frame_bytes 4) with 1024. rewrite Hlen in Hk. lia.
- intros k Hk. apply (vr_call_block c _ k H1 H2 Hn). lia.
Qed.

End call.
End e.
End f.
End d.
