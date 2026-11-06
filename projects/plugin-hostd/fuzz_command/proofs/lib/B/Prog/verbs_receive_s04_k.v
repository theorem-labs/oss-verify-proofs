(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of segment S04 (TOK, 0x8d070-0x8d0f0) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_s04.v), ported from the ASan walk's
   lib/A/Prog/verbs_receive_s04_k.v: the reader bridges, the transport of the boundary facts across a memory change,
   and the strdup meter steps over the interface's vri_meter_ok / vri_meter_step. B's GOT words (0xa6bc8 ..
   0xa6be0) and B's allocator-event constants (arg_s, record and xmalloc; arg_i and xstrdup are inlined). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_words strtok_r_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtAlloc04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c
answer_c answer_code_c hand_back_c pins_set_c rec_canonical_c arg_s_c arg_line_c socket_send_c record_c xmalloc_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma le_byte_range : forall v n k, 0 <= le_byte v n k < 256.
Proof. intros v n k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma abytes_aval : forall (rd : reader) a l v, abytes_atR rd a l -> length l = 8%nat ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hv k Hk. rewrite (H k ltac:(lia)). rewrite (Hv k Hk). reflexivity. Qed.
Lemma dropw_le : forall p l, (length (Verbs.dropw p l) <= length l)%nat.
Proof. intros p l. induction l as [|x l IH]; cbn; [lia|]. destruct (p x); cbn; lia. Qed.
Lemma upto0_find : forall D, Z.of_nat (length (Verbs.upto0 D)) <=
match StrFun.find_byte 0 D with Some i => Z.of_nat i | None => Z.of_nat (length D) end.
Proof.
unfold Verbs.upto0. induction D as [|b D IH]; cbn; [lia|].
destruct (bv_unsigned b =? 0); cbn; [lia|]. destruct (StrFun.find_byte 0 D); cbn in *; lia.
Qed.
(* the trimmed line is no longer than what strndup copied *)
Lemma line_le_l : forall D, Z.of_nat (length (Verbs.line D)) <= vr_l (Z.of_nat (length D)) D.
Proof.
intros D. unfold vr_l, StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all. pose proof (upto0_find D) as E.
unfold Verbs.line, Verbs.trim. rewrite length_rev. pose proof (dropw_le Verbs.is_trail (rev (Verbs.upto0 D))) as H.
rewrite length_rev in H. destruct (StrFun.find_byte 0 D); lia.
Qed.
(* the event counts of the route's callees, down to their constants (lib/B/Prog/HarnessArgsEv.v's ev_unfold) *)
Ltac s4_ev_unfold :=
  unfold ev_route, ev_step, ev_call, ev_after,
    EV_CHAIN_WORDS, EV_PIN_SET_WORDS, EV_SUP_ADD, EV_DESCRIPTORS_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET,
    EV_SUP_REMOVE, EV_SUP_REMOVE_ALL, EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR,
    EV_SUP_POLICY_SET, EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR,
    EV_SUP_PIN_ACCEPT, EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT, EV_SUP_REPLY_CODE, EV_PINS_SET,
    EV_PINS_CLEAR, EV_LV2_REFUSALS_FORGET, EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_SUP_AFTER_REPLY, EV_SUP_RESP,
    EV_ANSWER_CODE, EV_ANSWER, EV_HAND_BACK, EV_ARG_S, EV_ARG_LINE, EV_REC_CANONICAL, EV_RECORD, EV_XMALLOC,
    rec_spill_frees.
Ltac s4_rec_unfold :=
  unfold sup_add_m, sup_broadcast_m, pins_set_m, pins_clear_m, rec_stub_code, rec_answer_code, rec_stub,
    rec_answer, hand_back, rec_record, rec_mix.
Ltac s4_ifs := repeat (match goal with |- context [if ?c then _ else _] =>
  lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end end; cbn).

Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma aval_of_val : forall H mem a n v, val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
lazymatch goal with |- bv_unsigned (Z_to_bv 8 ?x) = ?y => change x with (le_byte v n k); change y with (le_byte v n k) end.
pose proof (le_byte_range v n k). rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
apply Z.mod_small. lia.
Qed.
Lemma val_of_aval : forall H mem a n v, aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as Hv. f_equal. rewrite <- (Z_to_bv_bv_unsigned _ b). f_equal. rewrite Hv.
lazymatch goal with |- ?x = ?y => change x with (le_byte v n k); change y with (le_byte v n k) end. reflexivity.
Qed.
Lemma rdword_of_aval : forall H mem a v, aval_mem (aview segs H mem) a 8 v -> 0 <= v < 2 ^ 64 ->
rdword (aview segs H mem) a = Some v.
Proof. intros H mem a v Hv Hr. exact (rdword_of_val_mem segs H mem a v (val_of_aval H mem a 8 v Hv) Hr). Qed.
(* the reader after a symbolic run: unchanged outside the written ranges of the run's regions *)
Lemma aview_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' Hf a Ha Hn. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
End j.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s1_shape : forall e, vr_sp0 e mod 16 = 0 ->
(vr_s1 e = vr_sp0 e - 192 \/ vr_s1 e = vr_sp0 e - 208) /\ vr_s1 e mod 32 = 0.
Proof.
intros e H. unfold vr_s1. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M2. split; [lia|].
rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.
Lemma s1_off : forall e, vr_sp0 e mod 16 = 0 -> (vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e H. destruct (s1_shape e H) as [[E | E] _]; rewrite E;
  [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia];
  (split; [reflexivity | lia]).
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis MTL : ameter_laws MT.

(* the four GOT words of cmd_got_ok are bytes of cmd_ro_ok (CmdRo.v RO_ptr_a6bc8 .. RO_ptr_a6be0) *)
Lemma got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
assert (H1 : abytes_atR rd 0xa6bc8 RO_ptr_a6bc8 /\ abytes_atR rd 0xa6bd0 RO_ptr_a6bd0 /\
  abytes_atR rd 0xa6bd8 RO_ptr_a6bd8 /\ abytes_atR rd 0xa6be0 RO_ptr_a6be0)
by (decompose [and] H; repeat split; assumption).
destruct H1 as (H1 & H2 & H3 & H4). unfold cmd_got_ok.
repeat split; (eapply abytes_aval; [eassumption | reflexivity |
  intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia]).
Qed.
(* vr_env at any AR state whose read-only bytes are the image's: cmd_ro_ok by ROA, the cells by RECC *)
Lemma env_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> vr_env B W mem.
Proof.
intros ly S W mem md HAR HR. destruct (RECC ly S W mem md HAR) as (Hf & Hg & He).
pose proof (ROA ly S W mem md HAR HR) as Hro.
split; [exact HR|]. split; [exact (got_of_ro _ Hro)|]. split; [exact Hro|]. split; [exact Hg|]. split; [exact Hf | exact He].
Qed.
(* the read-only bytes are bytes of the image (RRO), so a memory change that keeps the image keeps them *)
Lemma aro_keep : forall (rd rd' : reader), arodata_okP SEGS RLO RHI B rd ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd'.
Proof.
intros rd rd' HR Hk a Hro Ho He. rewrite (Hk a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)].
Qed.

(* the facts of a boundary state that only read memory the segment does not write: the side-stack frame's flag
   word and shadow, the prologue's saves, the read-only bytes, the recorder, the quit flag and the line *)
Definition s4_st (e : vrE) (pos F q : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
vr_frame lyc Wc memc pos F vr_sh2 /\ vr_saved e Wc memc /\ arodata_okP SEGS RLO RHI B (rdW Wc memc) /\
rec_repA B lyc Sc (rdW Wc memc) (e_R e) (e_O e) /\ aval_mem (rdW Wc memc) A_G_QUITTING 4 (e_q0 e) /\
vr_line B e q Wc memc.
(* the bytes those facts read *)
Definition s4_keepset (e : vrE) (F q a : Z) : Prop :=
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
(F + 1016 <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) \/
(vr_sp0 e - 104 <= a < vr_sp0 e) \/
(q <= a < q + Z.of_nat (length (Verbs.line (e_D e))) + 1) \/
(exists p n, In (p, n) (e_O e) /\ p <= a < p + n).
Lemma s4_st_keep : forall e pos F q lyc Sc (Wc : world SEGS) memc lyc' Sc' (Wc' : world SEGS) memc',
s4_st e pos F q lyc Sc Wc memc ->
frame_addr lyc' 4 pos = frame_addr lyc 4 pos -> flag_addr lyc' 4 pos = flag_addr lyc 4 pos ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc) -> In pn (ablocks B lyc' Sc')) ->
(forall a, s4_keepset e F q a -> rdW Wc' memc' a = rdW Wc memc a) ->
s4_st e pos F q lyc' Sc' Wc' memc'.
Proof.
intros e pos F q lyc Sc Wc memc lyc' Sc' Wc' memc' (HFr & HSv & HR & HRec & HQ & HL) EF EG HO Hk.
destruct HFr as (EF0 & Hfl & Hsh).
split; [|split; [|split; [|split; [|split]]]].
- split; [rewrite EF; exact EF0|]. split.
  + rewrite (rdword_ext (rdW Wc memc) (rdW Wc' memc') (F + 1016)); [rewrite EG; exact Hfl|].
    intros k Hk8. apply Hk. right; left. lia.
  + intros i Hi. rewrite Hk; [exact (Hsh i Hi)|]. right; right; left. lia.
- intros j r Hj. specialize (HSv j r Hj).
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn [length vr_saved_regs] in Hj13.
  apply (aval_mem_agree _ _ _ _ _ HSv). intros k Hk8. apply Hk. right; right; right; left. lia.
- apply (aro_keep _ _ HR). intros a H1 H2 H3. apply Hk. left. auto.
- apply (rec_repA_agree B lyc Sc lyc' Sc' _ _ _ _ HRec HO).
  + intros k Hk0. apply Hk. left. apply PROGU. exists (A_G_REC, A_G_REC + 960).
    split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hk0; lia].
  + intros k Hk0. apply Hk. left. apply PROGU. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hk0; lia].
  + intros [p n] Hpn k Hk0. apply Hk. right; right; right; right; right. exists p, n. cbn [fst snd] in Hk0 |- *.
    split; [exact Hpn | lia].
- apply (aval_mem_agree _ _ _ _ _ HQ). intros k Hk4. apply Hk. left. apply PROGU.
  exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn [fst snd]; lia].
- destruct HL as [Hfresh [HB HN]]. split; [exact Hfresh|]. split; [|exact HN].
  intros i Hi. rewrite Hk; [exact (HB i Hi)|]. right; right; right; right; left. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* a block a call adds was not live before it (the live blocks are pairwise apart) *)
Lemma blk_new : forall ly S (W : world SEGS) mem md l x, AR SEGS B ly S W mem md -> ablocks B ly S = l ++ [x] -> ~ In x l.
Proof.
intros ly S W mem md l [p n] HAR E Hin.
assert (Hin2 : In (p, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin2) as (_ & _ & _ & _ & _ & Hpw & Hn).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & ->).
assert (Heq : map (fun b : Z * Z => (fst b, req_size (snd b))) ((l1 ++ (p, n) :: l2) ++ [(p, n)]) =
  map (fun b : Z * Z => (fst b, req_size (snd b))) l1 ++ (p, req_size n) ::
  map (fun b : Z * Z => (fst b, req_size (snd b))) l2 ++ (p, req_size n) :: []).
{ rewrite <- app_assoc. rewrite map_app. cbn. rewrite map_app. reflexivity. }
pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw Heq) as Hd.
unfold zdisjoint in Hd. cbn in Hd. pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
Lemma bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' H. induction H; unfold bsum in *; cbn in *; lia. Qed.

(* the meter after the strdup call, the interface's vri_meter_step at a = 1 malloc of at most VERBS_RECEIVE_REQ
   bytes, b = 0 frees, ev = 1 event *)
Lemma meter_malloc : forall e Sc S2 k nm n, vr_meter MT e Sc k nm -> mo_le MT Sc S2 (mo_malloc MT n) ->
0 <= n <= VERBS_RECEIVE_REQ -> vr_meter MT e S2 (k + 1) (nm + 1).
Proof.
intros e Sc S2 k nm n HM H2 Hn. pose proof (mo_malloc_mono MT MTL n VERBS_RECEIVE_REQ Hn).
exact (vri_meter_step MT e Sc S2 k nm (mo_malloc MT n) 1 0 1 MTL HM H2 ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* the frame-pointer chain at a call of verbs_receive (class B: s0 = sp0): verbs_receive's own record (ra at sp0 - 8,
   the caller's s0 at sp0 - 16) pushed on the caller's chain by achain_push, or achain's empty case when sp0 lies in
   the top 16 bytes of the stack; the allocation entry's chain_pre from that achain by achain_chain_pre *)
Lemma s4_achain : forall ly0 rd0 sp0 v ch0 lyc (rd : reader) sp ra,
achain ly0 rd0 sp0 v ch0 -> ly_top lyc = ly_top ly0 -> ly_top ly0 <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> sp + 16 <= sp0 ->
exists ch, achain lyc rd sp sp0 ch.
Proof.
intros ly0 rd0 sp0 v ch0 lyc rd sp ra Hc Htop Htop64 Hk H8 H16 Hra Hceil Hal Hsp.
destruct (Z_lt_le_dec sp0 (ly_top ly0 - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch0). apply (achain_ly_top ly0 lyc); [exact Htop|].
  exact (achain_push ly0 rd0 rd sp0 v ra ch0 sp Hc Htop64 Hk H8 H16 Hra Hceil Hal Hlt Hsp).
- exists []. left. split; [right; left; rewrite Htop; lia | reflexivity].
Qed.
Lemma s4_chain : forall ly0 rd0 sp0 v ch0 lyc (rd : reader) (regs : bvmap 5 word) ra,
achain ly0 rd0 sp0 v ch0 -> ly_top lyc = ly_top ly0 -> ly_top ly0 <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
alloc_ceiling <= sp0 -> sp0 mod 8 = 0 ->
alloc_ceiling <= spZ regs -> spZ regs + 16 <= sp0 -> s0Z regs = sp0 -> 4096 <= raZ regs ->
exists ch, chain_pre lyc rd regs ch.
Proof.
intros ly0 rd0 sp0 v ch0 lyc rd regs ra Hc Htop Htop64 Hk H8 H16 Hra Hceil Hal Hc2 Hsp Hs0 Hra2.
destruct (s4_achain ly0 rd0 sp0 v ch0 lyc rd (spZ regs) ra Hc Htop Htop64 Hk H8 H16 Hra Hceil Hal Hsp) as (ch & HA).
exists ch. exact (achain_chain_pre lyc rd (spZ regs) sp0 ch regs HA ltac:(lia) Hs0 Hra2).
Qed.

(* the events of one message: at least the two duplications and their frees *)
Lemma ev_route_nn : forall R ln tk s, 0 <= ev_route R ln tk s.
Proof.
intros R ln tk s. unfold ev_route. destruct tk as [|v args]; [s4_ev_unfold; lia|].
match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
  [s4_ev_unfold; s4_rec_unfold; cbn; s4_ifs; lia|].
match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end.
- unfold EV_PIN_SET_WORDS. destruct (Verbs.pin_set_words_m ln args); s4_ev_unfold; s4_rec_unfold; cbn;
  s4_ifs; lia.
- destruct s as [c0|c|u i p q|u f l v'|u| |ln' tk']; [|destruct c|..];
  s4_ev_unfold; s4_rec_unfold; cbn; s4_ifs; lia.
Qed.
Lemma ev_vr_ge : forall R D, 4 <= ev_vr R D.
Proof.
intros R D. unfold ev_vr. destruct (Verbs.receive atoi_a D) as [st af].
pose proof (ev_route_nn R (Verbs.line D) (Verbs.toks D) st) as Hr.
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q].
assert (Ha : 0 <= ev_after (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) af).
{ destruct af as [p|]; s4_ev_unfold; [|lia]. s4_ifs; lia. }
assert (Hrp : EV_REPLY = 3) by reflexivity. lia.
Qed.
(* the meter premise of the strdup call, the interface's vri_meter_ok at a = 1, b = 0, ev = 1; the route's events
   (at least 4, ev_vr_ge) cover it while k <= 2 *)
Lemma meter_ok_dup : forall e Sc k nm n, vr_ent B MT e -> vr_meter MT e Sc k nm -> k <= 2 ->
0 <= n <= VERBS_RECEIVE_REQ -> mo_ok MT Sc (mo_malloc MT n).
Proof.
intros e Sc k nm n Hent HM Hk Hn. pose proof (mo_malloc_mono MT MTL n VERBS_RECEIVE_REQ Hn).
pose proof (ev_vr_ge (e_R e) (e_D e)).
exact (vri_meter_ok B MT e Sc k nm (mo_malloc MT n) 1 0 1 MTL Hent HM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* where the bytes the boundary facts read lie: below the allocation ceiling, or in the prologue's saves; never in
   the side-stack frame's words below its flag pointer (tok[], save) nor in the copy block *)
Lemma keep_disj : forall e pos F q c ly S (W : world SEGS) m md a,
AR SEGS B ly S W m md -> In (4, pos) (frames S) -> F = frame_addr ly 4 pos ->
In (vr_lb e q) (ablocks B ly S) -> In (vr_cb e c) (ablocks B ly S) -> vr_cb e c <> vr_lb e q -> ~ In (vr_cb e c) (e_O e) ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) ->
alloc_ceiling + 208 <= vr_sp0 e ->
s4_keepset e F q a ->
(0 <= a < alloc_ceiling \/ vr_sp0 e - 104 <= a < vr_sp0 e) /\
~ (F <= a < F + 1016) /\
~ (c <= a < c + req_size (Z.of_nat (length (Verbs.line (e_D e))) + 1)).
Proof.
intros e pos F q c ly S W m md a HAR Hfr EF Hlb Hcb Hne HcO HO Hll Hsp Hk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W m md 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
change (fs_frame_bytes 4) with 1024 in Hfc, Hfapp. rewrite <- EF in Hf0, Hfc, Hfapp.
destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hcb) as (_ & Hc4096 & Hcc & Hcapp & _ & _ & Hcn).
cbn [fst snd] in Hc4096, Hcc, Hcapp.
pose proof (sep_block_frame SEGS B LAWS ly S W m md _ _ 4 pos HAR Hcb Hfr) as Hcf.
unfold zdisjoint in Hcf. cbn [fst snd] in Hcf. change (fs_frame_bytes 4) with 1024 in Hcf. rewrite <- EF in Hcf.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrq1 Hrq2].
destruct Hk as [(Hi & Ho & He) | [Hfl | [Hsh | [Hsv | [Hl | (p & n & Hpn & Hp)]]]]].
- pose proof (pa_img_range a Hi) as Ha. split; [left; lia|]. split.
  + intros Hr. apply (frm_img SEGS B LAWS ly S W m md 4 pos a HAR Hfr); [change (fs_frame_bytes 4) with 1024; lia | exact Hi].
  + intros Hr. apply (blk_img SEGS B LAWS ly S W m md _ _ a HAR Hcb); [cbn [fst snd]; exact Hr | exact Hi].
- split; [left; lia|]. split; [lia|]. lia.
- unfold shadow_addr, SHADOW_OFF in Hsh. assert (Hd : F / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (Hd0 : 0 <= F / 8) by (apply Z.div_pos; lia). pose proof (Z.mul_div_le alloc_ceiling 8 ltac:(lia)).
  split; [left; lia|]. split.
  + intros Hr. exact (fshadow_not_app F 128 F 1024 a ltac:(lia) ltac:(lia) Hfapp ltac:(lia) ltac:(lia)).
  + intros Hr. exact (fshadow_not_app F 128 c _ a ltac:(lia) ltac:(lia) Hcapp ltac:(lia) Hr).
- split; [right; lia|]. split; lia.
- destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hlb) as (_ & Hq4096 & Hqc & _ & _ & _ & Hqn).
  cbn [fst snd vr_lb] in Hq4096, Hqc, Hqn.
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hrl].
  split; [left; lia|]. split.
  + pose proof (sep_block_frame SEGS B LAWS ly S W m md _ _ 4 pos HAR Hlb Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd vr_lb] in Hd. change (fs_frame_bytes 4) with 1024 in Hd. rewrite <- EF in Hd. lia.
  + pose proof (sep_blocks SEGS B LAWS ly S W m md _ _ _ _ HAR Hlb Hcb (fun E => Hne (eq_sym E))) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd vr_lb vr_cb] in Hd. lia.
- pose proof (HO _ Hpn) as Hpb.
  destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hpb) as (_ & Hp4096 & Hpc & _ & _ & _ & Hpn').
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrn].
  split; [left; lia|]. split.
  + pose proof (sep_block_frame SEGS B LAWS ly S W m md _ _ 4 pos HAR Hpb Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 4) with 1024 in Hd. rewrite <- EF in Hd. lia.
  + assert (Hne' : vr_cb e c <> (p, n)) by (intros E; rewrite E in HcO; exact (HcO Hpn)).
    pose proof (sep_blocks SEGS B LAWS ly S W m md _ _ _ _ HAR Hcb Hpb Hne') as Hd.
    unfold zdisjoint in Hd. cbn [fst snd vr_cb] in Hd. lia.
Qed.

(* a call that keeps memory as cgif's acall_kept says (strdup), with the copy block as its new block: the bytes
   the boundary facts read are kept *)
Lemma keep_call : forall e pos F q c lyc Sc (W : world SEGS) memT ly2 S2 (W2 : world SEGS) mem2 md2 slo shi,
acall_kept SEGS B lyc Sc W memT W2 mem2 slo shi
  (fun a => c <= a < c + req_size (Z.of_nat (length (Verbs.line (e_D e))) + 1)) ->
AR SEGS B ly2 S2 W2 mem2 md2 -> (forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)) ->
In (4, pos) (frames Sc) -> frames S2 = frames Sc -> F = frame_addr lyc 4 pos -> frame_addr ly2 4 pos = F ->
In (vr_lb e q) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B ly2 S2) -> vr_cb e c <> vr_lb e q ->
~ In (vr_cb e c) (e_O e) -> (forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)) ->
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) ->
alloc_ceiling + 208 <= vr_sp0 e -> vr_sp0 e <= 2 ^ 47 -> shi <= vr_sp0 e - 104 ->
forall a, s4_keepset e F q a -> rdW W2 mem2 a = rdW W memT a.
Proof.
intros e pos F q c lyc Sc W memT ly2 S2 W2 mem2 md2 slo shi (K1 & K2 & K3 & K4 & _) HAR2 Hinc Hfr Hfrs EF EF2
  Hlb Hcb Hne HcO HO Hll Hsp Hsp47 Hshi a Ha.
assert (Hfr2 : In (4, pos) (frames S2)) by (rewrite Hfrs; exact Hfr).
destruct (keep_disj e pos F q c ly2 S2 W2 mem2 md2 a HAR2 Hfr2 (eq_sym EF2) (Hinc _ Hlb) Hcb Hne HcO
  (fun pn H => Hinc _ (HO pn H)) Hll Hsp Ha) as (Hlow & Hnf & Hnc).
pose proof asan_consts as (C1 & _).
destruct Ha as [(Hi & Ho & He) | [Hfl | [Hsh | [Hsv | [Hl | (p & n & Hpn & Hp)]]]]].
- exact (K3 a Hi Ho He).
- apply (K4 4 pos a Hfr); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 4) with 1024; rewrite <- EF; lia | exact Hnc].
- apply (K4 4 pos a Hfr); [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 4 / 8) with 128; rewrite <- EF; lia
  | exact Hnc].
- apply K1; lia.
- pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 (Hinc _ Hlb))
    as (_ & _ & _ & _ & _ & _ & Hn'); cbn [snd vr_lb] in Hn'; lia)) as [_ Hrl].
  replace a with (q + (a - q)) by lia. apply (K2 q _ (a - q) Hlb); [lia|]. replace (q + (a - q)) with a by lia. exact Hnc.
- pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 (Hinc _ (HO _ Hpn))) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrn].
  replace a with (p + (a - p)) by lia. apply (K2 p n (a - p) (HO _ Hpn)); [lia|]. replace (p + (a - p)) with a by lia. exact Hnc.
Qed.

End e.
End f.
End d.
