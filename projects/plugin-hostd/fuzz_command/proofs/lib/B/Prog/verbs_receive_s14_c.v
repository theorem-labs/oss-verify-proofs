(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a recorder callee called from a route state of the walk of verbs_receive on
   the ASan+UBSan build of plugin-hostd/fuzz_command (arms S14-S16 of lib/B/Prog/verbs_receive_iface.v): the frame
   chain at the call (achain_push), the string arguments taken from tok[], the event, live-byte and meter budgets,
   the call rule PaFx.v cl_callS_wideF (the callee's post is FP-existential) with the join 0x8d4cc after it, and the
   jump into the join. The B twin of the A walk's verbs_receive_s14_c.v (join 0x8dc94, entry 0x8d480): B's entry is
   0x8ce4c, its join 0x8d4cc, and B's sup_after_reply events are record()'s and arg_s's (EV_SUP_AFTER_REPLY). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import reply_c sup_after_reply_c socket_send_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c sup_resp_c
sup_quarantine_clear_c sup_policy_set_c sup_lv2_worker_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_c verbs_receive_iface verbs_receive_kit PaFx verbs_receive_s14_k verbs_receive_s14_j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation NoDup := List.NoDup.

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
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis HB : YF0m.CmdBSyms B.

Lemma inFP_vr_fp_lo : forall e a, vr_ent B MT e -> inFP (vr_fp e) a -> a < alloc_ceiling.
Proof.
intros e a He Hf. pose proof He as (HPRE & _). pose proof HPRE as (HAR & _). pose proof asan_consts as (C1 & _).
apply inFP_app_or in Hf as [Hf | Hf].
- unfold VERBS_RECEIVE_PG in Hf. apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE in Hf; lia|].
  apply inFP_cons in Hf as [Hf | Hf]; [unfold A_REC_SPILL, SC_SIZE in Hf; lia|].
  apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_QUITTING in Hf; lia | exact (False_ind _ (inFP_nil a Hf))].
- destruct (inFP_ablocks_fp_inv (e_O e) a Hf) as (p & n & Hpn & Hr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (vr_ent_O_blocks B MT e _ He Hpn)) as (_ & _ & Hc & _). lia.
Qed.

(* the offset of s1 from the entry sp: 192 or 208 *)
Lemma vr_o_facts : forall e, vr_sp0 e mod 16 = 0 ->
(vr_s1 e - vr_sp0 e) mod 16 = 0 /\ -208 <= vr_s1 e - vr_sp0 e <= -192.
Proof.
intros e H.
assert (Hx : (vr_sp0 e - 192) mod 16 = 0) by (rewrite Zminus_mod, H; reflexivity).
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (vr_sp0 e - 192) 16 ltac:(lia)) as D2. rewrite Hx in D2.
assert (Hr : (vr_sp0 e - 192) mod 32 = 0 \/ (vr_sp0 e - 192) mod 32 = 16) by lia.
assert (Heq : vr_s1 e - vr_sp0 e = -192 - (vr_sp0 e - 192) mod 32) by (unfold vr_s1; lia).
rewrite Heq. destruct Hr as [Hr | Hr]; rewrite Hr; split; first [reflexivity | lia].
Qed.

(* the frame chain at a program call (verbs_receive is class B: s0 = sp0 at every call, a Theorem Labs lane's S0-SITES.md):
   achain_push on afn_pre's chain (vr_ent's 1st conjunct) with the ra and entry-s0 words the prologue stored at sp0 - 8
   and sp0 - 16 (vr_saved j = 0, 1), the words from sp0 up kept by the journal; achain's empty case when
   sp0 >= ly_top - 16 (PASS4-REFIT.md section B) *)
Lemma vr_achain : forall e lyc Sc (W : world SEGS) memc mdc k pos,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W memc mdc k ->
vr_saved e W memc ->
exists ch1, achain lyc (rdW W memc) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e lyc Sc W memc mdc k pos He HJ Hsav.
pose proof He as (HPRE & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk0 & Hwin & Hch & HQT).
pose proof Hstk0 as (Hal16 & HS0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
fold (vr_sp0 e) in *.
destruct (vr_o_facts e Hal16) as [_ Ho].
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W memc) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e) (vr_s1 e)).
  + exact Hch.
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (inFP_vr_fp_lo e a He Hf). lia.
  + apply rdword_of_aval; [|unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
    pose proof (Hsav 0%nat 1 eq_refl) as H. replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact H.
  + apply rdword_of_aval; [|unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
    pose proof (Hsav 1%nat 8 eq_refl) as H. replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia. exact H.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as Dm. rewrite Hal16 in Dm.
    pose proof (Z.div_mod (vr_sp0 e) 8 ltac:(lia)) as Dm8. pose proof (Z.mod_pos_bound (vr_sp0 e) 8 ltac:(lia)).
    assert (Hq : vr_sp0 e / 8 = 2 * (vr_sp0 e / 16)) by lia. lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* a word of tok[] is a string argument a recorder callee may take: in the copy block, apart from the recorder's *)
Lemma tok_argB : forall e F c tp lyc Sc (W : world SEGS) mem md q i p w,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
(in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\ astr_atR (rdW W mem) p w /\
 Z.of_nat (length w) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) (e_O e)) /\
aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling /\
Z.of_nat (length w) <= 8192.
Proof.
intros e F c tp lyc Sc W mem md q i p w HAR Hperm [(Hc4 & _) (Hal & Hlen & Hw & Hs)] Hp Hpw.
destruct (Hs i p w Hp Hpw) as (A1 & A2 & A3 & A4). unfold vr_cb in Hc4. cbn [fst] in Hc4.
pose proof (ablocks_nodup B _ _ _ _ _ HAR) as HND.
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
assert (Hcb' : In (c, Z.of_nat (length (Verbs.line (e_D e))) + 1) (ablocks B lyc Sc)) by exact Hcb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb') as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
split; [|split; [exact (Hw i p Hp) | split; [lia | split; [lia | exact A2]]]].
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcb' | lia]|].
split; [exact A1|]. split; [unfold LMAX; lia|].
apply Forall_forall. intros [b m] Hbm. cbn [fst snd].
assert (HbS : In (b, m) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hbm).
assert (Hne : (b, m) <> (c, Z.of_nat (length (Verbs.line (e_D e))) + 1)).
{ intros E. apply (NoDup_perm_disj _ _ _ _ HND Hperm Hbm). rewrite E. right. left. reflexivity. }
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b m c _ HAR HbS Hcb' Hne) as Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR HbS) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
Qed.

Lemma ev_after_nonneg : forall R af, 0 <= ev_after R af.
Proof.
intros R [[i v]|]; cbn [ev_after]; [|lia]. unfold EV_SUP_AFTER_REPLY, EV_RECORD, rec_spill_frees, EV_ARG_S, EV_XMALLOC.
destruct (Nat.ltb _ _); lia.
Qed.

(* the budgets a recorder callee asks, from the entry's and the route state's: the meter through the interface's
   vri_meter_ok (a mallocs and b frees, each at most the callee's EV1 events, which the route's events cover) *)
Lemma vr_budget : forall e pos F q c lyc Sc (W : world SEGS) regsc memc mdc k nm r EV1 XM1 LIVE1 m f,
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) r (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
0 <= m <= EV1 -> 0 <= f <= EV1 ->
XM1 <= m * mo_malloc MT VERBS_RECEIVE_REQ + f * mo_free MT ->
LIVE1 <= 29 * VERBS_RECEIVE_REQ ->
st_nev Sc + EV1 <= EV_MAX /\ blocks_bytes Sc + LIVE1 <= LIVE_MAX /\ mo_ok MT Sc XM1 /\ Z.of_nat (length (frames Sc)) <= 8.
Proof.
intros e pos F q c lyc Sc W regsc memc mdc k nm r EV1 XM1 LIVE1 m f He Hcore Hk1 Hm Hf HXM HL.
destruct Hcore as (HJ & Hk & Hmet & Hnm & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
pose proof He as (_ & _ & _ & _ & _ & _ & _ & Hn & HnD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _ & _ & _ & _ & _ & _ & _ & _ & Hfr4 & Hev & Hlive & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof (ev_vr_eq (e_R e) (e_D e)) as Eev. unfold vr_k3, vr_k2 in Eev. rewrite Hk1 in Eev.
pose proof (ev_after_nonneg (vr_R2 (e_R e) (e_D e)) (vr_aft (e_D e))) as Haft.
assert (HREP : EV_REPLY = 3) by reflexivity.
split; [lia|]. split.
- rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ Hperm).
  rewrite (blocks_bytes_bsum B (e_ly e) (e_S e)), (bsum_perm _ _ Hperm0) in Hlive.
  rewrite !bsum_app in *. cbn [bsum fold_right vr_lb vr_cb fst snd] in *.
  unfold vr_l. rewrite <- HnD, SlotWords.sw_strnlen_upto0.
  pose proof (SlotWords.sw_line_le (e_D e)) as L1.
  pose proof (verbs_receive_route.upto_len (fun b => bv_unsigned b =? 0) (e_D e)) as L2. fold (Verbs.upto0 (e_D e)) in L2.
  unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
- split; [|rewrite Hfrs; cbn [length app]; lia].
  eapply vri_meter_ok; [exact MTL | exact He | exact Hmet | exact HXM | exact Hm | exact Hf | lia].
Qed.

(* the post of a recorder callee (sup_quarantine_clear_c.v:100-119 and its siblings), over its model step Rt, its
   live-bytes bound LIVE1 and its meter XM1 *)
Definition rec_post (ly : alayout) (S : astate) (O : list (Z * Z)) (Rt : rstate * list byte) (LIVE1 XM1 : Z)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 Rt = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE1 /\
 mo_le MT S S' XM1.

Lemma w64_unsigned_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
Lemma vr_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma vr_rv_get_bv : forall (regs : bvmap 5 word) l (r : bv 5) v, vr_rv regs l -> In (bv_unsigned r, v) l -> getr regs r = w64 v.
Proof.
intros regs l r v H Hin.
replace (getr regs r) with (getr regs (Z_to_bv 5 (bv_unsigned r))) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
exact (vr_rv_get regs l (bv_unsigned r) v H Hin).
Qed.

(* the call of a recorder callee from a walk state with the route's blocks and recorder, and the join 0x8d4cc after
   it: the callee's contract CALL is handed
   every premise a recorder contract shares (the frame, rounding mode 0, the read-only environment, the recorder, the
   room for frames, events, live bytes and meter); the caller adds the argument registers. The callee's post is
   FP-existential (statement pass 4, apost_baseF; PaFx.v cl_callS_wideF): the join holds at the FP state fq the
   callee returns at, which fxrel relates to this one. The frame chain at the call is vr_achain's (achain_push) *)
Lemma vr_call_join : forall e (W : world SEGS) pos F q c tp lyc Sc regsc memc mdc k nm r
  memc' mdc' regsc' STK1 EV1 XM1 LIVE1 Rt m f ret pcal,
vr_ent B MT e -> (2 <= length (Verbs.toks (e_D e)))%nat ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) r (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
rd_same (rdW W memc) (rdW W memc') ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W memc' mdc' k ->
vr_rv regsc' (vr_base B e ++ [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]) ->
getr regsc' 1 = Z_to_bv 64 (vr_pc ret) ->
0 <= AF_verbs_receive + (ret - 0x8ce4c) < 2 ^ 40 -> (AF_verbs_receive + (ret - 0x8ce4c)) mod 2 = 0 ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= m <= EV1 -> 0 <= f <= EV1 -> m <= 25 -> XM1 <= m * mo_malloc MT VERBS_RECEIVE_REQ + f * mo_free MT ->
LIVE1 <= 29 * VERBS_RECEIVE_REQ ->
vr_h (e_R e) (e_D e) = (fst Rt, snd Rt, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
(forall ch1, afn_pre SEGS B STK1 lyc Sc W regsc' memc' mdc' ch1 ->
  frm0 fx ->
  arodata_okP SEGS RLO RHI B (rdW W memc') -> cmd_ro_ok (rdW W memc') ->
  rec_repA B lyc Sc (rdW W memc') (e_R e) (e_O e) ->
  Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (mkCfg (mkst regsc' pcal memc' (seg_rom SEGS)) mdc')
  (apost_baseF SEGS B STK1 (vr_cfp (e_O e)) regsc' lyc Sc W memc' mdc' EV1 (rec_post lyc Sc (e_O e) Rt LIVE1 XM1))) ->
SRr SEGS W (mkCfg (mkst regsc' pcal memc' (seg_rom SEGS)) mdc')
  (fun W2 c2 => exists fq : YK11.FPState, fxrel fx fq /\ vr_hdx (fx := fq) B MT e ret W2 c2).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm r memc' mdc' regsc' STK1 EV1 XM1 LIVE1 Rt m f ret pcal
He Hlen Hcore Hline Hcopy Hs HJ' Hrvc Hra Hret Hret2 HS1 HS1b Hm Hf Hm25 HXM HLV Hh Hk1 Hcallee.
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & Hsav & _ & Henv & Hrec & _ & Hperm & _).
pose proof He as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HS0 & Hceil0 & Hslo0 & Hshi0 & H470 & _). fold (vr_sp0 e) in *.
pose proof asan_consts as (C1 & _).
destruct (vr_o_facts e Hal16) as [Ho16 Ho].
pose proof (proj1 HJ') as HARc.
assert (HOc : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
destruct (vr_achain e lyc Sc W memc' mdc' k pos He HJ' (vr_saved_same _ _ _ _ Hs Hsav)) as (ch1 & Hch).
assert (Hsp : spZ regsc' = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ unfold spZ. rewrite (vr_rv_get_bv _ _ 2 (vr_s1 e) Hrvc ltac:(cbn; tauto)). rewrite w64_unsigned_small by lia. lia. }
assert (Hs0 : s0Z regsc' = vr_sp0 e).
{ unfold s0Z. rewrite (vr_rv_get_bv _ _ 8 (vr_sp0 e) Hrvc ltac:(cbn; tauto)). apply w64_unsigned_small. lia. }
destruct (vr_budget e pos F q c lyc Sc W regsc memc mdc k nm r EV1 XM1 LIVE1 m f He Hcore Hk1 Hm Hf HXM HLV)
  as (Hev1 & Hlv1 & Hmo1 & Hfr1).
pose proof (vr_env_of_journal B MT RRO RPG RECC ROA e _ _ _ _ _ _ _ He HJ') as (Haro' & _ & Hcro' & _).
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W regsc' memc' pcal VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc mdc' k STK1 (vr_cfp (e_O e)) EV1 (vr_s1 e - vr_sp0 e) (getr regsc' 1) ch1
    (rec_post lyc Sc (e_O e) Rt LIVE1 XM1) HJ' Hsp Ho16 ltac:(lia) HS1 ltac:(lia)).
  - exact (vr_rv_get_bv _ _ 3 (as_gp B) Hrvc ltac:(cbn; tauto)).
  - exact (vr_rv_get_bv _ _ 4 (as_tp B) Hrvc ltac:(cbn; tauto)).
  - reflexivity.
  - rewrite Hra. unfold vr_pc. apply ret_ok_codeptr_v; [exact Hret | exact Hret2].
  - rewrite Hra. unfold vr_pc. rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0. replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch.
  - intros Hpre. exact (Hcallee ch1 Hpre (v14_ent_frm0 B MT e He) Haro' Hcro' (rec_repA_same B _ _ _ _ _ _ Hs Hrec)
      Hfr1 Hev1 Hlv1 Hmo1).
  - intros a Ha. destruct (cfp_cases B PROGU (e_O e) a Ha) as [Himg | (p & n & Hpn & Hr)].
    + do 4 right. left.
      unfold vr_cfp in Ha. apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]].
      * split; [unfold vr_fp, VERBS_RECEIVE_PG; exists (A_G_REC, A_G_REC + REC_SIZE); split; [apply in_or_app; left; left; reflexivity | exact Ha]|].
        split; [|exact Himg]. rewrite (YF0m.ts_prog B HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
        unfold A_G_REC, REC_SIZE in Ha. lia.
      * split; [unfold vr_fp, VERBS_RECEIVE_PG; exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [apply in_or_app; left; right; left; reflexivity | exact Ha]|].
        split; [|exact Himg]. rewrite (YF0m.ts_prog B HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
        unfold A_REC_SPILL, SC_SIZE in Ha. lia.
      * destruct (inFP_ablocks_fp_inv (e_O e) a Ha) as (p & n & Hpn & Hr).
        exfalso. exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HARc (HOc _ Hpn) Hr Himg).
    + right. left. split.
      * unfold vr_fp. exists (p, p + req_size n). split; [apply in_or_app; right; unfold ablocks_fp; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hpn]|].
        cbn [fst snd]. lia.
      * exists p, n. split; [exact (HOc _ Hpn) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    apply (not_cfp_hi B PROGU (e_O e) lyc Sc W memc' mdc' a HARc HOc ltac:(lia) Ha). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
exists fx'. split; [exact Hfx|].
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
destruct HK as (R' & t & tq & O' & HRt & H10 & Htq & HREC' & HO'1 & Hq1 & Hq2 & Hq3 & Hqs & HO'2 & HO'3 & _ & HMLE).
rewrite Hra. rewrite HRt in Hh. cbn [fst snd] in Hh.
(* the join at the callee's return FP state fx' (vr_hdx_of_call is generic in the FP state) *)
exact (vr_hdx_of_call (fx := fx') B MT RRO RPG RECC ROA MTL PROGU e W pos F q c tp lyc Sc regsc memc mdc k nm r memc' mdc'
  regsc' STK1 EV1 XM1 m f ly2 S2 W2 regs2 mem2 md2 R' t tq O' ret (v14_ent_fxr B MT fx fx' e He Hfx) Hlen Hcore Hline Hcopy
  Hs HARc Hrvc HJ2 HJc HP H10 (proj1 Htq) HREC' HO'1 Hq1 Hq2 Hq3 Hqs
  (fun pn H1 H2 => proj1 (HO'2 pn H1 H2)) HO'3 HMLE Hm Hf Hm25 HXM Hh Hk1).
Qed.

(* the registers and the memory a run that writes nothing leaves *)
Lemma regs_all_kept : forall E ss ss' (W : world SEGS) ms1 ms2,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms1) -> st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms2) ->
ss_regs ss = ss_regs ss' -> forall r, getr (ms_regs ms2) r = getr (ms_regs ms1) r.
Proof.
intros E ss ss' W ms1 ms2 H1 H2 Hr r.
rewrite (st_ok_pi_restrict_reg (w_H W) E ss' ms2 r H2), (st_ok_pi_restrict_reg (w_H W) E ss ms1 r H1), Hr. reflexivity.
Qed.
Lemma vr_rv_all_kept : forall (regs regs' : bvmap 5 word) l, (forall r, getr regs' r = getr regs r) -> vr_rv regs l -> vr_rv regs' l.
Proof. intros regs regs' l H Hv. unfold vr_rv in *. eapply Forall_impl; [|exact Hv]. intros rv Hrv. rewrite H. exact Hrv. Qed.

(* the jump into the join 0x8d4cc (offset 28572 from the listing's base) *)
Lemma vr_jump : forall (e : vrE) (ret : Z) ss' st (W : world SEGS) cf,
vr_ent B MT e ->
sym_run_toN_pi pl_tpi FUEL 28572 (mkSS (AF_verbs_receive + (ret - 0x8ce4c)) sr_atoms [] None (mkFacts [] [] [])) = (ss', st) ->
pi_plain_stop st -> ss' = mkSS 28572 sr_atoms [] None (mkFacts [] [] []) ->
vr_hdx B MT e ret W cf -> SRr SEGS W cf (vr_hd B MT e 0x8d4cc).
Proof.
intros e ret ss' st W cf Hent Hrun Hst Hss' Hhdx. subst ss'.
destruct Hhdx as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & Htq & Hqs & Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsav & Hspl & Henv & Hrec & HdO & Hperm & Hquit).
set (E := Eimg (Ereg regsc [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_verbs_receive + (ret - 0x8ce4c)) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + (ret - 0x8ce4c)))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at, vr_pc. change (w64 (BASE + (AF_verbs_receive + (ret - 0x8ce4c)))) with (Z_to_bv 64 (BASE + (AF_verbs_receive + (ret - 0x8ce4c)))).
eapply (SRr_run_to_pi_AJ B LAWS W FUEL 28572 E _ _ st _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
  (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdc k _ HEI HS Hrun Hst HJ).
{ cbn [ms_mem mkst]. apply awr_ok_nil. }
intros ms' mat' HS2 HJ2 HF HFr HG. cbn [ms_mem mkst] in HF, HFr, HG, HJ2.
assert (Hreg : forall r, getr (ms_regs ms') r = getr regsc r)
  by (apply (regs_all_kept E _ _ W (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + (ret - 0x8ce4c)))) memc (seg_rom SEGS)) ms' HS HS2); reflexivity).
assert (Hsame : rd_same (rdW W memc) (rdW W (ms_mem ms'))).
{ apply (rd_same_of_frame E [] W memc (ms_mem ms')); [apply Forall_nil | exact HFr]. }
pose proof (st_ok_pi_restrict_mkst (w_H W) E _ ms' HS2 eq_refl) as Hshape. cbn [ss_pc] in Hshape.
apply SRr_ret. rewrite Hshape.
change (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 (BASE + 28572)) (ms_mem ms') (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdc) mat' mdc))
  with (cfg_at SEGS (vr_pc 0x8d4cc) (ms_regs ms') (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc)).
exists tq, O1, pos, F, q, c, tp, lyc, Sc, (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy mdc) mat' mdc), k, nm.
split; [reflexivity|]. split; [exact Hnt|]. split; [exact Htq|].
split; [exact (astr_atR_same _ _ _ _ Hsame Hqs)|].
split; [|split; [exact (vr_line_same B _ _ _ _ _ Hsame Hline) | exact (vr_copy_same B _ _ _ _ _ _ _ Hsame Hcopy)]].
split; [exact HJ2|]. split; [exact Hk|]. split; [exact Hmet|]. split; [exact Hnm|].
split; [exact (vr_frame_same _ _ _ _ _ _ _ Hsame Hfr)|].
split; [exact (vr_rv_all_kept regsc _ _ Hreg Hrv)|].
split; [exact (vr_saved_same _ _ _ _ Hsame Hsav)|]. split; [exact (vr_spill_same _ _ _ _ _ Hsame Hspl)|].
split; [exact (vr_env_of_journal B MT RRO RPG RECC ROA e _ _ _ _ _ _ _ Hent HJ2)|].
split; [exact (rec_repA_same B _ _ _ _ _ _ Hsame Hrec)|]. split; [exact HdO|]. split; [exact Hperm|].
exact (aval_mem_same _ _ _ _ _ Hsame Hquit).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   What the model does on the three routes *)
Lemma vr_st_plan : forall D, Verbs.toks D <> [] ->
vr_st D = VRR.plan_at (VRR.route (Verbs.toks D)) atoi_a (Verbs.line D) (Verbs.toks D).
Proof.
intros D H. unfold vr_st, Verbs.receive. destruct (Verbs.toks D) as [|v args] eqn:E; [congruence|].
cbn [fst]. apply VRR.plan_route. discriminate.
Qed.
Lemma vr_k1_val : forall R D v args, Verbs.toks D = v :: args ->
Verbs.list_eqb v Verbs.Lit.verb_chain = false -> Verbs.list_eqb v Verbs.Lit.verb_pin_set = false ->
vr_k1 R D = 2 + ev_step R (vr_st D).
Proof. intros R D v args Htk H1 H2. unfold vr_k1, ev_route. rewrite Htk, H1, H2. reflexivity. Qed.
Lemma route_v_eq : forall v args,
(VRR.route (v :: args) = VRR.RQclear -> v = Verbs.Lit.verb_quarantine_clear) /\
(VRR.route (v :: args) = VRR.RPolicy -> v = Verbs.Lit.verb_policy_set) /\
(VRR.route (v :: args) = VRR.RLv2 -> v = Verbs.Lit.verb_lv2_worker_set).
Proof.
intros v args. unfold VRR.route, VRR.route_mid, VRR.route_tail, VRR.route_conn, VRR.route_cd.
repeat (match goal with
| |- context [if ?b then _ else _] => destruct b eqn:?
| |- context [match ?x with _ => _ end] => destruct x eqn:?
end);
repeat split; intros HH; try discriminate; apply Verbs.list_eqb_eq; assumption.
Qed.
Ltac vr_notverb Hv := rewrite Hv; vm_compute; reflexivity.
Lemma qclear_facts : forall R D v args, Verbs.toks D = v :: args -> VRR.route (Verbs.toks D) = VRR.RQclear ->
(forall a, args = [a] ->
   vr_h R D = (fst (sup_quarantine_clear_m R (Some a)), snd (sup_quarantine_clear_m R (Some a)), false) /\
   vr_k1 R D = 2 + EV_SUP_QUARANTINE_CLEAR R) /\
(length args <> 1%nat -> vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP).
Proof.
intros R D v args Htk Hr.
assert (Hv : v = Verbs.Lit.verb_quarantine_clear) by (apply (proj1 (route_v_eq v args)); rewrite <- Htk; exact Hr).
assert (Hp : vr_st D = VRR.plan_at VRR.RQclear atoi_a (Verbs.line D) (v :: args))
  by (rewrite (vr_st_plan D ltac:(rewrite Htk; discriminate)), Hr, Htk; reflexivity).
assert (Hk : vr_k1 R D = 2 + ev_step R (vr_st D))
  by (apply (vr_k1_val R D v args Htk); vr_notverb Hv).
split.
- intros a ->. cbn [VRR.plan_at] in Hp. split.
  + unfold vr_h. rewrite Hp. cbn [VerbsRun.run_step VerbsRun.run_call].
    destruct (sup_quarantine_clear_m R (Some a)) as [R' t]. reflexivity.
  + rewrite Hk, Hp. reflexivity.
- intros Hl. assert (Hrej : vr_st D = Verbs.reject)
    by (rewrite Hp; destruct args as [|a [|b args']]; [reflexivity | cbn in Hl; lia | reflexivity]).
  split; [unfold vr_h; rewrite Hrej; reflexivity | rewrite Hk, Hrej; reflexivity].
Qed.
Lemma policy_facts : forall R D v args, Verbs.toks D = v :: args -> VRR.route (Verbs.toks D) = VRR.RPolicy ->
(forall a b, args = [a; b] ->
   vr_h R D = (fst (sup_policy_set_m R (Some a) (Some b)), snd (sup_policy_set_m R (Some a) (Some b)), false) /\
   vr_k1 R D = 2 + EV_SUP_POLICY_SET R) /\
(length args <> 2%nat -> vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP).
Proof.
intros R D v args Htk Hr.
assert (Hv : v = Verbs.Lit.verb_policy_set) by (apply (proj1 (proj2 (route_v_eq v args))); rewrite <- Htk; exact Hr).
assert (Hp : vr_st D = VRR.plan_at VRR.RPolicy atoi_a (Verbs.line D) (v :: args))
  by (rewrite (vr_st_plan D ltac:(rewrite Htk; discriminate)), Hr, Htk; reflexivity).
assert (Hk : vr_k1 R D = 2 + ev_step R (vr_st D))
  by (apply (vr_k1_val R D v args Htk); vr_notverb Hv).
split.
- intros a b ->. cbn [VRR.plan_at] in Hp. split.
  + unfold vr_h. rewrite Hp. cbn [VerbsRun.run_step VerbsRun.run_call].
    destruct (sup_policy_set_m R (Some a) (Some b)) as [R' t]. reflexivity.
  + rewrite Hk, Hp. reflexivity.
- intros Hl. assert (Hrej : vr_st D = Verbs.reject)
    by (rewrite Hp; destruct args as [|a [|b [|c args']]]; [reflexivity | reflexivity | cbn in Hl; lia | reflexivity]).
  split; [unfold vr_h; rewrite Hrej; reflexivity | rewrite Hk, Hrej; reflexivity].
Qed.
Lemma lv2_facts : forall R D v args, Verbs.toks D = v :: args -> VRR.route (Verbs.toks D) = VRR.RLv2 ->
(forall a b, args = [a; b] ->
   vr_h R D = (fst (sup_lv2_worker_set_m R (Some a) (Some b)), snd (sup_lv2_worker_set_m R (Some a) (Some b)), false) /\
   vr_k1 R D = 2 + EV_SUP_LV2_WORKER_SET R) /\
(length args <> 2%nat -> vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP).
Proof.
intros R D v args Htk Hr.
assert (Hv : v = Verbs.Lit.verb_lv2_worker_set) by (apply (proj2 (proj2 (route_v_eq v args))); rewrite <- Htk; exact Hr).
assert (Hp : vr_st D = VRR.plan_at VRR.RLv2 atoi_a (Verbs.line D) (v :: args))
  by (rewrite (vr_st_plan D ltac:(rewrite Htk; discriminate)), Hr, Htk; reflexivity).
assert (Hk : vr_k1 R D = 2 + ev_step R (vr_st D))
  by (apply (vr_k1_val R D v args Htk); vr_notverb Hv).
split.
- intros a b ->. cbn [VRR.plan_at] in Hp. split.
  + unfold vr_h. rewrite Hp. cbn [VerbsRun.run_step VerbsRun.run_call].
    destruct (sup_lv2_worker_set_m R (Some a) (Some b)) as [R' t]. reflexivity.
  + rewrite Hk, Hp. reflexivity.
- intros Hl. assert (Hrej : vr_st D = Verbs.reject)
    by (rewrite Hp; destruct args as [|a [|b [|c args']]]; [reflexivity | reflexivity | cbn in Hl; lia | reflexivity]).
  split; [unfold vr_h; rewrite Hrej; reflexivity | rewrite Hk, Hrej; reflexivity].
Qed.

End e.
End f.
End d.
