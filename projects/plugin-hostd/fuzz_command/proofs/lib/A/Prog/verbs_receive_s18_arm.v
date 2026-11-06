(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program-call arm of the segments S18 (sup_worker_env), S19 (chain_words),
   S21 (pin_set_words) and S22 (sup_pin_accept) of the walk of verbs_receive on the ASan build of
   plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v), on the fixed statements:
   - vr_call_gen: from the state at a callee's entry (vr_cs), the callee's contract (CALL, no astack_pres since
     statement pass 5) composed by PaFx's cl_callS_wideF, the frame chain at the call by achain_push (vr18_achain);
   - vr_jmp: the one `j` from the return pc to a join;
   - vr_after_core: what a boundary state keeps across a recorder callee (verbs_receive_s18_call.v's transports);
   - vr_hd_build (a recorder call that hands back a text block, vr_rc_post) and vr_pr_build_ps (pin_set_words,
     vr_ps_post): the boundary state after the call.
   Adapted from the S08/S09/S12 arm (verbs_receive_s08_lib.v). The record facts
   are the named Section hypotheses (HB, MTL, ROA, RRO, RPG, RECC, PROGU). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Setoid Morphisms.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
reply_c socket_send_c sup_after_reply_c arg_i_c xstrdup_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s18_kit verbs_receive_s18_call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the symbolic state at a return pc: the registers alone *)
Definition vr_ss_ret (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* the text of a recorder stub is at most 28 bytes (the plain proof's verbs_receive_br.v stub_text_len) *)
Lemma vr_stub_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
(length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- exact (proj1 (proj2 (shape_of_facts v))).
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.
Lemma vr_spill_frees0 : forall R, r_calls R = [] -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. rewrite H. reflexivity. Qed.

Lemma vr_nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. cbn in H. apply List.NoDup_cons_iff in H as [_ Hd].
exact (IH _ Hd).
Qed.
Lemma vr_nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x H Hx; [destruct Hx|]. cbn in H.
apply List.NoDup_cons_iff in H as [Hn Hd].
destruct Hx as [<- | Hx]; [intros H'; apply Hn; apply in_or_app; right; exact H' | exact (IH _ _ Hd Hx)].
Qed.
Lemma vr_nodup_app_intro : forall {A} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 ->
(forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. apply List.NoDup_cons_iff in H1 as [Hn H1].
cbn. apply List.NoDup_cons_iff. split.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (Hd y (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.

(* the 64 shadow bytes of tok[] in the side-stack frame are 0 once strndup has returned (vr_sh2) *)
Lemma vr_sh2_tok : forall j, (j < 64)%nat -> nth (4 + j) vr_sh2 0 = 0.
Proof.
intros j Hj. unfold vr_sh2.
rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
replace (4 + j - 4)%nat with j by lia.
rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.
Lemma vr_strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
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
Lemma vr_k1_ev : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, ev_after, EV_REPLY, EV_SOCKET_SEND.
destruct (vr_aft D) as [[i v]|]; [|lia].
unfold EV_SUP_AFTER_REPLY, rec_spill_frees, EV_ARG_I, EV_XSTRDUP. destruct (Nat.ltb _ _); lia.
Qed.
Lemma vr_rv_mk : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
Lemma vr_s1_cases : forall e, vr_sp0 e mod 16 = 0 -> vr_s1 e = vr_sp0 e - 192 \/ vr_s1 e = vr_sp0 e - 208.
Proof.
intros e H. unfold vr_s1. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M2.
rewrite H in D1. lia.
Qed.
Lemma vr_inFP_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma vr_inFP_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma vr_kept_regs : forall {segs : list Segment} E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok segs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros segs E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok segs E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma vr_env_agree_Eimg : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.


Lemma vr_rdeq_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
rd_same (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the record facts (names and types as the assembly collects them) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma vr_fp1_cases : forall O a, inFP (vr_fp1 O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a H. unfold vr_fp1 in H. apply inFP_cons in H as [H|H]; [left; exact H|].
apply inFP_cons in H as [H|H]; [right; left; exact H|]. right; right. exact (inFP_ablocks_fp_inv O a H).
Qed.

(* the walk's blocks at a route: live, none of the recorder's *)
Lemma vr_tmps_in : forall e q c lyc Sc (W : world SEGS) mem md, AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
forall y, In y ([vr_lb e q; vr_cb e c] ++ e_rest e) -> In y (ablocks B lyc Sc) /\ ~ In y (e_O e).
Proof.
intros e q c lyc Sc W mem md HAR Hperm y Hy.
assert (HndOT : List.NoDup (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e))
  by exact (Permutation_NoDup Hperm (vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
split.
- apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hy.
- intros Hy2. exact (vr_nodup_app_disj _ _ y HndOT Hy2 Hy).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The state at a callee's entry (after the `jal`): vr_core of the route with ra and the kept callee-saved
   registers rk named, the line and the copy *)
Definition vr_cs (e : vrE) (pos F q c retk : Z) (rk : list (Z * Z)) (tp : list Z) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k nm : Z) : Prop :=
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  ((1, BASE + retk) :: rk) (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md /\
vr_line B e q W mem /\ vr_copy B e F c tp W mem.

(* the post of a recorder call that hands back a text block (sup_worker_env_c.v:113-132, sup_pin_accept_c.v:99-118) *)
Definition vr_rc_post (R : rstate) (O : list (Z * Z)) (m : rstate * list byte) (LIVE1 XM1 : Z) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 m = (R', t) /\
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

(* the post of pin_set_words (pin_set_words_c.v:123-133) *)
Definition vr_ps_post (O : list (Z * Z)) (Rr : rstate * Z) (LIVE1 XM1 : Z) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 let '(R', r) := Rr in
 exists O' : list (Z * Z),
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE1 /\
 mo_le MT S S' XM1.

(* ---------------------------------------------------------------------------------------------------------------
   The parts of a boundary state after a recorder call. The meter steps are the interface's (vri_meter_ok at the
   call, vri_meter_step after it): a call that spends EV1 events, NM1 mallocs of at most VERBS_RECEIVE_REQ bytes and
   NF1 frees, with 0 <= NM1 <= EV1 and 0 <= NF1 <= EV1. *)

(* tok[] at F+32 in the side-stack frame: a frame object whose 8 * nt bytes have a zero shadow (vr_sh2) *)
Lemma vr_tok_afobj : forall ly S (W : world SEGS) mem pos F nt,
vr_frame ly W mem pos F vr_sh2 -> In (4, pos) (frames S) -> (F + 32) mod 8 = 0 -> 0 <= nt <= 64 ->
afobj SEGS B ly S W mem (F + 32) (8 * nt).
Proof.
intros ly S W mem pos F nt (EF & _ & HSH) HinF HT8 Hnt.
assert (HF8 : F mod 8 = 0)
  by (rewrite <- (Z.mod_add F 4 8) by lia; replace (F + 4 * 8) with (F + 32) by lia; exact HT8).
split; [exists 4, pos; split; [exact HinF|]; split; [lia|]; rewrite <- EF;
  split; [exact HF8|]; split; [lia|]; change (fs_frame_bytes 4) with 1024; lia|].
split; [exact HT8|].
apply zero_shadow_range; [exact HT8 | rewrite Z.mul_comm; apply Z_mod_mult |].
intros i Hi.
assert (Hi64 : 0 <= i < 64) by (rewrite Z.mul_comm, Z.div_mul in Hi by lia; lia).
replace (shadow_of_addr SHADOW_OFF (F + 32) + i) with (shadow_addr F + Z.of_nat (4 + Z.to_nat i)).
2: { unfold shadow_of_addr, shadow_addr. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
     replace (F + 32) with (F + 4 * 8) by lia. rewrite Z.div_add by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
rewrite (HSH (4 + Z.to_nat i)%nat ltac:(lia)). rewrite vr_sh2_tok by lia. reflexivity.
Qed.
Lemma vr_rv_after : forall e (regs regs2 regs3 : bvmap 5 word) ra rk v,
vr_rv regs (vr_base B e ++ (1, ra) :: rk) -> Forall (fun rv => acallee_saved (fst rv)) rk ->
aregs_preserved regs regs2 -> (forall r, getr regs3 r = getr regs2 r) ->
getr regs2 (Z_to_bv 5 10) = w64 v ->
vr_rv regs3 (vr_base B e ++ (10, v) :: rk).
Proof.
intros e regs regs2 regs3 ra rk v Hrv Hrk HP Er Ha0. apply vr_rv_mk. intros r v' Hin. rewrite Er.
apply in_app_or in Hin as [Hin | [Hin | Hin]].
- assert (Hcs : acallee_saved r).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; unfold acallee_saved; lia. }
  rewrite (HP r Hcs). apply (vr_rv_in regs _ _ _ Hrv). apply in_or_app; left; exact Hin.
- injection Hin as <- <-. exact Ha0.
- assert (Hcs : acallee_saved r) by (rewrite Forall_forall in Hrk; exact (Hrk (r, v') Hin)).
  rewrite (HP r Hcs). apply (vr_rv_in regs _ _ _ Hrv). apply in_or_app; right; right; exact Hin.
Qed.

Lemma vr_after_core : forall e pos F q c tp lyc Sc (W : world SEGS) mem md regs k nm rl STK1 EV1 W2 ly2 S2 mem2 md2 mem3,
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
ajournal SEGS B STK1 (vr_s1 e) (vr_fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
In (vr_lb e q) (ablocks B ly2 S2) -> In (vr_cb e c) (ablocks B ly2 S2) ->
rd_same (rdW W2 mem2) (rdW W2 mem3) ->
vr_frame ly2 W2 mem3 pos F vr_sh2 /\ vr_saved e W2 mem3 /\ vr_spill e W2 mem3 (vr_sl3 F q c) /\ vr_env B W2 mem3 /\
aval_mem (rdW W2 mem3) A_G_QUITTING 4 (e_q0 e) /\ vr_line B e q W2 mem3 /\ vr_copy B e F c tp W2 mem3.
Proof using ROA RRO RPG RECC PROGU LAWS.
intros e pos F q c tp lyc Sc W mem md regs k nm rl STK1 EV1 W2 ly2 S2 mem2 md2 mem3 Hent Hcore Hline Hcopy HJc Hlb Hcb Em.
pose proof Hcore as (HJ & _ & _ & _ & Hfr & _ & Hsv & Hsp & Henv & Hrec & _ & Hperm & Hq).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HlenD & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct (vr_ent_stk B MT e Hent) as (Hs1lo & Hs1sp & _ & Hsp47 & _ & _).
pose proof asan_consts as (C1 & _).
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (vr_tmps_in e q c lyc Sc W mem md HAR Hperm (vr_lb e q) ltac:(left; reflexivity)) as [Hlb1 Hlb2].
destruct (vr_tmps_in e q c lyc Sc W mem md HAR Hperm (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb1 Hcb2].
split; [apply (vr_frame_same ly2 W2 W2 mem2 mem3 pos F vr_sh2 Em);
  exact (vr_call_vrframe B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO pos F vr_sh2 HinF Hfr)|].
split; [apply (vr_saved_same e W2 W2 mem2 mem3 Em);
  apply (vr_call_saved B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO e); [lia | lia | lia | exact Hsv]|].
split.
{ apply (vr_spill_same e W2 W2 mem2 mem3 _ Em).
  apply (vr_call_spill B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO e); [reflexivity | lia | lia | | exact Hsp].
  unfold vr_sl3. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
split; [apply (vr_env_same B W2 W2 mem2 mem3 Em);
  exact (vr_call_env B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO RRO RPG ROA RECC Henv)|].
split; [exact (aval_mem_same _ _ _ _ _ Em (vr_call_quit B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO PROGU _ Hq))|].
split.
{ apply (vr_line_same B e q W2 W2 mem2 mem3 Em).
  apply (vr_call_line B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO e q Hline Hlb1 Hlb Hlb2).
  unfold vr_l. rewrite <- HlenD. exact (vr_line_le_l (e_D e)). }
apply (vr_copy_same B e F c tp W2 W2 mem2 mem3 Em).
destruct Hfr as (EF & _).
exact (vr_call_copy B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HAR HO e pos F c tp EF HinF Hcopy Hcb1 Hcb Hcb2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The join after a recorder call that hands back a text block: vr_hd at tgt *)
Lemma vr_hd_build : forall e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm STK1 EV1 LIVE1 XM1 NM1 NF1
  (m : rstate * list byte) W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
vr_ent B MT e ->
vr_cs e pos F q c retk rk tp lyc Sc W regs mem md k nm ->
vr_hd_ntok tgt (length (Verbs.toks (e_D e))) ->
(forall tq, vr_rl_hd e F q c tgt tq = (10, tq) :: rk) ->
Forall (fun rv => acallee_saved (fst rv)) rk ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
0 <= NF1 <= EV1 -> 0 <= NM1 <= EV1 -> NM1 + VR_NM_PRE <= VR_NM_HD ->
XM1 <= NM1 * mo_malloc MT VERBS_RECEIVE_REQ + NF1 * mo_free MT ->
ajournal SEGS B STK1 (vr_s1 e) (vr_fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
aregs_preserved regs regs2 ->
vr_rc_post (e_R e) (e_O e) m LIVE1 XM1 lyc Sc ly2 S2 W2 regs2 mem2 md2 ->
(forall r, getr regs3 r = getr regs2 r) -> rd_same (rdW W2 mem2) (rdW W2 mem3) ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem3 md3 (k + EV1) ->
vr_hd B MT e tgt W2 (cfg_at SEGS (vr_pc tgt) regs3 mem3 md3).
Proof using MTL ROA RRO RPG RECC PROGU LAWS.
intros e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm STK1 EV1 LIVE1 XM1 NM1 NF1 m W2 ly2 S2 regs2 mem2 md2
  regs3 mem3 md3 Hent Hcs Hntok Hrl Hrk Hvh Hk1 HNF1 HNM1 HNM2 HXM1 HJc HP HK Er Em HJ3.
destruct Hcs as (Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof HJ as (HAR & _).
pose proof HJc as (HAR2 & _).
pose proof (vr_tmps_in e q c lyc Sc W mem md HAR Hperm) as HinT0.
destruct HK as (R' & t & qq & O' & Em' & Ha0 & Hq4096 & Hrec' & HO'1 & Hqin & Hqnot & HqnotO' & Hstr & Hkeep & Hall
  & _ & Hmle).
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hvh, Em'; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = R') by (unfold vr_R1; rewrite Hvh, Em'; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e))
  by (pose proof (Permutation_in _ Hperm0 HinD) as H0; apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]).
destruct (HinT0 (vr_lb e q) ltac:(left; reflexivity)) as [Hlb1 Hlb2].
destruct (HinT0 (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb1 Hcb2].
destruct (vr_after_core e pos F q c tp lyc Sc W mem md regs k nm _ STK1 EV1 W2 ly2 S2 mem2 md2 mem3 Hent Hcore Hline Hcopy
  HJc (proj1 (Hkeep _ Hlb1 Hlb2)) (proj1 (Hkeep _ Hcb1 Hcb2)) Em) as (Afr & Asv & Asp & Aenv & Aq & Aline & Acopy).
destruct Hrec' as (Q' & HarQ & HOQ).
set (T0 := [vr_lb e q; vr_cb e c] ++ e_rest e) in *.
assert (HndOT : List.NoDup (e_O e ++ T0)) by exact (Permutation_NoDup Hperm (vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
unfold vr_hd. exists qq, (lay_blocks Q'), pos, F, q, c, tp, ly2, S2, regs3, mem3, md3, (k + EV1), (nm + NM1).
split; [reflexivity|].
split; [exact Hntok|].
split; [lia|].
split; [rewrite EX; exact (astr_same _ _ _ _ Em Hstr)|].
split; [|split; [exact Aline | exact Acopy]].
rewrite ER1, EQV, EX. unfold vr_core. rewrite (Hrl qq).
split; [exact HJ3|].
split; [rewrite Hk1; lia|].
split; [eapply vri_meter_step; [exact MTL | exact Hmet | exact Hmle | exact HXM1 | exact HNM1 | exact HNF1]|].
split; [unfold VR_NM_HD, VR_NM_PRE in *; lia|].
split; [exact Afr|].
split; [exact (vr_rv_after e regs regs2 regs3 (BASE + retk) rk qq Hrv Hrk HP Er Ha0)|].
split; [exact Asv|]. split; [exact Asp|]. split; [exact Aenv|].
split.
{ exists Q'. split.
  - apply (arep_at_agree (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2) (rdW W2 mem3) A_G_REC A_REC_SPILL R' Q' HarQ);
    [intros pn _ Hb; exact Hb | intros; apply Em | intros; apply Em | intros; apply Em].
  - intros pn. split; intros H; exact H. }
split.
{ intros Hin. apply HOQ in Hin. destruct (HO'1 _ Hin) as [H|H]; [exact (Hdat H)|]. apply H.
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. exact HinR. }
split; [|exact Aq].
change ([(qq, Z.of_nat (length t) + 1); vr_lb e q; vr_cb e c] ++ e_rest e) with ((qq, Z.of_nat (length t) + 1) :: T0).
apply NoDup_Permutation.
- exact (vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR2).
- apply vr_nodup_app_intro.
  + destruct HarQ as (_ & _ & _ & _ & _ & _ & _ & (Hnd & _)).
    first [exact (NoDup_map_inv _ _ Hnd) | exact (NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) Hnd))].
  + constructor; [intros Hin; destruct (HinT0 _ Hin) as [H1 H2]; exact (Hqnot _ H1 H2 eq_refl)
                 | exact (vr_nodup_app_r _ _ HndOT)].
  + intros y Hy Hy2. apply HOQ in Hy. destruct Hy2 as [<- | Hy2].
    * apply HqnotO'. apply in_map_iff. exists (qq, Z.of_nat (length t) + 1). split; [reflexivity | exact Hy].
    * destruct (HinT0 _ Hy2) as [H1 H2]. destruct (HO'1 _ Hy) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
- intros y. split.
  + intros Hy. destruct (Hall y Hy) as [(H1 & H2) | [H1 | H1]].
    * apply in_or_app; right; right. pose proof (Permutation_in _ Hperm H1) as H3.
      apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
    * apply in_or_app; left. apply HOQ. exact H1.
    * apply in_or_app; right; left. symmetry. exact H1.
  + intros Hy. apply in_app_or in Hy as [Hy | [Hy | Hy]].
    * apply HOQ in Hy. exact (rec_repA_in_blocks B _ _ _ _ _ _ (ex_intro _ Q' (conj HarQ HOQ)) Hy).
    * rewrite <- Hy. exact Hqin.
    * destruct (HinT0 _ Hy) as [H1 H2]. exact (proj1 (Hkeep _ H1 H2)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The refusal stub after pin_set_words (vr_pr at tgt, the code pin_set_words returned in a0) *)
Lemma vr_pr_build_ps : forall e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm STK1 EV1 LIVE1 XM1 NM1 NF1
  (Rr : rstate * Z) W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
vr_ent B MT e ->
vr_cs e pos F q c retk rk tp lyc Sc W regs mem md k nm ->
Verbs.toks (e_D e) <> [] -> vr_pr_ntok tgt (length (Verbs.toks (e_D e))) ->
(forall code, vr_rl_pr e F q c tgt code = (10, code) :: rk) ->
Forall (fun rv => acallee_saved (fst rv)) rk ->
vr_h (e_R e) (e_D e) = (fst Rr, resp (snd Rr), false) ->
(tgt <> 0x8dca0 -> snd Rr = -902) ->
k + EV1 <= vr_k1 (e_R e) (e_D e) - EV_SUP_RESP ->
0 <= NF1 <= EV1 -> 0 <= NM1 <= EV1 -> NM1 + VR_NM_PRE <= VR_NM_PR ->
XM1 <= NM1 * mo_malloc MT VERBS_RECEIVE_REQ + NF1 * mo_free MT ->
ajournal SEGS B STK1 (vr_s1 e) (vr_fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
aregs_preserved regs regs2 ->
vr_ps_post (e_O e) Rr LIVE1 XM1 lyc Sc ly2 S2 W2 regs2 mem2 md2 ->
(forall r, getr regs3 r = getr regs2 r) -> rd_same (rdW W2 mem2) (rdW W2 mem3) ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem3 md3 (k + EV1) ->
vr_pr B MT e tgt W2 (cfg_at SEGS (vr_pc tgt) regs3 mem3 md3).
Proof using MTL ROA RRO RPG RECC PROGU LAWS.
intros e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm STK1 EV1 LIVE1 XM1 NM1 NF1 Rr W2 ly2 S2 regs2 mem2 md2
  regs3 mem3 md3 Hent Hcs Hne Hntok Hrl Hrk Hvh Hcode Hk1 HNF1 HNM1 HNM2 HXM1 HJc HP HK Er Em HJ3.
destruct Rr as [R' r]. cbn [fst snd] in Hvh, Hcode.
destruct Hcs as (Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof HJ as (HAR & _).
pose proof HJc as (HAR2 & _).
pose proof (vr_tmps_in e q c lyc Sc W mem md HAR Hperm) as HinT0.
destruct HK as (O' & Ha0 & Hr32 & Hrec' & Hkeep & Hall & HO'1 & _ & Hmle).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e))
  by (pose proof (Permutation_in _ Hperm0 HinD) as H0; apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]).
destruct (HinT0 (vr_lb e q) ltac:(left; reflexivity)) as [Hlb1 Hlb2].
destruct (HinT0 (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb1 Hcb2].
destruct (vr_after_core e pos F q c tp lyc Sc W mem md regs k nm _ STK1 EV1 W2 ly2 S2 mem2 md2 mem3 Hent Hcore Hline Hcopy
  HJc (Hkeep _ Hlb1 Hlb2) (Hkeep _ Hcb1 Hcb2) Em) as (Afr & Asv & Asp & Aenv & Aq & Aline & Acopy).
destruct Hrec' as (Q' & HarQ & HOQ).
set (T0 := [vr_lb e q; vr_cb e c] ++ e_rest e) in *.
assert (HndOT : List.NoDup (e_O e ++ T0)) by exact (Permutation_NoDup Hperm (vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR)).
unfold vr_pr. exists r, R', (lay_blocks Q'), pos, F, q, c, tp, ly2, S2, regs3, mem3, md3, (k + EV1), (nm + NM1).
split; [reflexivity|].
split; [exact Hcode|].
split; [exact Hr32|].
split; [exact Hvh|].
split; [exact Hne|].
split; [exact Hntok|].
split; [|split; [exact Aline | exact Acopy]].
unfold vr_core. rewrite (Hrl r).
split; [exact HJ3|].
split; [exact Hk1|].
split; [eapply vri_meter_step; [exact MTL | exact Hmet | exact Hmle | exact HXM1 | exact HNM1 | exact HNF1]|].
split; [unfold VR_NM_PR, VR_NM_PRE in *; lia|].
split; [exact Afr|].
split; [exact (vr_rv_after e regs regs2 regs3 (BASE + retk) rk r Hrv Hrk HP Er Ha0)|].
split; [exact Asv|]. split; [exact Asp|]. split; [exact Aenv|].
split.
{ exists Q'. split.
  - apply (arep_at_agree (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2) (rdW W2 mem3) A_G_REC A_REC_SPILL R' Q' HarQ);
    [intros pn _ Hb; exact Hb | intros; apply Em | intros; apply Em | intros; apply Em].
  - intros pn. split; intros H; exact H. }
split.
{ intros Hin. apply HOQ in Hin. destruct (HO'1 _ Hin) as [H|H]; [exact (Hdat H)|]. apply H.
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. exact HinR. }
split; [|exact Aq].
apply NoDup_Permutation.
- exact (vr_ablocks_nodup SEGS B LAWS _ _ _ _ _ HAR2).
- apply vr_nodup_app_intro.
  + destruct HarQ as (_ & _ & _ & _ & _ & _ & _ & (Hnd & _)).
    first [exact (NoDup_map_inv _ _ Hnd) | exact (NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) Hnd))].
  + exact (vr_nodup_app_r _ _ HndOT).
  + intros y Hy Hy2. apply HOQ in Hy.
    destruct (HinT0 _ Hy2) as [H1 H2]. destruct (HO'1 _ Hy) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
- intros y. split.
  + intros Hy. destruct (Hall y Hy) as [(H1 & H2) | H1].
    * apply in_or_app; right. pose proof (Permutation_in _ Hperm H1) as H3.
      apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
    * apply in_or_app; left. apply HOQ. exact H1.
  + intros Hy. apply in_app_or in Hy as [Hy | Hy].
    * apply HOQ in Hy. exact (rec_repA_in_blocks B _ _ _ _ _ _ (ex_intro _ Q' (conj HarQ HOQ)) Hy).
    * destruct (HinT0 _ Hy) as [H1 H2]. exact (Hkeep _ H1 H2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The frame chain at a call (statement pass 5): verbs_receive is class B, s0 is
   its own sp0 at every program call, so the chain is afn_pre's (vr_ent's 1st conjunct) pushed by the frame record
   the prologue stored at sp0 - 8 (ra) and sp0 - 16 (the entry s0) (vr_saved, j = 0 and j = 1), with the words from
   sp0 up kept by the journal; when sp0 >= ly_top - 16 it is achain's empty case. Copied from verbs_receive_s14_c.v
   vr_achain under this file's names. *)
Lemma vr18_rdword_of_aval : forall rd a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v Hb Hr. unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Hb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Hb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Hb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Hb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Hb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Hb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Hb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Hb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* the walk's footprint lies below the allocator's ceiling *)
Lemma vr18_fp_lo : forall e a, vr_ent B MT e -> inFP (vr_fp e) a -> a < alloc_ceiling.
Proof.
intros e a He Ha. pose proof asan_consts as (C1 & _).
destruct He as ((HAR & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
unfold vr_fp in Ha. destruct Ha as (r & Hr & Hra). apply in_app_or in Hr as [Hr|Hr].
- unfold VERBS_RECEIVE_PG in Hr. cbn in Hr. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hra; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Hra.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma vr18_achain : forall e lyc Sc (W : world SEGS) memc mdc k pos,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W memc mdc k ->
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
pose proof (vr_s1_cases e Hal16) as Hs1.
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W memc) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e))
    (e_ch e) (vr_s1 e)).
  + exact Hch.
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (vr18_fp_lo e a He Hf). lia.
  + apply vr18_rdword_of_aval;
      [| unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 1)) as R;
         change (bv_modulus 64) with (2 ^ 64) in R; exact R].
    pose proof (Hsav 0%nat 1 eq_refl) as H. replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact H.
  + apply vr18_rdword_of_aval;
      [| unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 8)) as R;
         change (bv_modulus 64) with (2 ^ 64) in R; exact R].
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

(* ---------------------------------------------------------------------------------------------------------------
   The call: from the callee's entry, through its contract (CALL, FP-existential since statement pass 4:
   apost_baseF; no astack_pres since pass 5), to the return pc at the FP state fx' it returns at (AFTER, with
   fxrel fx fx'). The frame chain at the call is vr18_achain's; the callee's live-bytes premise comes from
   verbs_receive_live.v's vr_live_le (the entry's recorder holds no call). *)
Lemma vr_call_gen : forall e W pos F q c retk rk tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_cs e pos F q c retk rk tp lyc Sc W regs mem md k nm ->
2 + EV1 <= vr_k1 (e_R e) (e_D e) ->
0 <= NF1 <= EV1 -> 0 <= NM1 <= EV1 ->
XM1 <= NM1 * mo_malloc MT VERBS_RECEIVE_REQ + NF1 * mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 (vr_fp1 (e_O e)) regs lyc Sc W mem md EV1 K)) ->
(forall (fx' : YK11.FPState) W2 ly2 S2 regs2 mem2 md2, fxrel fx fx' ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem2 md2 (k + EV1) ->
  ajournal SEGS B STK1 (vr_s1 e) (vr_fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
  aregs_preserved regs regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md) Q.
Proof using HB MTL PROGU LAWS.
intros e W pos F q c retk rk tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1 K Q
  Hent Hcs Hk1 HNF1 HNM1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 CALL AFTER.
pose proof Hcs as (Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & Hrec0 & Hcalls & _ & _ & _ & _
  & Hperm0 & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm0 & Hev0 & Hlive0 & Hmok0).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (R1 : getr regs 1 = Z_to_bv 64 (BASE + retk))
  by (apply (vr_rv_in regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_in regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_in regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_in regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_in regs _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
(* the frame chain at the call: afn_pre's pushed by the prologue's frame record *)
destruct (vr18_achain e lyc Sc W mem md k pos Hent HJ Hsv) as (ch1 & Hch1).
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
destruct Hmet as (nf & Hnm0 & Hnf0 & Hnfk & Hmle0).
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
assert (Ho16 : (vr_s1 e - vr_sp0 e) mod 16 = 0)
  by (destruct Hs1 as [E|E]; rewrite E; [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia
      | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia]; reflexivity).
(* the live bytes now: the entry's, the recorder's (no call yet) and the line and copy blocks *)
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) + 10 * VERBS_RECEIVE_REQ).
{ pose proof (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W mem md (rdW W mem) (e_R e)
    (e_O e) (e_O e) [vr_lb e q; vr_cb e c] (e_rest e) HAR0 HAR Hperm0 Hperm Hrec) as HL.
  rewrite Hcalls in HL. cbn [length Z.of_nat] in HL. rewrite !bsum_cons in HL. unfold bsum in HL. cbn [fold_right] in HL.
  unfold vr_lb, vr_cb, vr_l in HL. cbn [snd] in HL.
  pose proof (vr_strnlen_le (e_n e) (e_D e) ltac:(lia)) as Hsl.
  pose proof (vr_line_le_l (e_D e)) as Hll. rewrite HlenD in Hll.
  unfold LMAX, VERBS_RECEIVE_REQ in *. lia. }
unfold cfg_at, w64.
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc md k STK1 (vr_fp1 (e_O e)) EV1 (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp1. lia.
  - exact Ho16.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { apply (CALL ch1 HPRE1).
      - exact (proj1 Henv).
      - exact (proj1 (proj2 (proj2 Henv))).
      - exact Hrec.
      - rewrite Hfrs. cbn [length app]. lia.
      - lia.
      - unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
      - eapply vri_meter_ok; [exact MTL | exact Hent | exact (ex_intro _ nf (conj Hnm0 (conj Hnf0 (conj Hnfk Hmle0))))
          | exact HXM1 | exact HNM1 | exact HNF1 | lia]. }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (vr_fp1_cases (e_O e) a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (vr_inFP_PG_rec a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
      unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
    + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (vr_inFP_PG_spill a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
    + right; left. split; [exists (p, p + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) Hpn) | cbn; lia]|].
      exists p, n. split; [exact (HO _ Hpn) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct (vr_fp1_cases (e_O e) a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + unfold A_G_REC, REC_SIZE in G. lia.
    + unfold A_REC_SPILL, SC_SIZE in G. lia.
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (AFTER fx' W2 ly2 S2 regs2 mem2 md2 Hfx HJ2 HJc HP HK).
Qed.

(* the jump of a return pc to a join (one `j`), run from a state that names only the registers *)
Lemma vr_jmp : forall retk stopk, 0 <= retk ->
sym_run_toN_pi pl_tpi FUEL stopk (vr_ss_ret retk) = (vr_ss_ret stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> rd_same (rdW W2 mem2) (rdW W2 mem3) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (vr_ss_ret retk)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold vr_ss_ret. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (vr_ss_ret retk) (vr_ss_ret stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (vr_ss_ret stopk) ms' HS' eq_refl). cbn [ss_pc vr_ss_ret].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (vr_ss_ret stopk) ms' r HS'). cbn [ss_regs vr_ss_ret].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem vr_ss_ret] in HFr. exact (vr_rdeq_of_frame _ [] _ _ _ HFr (Forall_nil _)).
  + exact HJ'.
Qed.

(* a word of tok[] handed to a recorder function: a C string inside the copy block, apart from every recorder block *)
Lemma vr_tok_blk : forall e F q c tp lyc Sc (W : world SEGS) mem md i p w,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\ astr_atR (rdW W mem) p w /\
Z.of_nat (length w) + 1 <= LMAX + 1 /\
Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) (e_O e) /\
aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling.
Proof.
intros e F q c tp lyc Sc W mem md i p w HAR Hperm (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
destruct (vr_tmps_in e q c lyc Sc W mem md HAR Hperm (vr_cb e c) ltac:(right; left; reflexivity)) as [Hcb HcbO].
unfold vr_cb in Hcb, HcbO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcb | lia]|].
split; [exact A1|]. split; [unfold LMAX; lia|].
split; [|split; [exact (Hptr i p Hp) | split; lia]].
apply Forall_forall. intros [p' n'] Hin'.
assert (Hin2 : In (p', n') (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin').
assert (Hne : (p', n') <> (c, Z.of_nat (length (Verbs.line (e_D e))) + 1)) by (intros E; rewrite E in Hin'; exact (HcbO Hin')).
pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md p' n' _ _ HAR Hin2 Hcb Hne) as Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hn').
pose proof (req_size_pos n' ltac:(lia)) as Hrs'.
unfold zdisjoint in Hd. unfold iv_apart. cbn [fst snd] in *. lia.
Qed.

Lemma vr_rec_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

(* rounding mode 0 at the entry FP state: vr_ent's last conjunct (statement pass 4) *)
Lemma vr18_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => apply proj2 in He end. exact He.
Qed.

End e.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------------
   The two arms: a recorder call that hands back a text block, then `j tgt` (vr_hd at tgt); pin_set_words, then
   `j tgt` (vr_pr at tgt, the refusal stub that answers with the code pin_set_words returned). The callee returns at
   some FP state fx' (apost_baseF), so the jump and the rebuild of the boundary state are the lemmas above, closed
   over the FP state and taken at fx'; the exit is the boundary predicate at fx' with fxrel fx fx'. *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* the entry facts at a later FP state: only rounding mode 0 names the FP state, and fxrel keeps it (the
   assembly's vr_ent_fxr) *)
Lemma vr18_ent_fxr : forall f0 f1 e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hr. revert He. unfold vr_ent. cbv zeta. intros He.
repeat lazymatch type of He with
| _ /\ _ => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
end.
exact (fxrel_frm0 f0 f1 He Hr).
Qed.

Lemma vr_call_arm_hd : forall e W pos F q c retk stopk rk tgt tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1
  (m : rstate * list byte),
vr_ent B MT e ->
vr_cs B MT e pos F q c retk rk tp lyc Sc W regs mem md k nm ->
vr_hd_ntok tgt (length (Verbs.toks (e_D e))) ->
(forall tq, vr_rl_hd e F q c tgt tq = (10, tq) :: rk) ->
Forall (fun rv => acallee_saved (fst rv)) rk ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
0 <= NF1 <= EV1 -> 0 <= NM1 <= EV1 -> NM1 + VR_NM_PRE <= VR_NM_HD ->
XM1 <= NM1 * mo_malloc MT VERBS_RECEIVE_REQ + NF1 * mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
vr_pc tgt = BASE + stopk ->
sym_run_toN_pi pl_tpi FUEL stopk (vr_ss_ret retk) = (vr_ss_ret stopk, PRS_running) ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 (vr_fp1 (e_O e)) regs lyc Sc W mem md EV1 (vr_rc_post B MT (e_R e) (e_O e) m LIVE1 XM1 lyc Sc))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_hd (fx := fq) B MT e tgt W' cf').
Proof using HB MTL ROA RRO RPG RECC PROGU.
intros e W pos F q c retk stopk rk tgt tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1 m
  Hent Hcs Hntok Hrl Hrk Hvh Hk1 HNF1 HNM1 HNM2 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 Hstop Hrun CALL.
apply (vr_call_gen B MT HB MTL PROGU e W pos F q c retk rk tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1 _ _
  Hent Hcs ltac:(lia) HNF1 HNM1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 CALL).
intros fx' W2 ly2 S2 regs2 mem2 md2 Hfx HJ2 HJc HP HK.
apply (vr_jmp (fx := fx') B retk stopk ltac:(lia) Hrun W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _ ly2 S2 _ HJ2).
intros regs3 mem3 md3 Er Em HJ3.
pose proof (vr_hd_build (fx := fx') B MT MTL ROA RRO RPG RECC PROGU e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm
  STK1 EV1 LIVE1 XM1 NM1 NF1 m W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3 (vr18_ent_fxr fx fx' e Hent Hfx) Hcs Hntok Hrl
  Hrk Hvh Hk1 HNF1 HNM1 HNM2 HXM1 HJc HP HK Er Em HJ3) as H.
unfold cfg_at, w64 in H. rewrite Hstop in H.
cbv beta. exists fx'. split; [exact Hfx | exact H].
Qed.

Lemma vr_call_arm_ps : forall e W pos F q c retk stopk rk tgt tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1
  (Rr : rstate * Z),
vr_ent B MT e ->
vr_cs B MT e pos F q c retk rk tp lyc Sc W regs mem md k nm ->
Verbs.toks (e_D e) <> [] -> vr_pr_ntok tgt (length (Verbs.toks (e_D e))) ->
(forall code, vr_rl_pr e F q c tgt code = (10, code) :: rk) ->
Forall (fun rv => acallee_saved (fst rv)) rk ->
vr_h (e_R e) (e_D e) = (fst Rr, resp (snd Rr), false) ->
(tgt <> 0x8dca0 -> snd Rr = -902) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 + EV_SUP_RESP ->
0 <= NF1 <= EV1 -> 0 <= NM1 <= EV1 -> NM1 + VR_NM_PRE <= VR_NM_PR ->
XM1 <= NM1 * mo_malloc MT VERBS_RECEIVE_REQ + NF1 * mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
vr_pc tgt = BASE + stopk ->
sym_run_toN_pi pl_tpi FUEL stopk (vr_ss_ret retk) = (vr_ss_ret stopk, PRS_running) ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 5 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 (vr_fp1 (e_O e)) regs lyc Sc W mem md EV1 (vr_ps_post B MT (e_O e) Rr LIVE1 XM1 lyc Sc))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_pr (fx := fq) B MT e tgt W' cf').
Proof using HB MTL ROA RRO RPG RECC PROGU.
intros e W pos F q c retk stopk rk tgt tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1 Rr
  Hent Hcs Hne Hntok Hrl Hrk Hvh Hcode Hk1 HNF1 HNM1 HNM2 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 Hstop Hrun CALL.
assert (HSR : 0 <= EV_SUP_RESP) by (unfold EV_SUP_RESP, EV_XSTRDUP; lia).
pose proof Hcs as ((_ & Hk & _) & _).
apply (vr_call_gen B MT HB MTL PROGU e W pos F q c retk rk tp lyc Sc regs mem md k nm AF STK1 EV1 LIVE1 XM1 NM1 NF1 _ _
  Hent Hcs ltac:(lia) HNF1 HNM1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 CALL).
intros fx' W2 ly2 S2 regs2 mem2 md2 Hfx HJ2 HJc HP HK.
apply (vr_jmp (fx := fx') B retk stopk ltac:(lia) Hrun W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _ ly2 S2 _ HJ2).
intros regs3 mem3 md3 Er Em HJ3.
pose proof (vr_pr_build_ps (fx := fx') B MT MTL ROA RRO RPG RECC PROGU e W pos F q c retk rk tgt tp lyc Sc regs mem md k nm
  STK1 EV1 LIVE1 XM1 NM1 NF1 Rr W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3 (vr18_ent_fxr fx fx' e Hent Hfx) Hcs Hne Hntok
  Hrl Hrk Hvh Hcode ltac:(lia) HNF1 HNM1 HNM2 HXM1 HJc HP HK Er Em HJ3) as H.
unfold cfg_at, w64 in H. rewrite Hstop in H.
cbv beta. exists fx'. split; [exact Hfx | exact H].
Qed.

End e2.
End f2.
End d2.
