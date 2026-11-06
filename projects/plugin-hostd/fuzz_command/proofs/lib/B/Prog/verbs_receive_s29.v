(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S29 (REJ) of the walk of verbs_receive on the ASan+UBSan build of
   plugin-hostd/fuzz_command (image B, entry 0x8ce4c): B's six refusal stubs (gen/dis/verbs_receive.s).
   Statement: vr_s29_stmt (lib/B/Prog/verbs_receive_iface.v). The B twin of lib/A/Prog/verbs_receive_s29.v
   (a working branch): its lemma shapes (v29_pr_call, v29_call_post) with B's pcs, B's
   register lists and B's sup_resp contract (lib/B/Prog/sup_resp_c.v: xmalloc where A has xstrdup), over the join
   kit of lib/B/Prog/verbs_receive_s30_kit.v (vr_seed, vr_core_move, vr_chain_at, vr_env_of_aro).
   - 0x8d4c4 `li a0,-902; jal sup_resp`, returning to JB 0x8d4cc with the text in a0;
   - 0x8d68c `li a0,-902; jal sup_resp`, then 0x8d694 `mv s10,a0; ld s4,16(s1); ld s9,8(s1); ld s3,40(s1)` -> JA 0x8d6a4;
   - 0x8d870 `li a0,-902; jal sup_resp`, then 0x8d878 `mv s9,a0; ld s3,40(s1); j 0x8d4d0` -> JB 0x8d4d0;
   - 0x8d88c `jal sup_resp` with the code already in a0, then 0x8d890 `j 0x8d55c` -> JA 0x8d55c;
   - 0x8d64c `li a0,-902; j 0x8d88c` and 0x8d884 `li a0,-902; ld s3,40(s1)`: the code set, into the stub 0x8d88c.
   No UBSan trap site lies in these ranges. The third piece reaches JB 0x8d4d0, whose boundary asks for two words
   (vr_hd_ntok, iface), while the stub's boundary at 0x8d870 gives one (vr_pr_ntok, iface): v29_seg_870 takes the
   two words as a premise and vr_s29_of_ntok closes vr_s29_stmt from that premise. All names carry the prefix v29_. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c sup_resp_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------
   Plain helpers *)
Lemma v29_atoks_atA_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (Hal & Hlen & Hp & Ht) HT HC.
split; [exact Hal|]. split; [exact Hlen|].
split.
- intros i p Hi. assert (Hib : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)). intros kk Hkk.
  replace (tok + 8 * Z.of_nat i + kk) with (tok + (8 * Z.of_nat i + kk)) by lia. apply HT. lia.
- intros i p w Hi Hw. destruct (Ht i p w Hi Hw) as (A1 & A2 & A3 & A4).
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  apply (astr_atR_agree rd rd' p w (Z.of_nat (length w) + 1) A1); [lia|].
  intros kk Hkk. replace (p + kk) with (cb + (p - cb + kk)) by lia. apply HC. lia.
Qed.

Lemma v29_m902 : Z_to_bv 64 18446744073709550714 = w64 (-902).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma v29_getr_ew : forall (regsc : bvmap 5 word) extra (n : nat) (r : bv 5) v,
Z.of_nat n = bv_unsigned r -> getr regsc r = w64 v -> ew (Ereg regsc extra) n = w64 v.
Proof. intros regsc extra n r v Hn Hg. rewrite (ew_Ereg_nat regsc extra n r Hn). exact Hg. Qed.

Ltac v29_inl := cbn [vr_base In app]; solve [ repeat first [left; reflexivity | right] ].
Ltac v29_incl := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx |- *; tauto.
Ltac v29_fa := cbv beta; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.

(* one register of a boundary list after a symbolic run seeded by vr_seed / vr_seed0 at a state whose registers
   satisfy Hrv: a register the run kept or moved (its value is the atom of a register of the seed, which Hrv lists),
   a spill slot the run loaded (an extra atom of the seed), or the constant -902 *)
Ltac v29_rvgoal HS Hrv :=
cbn [fst snd];
lazymatch goal with
| |- getr _ ?r = w64 _ =>
  let Hx := fresh "Hx" in
  prreg HS r Hx; cbv [A_TEXT A_LIM] in Hx; cbn [Nat.leb andb] in Hx; rewrite Hx; clear Hx;
  first
  [ lazymatch goal with
    | |- ew _ ?n = _ =>
      apply (v29_getr_ew _ _ n (Z_to_bv 5 (Z.of_nat n)) _ eq_refl);
      apply (vr_rv_get _ _ _ _ Hrv); apply in_or_app; first [ left; v29_inl | right; v29_inl ]
    end
  | exact v29_m902
  | reflexivity ]
end.

(* ------------------------------------------------------------------------------------------------------------
   Statement pass 4: sup_resp's post is FP-existential (CmdBase.v apost_baseF), so the code after its call runs at
   the FP state fx' the call returns. Section d0 holds everything that runs or holds after the call (the state at the
   return address, the move stubs to the joins) and the helpers; it is closed before the main section d, so its
   lemmas hold at every FP state. *)
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f0.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section eA.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma v29_core_regs : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md' k ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' md'
  (HJ & Hk & Hm & Hnm & Hfr & Hrv & H) HJ' Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|]. split; [exact Hfr|].
split; [exact Hrv' | exact H].
Qed.

Lemma v29_frameF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
In (4, pos) (frames Sc) /\ AR SEGS B lyc Sc Wc memc mdc /\ 4096 <= F /\ F + 1024 <= alloc_ceiling.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc HC.
pose proof HC as (HJ & _ & _ & _ & (HF & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes 4) with 1024 in H2. rewrite <- HF in H1, H2.
split; [exact Hin|]. split; [exact HAR|]. split; [exact H1 | exact H2].
Qed.

Lemma v29_stkF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e).
Proof.
intros. pose proof H as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact Hstk.
Qed.

Lemma v29_s1_bounds : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
4096 <= vr_s1 e /\ vr_s1 e + 224 <= vr_sp0 e + 32 /\ vr_sp0 e <= 2 ^ 47 /\ vr_s1 e + 16 <= 2 ^ 64 /\
vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia.
Qed.

(* the stack offset of a call of sup_resp: s1 lies 192 or 208 bytes below sp0 (sp0 mod 16 = 0), and
   SUP_RESP_STK + 224 <= VERBS_RECEIVE_STK (sup_resp is one of the callees VR_CALLEE_STK covers, chain_words' need is
   above it) *)
Lemma v29_s1_bounds2 : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
alloc_ceiling <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e mod 16 = 0 /\
SUP_RESP_STK - (vr_s1 e - vr_sp0 e) <= VERBS_RECEIVE_STK /\ 0 <= SUP_RESP_STK.
Proof.
intros e Hstk. pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HV : SUP_RESP_STK + 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HR : 0 <= SUP_RESP_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
unfold vr_s1 in *.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact Hal|]. split; lia.
Qed.

Lemma v29_shadow_bounds : forall F, 4096 <= F -> F + 1024 <= alloc_ceiling ->
0 <= shadow_addr F /\ shadow_addr F + 4 < 2 ^ 64.
Proof.
intros F H1 H2. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
assert (Hp : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hu : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* the entry's facts the call of sup_resp uses (vr_ent's 1st, 14th, 8th, 9th, 30th, 31st, 32nd, 29th, 15th and
   20th conjuncts) *)
Lemma v29_ent_facts : forall e, vr_ent B MT e ->
afn_pre SEGS B VERBS_RECEIVE_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
rec_repA B (e_ly e) (e_S e) (rdW (e_W e) (e_mem e)) (e_R e) (e_O e) /\
(0 <= e_n e <= 8192) /\ Z.of_nat (length (e_D e)) = e_n e /\
st_nev (e_S e) + ev_vr (e_R e) (e_D e) <= EV_MAX /\
blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE <= LIVE_MAX /\
mo_ok MT (e_S e) (XM_VERBS_RECEIVE MT (e_R e) (e_D e)) /\
Z.of_nat (length (frames (e_S e))) <= 4 /\
r_calls (e_R e) = [] /\
Permutation (ablocks B (e_ly e) (e_S e)) (e_O e ++ e_rest e).
Proof.
intros e H. unfold vr_ent in H. cbv zeta in H.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33).
split; [exact H1|]. split; [exact H14|]. split; [exact H8|]. split; [exact H9|].
split; [exact H30|]. split; [exact H31|]. split; [exact H32|]. split; [exact H29|].
split; [exact H15 | exact H20].
Qed.

Lemma v29_line_le_upto0 : forall D, (length (Verbs.line D) <= length (Verbs.upto0 D))%nat.
Proof.
intros D. unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (verbs_receive_route.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H.
rewrite length_rev in H. exact H.
Qed.

Lemma v29_line_le_l : forall e, vr_ent B MT e ->
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e).
Proof.
intros e He. destruct (v29_ent_facts e He) as (_ & _ & _ & HDn & _).
unfold vr_l. rewrite <- HDn. rewrite (proj2 (verbs_receive_pre.strnlen_upto (e_D e))).
pose proof (v29_line_le_upto0 (e_D e)). lia.
Qed.

(* vr_hd with the register list and the word count left open: the state at a stub's return address is of this
   shape too, and `vr_hd e pc` is this at the interface's list and count *)
Definition v29_hdX (e : vrE) (pc : Z) (rlf : Z -> Z -> Z -> Z -> list (Z * Z)) (P : nat -> Prop)
  : world SEGS -> config -> Prop := fun Wc cf =>
exists tq O1 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
P (length (Verbs.toks (e_D e))) /\
4096 <= tq /\ astr_atR (rdW Wc memc) tq (vr_x (e_R e) (e_D e)) /\
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c]
  vr_sh2 (vr_sl3 F q c) (rlf F q c tq) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* from the open form to the interface's vr_hd: the word count the join asks, the registers it names *)
Lemma v29_hdX_hd : forall e pc rlf P W cf,
(P (length (Verbs.toks (e_D e))) -> vr_hd_ntok pc (length (Verbs.toks (e_D e)))) ->
(forall F q c tq, incl (vr_rl_hd e F q c pc tq) (rlf F q c tq)) ->
v29_hdX e pc rlf P W cf -> vr_hd B MT e pc W cf.
Proof.
intros e pc rlf P W cf HP Hi
  (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hnt & Htq & Hstr & HC & Hline & Hcopy).
exists tq, O1, pos, F, q, c, tp, lyc, Sc, regsc, memc, mdc, k, nm.
split; [exact Hcf|]. split; [exact (HP Hnt)|]. split; [exact Htq|]. split; [exact Hstr|].
split; [|split; [exact Hline | exact Hcopy]].
pose proof HC as (HJ & Hk & Hm & Hnm & Hfr & Hrv & Hrest).
split; [exact HJ|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|]. split; [exact Hfr|].
split; [|exact Hrest].
unfold vr_rv in *. rewrite Forall_forall in *. intros rv Hin. apply Hrv.
apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left; exact Hin | right; exact (Hi F q c tq rv Hin)].
Qed.

End eA.

Section eB.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ------------------------------------------------------------------------------------------------------------
   The hypotheses the part after the call uses: the record facts with the interface's names *)
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
(* every lemma below takes all the section's hypotheses, so that the main section applies them with one fixed list *)
Local Set Default Proof Using "All".

(* the meter at sup_resp's call, the one call shape of S29: its account is one malloc (xmalloc's) of
   |resp code| + 1 <= 17 bytes, so a = 1, b = 0, ev = EV_SUP_RESP = 1 for the interface's vri_meter_ok (the room
   before the call) and vri_meter_step (vr_meter after it) *)
Lemma v29_meter_xm : forall code, - 2 ^ 31 <= code < 2 ^ 31 ->
XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof.
intros code Hcode. pose proof (resp_length code Hcode) as Hrl.
assert (HXM : XM_SUP_RESP MT code <= mo_malloc MT VERBS_RECEIVE_REQ).
{ unfold XM_SUP_RESP, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_mono MT MTL). unfold VERBS_RECEIVE_REQ. lia. }
lia.
Qed.

Lemma v29_meter_pre : forall e Sc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> k <= vr_k1 (e_R e) (e_D e) - EV_SUP_RESP ->
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e Sc k nm code He Hcode Hmet Hk.
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
apply vri_meter_ok with (B := B) (e := e) (k := k) (nm := nm) (a := 1) (b := 0) (ev := EV_SUP_RESP).
- exact MTL.
- exact He.
- exact Hmet.
- exact (v29_meter_xm code Hcode).
- unfold EV_SUP_RESP, EV_XMALLOC. lia.
- unfold EV_SUP_RESP, EV_XMALLOC. lia.
- lia.
Qed.

Lemma v29_meter_post : forall e Sc S2 k nm code,
- 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_meter MT e S2 (k + EV_SUP_RESP) (nm + 1).
Proof.
intros e Sc S2 k nm code Hcode Hmet Hmo.
apply vri_meter_step with (Sc := Sc) (X := XM_SUP_RESP MT code) (b := 0).
- exact MTL.
- exact Hmet.
- exact Hmo.
- exact (v29_meter_xm code Hcode).
- unfold EV_SUP_RESP, EV_XMALLOC. lia.
- unfold EV_SUP_RESP, EV_XMALLOC. lia.
Qed.

(* the premises of tsup_resp_spec at a refusal stub *)
Lemma v29_call_pre : forall e pos F q c rlp Rx Ox lyc Sc (W : world SEGS) regsc memc mdc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlp Rx Ox (e_q0 e)
  k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regsc memc mdc ->
Z.of_nat (length (frames Sc)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W memc) /\ cmd_ro_ok (rdW W memc) /\
st_nev Sc + EV_SUP_RESP <= EV_MAX /\ blocks_bytes Sc + LIVE_SUP_RESP code <= LIVE_MAX /\
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e pos F q c rlp Rx Ox lyc Sc W regsc memc mdc k nm code He Hcode Hh HC.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_ent_facts B MT e He) as (HPRE & HREC0 & Hn8 & HDn & Hev & Hlive & Hmok & Hfrs4 & Hcalls0 & Hperm0).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof HPRE as (HAR0 & _).
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
pose proof (resp_length code Hcode) as Hrl.
(* the live bytes: the recorder's blocks, the line and the copy (verbs_receive_live.v) *)
assert (Hc2 : (length (r_calls Rx) <= 2)%nat).
{ pose proof (vrm_calls reply_code_a (e_R e) (vr_st (e_D e)) Hcalls0) as Hcx.
  unfold vr_h in Hh. rewrite Hh in Hcx. cbn [fst] in Hcx. exact Hcx. }
assert (Hlb : vr_l (e_n e) (e_D e) <= 8192).
{ unfold vr_l. rewrite <- HDn. rewrite (proj2 (verbs_receive_pre.strnlen_upto (e_D e))).
  pose proof (verbs_receive_route.upto_len (fun b => bv_unsigned b =? 0) (e_D e)) as Hu.
  change (Verbs.upto0 (e_D e)) with (Verbs.upto (fun b => bv_unsigned b =? 0) (e_D e)). lia. }
assert (Hcb : Z.of_nat (length (Verbs.line (e_D e))) <= 8192).
{ pose proof (verbs_receive_route.line_len (e_D e)) as Hl. lia. }
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) +
  (6 * Z.of_nat (length (r_calls Rx)) + 8) * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c]).
{ exact (vr_live_le SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HAR Hperm0 Hperm Hrec). }
assert (Hbs : bsum [vr_lb e q; vr_cb e c] <= 16386).
{ unfold bsum, vr_lb, vr_cb. cbn [fold_right snd]. lia. }
assert (Hlm : LMAX = 8192) by reflexivity.
split; [rewrite Hfrs; cbn [length app]; rewrite Nat2Z.inj_succ; lia|].
split; [exact (proj1 Henv)|].
split; [exact (proj1 (proj2 (proj2 Henv)))|].
split; [unfold EV_SUP_RESP, EV_XMALLOC in *; lia|].
split.
{ unfold LIVE_SUP_RESP, LIVE_XMALLOC, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *.
  assert (Hq : (6 * Z.of_nat (length (r_calls Rx)) + 8) * (LMAX + 2) <= 20 * 8194).
  { rewrite Hlm. apply Z.mul_le_mono_nonneg_r; lia. }
  lia. }
exact (v29_meter_pre e Sc k nm code He Hcode Hmet Hk).
Qed.

(* after sup_resp returned: the text is a block of its own, the frame, the spills, the saves, the blocks and the
   read-only and record facts are kept (the callee's journal has an empty footprint) *)
Lemma v29_call_post : forall (e : vrE) (pc : Z) rlf (P : nat -> Prop) (code : Z) Rx Ox pos F q c tp
  lyc Sc (W : world SEGS) regsc memc mdc k nm rlp
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 tq,
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
- 2 ^ 31 <= code < 2 ^ 31 ->
P (length (Verbs.toks (e_D e))) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlp Rx Ox (e_q0 e)
  k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_RESP) ->
ajournal SEGS B SUP_RESP_STK (vr_s1 e) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV_SUP_RESP ->
4096 <= tq ->
Permutation (ablocks B ly2 S2) ((tq, Z.of_nat (length (resp code)) + 1) :: ablocks B lyc Sc) ->
astr_atR (rdW W2 mem2) tq (resp code) ->
(forall R O, rec_repA B lyc Sc (rdW W memc) R O -> rec_repA B ly2 S2 (rdW W2 mem2) (fst (sup_resp_m R code)) O) ->
mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_rv regs2 (vr_base B e ++ rlf F q c tq) ->
v29_hdX B MT e pc rlf P W2 (cfg_at SEGS (vr_pc pc) regs2 mem2 md2).
Proof.
intros e pc rlf P code Rx Ox pos F q c tp lyc Sc W regsc memc mdc k nm rlp ly2 S2 W2 regs2 mem2 md2 tq
  Hll Hh Hcode HP HC Hline Hcopy HJ2 HJc Htq Hpq Hstr Hrectr Hmo Hrv2.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_frameF B MT HC) as (Hinf & HAR & HF1 & HF2).
pose proof (v29_stkF B MT HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (v29_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & G1 & G2 & G3 & G4 & _ & _ & _ & _ & _).
assert (Hnofp : forall a : Z, ~ inFP ([] : list (Z * Z)) a) by (intros a (r & [] & _)).
assert (Hsp2 : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply G1; [lia | lia | apply Hnofp]).
assert (Hblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW W memc (p + i)) by (intros p n i H1 H2 H3; exact (G2 p n i H1 H2 H3 (Hnofp _))).
assert (Himg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W memc a).
{ intros a H1 H2 H3. apply G3; try assumption.
  split; [intros Hs; destruct (sink_closed_pos [] (Forall_nil _) Hs) | apply Hnofp]. }
assert (Hfrm : forall a, (in_zr a (frame_rng lyc (4, pos)) \/
    in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply (G4 4 pos a Hinf Ha); apply Hnofp).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly2 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hh; reflexivity).
assert (Hxv : vr_x (e_R e) (e_D e) = resp code) by (unfold vr_x; rewrite Hh; reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = Rx) by (unfold vr_R1; rewrite Hh; reflexivity).
pose proof (resp_length code Hcode) as Hrl.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Hfr as (HFeq & HFflag & HFsh).
(* the line block and the copy block are live before and after the call *)
assert (HinLb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (HinCb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
assert (HinLb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinLb).
assert (HinCb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinCb).
exists tq, Ox, pos, F, q, c, tp, ly2, S2, regs2, mem2, md2, (k + EV_SUP_RESP), (nm + 1).
split; [reflexivity|]. split; [exact HP|]. split; [exact Htq|].
split; [rewrite Hxv; exact Hstr|].
split; [|split].
- (* vr_core *)
  split; [exact HJ2|].
  split; [lia|].
  split.
  { exact (v29_meter_post e Sc S2 k nm code Hcode Hmet Hmo). }
  split; [unfold VR_NM_PR, VR_NM_HD in *; lia|].
  split.
  { split; [rewrite EFA; exact HFeq|]. split.
    - rewrite EFL, <- HFflag. apply rdword_ext. intros kk Hkk. apply Hfrm. left.
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq. lia.
    - intros i Hi. rewrite Hfrm; [exact (HFsh i Hi)|]. right. unfold in_zr. cbn [fst snd].
      rewrite FB, <- HFeq. change (1024 / 8) with 128. lia. }
  split; [exact Hrv2|].
  split.
  { intros j r Hj.
    assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbv [vr_saved_regs] in Hjl; cbn [length] in Hjl.
    apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk. apply Hsp2. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov.
    assert (Hob : 0 <= fst ov <= 72).
    { unfold vr_sl3 in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
    apply (aval_mem_agree _ _ _ 8 _ (Hsp ov Hov)). intros kk Hkk.
    replace (vr_s1 e + fst ov + kk) with (vr_s1 e + (fst ov + kk)) by lia. apply Hsp2. lia. }
  split.
  { (* the read-only bytes, the GOT words, the record cells: vr_env from arodata_okP (the kit's vr_env_of_aro) *)
    destruct Henv as (Haro & _).
    assert (HAR2s : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2).
    assert (Haro2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
    { intros a Hro Ho He'. rewrite Himg; [exact (Haro a Hro Ho He') | | exact Ho | exact He'].
      destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)]. }
    exact (vr_env_of_aro B MT RRO RPG RECC PROGU ROA ly2 S2 W2 mem2 md2 HAR2s Haro2). }
  split.
  { rewrite HR1. pose proof (Hrectr Rx Ox Hrec) as Hr2. cbn [sup_resp_m fst] in Hr2. exact Hr2. }
  split; [exact HnO|].
  split.
  { rewrite Hxv. eapply Permutation_trans; [exact Hpq|].
    eapply Permutation_trans; [apply perm_skip; exact Hperm|]. apply Permutation_middle. }
  { rewrite Hqv. intros j Hj. rewrite Himg; [exact (Hquit j Hj) | | |].
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj1 (PROGU _ HPG)).
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj1 (proj2 (PROGU _ HPG))).
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj2 (proj2 (PROGU _ HPG))). }
- (* the line *)
  destruct Hline as (Hfresh & Hls). split; [exact Hfresh|].
  apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hls); [lia|].
  intros kk Hkk. apply (Hblk q (vr_l (e_n e) (e_D e) + 1) kk HinLb HinLb2).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)). lia.
- (* the copy and tok[] *)
  destruct Hcopy as (Hfresh & Htoks). split; [exact Hfresh|].
  pose proof Htoks as (_ & Hlen & _).
  pose proof (Verbs.toks_length (e_D e)) as Htl.
  apply (v29_atoks_atA_agree _ _ _ _ _ _ _ Htoks).
  + intros kk Hkk. apply Hfrm. left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq.
    rewrite Hlen in Hkk. lia.
  + intros kk Hkk. apply (Hblk c (Z.of_nat (length (Verbs.line (e_D e))) + 1) kk HinCb HinCb2).
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The stubs after sup_resp's return (no call, no store): the run from the return address to the join, seeded
   with the registers and the spill slots s1+8 (shadow_addr F), s1+16 (F) and s1+40 (tok = F+32) (the kit's
   vr_seed: the slots are the seed's atoms 32, 33, 34), and the boundary moved across it (the kit's vr_core_move) *)
Ltac v29_mv_tac srcpc srcoff tgtpc tgtoff :=
intros P e W cf H;
destruct H as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & Htq & Hstr & HC
  & Hline & Hcopy);
cbv beta in HC;
pose proof HC as (HJ & _ & _ & _ & _ & Hrv & _ & Hsp & _);
destruct (v29_frameF B MT HC) as (Hinf & HAR & HF1 & HF2);
pose proof (v29_stkF B MT HC) as Hstk;
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e);
destruct (v29_shadow_bounds F HF1 HF2) as (Hsha & Hshb);
pose proof asan_consts as (C1 & _);
assert (Hsp3 : vr_spill e W memc [(8, shadow_addr F); (16, F); (40, F + 32)])
  by (unfold vr_spill in Hsp |- *; rewrite Forall_forall in Hsp |- *; intros ov Hov; apply Hsp;
      destruct Hov as [<- | [<- | [<- | []]]]; unfold vr_sl3; v29_inl);
pose proof (vr_seed B e W regsc memc srcoff [(8, shadow_addr F); (16, F); (40, F + 32)] []
  (proj1 (proj1 (vr_rv_app regsc _ _) Hrv)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)
  ltac:(lia) ltac:(lia) Hsp3
  ltac:(repeat (apply Forall_cons; [cbn [snd]; lia|]); apply Forall_nil)) as HS;
cbn [map fst snd vr_vals app] in HS;
lazymatch type of HS with st_ok_pi _ _ ?E _ _ => assert (HEI : img_env VAL A_LIM E) by apply Eimg_env end;
unfold cfg_at; change (w64 (vr_pc srcpc)) with (Z_to_bv 64 (BASE + srcoff));
paj_run_to_shc RUNTOP HS HJ tgtoff;
[ awr_ok_tac
| lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end;
  pmkst HS;
  apply SRr_ret;
  lazymatch goal with
  | Hfr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm)
    |- v29_hdX _ _ _ _ _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) =>
    assert (Eq : forall a, rdW W mm a = rdW W memc a)
      by (apply (vr_rdW_frame _ _ W memc mm Hfr); apply vr_no_wrange; apply vr_ss_ro);
    exists tq, O1, pos, F, q, c, tp, lyc, Sc, rg, mm, mdx, k, nm;
    split; [unfold cfg_at; change (w64 (vr_pc tgtpc)) with (Z_to_bv 64 (BASE + tgtoff)); reflexivity|];
    split; [exact Hnt|]; split; [exact Htq|]; split; [exact (vr_astr_eq _ _ tq _ Eq Hstr)|];
    split; [| split; [exact (vr_line_eq B e q W memc _ Eq Hline) | exact (vr_copy_eq B e F c tp W memc _ Eq Hcopy)]];
    cbv beta;
    apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ _ O1 (vr_qv e) k _ nm _ lyc Sc W regsc memc mdc
      (vr_sl3 F q c) _ _ _ rg mm mdx HC HJ Eq);
    [ unfold vr_rv, vr_base; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; v29_rvgoal HS Hrv
    | apply incl_refl | lia | lia ]
  end ].

(* 0x8d694 mv s10,a0; ld s4,16(s1); ld s9,8(s1); ld s3,40(s1), falling into JA 0x8d6a4 (after sup_resp at the stub
   0x8d68c); the target list is vr_rl_hd at 0x8d6a4 *)
Lemma v29_mv_694 : forall P e W cf,
v29_hdX B MT e 0x8d694
  (fun F q c tq => (10, tq) :: [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX B MT e 0x8d6a4
  (fun F q c tq => [(26, tq); (19, F + 32); (20, F); (21, vr_ntok (e_D e)); (25, shadow_addr F);
                    (18, q); (22, F); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8d694 29028 0x8d6a4 29044. Qed.

(* 0x8d878 mv s9,a0; ld s3,40(s1); j 0x8d4d0 (after sup_resp at the stub 0x8d870); the target list is vr_rl_hd at
   0x8d4d0 *)
Lemma v29_mv_878 : forall P e W cf,
v29_hdX B MT e 0x8d878
  (fun F q c tq => (10, tq) :: [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX B MT e 0x8d4d0
  (fun F q c tq => [(25, tq); (19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8d878 29512 0x8d4d0 28576. Qed.

(* 0x8d890 j 0x8d55c (after sup_resp at the stub 0x8d88c); the target list is vr_rl_hd at 0x8d55c *)
Lemma v29_mv_890 : forall P e W cf,
v29_hdX B MT e 0x8d890
  (fun F q c tq => (10, tq) :: [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F);
                                (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX B MT e 0x8d55c
  (fun F q c tq => [(10, tq); (19, F + 32); (21, vr_ntok (e_D e)); (18, q); (22, F);
                    (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8d890 29536 0x8d55c 28716. Qed.

End eB.
End f0.
End d0.

(* ------------------------------------------------------------------------------------------------------------
   The main section: the refusal stubs at the entry's FP state fx, the call of sup_resp (an FP-existential callee,
   taken at every FP state as verbs_receive_c.v takes it), the rest at the FP state fx' it returns (section d0's
   lemmas at fx'), the two feeders of 0x8d88c, and the six pieces of S29 *)
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

(* the Section hypotheses: the callee contract of verbs_receive_c.v that this segment reaches (fx-generic, statement
   pass 4), the record facts with the interface's names *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let MOVE := vr_core_move B MT RRO RPG RECC PROGU ROA.
Local Set Default Proof Using "All".

(* rounding mode 0 at the entry FP state: vr_ent's last conjunct *)
Lemma v29_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e H. unfold vr_ent in H. cbv zeta in H.
repeat lazymatch type of H with _ /\ _ => apply proj2 in H end. exact H.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The call of sup_resp at a refusal stub: from the state at sup_resp's entry (ra = the return pc, a0 = code, the
   kept registers rlk) through tsup_resp_spec (cl_callSF: the callee returns at some FP state fx') to the state at
   the return pc, at fx', where a0 holds the text, a live block of its own *)
Definition v29_resp_post (code : Z) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists q,
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, Z.of_nat (length (resp code)) + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q (Z.of_nat (length (resp code)) + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 In (q, Z.of_nat (length (resp code)) + 1) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP MT code).

Lemma v29_pr_call : forall (e : vrE) (retpc : Z) (rlk : Z -> Z -> Z -> list (Z * Z)) (P : nat -> Prop) (code : Z)
  Rx Ox pos F q c tp lyc Sc (W : world SEGS) regs mem md k nm,
vr_ent B MT e ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
- 2 ^ 31 <= code < 2 ^ 31 ->
P (length (Verbs.toks (e_D e))) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) ((1, vr_pc retpc) :: (10, code) :: rlk F q c)
  Rx Ox (e_q0 e) k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
0 <= AF_verbs_receive + (retpc - 0x8ce4c) < 2 ^ 40 -> (AF_verbs_receive + (retpc - 0x8ce4c)) mod 2 = 0 ->
Forall (fun rv => 18 <= fst rv <= 27) (rlk F q c) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_sup_resp)) mem (seg_rom SEGS)) md)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
     v29_hdX (fx := fq) B MT e retpc (fun F' q' c' tq => (10, tq) :: rlk F' q' c') P W' cf').
Proof.
intros e retpc rlk P code Rx Ox pos F q c tp lyc Sc W regs mem md k nm He Hh Hcode HP HC Hline Hcopy Hrk1 Hrk2 Hcs.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_call_pre B MT MTL ROA RRO RPG RECC PROGU e pos F q c _ Rx Ox lyc Sc W regs mem md k nm code He Hcode Hh HC)
  as (Hfrs8 & Haro & Hro & Hev1 & Hlv1 & Hmo1).
pose proof (v29_ent_frm0 e He) as Hfrm.
pose proof (v29_stkF B MT HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (v29_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (R1 : getr regs 1 = w64 (vr_pc retpc))
  by (apply (vr_rv_get regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R10 : getr regs 10 = w64 code)
  by (apply (vr_rv_get regs _ 10 _ Hrv); apply in_or_app; right; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; v29_inl).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; v29_inl).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; v29_inl).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; v29_inl).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the frame chain at the call: s0 holds the entry sp, the chain is the entry's with verbs_receive's own record on
   top (the kit's vr_chain_at, statement pass 5) *)
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W mem md k pos regs He HJ Hsv R8) as (ch1 & Hch1).
eapply SRr_mono.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_sup_resp)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k SUP_RESP_STK [] EV_SUP_RESP (vr_s1 e - vr_sp0 e)
    (w64 (vr_pc retpc)) ch1 (v29_resp_post code lyc Sc W mem) HJ).
  - rewrite Hsp1. lia.
  - exact Hs2b.
  - lia.
  - exact Hs2e.
  - exact Hs2d.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64, vr_pc. apply ret_ok_codeptr_v; [exact Hrk1 | exact Hrk2].
  - unfold w64, vr_pc. rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TSUP_RESP fx lyc Sc W regs mem md ch1 code HPRE1 Hfrm Hfrs8 Haro Hro R10 Hcode Hev1 Hlv1 Hmo1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|].
    split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (tq & Htq10 & Htq & Hpq & Hap & Hin & Hstr & Hrectr & Hbb & Hmo).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exists fx'. split; [exact Hfx|].
apply (v29_call_post (fx := fx') B MT MTL ROA RRO RPG RECC PROGU e retpc (fun F' q' c' tq => (10, tq) :: rlk F' q' c') P
  code Rx Ox pos F q c tp lyc Sc W regs mem md k nm _ ly2 S2 W2 regs2 mem2 md2 tq (v29_line_le_l B MT e He)
  Hh Hcode HP HC Hline Hcopy HJ2 HJc ltac:(lia) Hpq Hstr Hrectr Hmo).
cbv beta. apply vr_rv_intro. intros r v Hin'. apply in_app_or in Hin' as [Hin' | [Hin' | Hin']].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin'. cbn in Hin'. destruct Hin' as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. left. exact Hin'.
- injection Hin' as <- <-. exact Htq10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin') as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (HP2 r Hr). apply (vr_rv_get regs _ _ _ Hrv). apply in_or_app. right. right. right. exact Hin'.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The registers at sup_resp's entry: ra the return pc, a0 the code, the callee-saved registers kept *)
Lemma v29_in15 : forall r, acallee_saved r -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Proof. intros r Hr. unfold acallee_saved in Hr. cbn [In]. lia. Qed.

Lemma v29_pres_of_kept : forall (regs regsc : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
aregs_preserved regsc regs.
Proof. intros regs regsc H r Hr. exact (H r (v29_in15 r Hr)). Qed.

Lemma v29_rv_call : forall e (regs regsc : bvmap 5 word) rl rlk retpc code,
vr_rv regsc (vr_base B e ++ rl) ->
aregs_preserved regsc regs ->
getr regs (Z_to_bv 5 1) = w64 (vr_pc retpc) ->
getr regs (Z_to_bv 5 10) = w64 code ->
incl rlk rl -> Forall (fun rv => 18 <= fst rv <= 27) rlk ->
vr_rv regs (vr_base B e ++ (1, vr_pc retpc) :: (10, code) :: rlk).
Proof.
intros e regs regsc rl rlk retpc code Hrv Hpr H1 H10 Hinc Hcs.
apply vr_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin | [Hin | [Hin | Hin]]].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (Hpr r Hr). apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app. left. exact Hin.
- injection Hin as <- <-. exact H1.
- injection Hin as <- <-. exact H10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin) as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (Hpr r Hr). apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app. right. exact (Hinc _ Hin).
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The refusal stubs: from vr_pr at the stub, the run `li a0,-902; jal sup_resp` (0x8d88c: `jal sup_resp`) to
   sup_resp's entry (no memory read or written), then the call (v29_pr_call) *)
Ltac v29_pr_run HC W regsc memc srcpc srcoff :=
pose proof HC as (HJ & _ & _ & _ & _ & Hrv & _);
remember (Eimg (Ereg regsc [])) as E eqn:HE;
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply vr_env_agree);
assert (HS : st_ok_pi SEGS VAL E (vr_ss0 srcoff)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + srcoff)) memc (seg_rom SEGS)))) by (subst E; apply vr_seed0);
clear HE;
unfold cfg_at; change (w64 (vr_pc srcpc)) with (Z_to_bv 64 (BASE + srcoff));
paj_run_shc RUNP RUNC HS HJ;
[ apply awr_ok_nil
| lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end;
  let Hmem := fresh "Hmem" in
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem _) |- _ =>
    pose proof (frame_of_read_only _ _ _ _ (eq_refl : rs_read_only [] = true) HFx) as Hmem
  end;
  rewrite Hmem in HJ;
  let Q1 := fresh "Q1" in prreg HS (Z_to_bv 5 1) Q1;
  pose proof (vr_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  pmkst HS; rewrite Hmem;
  rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; v29_inl));
  change (cmd_af CS_sup_resp) with AF_sup_resp ].

(* 0x8d4c4 li a0,-902; jal sup_resp (0x8d4c8) -> 0x8d4cc *)
Lemma v29_pr_4c4 : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8d4c4 W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8d4cc
    (fun F q c tq => (10, tq) :: [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d4c4) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8d4c4 (-902))
  with [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8d4c4 28564.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8d4cc (fun F q c => [(19, F + 32); (18, q); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d4c4) (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8d4cc (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + v29_incl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

(* 0x8d68c li a0,-902; jal sup_resp (0x8d690) -> 0x8d694 *)
Lemma v29_pr_68c : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8d68c W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8d694
    (fun F q c tq => (10, tq) :: [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d68c) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8d68c (-902))
  with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8d68c 29020.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8d694 (fun F q c => [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d68c) (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8d694 (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

(* 0x8d870 li a0,-902; jal sup_resp (0x8d874) -> 0x8d878 *)
Lemma v29_pr_870 : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8d870 W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8d878
    (fun F q c tq => (10, tq) :: [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d870) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8d870 (-902))
  with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8d870 29504.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8d878 (fun F q c => [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d870) (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8d878 (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

(* 0x8d88c jal sup_resp, a0 = the code (pin_set_words', pins_clear's, or -902 from the feeders) -> 0x8d890 *)
Lemma v29_pr_88c : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8d88c W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8d890
    (fun F q c tq => (10, tq) :: [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F);
                                  (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d88c) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
change (vr_rl_pr e F q c 0x8d88c code)
  with [(10, code); (19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8d88c 29532.
pose proof (vr_kept_regs E _ _ regsc [] [10] HS HAE ltac:(vm_compute; reflexivity)) as KR10.
cbn [ms_regs restrict] in KR10.
apply (v29_pr_call e 0x8d890
  (fun F q c => [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8d88c) code Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8d890 code Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite (KR10 10 (or_introl eq_refl)).
    apply (vr_rv_get regsc _ 10 code Hrv). apply in_or_app. right. left. reflexivity.
  + intros x Hx. right. exact Hx.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The six pieces of S29. A refusal stub runs at fx up to sup_resp, the stub after the call runs at the FP state fq
   the call returned (section d0's lemmas at fq); the feeders of 0x8d88c run at fx and call nothing. *)
Lemma v29_seg_4c4 : vr_segF B MT (vr_atpr B MT 0x8d4c4) (vrF_hd B MT 0x8d4cc).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_pr_4c4 e W cf He H)|].
intros W3 c3 _ (fq & Hfx & H3). exists fq. split; [exact Hfx|].
exact (v29_hdX_hd (fx := fq) B MT e 0x8d4cc _ _ W3 c3 (fun Hn => Hn) (fun F q c tq => incl_refl _) H3).
Qed.

Lemma v29_seg_68c : vr_segF B MT (vr_atpr B MT 0x8d68c) (vrF_hd B MT 0x8d6a4).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_68c e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2).
eapply SRr_mono; [exact (v29_mv_694 (fx := fq) B MT MTL ROA RRO RPG RECC PROGU _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx|].
exact (v29_hdX_hd (fx := fq) B MT e 0x8d6a4 _ _ W3 c3 (fun Hn => Hn) (fun F q c tq => incl_refl _) H3).
Qed.

(* 0x8d870 -> JB 0x8d4d0, for a message of at least two words: vr_hd at 0x8d4d0 asks for them
   (vr_hd_ntok, iface), the stub's boundary vr_pr at 0x8d870 gives one (vr_pr_ntok, iface) *)
Lemma v29_seg_870 : vr_segF B MT (fun e W cf => vr_pr B MT e 0x8d870 W cf /\ (2 <= length (Verbs.toks (e_D e)))%nat)
  (vrF_hd B MT 0x8d4d0).
Proof.
intros e W cf He (H & Hn2). eapply SRr_bind; [exact (v29_pr_870 e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2).
eapply SRr_mono; [exact (v29_mv_878 (fx := fq) B MT MTL ROA RRO RPG RECC PROGU _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx|].
exact (v29_hdX_hd (fx := fq) B MT e 0x8d4d0 _ _ W3 c3 (fun _ => Hn2) (fun F q c tq => incl_refl _) H3).
Qed.

Lemma v29_seg_88c : vr_segF B MT (vr_atpr B MT 0x8d88c) (vrF_hd B MT 0x8d55c).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_88c e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2).
eapply SRr_mono; [exact (v29_mv_890 (fx := fq) B MT MTL ROA RRO RPG RECC PROGU _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx|].
exact (v29_hdX_hd (fx := fq) B MT e 0x8d55c _ _ W3 c3 (fun Hn => Hn) (fun F q c tq => incl_refl _) H3).
Qed.

(* 0x8d64c li a0,-902; j 0x8d88c: the code set, the registers kept *)
Lemma v29_seg_64c : vr_seg B MT (vr_atpr B MT 0x8d64c) (vr_atpr B MT 0x8d88c).
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8d64c (-902))
  with [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
pose proof HC as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof (vr_seed0 W regsc memc 28956) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
unfold cfg_at; change (w64 (vr_pc 0x8d64c)) with (Z_to_bv 64 (BASE + 28956)).
paj_run_to_shc RUNTOP HS HJ 29532.
{ apply awr_ok_nil. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a)
  by (apply (vr_rdW_frame _ _ W memc (ms_mem ms) HFr); apply vr_no_wrange; apply Forall_nil).
clear HF HFr HG.
pmkst HS.
apply SRr_ret.
exists (-902), Rx, Ox, pos, F, q, c, tp, lyc, Sc, (ms_regs ms), (ms_mem ms), mdv, k, nm.
split; [unfold cfg_at; change (w64 (vr_pc 0x8d88c)) with (Z_to_bv 64 (BASE + 29532)); reflexivity|].
split; [intros _; reflexivity|].
split; [exact Hcode|]. split; [exact Hh|]. split; [exact Htk|]. split; [exact Hntk|].
split; [| split; [exact (vr_line_eq B e q W memc _ Eq Hline) | exact (vr_copy_eq B e F c tp W memc _ Eq Hcopy)]].
change (vr_rl_pr e F q c 0x8d88c (-902))
  with [(10, -902); (19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)].
apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ Rx Ox (e_q0 e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ _ _ (ms_regs ms) (ms_mem ms) mdv HC HJ Eq).
- unfold vr_rv, vr_base; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; v29_rvgoal HS Hrv.
- apply incl_refl.
- lia.
- lia.
Qed.

(* 0x8d884 li a0,-902; ld s3,40(s1), falling into 0x8d88c: the code set, tok reloaded into s3 *)
Lemma v29_seg_884 : vr_seg B MT (vr_atpr B MT 0x8d884) (vr_atpr B MT 0x8d88c).
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8d884 (-902))
  with [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] in HC.
pose proof HC as (HJ & _ & _ & _ & _ & Hrv & _ & Hsp & _).
destruct (v29_frameF B MT HC) as (Hinf & HAR & HF1 & HF2).
pose proof (v29_stkF B MT HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
pose proof asan_consts as (C1 & _).
assert (Hsp1 : vr_spill e W memc [(40, F + 32)])
  by (unfold vr_spill in Hsp |- *; rewrite Forall_forall in Hsp |- *; intros ov Hov; apply Hsp;
      destruct Hov as [<- | []]; unfold vr_sl3; v29_inl).
pose proof (vr_seed B e W regsc memc 29524 [(40, F + 32)] [] (proj1 (proj1 (vr_rv_app regsc _ _) Hrv))
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) ltac:(lia) ltac:(lia) Hsp1
  ltac:(apply Forall_cons; [cbn [snd]; lia | apply Forall_nil])) as HS.
cbn [map fst snd vr_vals app] in HS.
lazymatch type of HS with st_ok_pi _ _ ?E _ _ => assert (HEI : img_env VAL A_LIM E) by apply Eimg_env end.
unfold cfg_at; change (w64 (vr_pc 0x8d884)) with (Z_to_bv 64 (BASE + 29524)).
paj_run_to_shc RUNTOP HS HJ 29532.
{ awr_ok_tac. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (Eq : forall a, rdW W (ms_mem ms) a = rdW W memc a)
  by (apply (vr_rdW_frame _ _ W memc (ms_mem ms) HFr); apply vr_no_wrange; apply vr_ss_ro).
clear HF HFr HG.
pmkst HS.
apply SRr_ret.
exists (-902), Rx, Ox, pos, F, q, c, tp, lyc, Sc, (ms_regs ms), (ms_mem ms), mdv, k, nm.
split; [unfold cfg_at; change (w64 (vr_pc 0x8d88c)) with (Z_to_bv 64 (BASE + 29532)); reflexivity|].
split; [intros _; reflexivity|].
split; [exact Hcode|]. split; [exact Hh|]. split; [exact Htk|]. split; [exact Hntk|].
split; [| split; [exact (vr_line_eq B e q W memc _ Eq Hline) | exact (vr_copy_eq B e F c tp W memc _ Eq Hcopy)]].
change (vr_rl_pr e F q c 0x8d88c (-902))
  with [(10, -902); (19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)].
apply (MOVE e pos F _ vr_sh2 (vr_sl3 F q c) _ Rx Ox (e_q0 e) k _ nm _ lyc Sc W regsc memc mdc
  (vr_sl3 F q c) _ _ _ (ms_regs ms) (ms_mem ms) mdv HC HJ Eq).
- unfold vr_rv, vr_base; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; v29_rvgoal HS Hrv.
- apply incl_refl.
- lia.
- lia.
Qed.

(* vr_s29_stmt from the two words at 0x8d870 (the premise the interface's vr_pr does not carry there: RQuit leaves
   for 0x8d870 at `bne s5,a0` 0x8d2a4 with s5 = ntok <> 1, and ntok >= 1) *)
Lemma vr_s29_of_ntok :
(forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8d870 W cf -> (2 <= length (Verbs.toks (e_D e)))%nat) ->
vr_s29_stmt B MT.
Proof.
intros H870.
exact (conj v29_seg_4c4 (conj v29_seg_68c
  (conj (fun e W cf He H => v29_seg_870 e W cf He (conj H (H870 e W cf He H)))
  (conj v29_seg_88c (conj v29_seg_64c v29_seg_884))))).
Qed.

(* the interface now carries the two words at 0x8d870 (verbs_receive_iface.v vr_pr_ntok), so the premise of
   vr_s29_of_ntok is vr_pr's own conjunct *)
Lemma vr_s29 : vr_s29_stmt B MT.
Proof.
apply vr_s29_of_ntok. intros e W cf _ H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & _ & _ & _ & _ & _ &
  Hntk & _).
exact Hntk.
Qed.

End e.
End f.
End d.
