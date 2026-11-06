(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the call kit of segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): a boundary-shaped
   state carried over a run that writes nothing (run07), over a runtime entry stated by a Theorem Labs lane's art_post (art07,
   through PaArt.aj_art_at), and the call of a program function (call07, through PaNoChain.cl_callS_wide), with the
   frame chain the call rules ask (chain07, achain_push on afn_pre's chain) and the blocks a call keeps (blk07); the
   registers a run keeps (kept_regs07, rv_keep07); a callee's budgets at a point of the walk (frames07, ev07, live07,
   mok07). Statement passes 4 and 5: the call of an FP-existential callee (call07F, through PaFx.cl_callS_wideF),
   rounding mode 0 at the entry (frm07), vr_ent at a later FP state (ent_fxr07), and JB at such a state (hdF07).
   The B twin of lib/A/Prog/verbs_receive_s07c.v; it adds B's frame bounds (HF_bounds07), from which each segment
   file refutes its UBSan trap branches on tok = F + 32, and a length-agnostic register-list tactic (rv07). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_after_reply_c reply_c socket_send_c record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s30_m verbs_receive_s30_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s07a verbs_receive_s07b.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* the tactics of the S07 runs: read-only regions write nothing; the model term after a run gets a name *)
Ltac awr07 := repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac roF := repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
Ltac mdv_set := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  let x := fresh "mdv" in set (x := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody x end.
(* a register list of callee-saved registers only *)
Ltac cs07_tac := repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; clear; lia|]); apply Forall_nil.

(* The registers of a boundary list after a run: each entry is either a register the run set (a hypothesis of the
   goal's own shape, closed by assumption) or one it kept (KR, from the run's symbolic state). Length-agnostic, so
   a list that gains or loses an entry needs no new pattern. *)
Ltac rv07 Hrv KR regs0 :=
  apply vr_rv_intro; intros r v Hin; apply in_app_or in Hin as [Hin|Hin];
  [unfold vr_base in Hin|]; cbn in Hin;
  repeat (let E1 := fresh "E1" in destruct Hin as [E1|Hin]; [injection E1 as <- <-|]);
  try (destruct Hin);
  first [ assumption
        | rewrite KR by (cbn; tauto); apply (vr_rv_get regs0 _ _ _ Hrv); cbn; tauto ].

(* lists without repeats whose members are those of two disjoint lists are a permutation of their concatenation *)
Lemma perm_of_mem07 : forall (bl O2 T : list (Z * Z)), List.NoDup bl -> List.NoDup O2 -> List.NoDup T ->
(forall x, In x O2 -> ~ In x T) -> (forall x, In x bl <-> In x O2 \/ In x T) -> Permutation bl (O2 ++ T).
Proof.
intros bl O2 T Hbl HO HT Hd Hm. apply NoDup_Permutation; [exact Hbl | |].
- clear Hm Hbl. induction O2 as [|a O2 IH]; [exact HT|]. cbn. apply List.NoDup_cons_iff in HO as [Ha HO].
  apply List.NoDup_cons.
  + intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Ha Hin) | exact (Hd a (or_introl eq_refl) Hin)].
  + apply IH; [exact HO | intros x Hx; apply Hd; right; exact Hx].
- intros x. rewrite Hm. split; intros H; [apply in_or_app; exact H | apply in_app_or; exact H].
Qed.
Lemma nodup_app07 : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1 /\ List.NoDup l2 /\
(forall x, In x l1 -> ~ In x l2).
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 H.
- split; [constructor|]. split; [exact H | intros x []].
- cbn in H. apply List.NoDup_cons_iff in H as [Ha H]. destruct (IH l2 H) as (H1 & H2 & H3).
  split; [apply List.NoDup_cons; [intros Hin; apply Ha; apply in_or_app; left; exact Hin | exact H1]|].
  split; [exact H2|]. intros x [<- | Hx] Hx2; [apply Ha; apply in_or_app; right; exact Hx2 | exact (H3 x Hx Hx2)].
Qed.

(* `not a2,s3` with the decoder's canonical immediate (-1 read as 2 ^ 64 - 1): YI08.U_not for that literal *)
Lemma U_not07 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit 18446744073709551615)) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon 18446744073709551615) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
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

(* registers a run leaves as they were, read off its symbolic state *)
Lemma kept_regs07 : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma env_agree07 : forall (regs : bvmap 5 word) shf F tps,
env_agree 32 (Ereg regs (map (Z_to_bv 64) ([shf; F + 32] ++ tps))) (E07 regs shf F tps).
Proof. intros. unfold E07. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).
Let C07 := c07_wr B MT TL ROA RECC RRO PROGU.

(* ---------------------------------------------------------------------------------------------------------------
   Registers *)
Definition cs07 (rl : list (Z * Z)) : Prop := Forall (fun rv => acallee_saved (fst rv)) rl.

Lemma rv_get07 : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma rv_intro07 : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
Lemma rv_keep07 : forall e (regs regs' : bvmap 5 word) rl,
vr_rv regs (vr_base B e ++ rl) -> cs07 rl -> aregs_preserved regs regs' -> vr_rv regs' (vr_base B e ++ rl).
Proof.
intros e regs regs' rl Hrv Hcs HP. apply rv_intro07. intros r v Hin.
assert (Hr : acallee_saved r).
{ apply in_app_or in Hin as [Hin|Hin].
  - unfold vr_base in Hin. cbn in Hin. unfold acallee_saved.
    destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; lia.
  - unfold cs07 in Hcs. rewrite Forall_forall in Hcs. exact (Hcs (r, v) Hin). }
rewrite (HP r Hr). exact (rv_get07 regs _ r v Hrv Hin).
Qed.
Lemma rv_sub07 : forall (regs : bvmap 5 word) l l', vr_rv regs l -> (forall x, In x l' -> In x l) -> vr_rv regs l'.
Proof.
intros regs l l' H Hs. apply rv_intro07. intros r v Hin. exact (rv_get07 regs l r v H (Hs _ Hin)).
Qed.

Lemma core_regs07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
getr regs 2 = w64 (vr_s1 e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (vr_sp0 e) /\ getr regs 9 = w64 (vr_s1 e) /\
spZ regs = vr_s1 e /\ s0Z regs = vr_sp0 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\
vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ alloc_ceiling + VERBS_RECEIVE_STK <= vr_sp0 e /\
vr_sp0 e <= 2 ^ 47.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md Hcore.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (vr_s1_bounds e Hal) as [Hs1 Hs1m].
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (rv_get07 regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (rv_get07 regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (rv_get07 regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (rv_get07 regs _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R9 : getr regs 9 = w64 (vr_s1 e)) by (apply (rv_get07 regs _ 9 _ Hrv); apply in_or_app; left; cbn; tauto).
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia|].
split; [unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia|].
split; [exact Hs1m|]. split; [lia|]. split; lia.
Qed.

(* the side-stack frame's bounds (class 4, below the allocation ceiling): what refutes every UBSan check on
   tok + 8k, since tok = F + 32 *)
Lemma HF_bounds07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
4096 <= F /\ F + 1024 <= alloc_ceiling.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md Hcore.
pose proof Hcore as (HJ & _ & _ & _ & Hfr & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct Hfr as (HF & _ & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (HF0 & HF1 & _).
rewrite <- HF in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   A run that leaves the memory as it was *)
Lemma run07 : forall e pos F q c tp tmps rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs regs' mem mem' md md',
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
(forall a, 0 <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a) ->
vr_rv regs' (vr_base B e ++ rl') ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps -> Z.of_nat (length (e_D e)) = e_n e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem' md' /\
vr_line B e q W mem' /\ vr_copy B e F c tp W mem'.
Proof.
intros e pos F q c tp tmps rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs regs' mem mem' md md'
  Hcore Hline Hcopy HJ' V Hrv' Hlb Hcb HDn.
pose proof (core_regs07 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & _). pose proof vr_stk_ge as [Hstk4 _]. unfold ESTACK in Hstk4.
assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (as_errno B <= a < as_errno B + 4) -> rdW W mem' a = rdW W mem a).
{ intros a Ha _. apply V. clear - Ha C1. lia. }
assert (KS : forall a, vr_s1 e <= a < vr_sp0 e -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply V. clear - Ha Hs1 H47 Hceil C1 Hstk4. lia. }
exact (C07 e pos F q c tp tmps rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs regs' mem mem' md md' Hcore Hline Hcopy HJ'
  KL KS Hrv' Hlb Hcb HDn).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   A runtime entry stated by art_post, whose window lies under s1 and which writes at most the errno cell besides *)
Lemma art07 : forall e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT stk Eb Qr retk pc
  (Q : world SEGS -> config -> Prop),
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT ->
vr_line B e q W memT -> vr_copy B e F c tp W memT ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps -> Z.of_nat (length (e_D e)) = e_n e -> cs07 rl ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
ESTACK <= stk <= 3 * ESTACK -> (forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
(ecall_pre_stk SEGS B stk lyc Sc W regsT memT mdT ->
 SRr SEGS W (cfg_at SEGS pc regsT memT mdT) (art_post SEGS B stk lyc Sc W regsT memT mdT Eb Qr)) ->
(forall regs2 mem2 md2,
  vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regs2 mem2 md2 ->
  vr_line B e q W mem2 -> vr_copy B e F c tp W mem2 ->
  Qr regs2 mem2 -> aregs_preserved regsT regs2 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e pos F q c tp tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT stk Eb Qr retk pc Q
  Hcore Hline Hcopy Hlb Hcb HDn Hcs R1 Hretk Hretk2 Hstk HEb HC K.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof (core_regs07 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hsp & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vr_stk_ge as [Hstk4 Hstk5]. unfold ESTACK, ASTACK in *.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _).
assert (Hra : YK0s.ret_ok (getr regsT 1)) by (rewrite R1; apply ret_ok_codeptr_v; lia).
pose proof (ecall_pre_stk_at SEGS B stk VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
  (e_md e) [(4, pos)] lyc Sc W memT mdT k regsT (vr_s1 e - vr_sp0 e) HJ ltac:(rewrite Hsp; lia) Ho16
  ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia) Hra R3 R4) as HPRE.
eapply SRr_bind.
{ eapply (ART stk Eb pc W regsT memT VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc mdT k (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) Qr HJ);
    [rewrite Hsp; lia | exact Ho16 | lia | lia | lia | exact R1 | exact HEb | exact (HC HPRE)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
assert (Hrv2 : vr_rv regs2 (vr_base B e ++ rl)) by exact (rv_keep07 e regsT regs2 rl Hrv Hcs HP2).
assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (as_errno B <= a < as_errno B + 4) -> rdW W mem2 a = rdW W memT a).
{ intros a Ha He. apply HK2; [lia | lia | intros HE; exact (He (HEb a HE))]. }
assert (KS : forall a, vr_s1 e <= a < vr_sp0 e -> rdW W mem2 a = rdW W memT a).
{ intros a Ha. apply HK2; [lia | lia |]. intros HE. pose proof (HEb a HE) as He.
  pose proof (pa_segs_low a (Heimg a He)). lia. }
destruct (C07 e pos F q c tp tmps rl rl Rc Oc qv k kmax nm nmax lyc Sc W regsT regs2 memT mem2 mdT md2
  Hcore Hline Hcopy HJ2 KL KS Hrv2 Hlb Hcb HDn) as (Hc2 & Hl2 & Hcp2).
exact (K regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ2 HP2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   A program call. The callee's footprint is g_rec, record.spill and blocks of the recorder; a recorder block is one
   of the entry's recorder blocks or a block the walk's callees made *)
Definition fpok07 (Oc FP1 : list (Z * Z)) : Prop :=
forall a, inFP FP1 a -> (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists b n, In (b, n) Oc /\ b <= a < b + req_size n.

Lemma Osplit07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md b n,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
In (b, n) Oc -> In (b, n) (e_O e) \/ ~ In (b, n) (ablocks B (e_ly e) (e_S e)).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md b n Hent Hcore Hin.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Hdec (b, n) (ablocks B (e_ly e) (e_S e))) as [H0|H0]; [|right; exact H0].
pose proof (Permutation_in _ Hperm0 H0) as H1. apply in_app_or in H1 as [H1|H1]; [left; exact H1|].
exfalso. pose proof (Permutation_NoDup Hperm (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR)) as Hnd.
destruct (nodup_app07 _ _ Hnd) as (_ & _ & Hd). apply (Hd (b, n) Hin). apply in_or_app. right. exact H1.
Qed.

Lemma inFP_PG_rec07 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma inFP_PG_spill07 : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.

(* the bytes a callee with footprint fpok07 writes are bytes the walk's journal allows *)
Lemma fpwr07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md FP1,
vr_ent B MT e -> vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md -> fpok07 Oc FP1 ->
forall a, inFP FP1 a ->
awr_byte SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (ablocks B (e_ly e) (e_S e)) (ablocks B lyc Sc) (frames (e_S e))
  lyc [(4, pos)] a.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md FP1 Hent Hcore HFP a Ha.
pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _).
destruct (HFP a Ha) as [G|[G|(b & n & Hbn & Hr)]].
- right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
    [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
  split; [|exact (proj1 (PROGU a (inFP_PG_rec07 a G)))].
  rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
  unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
- right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
    [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
  split; [|exact (proj1 (PROGU a (inFP_PG_spill07 a G)))].
  rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
- pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn) as Hbl.
  destruct (Osplit07 e pos F tmps _ _ rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md b n Hent Hcore Hbn) as [HO|HnO].
  + right; left. split; [exists (b, b + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
      exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (b, n) HO) | cbn; lia]|].
    exists b, n. split; [exact Hbl | exact Hr].
  + right; right; left. exists b, n. split; [exact Hbl|]. split; [exact HnO | exact Hr].
Qed.

(* a callee with footprint fpok07 writes nothing in the walk's frame window *)
Lemma fplow07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md FP1,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md -> fpok07 Oc FP1 ->
forall a, inFP FP1 a -> vr_sp0 e - VERBS_RECEIVE_STK <= a -> False.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md FP1 Hcore HFP a Ha Hw.
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _).
pose proof (proj1 HJ) as HAR.
pose proof (core_regs07 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (HFP a Ha) as [G|[G|(b & n & Hbn & Hr)]].
- unfold A_G_REC, REC_SIZE in G. lia.
- unfold A_REC_SPILL, SC_SIZE in G. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma call07 : forall e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT AF STK1 FP1 EV1 retk
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK -> fpok07 Oc FP1 ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regsT memT mdT ch ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regsT memT mdT) (apost_base SEGS B STK1 FP1 regsT lyc Sc W memT mdT EV1 K)) ->
(forall ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem2 md2 (k + EV1) ->
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memT mdT [] ly2 S2 W2 mem2 md2 EV1 ->
  aregs_preserved regsT regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT AF STK1 FP1 EV1 retk K Q
  Hent Hcore R1 Hretk Hretk2 HST0 HSTK1 HFP CALL KONT.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & Hsv & _ & _ & Hrec & _ & Hperm & _).
pose proof (core_regs07 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hsp & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (proj1 HJ) as HAR.
destruct (chain07 B MT e pos lyc Sc W memT mdT k Hent HJ Hsv) as (ch1 & Hch1).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsT memT (Z_to_bv 64 (BASE + AF)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdT k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e)
    (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp. lia.
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
    { exact (CALL ch1 HPRE1). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact (fpwr07 e pos F tmps _ _ rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT FP1 Hent Hcore HFP).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    exact (fplow07 e pos F tmps _ _ rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT FP1 Hcore HFP a Ha ltac:(lia)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (KONT ly2 S2 W2 regs2 mem2 md2 HJ2 HJc HP HK).
Qed.

(* the call of a callee whose post is FP-existential (apost_baseF, statement pass 4): the walk resumes at the return
   address at some FP state fx' related to the caller's by fxrel (PaFx.v cl_callS_wideF) *)
Lemma call07F : forall e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT AF STK1 FP1 EV1 retk
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK -> fpok07 Oc FP1 ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regsT memT mdT ch ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regsT memT mdT) (apost_baseF SEGS B STK1 FP1 regsT lyc Sc W memT mdT EV1 K)) ->
(forall (fx' : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, fxrel fx fx' ->
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem2 md2 (k + EV1) ->
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memT mdT [] ly2 S2 W2 mem2 md2 EV1 ->
  aregs_preserved regsT regs2 -> K ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e pos F q c tmps rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT AF STK1 FP1 EV1 retk K Q
  Hent Hcore R1 Hretk Hretk2 HST0 HSTK1 HFP CALL KONT.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & Hsv & _).
pose proof (core_regs07 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hsp & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (chain07 B MT e pos lyc Sc W memT mdT k Hent HJ Hsv) as (ch1 & Hch1).
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W regsT memT (Z_to_bv 64 (BASE + AF)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdT k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e)
    (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp. lia.
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
    { exact (CALL ch1 HPRE1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1.
    split; [reflexivity|]. split; [exact HR'|]. split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact (fpwr07 e pos F tmps _ _ rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT FP1 Hent Hcore HFP).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    exact (fplow07 e pos F tmps _ _ rl Rc Oc qv k kmax nm nmax lyc Sc W regsT memT mdT FP1 Hcore HFP a Ha ltac:(lia)). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (KONT fx' ly2 S2 W2 regs2 mem2 md2 Hfx HJ2 HJc HP HK).
Qed.

(* rounding mode 0 at the entry FP state (vr_ent's last conjunct, statement pass 4) *)
Lemma frm07 : forall e, vr_ent B MT e -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => apply proj2 in He end. exact He.
Qed.
(* the entry facts at a later FP state (the assembly's vr_ent_fxr) *)
Lemma ent_fxr07 : forall f0 f1 e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hr. revert He. unfold vr_ent. cbv zeta. intros He.
repeat lazymatch type of He with
| _ /\ _ => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
end.
exact (fxrel_frm0 f0 f1 He Hr).
Qed.
(* the join JB at some FP state related to the walk's: the exit of a leg that calls an FP-existential callee *)
Definition hdF07 (pc : Z) (e : vrE) : world SEGS -> config -> Prop :=
fun W cf => exists fq : YK11.FPState, fxrel fx fq /\ vr_athd (fx := fq) B MT pc e W cf.

(* the bytes of a block of the walk's own that the callee kept *)
Lemma blk07 : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md STK1 sp1 FP1
  ly2 S2 W2 mem2 md2 EV1 p n,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B STK1 sp1 FP1 lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 -> fpok07 Oc FP1 ->
In (p, n) tmps -> In (p, n) (ablocks B ly2 S2) ->
forall i, 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md STK1 sp1 FP1 ly2 S2 W2 mem2 md2 EV1 p n
  Hcore HJc HFP Hin Hin2 i Hi.
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
assert (Hb : In (p, n) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hin. }
assert (HnO : ~ In (p, n) Oc) by exact (perm_tmp_notin B _ _ _ _ _ _ _ _ _ HAR Hperm Hin).
apply (G2 p n i Hb Hin2 Hi). intros Hf.
pose proof (blk_img SEGS B LAWS lyc Sc W mem md p n (p + i) HAR Hb ltac:(lia)) as Himg.
destruct (HFP _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
- exact (Himg (proj1 (PROGU _ (inFP_PG_rec07 _ G)))).
- exact (Himg (proj1 (PROGU _ (inFP_PG_spill07 _ G)))).
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (HnO Hbm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md b m p n HAR (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hbm) Hb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a recorder's block list without repeats, with the same members *)
Lemma rec_nodup07 : forall ly S rd R O, rec_repA B ly S rd R O ->
exists O2, rec_repA B ly S rd R O2 /\ (forall x, In x O2 <-> In x O) /\ List.NoDup O2.
Proof.
intros ly S rd R O (Q & HA & HOQ). exists (lay_blocks Q).
split; [exists Q; split; [exact HA | intros pn; tauto]|].
split; [intros x; rewrite HOQ; tauto|].
destruct HA as (_ & _ & _ & _ & _ & _ & _ & (Hnd & _)).
first [exact (NoDup_map_inv _ _ Hnd) | exact (NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) Hnd))].
Qed.

Lemma ap_of_kept07 : forall regs regs' : bvmap 5 word,
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. apply H. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [cbn; tauto|]). subst r. cbn. tauto.
Qed.

Lemma strnlen_le07 : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma vr_k1_ev07 : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof. exact vr_k1_ev. Qed.

(* the callee budgets at a point of the walk: frames, events, live bytes of the arm's first call, the meter *)
Lemma frames07 : forall e pos lyc Sc W mem md k, vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W mem md k ->
Z.of_nat (length (frames Sc)) <= 5.
Proof.
intros e pos lyc Sc W mem md k Hent HJ.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [length app]. lia.
Qed.

Lemma ev07 : forall e own lyc Sc W mem md k EV, vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) own lyc Sc W mem md k ->
k + EV <= vr_k1 (e_R e) (e_D e) -> st_nev Sc + EV <= EV_MAX.
Proof.
intros e own lyc Sc W mem md k EV Hent HJ HkE.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (vr_k1_ev07 (e_R e) (e_D e)). lia.
Qed.

Lemma live07 : forall e pos F q c sh sl rl Oc qv k kmax nm nmax lyc Sc W regs mem md,
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] sh sl rl (e_R e) Oc qv k kmax nm nmax lyc Sc W regs mem md ->
blocks_bytes Sc + 10 * VERBS_RECEIVE_REQ <= blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE.
Proof.
intros e pos F q c sh sl rl Oc qv k kmax nm nmax lyc Sc W regs mem md Hent Hcore.
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & Hcalls & _ & _ & _ & _ & Hperm0 & _).
pose proof HPRE0 as (HAR0 & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
pose proof (verbs_receive_live.vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W mem md
  (rdW W mem) (e_R e) (e_O e) Oc [vr_lb e q; vr_cb e c] (e_rest e) HAR0 HAR Hperm0 Hperm Hrec) as HL.
rewrite Hcalls in HL. cbn [length Z.of_nat] in HL. rewrite !bsum_cons in HL. unfold bsum in HL. cbn [fold_right] in HL.
unfold vr_lb, vr_cb, vr_l in HL. cbn [snd] in HL.
pose proof (strnlen_le07 (e_n e) (e_D e) ltac:(lia)) as Hsl.
pose proof (line_le_l (e_D e) (e_n e) HlenD) as Hll. unfold vr_l in Hll.
unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, LMAX, VERBS_RECEIVE_REQ in *. lia.
Qed.

Hypothesis MTL : ameter_laws MT.
(* a callee's mo_ok premise (the interface's vri_meter_ok): am mallocs and af frees, each at most its EV events *)
Lemma mok07 : forall e Sc k nm am af X EV,
vr_ent B MT e -> vr_meter MT e Sc k nm -> k + EV <= vr_k1 (e_R e) (e_D e) ->
X <= am * mo_malloc MT VERBS_RECEIVE_REQ + af * mo_free MT -> 0 <= am <= EV -> 0 <= af <= EV ->
mo_ok MT Sc X.
Proof.
intros e Sc k nm am af X EV Hent Hmet HkE HX Ham Haf.
pose proof (vr_k1_ev07 (e_R e) (e_D e)) as Hkev.
eapply vri_meter_ok; [exact MTL | exact Hent | exact Hmet | exact HX | exact Ham | exact Haf | lia].
Qed.

End e.
End f.
End d.
