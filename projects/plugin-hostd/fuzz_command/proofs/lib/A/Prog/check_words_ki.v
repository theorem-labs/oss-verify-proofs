(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared definitions of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0, 198 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_cx, cl_post, cl_mid and the segment statements CL_*_stmt): the entry context, the post, the invariant of the body between the frame's allocation and its release, and the three cut points the segment walks meet at (BODY after the shadow fills, HEAD of syntax_instantiate's loop, JOIN before hand_back); the walk tactics of cgif's lib/A/ACkc.v over fuzz_command's listing; and the facts every segment carries over a journal of the walk (read-only bytes, the shape string, arodata_okP). *)
(* Modified by Theorem Labs, 2026-10: statement passes 4 and 5 (lib/A/Prog/answer_c.v): an_pre without the stack's presence (astack_pres), BODY with the rounding-mode premise and the FP-existential post an_postF; HEAD and JOIN keep apost_base, at whatever FP state they are used. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_s1.v, with its module paths and module names changed; 353 of its 398 lines of code are new or changed and 204 lines of the source are left out. *)
(* check_words' ASan walk: facts every segment of the item loop reads at its current state (lib/A/Prog/check_words_d.v's
   points IH .. IL), proved once.
   - cw_icommon_kept / cw_base_kept: the state of a point (cw_core, cw_line, cw_lscr, cw_cscr, the item registers)
     carried to a later state of the same call when the memory changed only in the stack window below sp1 that a
     runtime entry uses (3 * ESTACK bytes), in the errno cell, and in number[16] = [F + 32, F + 48) of the own frame.
   - cw_tpl_at / cw_sp1_at: the template string of every recorded function, and the literal " ", at the current state:
     its bytes (cmd_ro_ok at the entry, carried by the journal's image clause), its shadow (CW_ZSH_P) and the readable
     tail of its last 8-byte word (cmd_tail_vis_P).
   - cw_word_at: the word array, the word pointers and the words of the message at the current state (cw_ent at the
     entry, carried by the journal's clauses for the caller's stack and for the heap blocks live at the entry). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* list facts *)
Lemma cw_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH].
{ change (join_sp []) with (@nil byte). cbn [length PJn.join_need fold_right]. lia. }
destruct ws as [|w2 ws'].
- change (join_sp [w]) with w. cbn [PJn.join_need fold_right]. lia.
- change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  rewrite length_app. cbn [length PJn.join_need fold_right] in *. lia.
Qed.
Lemma cw_join_nonul : forall ws, (forall k, (k < length ws)%nat -> ~ In (Z_to_bv 8 0) (nth k ws [])) ->
~ In (Z_to_bv 8 0) (join_sp ws).
Proof.
induction ws as [|w ws IH]; intros H.
{ change (join_sp []) with (@nil byte). cbn [In]. tauto. }
destruct ws as [|w2 ws'].
- change (join_sp [w]) with w.
  exact (H 0%nat ltac:(cbn [length]; lia)).
- change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H 0%nat ltac:(cbn [length]; lia) Hin)|].
  destruct Hin as [Hs|Hin].
  + unfold SPACE in Hs. apply (f_equal bv_unsigned) in Hs. vm_compute in Hs. discriminate Hs.
  + apply IH; [|exact Hin]. intros k Hk. exact (H (S k) ltac:(cbn [length] in *; lia)).
Qed.
Lemma cw_notin0 : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate. Qed.
Lemma cw_in_of_existsb : forall e l, existsb (Z.eqb e) l = true -> In e l.
Proof. intros e l H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He. subst. exact Hx. Qed.
Lemma cw_in_pair_of_existsb : forall a n (l : list (Z * Z)),
existsb (fun p => (fst p =? a) && (snd p =? n)) l = true -> In (a, n) l.
Proof.
intros a n l H. apply existsb_exists in H as ([x y] & Hx & He). cbn [fst snd] in He.
apply andb_prop in He as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hx.
Qed.

(* every recorded function's template is one of the 26 of fn in [0, 25] (the match's last case is fn = 25) *)
Lemma cw_fn_dflt : forall fn, ~ (0 <= fn <= 24) ->
cw_tptr fn = cw_tptr 25 /\ cw_tpl fn = cw_tpl 25 /\ PCW.call_items fn = PCW.call_items 25.
Proof.
intros fn Hfn. destruct fn as [|p|p]; [lia| |split; [reflexivity | split; reflexivity]].
do 5 (try destruct p as [p|p|]).
all: first [ split; [reflexivity | split; reflexivity] | exfalso; lia ].
Qed.
Lemma cw_fn26 : forall fn, exists f, 0 <= f <= 25 /\
cw_tptr fn = cw_tptr f /\ cw_tpl fn = cw_tpl f /\ PCW.call_items fn = PCW.call_items f.
Proof.
intros fn. destruct (Z_le_dec 0 fn) as [H0|H0]; [destruct (Z_le_dec fn 24) as [H1|H1]|].
- exists fn. split; [lia | split; [reflexivity | split; reflexivity]].
- exists 25. split; [lia|]. apply cw_fn_dflt. lia.
- exists 25. split; [lia|]. apply cw_fn_dflt. lia.
Qed.

(* the 17 read-only objects the item loop reads: the 16 distinct templates and " " *)
Definition CW_TPLRO : list (Z * list byte) :=
[(0x218c0, RO_lit_218c0); (0x218e0, RO_lit_218e0); (0x21900, RO_lit_21900); (0x21280, RO_lit_21280);
 (0x21920, RO_lit_21920); (0x21940, RO_lit_21940); (0x21960, RO_lit_21960); (0x21980, RO_lit_21980);
 (0x219a0, RO_lit_219a0); (0x219c0, RO_lit_219c0); (0x219e0, RO_lit_219e0); (0x21a00, RO_lit_21a00);
 (0x21a20, RO_lit_21a20); (0x21a40, RO_lit_21a40); (0x21a60, RO_lit_21a60); (0x21a80, RO_lit_21a80);
 (0x21aa0, RO_lit_21aa0); (0x21120, RO_lit_21120)].
Lemma cw_tplro_of : forall rd, cmd_ro_bytes rd -> Forall (fun t => abytes_atR rd (fst t) (snd t)) CW_TPLRO.
Proof.
intros rd HRO. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with _ /\ _ => let H := fresh "Hb" in destruct HRO as [H HRO] end.
unfold CW_TPLRO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
Qed.
(* the computed facts of one template *)
Definition cw_tpl_chk (f : Z) : bool :=
let tp := cw_tptr f in let n := Z.of_nat (length (cw_tpl f)) in
existsb (Z.eqb (tp + n)) cmd_ro_ends &&
existsb (fun p => (fst p =? tp) && (snd p =? n + 1)) CW_ZSH &&
forallb (fun b => negb (bv_unsigned b =? 0)) (cw_tpl f) &&
(0x21120 <=? tp) && (tp + n + 1 <=? 0x21ab0) && Nat.leb (length (cw_tpl f)) 8 && negb (tp =? A_G_REC) &&
existsb (fun t => (fst t =? tp) &&
  (if list_eq_dec Z.eq_dec (map bv_unsigned (snd t)) (map bv_unsigned (cw_tpl f ++ [Z_to_bv 8 0])) then true else false))
  CW_TPLRO.
Lemma cw_tpl_chk_ok : forall f, 0 <= f <= 25 -> cw_tpl_chk f = true.
Proof.
intros f Hf.
assert (Hc : forallb cw_tpl_chk (map Z.of_nat (seq 0 26)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hc. apply Hc. apply in_map_iff. exists (Z.to_nat f). split; [lia | apply in_seq; lia].
Qed.
Lemma cw_map_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma cw_tpl_facts : forall fn,
In (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) cmd_ro_ends /\
In (cw_tptr fn, Z.of_nat (length (cw_tpl fn)) + 1) CW_ZSH /\
~ In (Z_to_bv 8 0) (cw_tpl fn) /\
0x21120 <= cw_tptr fn /\ cw_tptr fn + Z.of_nat (length (cw_tpl fn)) + 1 <= 0x21ab0 /\ (length (cw_tpl fn) <= 8)%nat /\
cw_tptr fn <> A_G_REC /\
In (cw_tptr fn, cw_tpl fn ++ [Z_to_bv 8 0]) CW_TPLRO.
Proof.
intros fn. destruct (cw_fn26 fn) as (f & Hf & E1 & E2 & _). rewrite E1, E2.
pose proof (cw_tpl_chk_ok f Hf) as H. unfold cw_tpl_chk in H. cbv zeta in H.
repeat match type of H with (_ && _) = true => apply andb_prop in H as [H ?H] end.
repeat match goal with Hx : (_ <=? _) = true |- _ => apply Z.leb_le in Hx end.
repeat match goal with Hx : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hx end.
repeat match goal with Hx : negb (_ =? _) = true |- _ => apply negb_true_iff in Hx; apply Z.eqb_neq in Hx end.
split; [apply cw_in_of_existsb; assumption|].
split; [apply cw_in_pair_of_existsb; assumption|].
split; [apply cw_notin0; assumption|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [assumption|].
lazymatch goal with Hx : existsb (fun t => (fst t =? _) && _) CW_TPLRO = true |- _ =>
  apply existsb_exists in Hx as ([a l] & Hin & He) end.
cbn [fst snd] in He. apply andb_prop in He as [Ea El]. apply Z.eqb_eq in Ea. subst a.
destruct (list_eq_dec Z.eq_dec _ _) as [Em|]; [|discriminate El].
replace (cw_tpl f ++ [Z_to_bv 8 0]) with l
  by (first [apply cw_map_inj; exact Em | symmetry; apply cw_map_inj; exact Em]). exact Hin.
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
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the memory a stretch of the item loop may change: the stack window of a runtime entry called at sp1, the errno
   cell, number[16] of the own frame F *)
Definition cw_mem_kept (rd rd' : reader) (sp1 F : Z) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ (sp1 - 3 * ESTACK <= x < sp1) -> ~ (as_errno B <= x < as_errno B + 4) ->
~ (F + 32 <= x < F + 48) -> rd' x = rd x.
(* the registers a point's state names (callee-saved, so kept by every call) *)
Definition cw_regs_kept (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = getr regs 19 /\
getr regs' 20 = getr regs 20 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Lemma cw_regs_kept_of_pres : forall regs regs', aregs_preserved regs regs' -> cw_regs_kept regs regs'.
Proof.
intros regs regs' HP. unfold aregs_preserved, acallee_saved in HP.
split; [exact (HP 2 ltac:(lia))|]. split; [exact (HP 3 ltac:(lia))|]. split; [exact (HP 4 ltac:(lia))|].
split; [exact (HP 8 ltac:(lia))|]. split; [exact (HP 9 ltac:(lia))|]. split; [exact (HP 19 ltac:(lia))|].
split; [exact (HP 20 ltac:(lia))|]. split; [exact (HP 23 ltac:(lia))|]. split; [exact (HP 24 ltac:(lia))|].
split; [exact (HP 25 ltac:(lia))|]. split; [exact (HP 26 ltac:(lia)) | exact (HP 27 ltac:(lia))].
Qed.
(* the registers cw_core names *)
Definition cw_cregs_kept (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 23 = getr regs 23.
Lemma cw_cregs_of_regs : forall regs regs', cw_regs_kept regs regs' -> cw_cregs_kept regs regs'.
Proof. intros regs regs' (R2 & R3 & R4 & R8 & R9 & _ & _ & R23 & _). repeat split; assumption. Qed.
Lemma cw_regs_kept_refl : forall regs, cw_regs_kept regs regs.
Proof. intros regs. repeat split. Qed.
Lemma cw_regs_kept_trans : forall r1 r2 r3, cw_regs_kept r1 r2 -> cw_regs_kept r2 r3 -> cw_regs_kept r1 r3.
Proof.
intros r1 r2 r3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12)
  (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
repeat split; congruence.
Qed.
Lemma cw_mem_kept_refl : forall rd sp1 F, cw_mem_kept rd rd sp1 F.
Proof. intros rd sp1 F x _ _ _ _. reflexivity. Qed.
Lemma cw_mem_kept_trans : forall rd1 rd2 rd3 sp1 F, cw_mem_kept rd1 rd2 sp1 F -> cw_mem_kept rd2 rd3 sp1 F ->
cw_mem_kept rd1 rd3 sp1 F.
Proof. intros rd1 rd2 rd3 sp1 F H12 H23 x H0 H1 H2 H3. rewrite (H23 x H0 H1 H2 H3). exact (H12 x H0 H1 H2 H3). Qed.

Lemma cw_aval_kept : forall (rd rd' : reader) a n v,
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cw_abytes_kept : forall (rd rd' : reader) a l,
(forall k, (k < length l)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.

(* the parts of a point's state that do not depend on the item registers *)
Lemma cw_base_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c,
cw_ent B MT e ->
cw_core B e lyc Sc Wc regs mem md pos sp1 EV_JOINED -> cw_line B MT e lyc Sc (rdW Wc mem) line ->
cw_lscr e (rdW Wc mem) sp1 (frame_addr (e_ly e) 0 pos) line c -> cw_cscr (rdW Wc mem) sp1 c ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc mem' md' EV_JOINED ->
cw_cregs_kept regs regs' -> cw_mem_kept (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
cw_core B e lyc Sc Wc regs' mem' md' pos sp1 EV_JOINED /\ cw_line B MT e lyc Sc (rdW Wc mem') line /\
cw_lscr e (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) line c /\ cw_cscr (rdW Wc mem') sp1 c.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c HE HC HL HLS HCS HJ' HR HM.
set (F := frame_addr (e_ly e) 0 pos) in *.
set (sp0 := cw_sp0 e) in *.
destruct HC as (HJ & Hsp & Hal & Hrng & H3 & H4 & H8 & H9 & H23 & Hsav & V16 & V24 & V32 & V152 & V56 & Z4 & Z5).
destruct HL as (Hperm & Hl4096 & Hapart & Hlb & Hmo).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R23).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as ((Herr0 & Herr1) & Herrimg & _).
assert (WS : CHECK_WORDS_STK = 16800) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
(* the own frame at the current layout *)
assert (HFeq : frame_addr lyc 0 pos = F).
{ subst F. unfold frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hfin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mem md 0 pos HAR Hfin) as (HF0 & HF64 & HFapp).
rewrite HFeq in HF0, HF64, HFapp. change (fs_frame_bytes 0) with 64 in HF64, HFapp.
(* the kept bytes *)
assert (KS : forall x, sp1 <= x < 2 ^ 47 -> rdW Wc mem' x = rdW Wc mem x).
{ intros x Hx. apply HM; lia. }
assert (KF : forall x, F <= x < F + 64 -> ~ (F + 32 <= x < F + 48) -> rdW Wc mem' x = rdW Wc mem x).
{ intros x Hx Hn. apply HM; [lia | lia | | exact Hn].
  assert (HinF : frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + fs_frame_bytes 0)
    by (rewrite HFeq; change (fs_frame_bytes 0) with 64; lia).
  intros He. apply (proj2 (al_client_img _ _ LAWS lyc Sc Wc mem md x HAR
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hfin HinF))))))).
  exact (Herrimg x He). }
assert (KZ : forall x, CW_SB + F / 8 <= x < CW_SB + F / 8 + 8 -> rdW Wc mem' x = rdW Wc mem x).
{ intros x Hx. unfold CW_SB in Hx. pose proof (Z.div_le_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  apply HM; [lia | lia | lia |].
  intros Hn. apply (fshadow_not_app F 8 (F + 32) 16 x); [lia | lia | | lia | lia].
  apply (in_app_sub F 64); [exact HFapp | lia | lia | lia]. }
assert (KB : forall p n x, In (p, n) (ablocks B lyc Sc) -> p <= x < p + req_size n -> rdW Wc mem' x = rdW Wc mem x).
{ intros p n x Hin Hx.
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem md p n HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc mem md p n 0 pos HAR Hin Hfin) as Hdis.
  rewrite HFeq in Hdis. unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. change (fs_frame_bytes 0) with 64 in Hdis.
  apply HM; [lia | lia | | lia].
  intros He. apply (proj2 (al_client_img _ _ LAWS lyc Sc Wc mem md x HAR
    (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hx)))))).
  exact (Herrimg x He). }
split; [|split; [|split]].
- (* cw_core *)
  unfold cw_core. cbv zeta. change (frame_addr (e_ly e) 0 pos) with F. change (cw_sp0 e) with sp0.
  split; [exact HJ'|].
  assert (Hsp' : spZ regs' = sp1) by (unfold spZ; rewrite R2; exact Hsp).
  split; [exact Hsp'|]. split; [exact Hal|]. split; [exact Hrng|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R23; exact H23|].
  split.
  { intros j r Hj. apply (cw_aval_kept (rdW Wc mem)); [|exact (Hsav j r Hj)].
    assert (Hjl : (j < 13)%nat) by (change 13%nat with (length cw_saved); apply nth_error_Some; rewrite Hj; discriminate).
    intros k Hk. apply KS. lia. }
  split; [apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | exact V16]|].
  split; [apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | exact V24]|].
  split; [apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | exact V32]|].
  split; [apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | exact V152]|].
  split; [apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KF; lia | exact V56]|].
  split; [rewrite (KZ (CW_SB + F / 8 + 4)) by lia; exact Z4|].
  rewrite (KZ (CW_SB + F / 8 + 5)) by lia; exact Z5.
- (* cw_line *)
  split; [exact Hperm|]. split; [exact Hl4096|]. split; [exact Hapart|]. split; [|exact Hmo].
  apply (cw_abytes_kept (rdW Wc mem)); [|exact Hlb].
  intros k Hk. apply (KB line (cw_JN e)); [apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity|].
  rewrite length_app in Hk. cbn [length] in Hk.
  pose proof (cw_join_len (e_ws e)) as HJl. unfold cw_JN.
  pose proof (req_size_pos (PJn.join_need (e_ws e) + 1)) as Hrq.
  assert (0 <= PJn.join_need (e_ws e)) by (pose proof (Zle_0_nat (length (join_sp (e_ws e)))); lia).
  specialize (Hrq ltac:(lia)). lia.
- (* cw_lscr *)
  destruct HLS as (L144 & L8 & L40 & L48 & L56 & L64 & L72 & L88 & L96 & L104 & L128 & L136).
  repeat split; (apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | assumption]).
- (* cw_cscr *)
  destruct HCS as (S80 & S112 & S120).
  repeat split; (apply (cw_aval_kept (rdW Wc mem)); [intros k Hk; apply KS; lia | assumption]).
Qed.

Lemma cw_icommon_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args,
cw_ent B MT e -> cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc mem' md' EV_JOINED ->
cw_regs_kept regs regs' -> cw_mem_kept (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
cw_icommon B MT e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args HE HI HJ' HR HM.
destruct HI as (HC & HL & HLS & HCS & HIR & Hc & Hnth & Ha).
destruct (cw_base_kept e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c HE HC HL HLS HCS HJ' (cw_cregs_of_regs _ _ HR) HM)
  as (HC' & HL' & HLS' & HCS').
pose proof HR as (_ & _ & _ & _ & _ & R19 & R20 & _ & R24 & R25 & R26 & R27).
destruct HIR as (I19 & I20 & I25 & I26 & I27 & I24).
split; [exact HC'|]. split; [exact HL'|]. split; [exact HLS'|]. split; [exact HCS'|].
split; [|split; [exact Hc | split; [exact Hnth | exact Ha]]].
split; [rewrite R19; exact I19|]. split; [rewrite R20; exact I20|]. split; [rewrite R25; exact I25|].
split; [rewrite R26; exact I26|]. split; [rewrite R27; exact I27 | rewrite R24; exact I24].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the image bytes of the journal: a byte of the image outside the runtime's statics and the errno cell is the
   entry's *)
Lemma cw_img_kept : forall e lyc Sc Wc memc mdc pos k a,
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc memc mdc k ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW Wc memc a = rdW (e_W e) (e_mem e) a.
Proof.
intros e lyc Sc Wc memc mdc pos k a HJ H1 H2 H3.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
apply Himg; [exact H1 | exact H2 | exact H3|].
apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil].
Qed.

(* the template of fn and the literal " " at the current state *)
Lemma cw_tpl_at : forall e lyc Sc Wc memc mdc pos k fn,
cw_ent B MT e ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc memc mdc k ->
astr_atR (rdW Wc memc) (cw_tptr fn) (cw_tpl fn) /\
range_addressable (rdW Wc memc) SHADOW_OFF (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1) /\
shadow_hull_vis (rdW Wc memc) (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1) /\
atail_vis SEGS Wc memc (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) /\
0x21120 <= cw_tptr fn /\ cw_tptr fn + Z.of_nat (length (cw_tpl fn)) + 1 <= 0x21ab0 /\ (length (cw_tpl fn) <= 8)%nat.
Proof.
intros e lyc Sc Wc memc mdc pos k fn HE HJ.
destruct (cw_tpl_facts fn) as (Hend & Hzsh & Hnz & Hlo & Hhi & Hl8 & Hng & Hro).
pose proof HE as (_ & _ & _ & _ & HRO & _). destruct HRO as [HROB _].
pose proof (proj1 (Forall_forall _ _) (cw_tplro_of _ HROB) _ Hro) as Hb0. cbn [fst snd] in Hb0.
destruct (ZSH_cw lyc Sc Wc memc mdc _ _ (proj1 HJ) Hzsh) as [Hra Hhv].
split; [split; [|exact Hnz]|].
{ apply (cw_abytes_kept (rdW (e_W e) (e_mem e))); [|exact Hb0].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (cw_ro_unowned (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1) (Z.of_nat i) Hzsh Hng ltac:(lia))
    as (H1 & H2 & H3).
  exact (cw_img_kept e lyc Sc Wc memc mdc pos k _ HJ H1 H2 H3). }
split; [exact Hra|]. split; [exact Hhv|]. split; [exact (cmd_tail_vis lyc Sc Wc memc mdc _ (proj1 HJ) Hend)|].
split; [exact Hlo|]. split; [exact Hhi | exact Hl8].
Qed.
Lemma cw_sp1_at : forall e lyc Sc Wc memc mdc pos k,
cw_ent B MT e ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc memc mdc k ->
astr_atR (rdW Wc memc) 0x21120 CW_SP1 /\ range_addressable (rdW Wc memc) SHADOW_OFF 0x21120 2 /\
shadow_hull_vis (rdW Wc memc) 0x21120 2 /\ atail_vis SEGS Wc memc 0x21121.
Proof.
intros e lyc Sc Wc memc mdc pos k HE HJ.
assert (Hzsh : In (0x21120, 2) CW_ZSH) by (apply cw_in_pair_of_existsb; vm_compute; reflexivity).
assert (Hro : In (0x21120, CW_SP1 ++ [Z_to_bv 8 0]) CW_TPLRO).
{ replace (CW_SP1 ++ [Z_to_bv 8 0]) with RO_lit_21120 by (vm_compute; reflexivity). unfold CW_TPLRO.
  do 17 right. left. reflexivity. }
pose proof HE as (_ & _ & _ & _ & HRO & _). destruct HRO as [HROB _].
pose proof (proj1 (Forall_forall _ _) (cw_tplro_of _ HROB) _ Hro) as Hb0. cbn [fst snd] in Hb0.
destruct (ZSH_cw lyc Sc Wc memc mdc _ _ (proj1 HJ) Hzsh) as [Hra Hhv].
split; [split|].
{ apply (cw_abytes_kept (rdW (e_W e) (e_mem e))); [|exact Hb0].
  intros i Hi. cbn [length app CW_SP1] in Hi.
  destruct (cw_ro_unowned 0x21120 2 (Z.of_nat i) Hzsh ltac:(unfold A_G_REC; lia) ltac:(lia)) as (H1 & H2 & H3).
  exact (cw_img_kept e lyc Sc Wc memc mdc pos k _ HJ H1 H2 H3). }
{ apply cw_notin0. vm_compute. reflexivity. }
split; [exact Hra|]. split; [exact Hhv|].
apply (cmd_tail_vis lyc Sc Wc memc mdc _ (proj1 HJ)). apply cw_in_of_existsb. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the words of the message at the current state *)
Lemma cw_word_at : forall e lyc Sc Wc memc mdc pos k n,
cw_ent B MT e ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  lyc Sc Wc memc mdc k ->
(forall b, In b (ablocks B (e_ly e) (e_S e)) -> In b (ablocks B lyc Sc)) ->
(n < length (e_ws e))%nat ->
aval_mem (rdW Wc memc) (e_Wd e + 16) 8 (e_arr e) /\ 0 <= e_arr e < 2 ^ 64 /\
in_blockA (ablocks B lyc Sc) (e_arr e) (8 * Z.of_nat (length (e_ws e))) /\
aval_mem (rdW Wc memc) (e_arr e + 8 * Z.of_nat n) 8 (nth n (e_wp e) 0) /\ 0 <= nth n (e_wp e) 0 < 2 ^ 64 /\
in_blockA (ablocks B lyc Sc) (nth n (e_wp e) 0) (Z.of_nat (length (nth n (e_ws e) [])) + 1) /\
astr_atR (rdW Wc memc) (nth n (e_wp e) 0) (nth n (e_ws e) []).
Proof.
intros e lyc Sc Wc memc mdc pos k n HE HJ Hsub Hn.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & Hsp & Hhi & Harr & Harr64 & _ & _ & _ & Hblk & Hwords & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkb & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & Hshi & H47 & _).
destruct (Hwords n Hn) as (Hwp & Hwp64 & Hwb & Hws).
(* bytes of a block live at the entry and now *)
assert (KB : forall p q x, In (p, q) (ablocks B (e_ly e) (e_S e)) -> p <= x < p + q ->
  rdW Wc memc x = rdW (e_W e) (e_mem e) x).
{ intros p q x Hin Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p q (proj1 HPRE) Hin) as (_ & _ & _ & _ & _ & _ & Hq).
  pose proof (req_size_pos q ltac:(lia)) as [_ Hrq].
  replace x with (p + (x - p)) by lia.
  apply (Hkb p q (x - p) Hin (Hsub _ Hin)); [lia | apply inFP_nil]. }
assert (KBI : forall a m, in_blockA (ablocks B (e_ly e) (e_S e)) a m -> forall x, a <= x < a + m ->
  rdW Wc memc x = rdW (e_W e) (e_mem e) x).
{ intros a m (p & q & Hin & Hp & Hq) x Hx. apply (KB p q x Hin). lia. }
assert (HinB : forall a m, in_blockA (ablocks B (e_ly e) (e_S e)) a m -> in_blockA (ablocks B lyc Sc) a m).
{ intros a m (p & q & Hin & Hp & Hq). exists p, q. split; [exact (Hsub _ Hin) | lia]. }
split.
{ apply (cw_aval_kept (rdW (e_W e) (e_mem e))); [|exact Harr].
  intros j Hj. apply (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [unfold cw_sp0; lia | apply inFP_nil]. }
split; [exact Harr64|]. split; [exact (HinB _ _ Hblk)|].
split.
{ apply (cw_aval_kept (rdW (e_W e) (e_mem e))); [|exact Hwp].
  intros j Hj. apply (KBI _ _ Hblk). lia. }
split; [exact Hwp64|]. split; [exact (HinB _ _ Hwb)|].
destruct Hws as [Hb Hnz]. split; [|exact Hnz].
apply (cw_abytes_kept (rdW (e_W e) (e_mem e))); [|exact Hb].
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply (KBI _ _ Hwb). lia.
Qed.
End e.
End f.
End d.
