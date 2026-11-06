(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the segments S25 (the scan of g_instance_info_verbs, 0x8d7e0-0x8d82c)
   and S26 (the ledger call, 0x8d894-0x8d8c0) of the walk of verbs_receive on the ASan+UBSan build (image B) of
   plugin-hostd/fuzz_command (interface: lib/B/Prog/verbs_receive_iface.v): the table's rows, names and ledger words as
   the image holds them (0xa5c40, the names at 0x22920 .. 0x22a40: A's + 0x40), the model's route behind the scan, and
   the transport of a boundary state's memory facts to a memory that agrees with it below the allocation ceiling and
   above the realigned stack pointer (every write of a run without stores and of a runtime entry lands in the stack
   window below it). The B twin of lib/A/Prog/verbs_receive_s25_k.v; the frame chain at a program call is the B
   kit's vr_chain_at (verbs_receive_s30_kit.v), and vr_rv_get / vr_val_mem_of_aval / vr_got_of_ro come from there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre verbs_receive_tail_m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s30_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* ---------------------------------------------------------------------------------------------------------------
   The table g_instance_info_verbs (0xa5c40, 10 rows of 16 bytes: the name pointer and the ledger word) *)
Definition vr_tbl : list (list byte * Z) := Verbs.Lit.instance_info_verbs.
Definition vr_rowps : list Z :=
[0x22920; 0x22940; 0x22960; 0x22980; 0x229a0; 0x229c0; 0x229e0; 0x22a00; 0x22a20; 0x22a40].
Definition vr_rowp (j : nat) : Z := nth j vr_rowps 0.
Definition vr_rowlits : list (list byte) :=
[RO_lit_22920; RO_lit_22940; RO_lit_22960; RO_lit_22980; RO_lit_229a0; RO_lit_229c0; RO_lit_229e0;
 RO_lit_22a00; RO_lit_22a20; RO_lit_22a40].
Definition vr_rowlit (j : nat) : list byte := nth j vr_rowlits [].

Lemma vr_tbl_len : length vr_tbl = 10%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma vr_row_nth : forall j nmj led, nth_error vr_tbl j = Some (nmj, led) -> (j < 10)%nat.
Proof. intros j nmj led H. rewrite <- vr_tbl_len. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma vr_nz_of_forallb : forall l : list byte,
forallb (fun b : byte => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). cbv beta in H.
rewrite Z_to_bv_unsigned in H. vm_compute in H. discriminate H.
Qed.

(* each row: its name is the literal at the row's pointer, without the terminator; its ledger is 0 or 1 *)
Lemma vr_row_facts : forall j nmj led, nth_error vr_tbl j = Some (nmj, led) ->
(j < 10)%nat /\ (led = 0 \/ led = 1) /\ vr_rowlit j = nmj ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) nmj /\
(length nmj <= 15)%nat /\ 0x22920 <= vr_rowp j /\ vr_rowp j + 16 <= 0x22a50 /\
In (vr_rowp j + Z.of_nat (length nmj)) cmd_ro_ends /\
In (vr_rowp j, Z.of_nat (length (vr_rowlit j))) vr_shr.
Proof.
intros j nmj led H. pose proof (vr_row_nth j nmj led H) as Hj.
do 10 (destruct j as [|j]; [vm_compute in H; injection H as <- <-;
  split; [lia|]; split; [first [left; reflexivity | right; reflexivity]|];
  split; [vm_compute; reflexivity|]; split; [apply vr_nz_of_forallb; vm_compute; reflexivity|];
  split; [vm_compute; lia|]; split; [unfold vr_rowp; cbn [vr_rowps nth]; lia|];
  split; [unfold vr_rowp; cbn [vr_rowps nth]; lia|];
  split; [apply In_of_existsb; vm_compute; reflexivity|];
  vm_compute; repeat (first [left; reflexivity | right])
  |]).
lia.
Qed.

(* the table's bytes: the name pointer and the ledger word of row j *)
Lemma vr_tab_word : forall rd, abytes_atR rd 0xa5c40 RO_g_instance_info_verbs ->
forall j, (j < 10)%nat ->
aval_mem rd (0xa5c40 + 16 * Z.of_nat j) 8 (vr_rowp j) /\
aval_mem rd (0xa5c48 + 16 * Z.of_nat j) 4 (snd (nth j vr_tbl ([], 0))).
Proof.
intros rd H j Hj.
assert (HL : (160 <= length RO_g_instance_info_verbs)%nat) by (vm_compute; lia).
split; intros k Hk.
- replace (0xa5c40 + 16 * Z.of_nat j + Z.of_nat k) with (0xa5c40 + Z.of_nat (16 * j + k)) by lia.
  rewrite (H (16 * j + k)%nat) by lia. f_equal.
  do 10 (destruct j as [|j]; [do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
- replace (0xa5c48 + 16 * Z.of_nat j + Z.of_nat k) with (0xa5c40 + Z.of_nat (16 * j + 8 + k)) by lia.
  rewrite (H (16 * j + 8 + k)%nat) by lia. f_equal.
  do 10 (destruct j as [|j]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

Lemma vr_row_led : forall j nmj led, nth_error vr_tbl j = Some (nmj, led) -> snd (nth j vr_tbl ([], 0)) = led.
Proof. intros j nmj led H. rewrite (nth_error_nth _ _ _ H). reflexivity. Qed.

(* the literals of the names in cmd_ro_bytes *)
Lemma vr_row_bytes : forall rd, cmd_ro_ok rd -> forall j, (j < 10)%nat -> abytes_atR rd (vr_rowp j) (vr_rowlit j).
Proof.
intros rd [H _] j Hj. unfold cmd_ro_bytes in H.
repeat match goal with G : _ /\ _ |- _ => destruct G end.
do 10 (destruct j as [|j]; [cbn [vr_rowp vr_rowlit vr_rowps vr_rowlits nth]; assumption|]). lia.
Qed.

Lemma vr_tab_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0xa5c40 RO_g_instance_info_verbs.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat match goal with G : _ /\ _ |- _ => destruct G end. assumption.
Qed.

Lemma vr_tab_shr : In (0xa5c40, 160) vr_shr.
Proof. unfold vr_shr. apply in_or_app. right. left. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The model behind the scan *)
Lemma vr_route_tail : forall v args, vr_is_tail (VRR.route (v :: args)) = true ->
VRR.route (v :: args) = VRR.route_tail v args.
Proof.
intros v args H. cbv beta iota delta [VRR.route VRR.route_mid] in *.
repeat (match goal with |- context [if ?b then _ else _] =>
  destruct b; [cbn [vr_is_tail] in H; discriminate H|] end).
reflexivity.
Qed.

Lemma vr_ledger_app : forall v l1 l2,
Verbs.ledger_of v (l1 ++ l2) = match Verbs.ledger_of v l1 with Some x => Some x | None => Verbs.ledger_of v l2 end.
Proof.
intros v l1 l2. induction l1 as [|[nm ld] l1 IH]; [reflexivity|].
cbn [app Verbs.ledger_of]. destruct (Verbs.list_eqb v nm); [reflexivity | exact IH].
Qed.

Lemma vr_firstn_S : forall {A} (l : list A) (d : A) n, (n < length l)%nat ->
firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l d. induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
destruct n as [|n]; cbn [firstn nth length app] in *; [reflexivity|].
rewrite (IH n ltac:(lia)). reflexivity.
Qed.

Lemma vr_ledger_miss : forall v j nmj led, Verbs.ledger_of v (firstn j vr_tbl) = None ->
nth_error vr_tbl j = Some (nmj, led) -> v <> nmj -> Verbs.ledger_of v (firstn (S j) vr_tbl) = None.
Proof.
intros v j nmj led H Hn Hne. pose proof (vr_row_nth j nmj led Hn) as Hj.
rewrite (vr_firstn_S vr_tbl ([], 0) j) by (rewrite vr_tbl_len; exact Hj).
rewrite vr_ledger_app, H. rewrite (nth_error_nth _ _ ([], 0) Hn). cbn [Verbs.ledger_of].
destruct (Verbs.list_eqb v nmj) eqn:E; [apply Verbs.list_eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma vr_ledger_hit : forall v j nmj led, Verbs.ledger_of v (firstn j vr_tbl) = None ->
nth_error vr_tbl j = Some (nmj, led) -> v = nmj -> Verbs.ledger_of v vr_tbl = Some led.
Proof.
intros v j nmj led H Hn Heq. pose proof (vr_row_nth j nmj led Hn) as Hj.
rewrite <- (firstn_skipn (S j) vr_tbl), vr_ledger_app.
rewrite (vr_firstn_S vr_tbl ([], 0) j) by (rewrite vr_tbl_len; exact Hj).
rewrite vr_ledger_app, H. rewrite (nth_error_nth _ _ ([], 0) Hn). cbn [Verbs.ledger_of].
replace (Verbs.list_eqb v nmj) with true by (symmetry; apply Verbs.list_eqb_eq; exact Heq). reflexivity.
Qed.

Lemma vr_ledger_all : forall v, Verbs.ledger_of v (firstn 10 vr_tbl) = None -> Verbs.ledger_of v vr_tbl = None.
Proof. intros v H. rewrite <- (firstn_all vr_tbl), vr_tbl_len. exact H. Qed.

(* the step of a message whose route is the ledger call *)
Lemma vr_led_model : forall R D led, VRR.route (Verbs.toks D) = VRR.RLedger led -> Verbs.toks D <> [] ->
vr_h R D = (sup_instance_verb_m R (Verbs.line D) led, false) /\
vr_k1 R D = 2 + EV_SUP_INSTANCE_VERB R.
Proof.
intros R D led Hr Hne.
destruct (Verbs.toks D) as [|v args] eqn:Et; [exfalso; exact (Hne eq_refl)|].
assert (Hst : vr_st D = Verbs.SCall (Verbs.sup_instance_verb (Verbs.line D) led)).
{ unfold vr_st, Verbs.receive. rewrite Et. cbn [fst].
  rewrite (VRR.plan_route atoi_a (Verbs.line D) (v :: args)) by discriminate.
  rewrite Hr. reflexivity. }
split.
- unfold vr_h. rewrite Hst. reflexivity.
- unfold vr_k1. rewrite Hst, Et. unfold ev_route.
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:Ec.
  { apply Verbs.list_eqb_eq in Ec. subst v. vm_compute in Hr. discriminate Hr. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:Ep.
  { apply Verbs.list_eqb_eq in Ep. subst v. vm_compute in Hr. discriminate Hr. }
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Bounds *)
Lemma vr_line_le : forall D, (length (Verbs.line D) <= length (Verbs.upto0 D))%nat.
Proof.
intros D. unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (VRR.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as L. rewrite length_rev in L. exact L.
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

Lemma vr_s1_facts : forall e, vr_sp0 e mod 16 = 0 ->
vr_s1 e mod 16 = 0 /\ vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ (vr_s1 e - vr_sp0 e) mod 16 = 0.
Proof.
intros e H. unfold vr_s1. set (sp := vr_sp0 e) in *.
pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as M.
pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as D.
pose proof (Z.div_mod sp 16 ltac:(lia)) as D2.
set (q := (sp - 192) / 32) in *. set (r := (sp - 192) mod 32) in *.
split; [|split].
- replace (sp - 192 - r) with ((2 * q) * 16) by lia. apply Z.mod_mul. lia.
- lia.
- replace (sp - 192 - r - sp) with ((2 * q - sp / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* memory that agrees below the allocation ceiling and from lo up *)
Definition vr_kept (W : world SEGS) (m m' : word -> option byte) (lo : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ lo <= a) -> rdW W m' a = rdW W m a.

Lemma vr_kept_refl : forall W m lo, vr_kept W m m lo.
Proof. intros W m lo a _ _. reflexivity. Qed.

Lemma vr_kept_trans : forall W m1 m2 m3 lo, vr_kept W m1 m2 lo -> vr_kept W m2 m3 lo -> vr_kept W m1 m3 lo.
Proof. intros W m1 m2 m3 lo H1 H2 a Ha Hb. rewrite (H2 a Ha Hb). exact (H1 a Ha Hb). Qed.

Lemma vr_kept_of_win : forall W m m' wl wh lo, alloc_ceiling <= wl -> wh <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wh) -> rdW W m' a = rdW W m a) -> vr_kept W m m' lo.
Proof. intros W m m' wl wh lo H1 H2 H a Ha Hb. apply H; [exact Ha | lia]. Qed.

Lemma vr_aval_kept : forall W m m' lo a n v, vr_kept W m m' lo -> aval_mem (rdW W m) a n v ->
0 <= a -> (a + Z.of_nat n <= alloc_ceiling \/ lo <= a) -> a + Z.of_nat n <= 2 ^ 64 -> aval_mem (rdW W m') a n v.
Proof.
intros W m m' lo a n v K H Ha Hb Hc. apply (aval_mem_agree _ _ a n v H). intros k Hk. apply K; lia.
Qed.

Lemma vr_bytes_kept : forall W m m' lo a l, vr_kept W m m' lo -> abytes_atR (rdW W m) a l ->
0 <= a -> (a + Z.of_nat (length l) <= alloc_ceiling \/ lo <= a) -> a + Z.of_nat (length l) <= 2 ^ 64 ->
abytes_atR (rdW W m') a l.
Proof.
intros W m m' lo a l K H Ha Hb Hc. apply (abytes_atR_agree _ _ a l (Z.of_nat (length l)) H); [lia|].
intros k Hk. apply K; lia.
Qed.

Lemma vr_str_kept : forall W m m' lo a s, vr_kept W m m' lo -> astr_atR (rdW W m) a s ->
0 <= a -> (a + Z.of_nat (length s) + 1 <= alloc_ceiling \/ lo <= a) -> a + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
astr_atR (rdW W m') a s.
Proof.
intros W m m' lo a s K H Ha Hb Hc. apply (astr_atR_agree _ _ a s (Z.of_nat (length s) + 1) H); [lia|].
intros k Hk. apply K; lia.
Qed.

Lemma vr_frames_own : forall STK sp0 FP ly S W mem md pos lyc Sc Wc memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md [(4, pos)] lyc Sc Wc memc mdc k -> In (4, pos) (frames Sc).
Proof.
intros STK sp0 FP ly S W mem md pos lyc Sc Wc memc mdc k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity.
Qed.

Lemma vr_frame_bounds : forall lyc Sc Wc memc mdc pos,
AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) ->
4096 <= frame_addr lyc 4 pos /\ frame_addr lyc 4 pos + 1024 <= alloc_ceiling /\
shadow_addr (frame_addr lyc 4 pos) + 128 <= alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc pos HAR Hin.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & _).
assert (E : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E in H2.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
set (F := frame_addr lyc 4 pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* the parts of a boundary state that do not mention the registers or the allocator state, carried to a memory
   that agrees below the ceiling and from the realigned stack pointer up *)
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RECC : vr_rec_cells B.
Hypothesis RRO : vr_relro_img.

Lemma vr_env_kept : forall lyc Sc W mem mem' md' lo, AR SEGS B lyc Sc W mem' md' ->
vr_env B W mem -> vr_kept W mem mem' lo -> vr_env B W mem'.
Proof.
intros lyc Sc W mem mem' md' lo HAR (HRO & HGOT & _ & _ & _ & _) K.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HRO' : arodata_okP SEGS RLO RHI B (rdW W mem')).
{ intros a Hro Ho He. assert (Hi : in_img SEGS a).
  { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. }
  pose proof (pa_img_range a Hi). rewrite (K a) by lia. exact (HRO a Hro Ho He). }
destruct (RECC _ _ _ _ _ HAR) as (Hfl & Hg & Her).
split; [exact HRO'|]. split.
{ destruct HGOT as (G1 & G2 & G3 & G4). unfold A_G_REC, A_G_QUITTING in *.
  split; [|split; [|split]]; (eapply vr_aval_kept; [exact K | eassumption | lia | left; cbn; lia | cbn; lia]). }
split; [exact (ROA _ _ _ _ _ HAR HRO')|].
split; [exact Hg|]. split; [exact Hfl | exact Her].
Qed.

Lemma vr_rec_kept : forall lyc Sc W mem mem' md lo R O, AR SEGS B lyc Sc W mem md ->
rec_repA B lyc Sc (rdW W mem) R O -> vr_kept W mem mem' lo -> rec_repA B lyc Sc (rdW W mem') R O.
Proof.
intros lyc Sc W mem mem' md lo R O HAR HR K.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
apply (rec_repA_agree B _ _ _ _ _ _ R O HR (fun pn _ Hb => Hb)).
- intros k Hk. apply K; unfold A_G_REC, REC_SIZE in *; lia.
- intros k Hk. apply K; unfold A_REC_SPILL, SC_SIZE in *; lia.
- intros [p n] Hpn k Hk. cbn [fst snd] in *.
  pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HR Hpn) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. apply K; lia.
Qed.

Lemma vr_core_kept : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc regs' mem' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
vr_kept W memc mem' (vr_s1 e) ->
Forall (fun ov => 0 <= fst ov <= 200) sl ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc regs' mem' md'
(HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit) HJ' K Hsl Hrv'.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (vr_s1_facts e Hal16) as (_ & Hs1 & _).
pose proof (vr_frames_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
split; [exact HJ'|]. split; [exact Hkk|]. split; [exact Hmeter|]. split; [exact Hnm|].
split.
{ destruct Hframe as (HF & Hfl & Hsh). subst F.
  destruct (vr_frame_bounds _ _ _ _ _ pos HAR Hin4) as (B1 & B2 & B3).
  split; [reflexivity|]. split.
  - rewrite (rdword_ext (rdW W memc) (rdW W mem')); [exact Hfl|]. intros kk Hkk'. apply K; lia.
  - intros i Hi. rewrite (K (shadow_addr (frame_addr lyc 4 pos) + Z.of_nat i)) by (unfold shadow_addr, SHADOW_OFF in *; lia).
    exact (Hsh i Hi). }
split; [exact Hrv'|].
split.
{ intros j r Hj. assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length vr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
  eapply vr_aval_kept; [exact K | exact (Hsaved j r Hj) | unfold vr_sp0 in *; lia | right; unfold vr_sp0 in *; lia | unfold vr_sp0 in *; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill, Hsl |- *. intros ov Hov.
  pose proof (Hsl ov Hov) as Hb.
  eapply vr_aval_kept; [exact K | exact (Hspill ov Hov) | unfold vr_sp0 in *; lia | right; lia | unfold vr_sp0 in *; lia]. }
split; [exact (vr_env_kept _ _ _ _ _ _ _ HAR' Henv K)|].
split; [exact (vr_rec_kept _ _ _ _ _ _ _ _ _ HAR Hrec K)|].
split; [exact HdO|]. split; [exact Hperm|].
eapply vr_aval_kept; [exact K | exact Hquit | unfold A_G_QUITTING; lia | left; unfold A_G_QUITTING; cbn; lia | unfold A_G_QUITTING; cbn; lia].
Qed.

Lemma vr_core_blocks : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc b,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc ->
In b tmps -> In b (ablocks B lyc Sc).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs memc mdc b
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm & _) Hb.
apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hb.
Qed.

Lemma vr_line_kept : forall e q lyc Sc W mem md mem' lo, AR SEGS B lyc Sc W mem md ->
vr_ent B MT e -> In (vr_lb e q) (ablocks B lyc Sc) ->
vr_line B e q W mem -> vr_kept W mem mem' lo -> vr_line B e q W mem'.
Proof.
intros e q lyc Sc W mem md mem' lo HAR Hent Hin (Hfr & Hs) K.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
split; [exact Hfr|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _). cbn [fst snd] in *.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HlenD & _).
pose proof (vr_line_le (e_D e)) as L1.
pose proof (verbs_receive_pre.strnlen_upto (e_D e)) as [_ L2].
rewrite HlenD in L2. unfold vr_l in Hc.
pose proof (req_size_pos (StrFun.strnlen_res (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hrq].
eapply vr_str_kept; [exact K | exact Hs | lia | left; lia | lia].
Qed.

Lemma vr_copy_kept : forall e F c tp pos lyc Sc W mem md mem' lo, AR SEGS B lyc Sc W mem md ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp W mem -> vr_kept W mem mem' lo -> vr_copy B e F c tp W mem'.
Proof.
intros e F c tp pos lyc Sc W mem md mem' lo HAR Hin4 HF Hin (Hfr & Hal & Hlen & Hptr & Hw) K.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct (vr_frame_bounds _ _ _ _ _ pos HAR Hin4) as (B1 & B2 & _). rewrite <- HF in B1, B2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _). cbn [fst snd] in *.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat).
{ unfold Verbs.toks. rewrite length_firstn. unfold Verbs.line_words_max. lia. }
split; [exact Hfr|]. split; [exact Hal|]. split; [exact Hlen|]. split.
- intros i p Hi. assert (Hi64 : (i < 64)%nat) by (rewrite <- Hlen in Htk; pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)); lia).
  eapply vr_aval_kept; [exact K | exact (Hptr i p Hi) | lia | left; lia | lia].
- intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2). split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
  eapply vr_str_kept; [exact K | exact Hs | lia | left; lia | lia].
Qed.

Lemma vr_spill_get : forall e W m sl o v, vr_spill e W m sl -> In (o, v) sl -> aval_mem (rdW W m) (vr_s1 e + o) 8 v.
Proof. intros e W m sl o v H Hin. unfold vr_spill in H. rewrite Forall_forall in H. exact (H (o, v) Hin). Qed.


(* the zero shadow of g_instance_info_verbs, granule i *)
Hypothesis SHOK : vr_shadow_ok B.
Lemma vr_tab_shadow0 : forall lyc Sc W mem md i, AR SEGS B lyc Sc W mem md -> 0 <= i < 20 ->
rdW W mem (SHADOW_OFF + 0x14b88 + i) = Some 0.
Proof.
intros lyc Sc W mem md i HAR Hi. destruct (SHOK _ _ _ _ _ _ _ HAR vr_tab_shr) as [HRA _].
destruct (HRA (0xa5c40 + 8 * i + 7) ltac:(lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs.
assert (E1 : (0xa5c40 + 8 * i + 7) / 8 = 0x14b88 + i) by (symmetry; apply Z.div_unique with (r := 7); lia).
assert (E2 : (0xa5c40 + 8 * i + 7) mod 8 = 7) by (symmetry; apply Z.mod_unique with (q := 0x14b88 + i); lia).
rewrite E1, Z.add_assoc in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | [Hm Hs8]]; [reflexivity|]. rewrite E2 in Hm. lia.
Qed.

End e.
End f.
End d.
