(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared part of descriptors_panel_get's ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan, 0x8ccfc, 22 instructions), re-made at B's addresses from the ASan walk's segments lib/A/Prog/descriptors_panel_get_s1.v .. _s8.v (a working branch 2db68b2223b); the recorder-state transports copied from its _s2.v. *)

(* descriptors_panel_get on B (recorder.c:554-560; listing slots AF_descriptors_panel_get + 0x0 .. + 0x54):
     +0x00 addi sp,sp,-32   +0x04 sd ra,24(sp)   +0x08 sd s0,16(sp)   +0x0c sd s1,8(sp)
     +0x10 mv s0,a0         +0x14 li a0,24       +0x18 jal record                       (PCall CS_record)
     +0x1c mv s1,a0         +0x20 mv a1,s0       +0x24 jal arg_s                        (PCall CS_arg_s)
     +0x28 auipc a0 / +0x2c addi a0 (PHi 205 / PAddHi .. (A_OBJ 88): a0 = 0x21fc0, "panel_get")
     +0x30 li a1,9          +0x34 jal rec_shape_of                                  (PCall CS_rec_shape_of)
     +0x38 mv a1,a0         +0x3c mv a0,s1       +0x40 li a2,0
     +0x44 ld ra,24(sp)     +0x48 ld s0,16(sp)   +0x4c ld s1,8(sp)   +0x50 addi sp,sp,32
     +0x54 j answer                                                                  (PTail CS_answer)
   No branch, no inline ASan check, no UBSan trap, no load or store through an auipc base: the only memory accesses
   are the frame's stores and loads. This file gives:
   - the verb "panel_get" (RO_lit_21fc0 without its terminator) as rec_shape_of's string argument, through
     astr_argA's read-only arm (cmd_addr_b / cmd_hull_b by computation, the end 0x21fc9 in cmd_ro_ends), and the
     model's step (descriptors_panel_get_m as rec_answer of the recorded call with the verb's shape, changes = 0);
   - the call targets SIG CS_<f> = BASE + AF_<f>, A_OBJ 88 = 0x21fc0, the statement's footprint;
   - the symbolic seeds: at the entry (the 32-byte frame writable), between calls (registers only), and at the return
     from rec_shape_of (the frame holding the entry's ra, s0, s1, read by the epilogue);
   - the recorder-state transports (rec_repA across writes outside g_rec, record.spill and the recorder's blocks)
     and the block facts of the walk's points;
   - the assembly of the contract's post (dpgb_post_of) and the statements of the walk's two later segments:
     dpgb_A_stmt at the call of arg_s (0x8cd20) and dpgb_R_stmt at the call of rec_shape_of (0x8cd30). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c hand_back_c mix_call_c answer_c descriptors_panel_get_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the verb ---------- *)

(* the verb's bytes "panel_get" at 0x21fc0 (RO_lit_21fc0 without its terminator) *)
Definition dpgb_verb : list byte := map (Z_to_bv 8) [112; 97; 110; 101; 108; 95; 103; 101; 116].
Lemma dpgb_verb_bstr : dpgb_verb = bstr "panel_get".
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_verb_lit : dpgb_verb ++ [Z_to_bv 8 0] = RO_lit_21fc0.
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_verb_len : length dpgb_verb = 9%nat.
Proof. reflexivity. Qed.
Lemma dpgb_fits : fits (shape_of dpgb_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* the model's step: rec_stub of the call (24, [x]) with the shape of "panel_get" and changes = 0
   (lib/Prog/RecModel.v:171) *)
Lemma dpgb_model : forall R x, descriptors_panel_get_m R (Some x) =
rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpgb_verb) false.
Proof. intros R x. unfold descriptors_panel_get_m, rec_stub, daemon_shape. rewrite <- dpgb_verb_bstr. reflexivity. Qed.

(* ---------- small list facts ---------- *)

Lemma dpgb_abytes_prefix : forall rd a (l1 l2 : list byte), abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
Qed.
(* a register index as a 5-bit literal *)
Lemma dpgb_z5 : forall (rr : bv 5) r, bv_unsigned rr = r -> Z_to_bv 5 r = rr.
Proof. intros rr r <-. apply Z_to_bv_bv_unsigned. Qed.
(* a member of a filtered list is a member of the list (the filter of answer's footprint) *)
Lemma dpgb_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
destruct (fst a =? old); [destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H)].
Qed.
(* a range of addresses outside every range of a list *)
Lemma dpgb_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi H a Ha HE. apply Exists_exists in HE as (r & Hr & Hin). rewrite forallb_forall in H.
specialize (H r Hr). unfold in_zr in Hin. apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* g_rec, record.spill and the verb literal lie outside every range of the record's owned statics (closed checks) *)
Lemma dpgb_grec_out : forallb (fun r => (0x5e32c0 + 960 <=? fst r) || (fst r + snd r <=? 0x5e32c0)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_spill_out : forallb (fun r => (0x5e3760 + 56 <=? fst r) || (fst r + snd r <=? 0x5e3760)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_verb_out : forallb (fun r => (0x21fc0 + 10 <=? fst r) || (fst r + snd r <=? 0x21fc0)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.


Lemma dpgb_req_ge : forall x, 0 <= x -> 1 <= req_size x /\ x <= req_size x.
Proof. intros x Hx. unfold req_size. destruct (Z.eqb_spec x 0); lia. Qed.

(* ---------- the program's own statics and record()'s slot ---------- *)

(* the program's own writable statics, as the record lists them (CmdBSyms' ts_prog : as_prog_static B =
   TFIB_PROG_STATIC, lib/B/YF0m.v), a base and a length *)
Lemma dpgb_in_PG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.
(* the slot record() returns (record_c.v's rec_slot): a 56-byte call of g_rec's table, or record.spill *)
Lemma dpgb_slot_ok : forall R, (length (r_calls R) <= 16)%nat ->
A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + 16 <= A_REC_SPILL + SC_SIZE /\ rec_slot R mod 8 = 0 /\
((rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/
 rec_slot R = A_REC_SPILL).
Proof.
intros R HL. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, REC_SIZE, OFF_ANSWER.
  split; [lia|]. split; [lia|]. split; [|left; lia].
  match goal with |- ?e mod 8 = 0 =>
    replace e with ((771674 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia end.
  apply Z_mod_mult.
- unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE. split; [lia|]. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.
Lemma dpgb_slot_PG : forall c a, A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) -> c <= a < c + 16 ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros c a H1 H2 [H3 | ->] Ha; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma dpgb_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma dpgb_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma dpgb_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (dpgb_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma dpgb_acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (dpgb_aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (dpgb_aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (dpgb_rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma dpgb_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
End t.

(* rd' agrees with rd on every byte arep_at reads (g_rec, record.spill and the recorder's blocks of Q), except the
   bytes Wr that a step wrote *)
Definition dpgb_rd_kept (Q : rlay) (rd rd' : reader) (Wr : Z -> Prop) : Prop :=
forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
           (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn)) -> ~ Wr a -> rd' a = rd a.

Ltac dpgb_lia := cbv beta in *;
unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, CALL_SIZE, CALL_OFF_FN,
CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.

(* the recorder's blocks lie outside g_rec and record.spill (ag1_own) *)
Lemma dpgb_rd_blk : forall bl (rd rd' : reader) R Q (Wr : Z -> Prop), arep_at bl rd A_G_REC A_REC_SPILL R Q ->
dpgb_rd_kept Q rd rd' Wr ->
(forall a, Wr a -> (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)) ->
forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).
Proof.
intros bl rd rd' R Q Wr HA Hk HW pn i Hpn Hi. unfold dpgb_rd_kept in Hk.
destruct HA as (_ & _ & _ & _ & _ & _ & _ & (_ & Hap)).
destruct (Hap pn Hpn) as [H1 H2].
apply Hk.
- right. right. exists pn. split; [exact Hpn | lia].
- intro Hw. destruct (HW _ Hw) as [Hw' | Hw']; unfold iv_apart in H1, H2; lia.
Qed.

Lemma dpgb_tail_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd' A_G_REC R.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hg HbQ.
unfold lay_blocks in HblQ, HbQ.
destruct HA as (_ & _ & _ & _ & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & _).
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (dpgb_aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (dpgb_rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (dpgb_aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (dpgb_aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (dpgb_rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (dpgb_aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [apply (dpgb_aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (dpgb_aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

Lemma dpgb_slot_kept : forall bl bl' (rd rd' : reader) R Q i c P,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall pn j, In pn (lay_blocks Q) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
(forall j, 0 <= j < CALL_SIZE -> rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + j) =
  rd (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + j)) ->
acall_at bl' rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros bl bl' rd rd' R Q i c P HA HblQ HbQ Hc Hp Hsl.
destruct HA as (_ & _ & _ & (_ & _ & _ & C4 & _ & _) & _).
destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof HC as (_ & HL6 & _).
apply (dpgb_acall_at_kept bl _ rd); [exact HC | | |].
- intros pn Hpn. apply HblQ. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
  split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- intros j Hj. apply Hsl. unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
- intros pn j Hpn Hj. apply HbQ; [|exact Hj]. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
  split; [exact (nth_error_In _ _ Hp) | exact Hpn].
Qed.

Lemma dpgb_spill_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall pn j, In pn (lay_blocks Q) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
(forall j, 0 <= j < SC_SIZE -> rd' (A_REC_SPILL + j) = rd (A_REC_SPILL + j)) ->
acall_at bl' rd' A_REC_SPILL (r_spill R) (l_spill Q) /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd (r_spill R)).
Proof.
intros bl bl' rd rd' R Q HA HblQ HbQ Hsl.
destruct HA as (_ & _ & _ & (_ & _ & _ & _ & C5 & C6) & _).
split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (dpgb_acall_at_kept bl _ rd); [exact C5 | | |].
- intros pn Hpn. apply HblQ. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
- intros j Hj. apply Hsl. unfold CALL_OFF_ARGS, SC_SIZE in *. lia.
- intros pn j Hpn Hj. apply HbQ; [|exact Hj]. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
Qed.

Lemma dpgb_arep_kept : forall bl bl' rd rd' R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
dpgb_rd_kept Q rd rd' (fun _ => False) -> arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA Hin Hk.
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpgb_rd_blk bl rd rd' R Q _ HA Hk). intros a []. }
unfold dpgb_rd_kept in Hk.
assert (Hg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; exact Ha | intros []]. }
assert (Hs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [right; left; exact Ha | intros []]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hg. dpgb_lia. }
destruct (dpgb_tail_kept bl bl' rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
unfold arep_at, ag1_calls.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown]]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (dpgb_aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hg; dpgb_lia]|].
split; [| apply (dpgb_spill_kept bl bl' rd rd' R Q HA Hin HbQ); intros j Hj; apply Hs; lia].
intros i c P Hc Hp. apply (dpgb_slot_kept bl bl' rd rd' R Q i c P HA Hin HbQ Hc Hp).
intros j Hj. apply Hg.
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)). dpgb_lia.
Qed.

Lemma dpgb_answer_ptr : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (match l_answer Q with Some pn => fst pn | None => 0 end).
Proof.
intros bl rd R Q (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
destruct (r_answer R), (l_answer Q); try contradiction.
all: first [exact Ha | exact (proj1 Ha)].
Qed.

(* ---------- B's frame and the symbolic states ---------- *)

(* the 32-byte frame: ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24 (sp0 the entry's sp) *)
Definition DPGB_FRAME : Z := 32.
Definition dpgb_saved : list Z := [1; 8; 9].
Definition dpgb_extra (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) dpgb_saved.
(* listing offsets: the return points of the calls of record (0x8cd18), arg_s (0x8cd24) and rec_shape_of (0x8cd34) *)
Definition DPGB_RET_REC : Z := AF_descriptors_panel_get + 0x1c.
Definition DPGB_RET_ARG : Z := AF_descriptors_panel_get + 0x28.
Definition DPGB_RET_R : Z := AF_descriptors_panel_get + 0x38.
(* the frame after the prologue, read only: atoms 32, 33, 34 are the entry's ra, s0, s1 *)
Definition dpgb_frame_r : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
[YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition dpgb_tfacts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* the entry: the frame below sp writable *)
Definition ssb_entry : sstate := mkSS AF_descriptors_panel_get sr_atoms [stack_region DPGB_FRAME] None dpgb_tfacts.
(* the return from rec_shape_of: only the frame is read, by the epilogue's restores *)
Definition ssb_tail : sstate := mkSS DPGB_RET_R sr_atoms [dpgb_frame_r] None dpgb_tfacts.
(* a return point where the code next touches only registers (after record and after arg_s) *)
Definition ssb_reg (k : Z) : sstate := mkSS k sr_atoms [] None (mkFacts [] [] []).

Lemma dpgb_saved_range : forall j r, nth_error dpgb_saved j = Some r -> 0 <= r < 32.
Proof.
intros j r Hj.
assert (H32 : Forall (fun x => 0 <= x < 32) dpgb_saved) by (unfold dpgb_saved; repeat constructor; lia).
rewrite Forall_forall in H32. apply H32. eapply nth_error_In. exact Hj.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Lemma dpgb_val_mem : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hv. unfold aview in Hv.
unfold val_mem.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hv. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

(* the verb's address: the listing's object atom 88 (0x8cd28 `PAddHi a0 a0 205 (A_OBJ 88) 0`) *)
Lemma dpgb_obj88 : cmd_val_objs (PI := PI) -> VAL (A_OBJ 88) = 0x21fc0.
Proof. intros V. rewrite (V 88%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* ---------- the seeds ---------- *)

(* the entry: the prologue stores ra, s0, s1 into [sp - 32, sp) *)
Lemma dpgb_entry_seed : forall (W : world SEGS) mem (regs1 : bvmap 5 word) Bx,
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
(forall a, spZ regs1 - DPGB_FRAME <= a < spZ regs1 -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) ssb_entry
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AF_descriptors_panel_get)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx [] (Eimg (Ereg regs1 [])) (mrestrict (w_H W) mem).
Proof.
intros W mem regs1 Bx Hsp Hsp16 Hpres.
set (E := Eimg (Ereg regs1 [])).
assert (E2 : bv_unsigned (ew E 2) = spZ regs1).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 [] 2%nat 2%bv eq_refl). reflexivity. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ssb_entry. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. unfold DPGB_FRAME. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold DPGB_FRAME. lia. }
  constructor.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok, dpgb_tfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp16 | lia].
Qed.

(* a return point where only registers are read next: no region, no fact *)
Lemma dpgb_reg_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem k Bx,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ssb_reg k)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem k Bx. split; [| apply Forall_nil].
rewrite restrict_mkst_fx. unfold ssb_reg. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I | split; exact I].
Qed.

(* the return from rec_shape_of (0x8cd34): the frame holds the entry's ra, s0, s1 *)
Lemma dpgb_tail_seed : forall (W : world SEGS) mem (regs1 regs : bvmap 5 word) Bx,
2 ^ 46 <= spZ regs1 <= 2 ^ 47 - 32 -> spZ regs1 mod 16 = 0 ->
(forall j r, nth_error dpgb_saved j = Some r ->
 aval_mem (rdW W mem) (spZ regs1 + 24 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dpgb_extra regs))) ssb_tail
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DPGB_RET_R)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx [] (Eimg (Ereg regs1 (dpgb_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros W mem regs1 regs Bx Hsp Hsp16 HFR.
set (E := Eimg (Ereg regs1 (dpgb_extra regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (dpgb_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ssb_tail. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dpgb_frame_r. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (HC : forall j off, (j < 3)%nat -> off = 24 - 8 * Z.of_nat j ->
    YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (spZ regs1) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
  { intros j off Hj ->.
    destruct (nth_error dpgb_saved j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; cbn in Hr; lia].
    apply (chunk_ok_val SEGS E _ (spZ regs1) (24 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
    - cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned, (EX j ltac:(lia)).
      assert (Hx : nth_error (dpgb_extra regs) j = Some (getr regs (Z_to_bv 5 r)))
        by (unfold dpgb_extra; rewrite nth_error_map, Hr; reflexivity).
      rewrite (nth_error_nth _ _ _ Hx). reflexivity.
    - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HR.
    - cbn. lia.
    - change (N.to_nat 8) with 8%nat. replace (spZ regs1 + (24 - 8 * Z.of_nat j)) with (spZ regs1 + 24 - 8 * Z.of_nat j) by lia.
      apply dpgb_val_mem. exact (HFR j r Hr). }
  apply Forall_cons; [exact (HC 0%nat 24 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 1%nat 16 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 2%nat 8 ltac:(lia) eq_refl)|].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok, dpgb_tfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp16 | lia].
Qed.

(* the frame the prologue wrote, as the symbolic state's stack region holds it *)
Lemma dpgb_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (- DPGB_FRAME) 0 (- DPGB_FRAME) 0 cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error dpgb_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
forall j r, nth_error dpgb_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E m sp0 regs cs HR Hsp HE HIn j r Hj.
pose proof (dpgb_saved_range j r Hj) as Hr32.
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2%nat sp0 cs (- DPGB_FRAME) 0 (- DPGB_FRAME) 0 (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

Lemma dpgb_aval_mem : forall (W : world SEGS) mem a n v,
val_mem SEGS (mrestrict (w_H W) mem) a n v -> aval_mem (rdW W mem) a n v.
Proof.
intros W mem a n v H k Hk. unfold aview. rewrite (H k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HB : CmdBSyms B.
(* a Theorem Labs lane's CmdRecRest.v `cmd_sig_prog_PB` (lib/B/Prog/CmdObj.v:44's cmd_sig_prog), for the abstract instance *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
(* a Theorem Labs lane's CmdRecRo.v `CMD_RO_IN` (lib/B/Prog/CmdRo.v:452): the verb literal's bytes are read-only *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).
(* a Theorem Labs lane's CmdRecRest.v `cmd_prog_img` and `cmd_ro_prog_apart`, in their B forms *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* ---------- the call targets ---------- *)

Lemma dpgb_sig_arg : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dpgb_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (cmd_sig_prog_PB CS_rec_shape_of ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dpgb_sig_ans : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (cmd_sig_prog_PB CS_answer ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* ---------- g_rec and record.spill ---------- *)

(* their bytes are outside the runtime's owned statics and the errno cell *)
Lemma dpgb_unowned : forall a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO.
destruct Ha as [Ha | Ha]; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; split.
- exact (dpgb_not_in_ranges _ 0x5e32c0 (0x5e32c0 + 960) dpgb_grec_out a Ha).
- clear - Ha. lia.
- exact (dpgb_not_in_ranges _ 0x5e3760 (0x5e3760 + 56) dpgb_spill_out a Ha).
- clear - Ha. lia.
Qed.

(* a store to g_rec or record.spill is one a journal over the statement's footprint allows *)
Lemma dpgb_awr_slot : forall STK sp0 O bl0 blc fr0 ly own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
  bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha. right; right; right; right. left.
split; [|split].
- destruct Ha as [Ha | Ha];
  [ exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
  | exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia] ].
- rewrite (ts_prog B HB). exact (dpgb_in_PG a Ha).
- apply cmd_prog_img. exact (dpgb_in_PG a Ha).
Qed.

(* ---------- the verb as rec_shape_of's string argument ---------- *)

Lemma dpgb_verb_addr : cmd_addr_b 0x21fc0 10 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_verb_hull : cmd_hull_b 0x21fc0 10 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dpgb_verb_end : In (0x21fc0 + 9) cmd_ro_ends.
Proof.
assert (Hb : existsb (Z.eqb (0x21fc0 + 9)) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (e & He & Heq). apply Z.eqb_eq in Heq. rewrite Heq. exact He.
Qed.

(* astr_argA's read-only arm for "panel_get" (lib/B/Prog/CmdRep.v:139-150) *)
Lemma dpgb_verb_argA : forall ly S rd O, abytes_atR rd 0x21fc0 RO_lit_21fc0 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O 0x21fc0 (Some dpgb_verb).
Proof.
intros ly S rd O HL. unfold astr_argA. cbv zeta. rewrite dpgb_verb_len. change (Z.of_nat 9) with 9.
change (9 + 1) with 10.
split; [lia|]. split.
{ split; [rewrite dpgb_verb_lit; exact HL|].
  unfold dpgb_verb. cbn [map In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. }
split; [unfold LMAX; lia|]. right. split; [|split; [exact dpgb_verb_addr | split; [exact dpgb_verb_hull | exact dpgb_verb_end]]].
intros i Hi. split; [|split].
- clear - CMD_RO_IN Hi. unfold cmd_ro_in in CMD_RO_IN.
  repeat match type of CMD_RO_IN with
  | (forall i, 0 <= i < 10 -> _ (0x21fc0 + i)) /\ _ => exact (proj1 CMD_RO_IN i Hi)
  | _ /\ _ => apply proj2 in CMD_RO_IN
  end.
- rewrite (ts_owned B HB). exact (dpgb_not_in_ranges _ 0x21fc0 (0x21fc0 + 10) dpgb_verb_out (0x21fc0 + i) ltac:(clear - Hi; lia)).
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.

(* the literal in cmd_ro_ok *)
Lemma dpgb_lit : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21fc0 RO_lit_21fc0.
Proof.
intros rd HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21fc0 _ /\ _ => exact (proj1 HRO)
| abytes_atR _ 0x21fc0 _ => exact HRO
| _ /\ _ => apply proj2 in HRO
end.
Qed.

(* rec_shape_of's string premise (rec_shape_of_c.v:88-92) for the verb at the call (0x8cd30) *)
Lemma dpgb_verb_pre : forall ly S rd, cmd_ro_ok rd ->
Z.of_nat (length dpgb_verb) <= 16 ->
abytes_atR rd 0x21fc0 dpgb_verb /\
(in_blockA (ablocks B ly S) 0x21fc0 (Z.of_nat (length dpgb_verb)) \/
 astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21fc0 (Some dpgb_verb)).
Proof.
intros ly S rd HRO _. pose proof (dpgb_lit _ HRO) as HL. split.
- apply (dpgb_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite dpgb_verb_lit. exact HL.
- right. exact (dpgb_verb_argA ly S rd [] HL).
Qed.

(* astr_argA reads its reader only through the string's bytes *)
Lemma dpgb_argA_rd : forall ly S rd rd' O p x, astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S rd rd' O p x H Hk. unfold astr_argA in *. cbv zeta in *.
destruct H as (H0 & [Hb Hnz] & Hl & Harm). split; [exact H0|]. split; [|split; [exact Hl | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

(* the bytes of such a string lie in a heap block or in the image *)
Lemma dpgb_argA_bound : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md -> 0 <= p ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md rd O p x HAR Hp H i Hi. unfold astr_argA in H. cbv zeta in H.
pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [((pb & kb & Hin & Hlo & Hhi) & _) | (Hro & _)]).
- destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Rk]. lia.
- destruct (Hro i Hi) as (Hr & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
  pose proof (pa_img_range _ Himg). lia.
Qed.

(* what the walk keeps of rec_shape_of's post (rec_shape_of_c.v:95-117, v = "panel_get") *)
Definition dpgb_Krso (lyc : alayout) (Sc : astate) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 (exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
  forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of dpgb_verb))) /\
 Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc.

(* ---------- the statement's footprint ---------- *)

Definition dpgb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma dpgb_inFP : forall O a, inFP (dpgb_FP O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. left. exact Ha.
- left. right. exact Ha.
- right. apply (inFP_ablocks_fp_inv O a). exists r. split; [exact Hr | exact Ha].
Qed.

Lemma dpgb_inFP_blk : forall O b m i, In (b, m) O -> 0 <= i < req_size m -> inFP (dpgb_FP O) (b + i).
Proof.
intros O b m i Hin Hi. destruct (inFP_ablocks_fp O b m i Hin Hi) as (r & Hr & Ha).
exists r. split; [right; right; exact Hr | exact Ha].
Qed.

Lemma dpgb_FP_closed : forall ly S O, (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall (W : world SEGS) mem md, AR SEGS B ly S W mem md -> ~ YI16.sink_open_fp (dpgb_FP O).
Proof.
intros ly S O HO W mem md HAR. unfold dpgb_FP. apply sink_closed_cons; [cbn; unfold A_G_REC; lia|].
apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|]. apply sink_closed_ablocks_fp.
apply Forall_forall. intros [p n] Hpn. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hpn)) as (_ & H4096 & _). lia.
Qed.

(* the footprint lies below the allocator's ceiling, so below every stack byte *)
Lemma dpgb_FP_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (dpgb_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Ha. pose proof asan_consts as (C1 & _).
destruct (dpgb_inFP O a Ha) as [[Hg | Hg] | (pb & nb & Hpn & Hr)].
- unfold A_G_REC, REC_SIZE in Hg. lia.
- unfold A_REC_SPILL, SC_SIZE in Hg. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

(* ---------- the live blocks ---------- *)

Lemma dpgb_blk_rng : forall ly1 S1 (W1 : world SEGS) mem1 md1 p m a,
AR SEGS B ly1 S1 W1 mem1 md1 -> In (p, m) (ablocks B ly1 S1) -> p <= a < p + m -> 0 <= a < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 p m a HAR Hin Ha.
destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 p m HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
Qed.

Lemma dpgb_blocks_nodup : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
assert (Hpos : forall pn, In pn (ablocks B ly S) -> 1 <= req_size (snd pn)).
{ intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos n ltac:(lia))). }
revert Hp Hpos. generalize (ablocks B ly S) as l. intros l.
induction l as [|x t IH]; intros Hp Hpos; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor.
- intros Hin. rewrite Forall_forall in Hf.
  pose proof (Hf (fst x, req_size (snd x)) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) t x Hin)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. pose proof (Hpos x (or_introl eq_refl)). lia.
- apply IH; [exact Hp | intros pn Hpn; apply Hpos; right; exact Hpn].
Qed.

(* two live blocks with one start are one block *)
Lemma dpgb_same_start : forall ly S (W : world SEGS) mem md p m n, AR SEGS B ly S W mem md ->
In (p, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> m = n.
Proof.
intros ly S W mem md p m n HAR H1 H2.
destruct (Z.eq_dec m n) as [E | E]; [exact E|]. exfalso.
pose proof (al_blocks _ _ LAWS ly S W mem md p m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
assert (Hne : (p, m) <> (p, n)) by congruence.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p m p n HAR H1 H2 Hne) as Hd.
pose proof (dpgb_req_ge m ltac:(lia)) as Rm. pose proof (dpgb_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* two distinct live blocks are apart *)
Lemma dpgb_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) -> iv_apart b m p n.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (al_blocks _ _ LAWS ly S W mem md b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as Hd.
pose proof (dpgb_req_ge m ltac:(lia)) as Rm. pose proof (dpgb_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
Qed.

(* the live blocks' sizes are not negative *)
Lemma dpgb_bsum_nonneg : forall ly S (W : world SEGS) mem md l, AR SEGS B ly S W mem md ->
(forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l.
Proof.
intros ly S W mem md l HAR. induction l as [|[p n] l IH]; intros Hl; cbn [bsum fold_right]; [lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. assert (0 <= fold_right (fun b acc => snd b + acc) 0 l) by (apply IH; intros pn Hpn; apply Hl; right; exact Hpn).
lia.
Qed.

(* ---------- the recorder's bytes and the read-only bytes along the walk ---------- *)

Lemma dpgb_rdkept_of : forall ly1 S1 (W1 : world SEGS) mem1 md1 (rd' : reader) Qx R1 (Wr : Z -> Prop),
AR SEGS B ly1 S1 W1 mem1 md1 ->
arep_at (ablocks B ly1 S1) (rdW W1 mem1) A_G_REC A_REC_SPILL R1 Qx ->
(forall a, 0 <= a < alloc_ceiling -> ~ Wr a -> rd' a = rdW W1 mem1 a) ->
dpgb_rd_kept Qx (rdW W1 mem1) rd' Wr.
Proof.
intros ly1 S1 W1 mem1 md1 rd' Qx R1 Wr HAR HA HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
intros a Ha Hw. apply HK; [| exact Hw].
destruct Ha as [Ha | [Ha | ([q m] & Hpn & Hr)]].
- unfold A_G_REC, REC_SIZE in *. lia.
- unfold A_REC_SPILL, SC_SIZE in *. lia.
- cbn [fst snd] in Hr.
  exact (dpgb_blk_rng ly1 S1 W1 mem1 md1 q m a HAR
    (lay_blocks_in (ablocks B ly1 S1) (rdW W1 mem1) A_G_REC A_REC_SPILL R1 Qx HA (q, m) Hpn) Hr).
Qed.

(* the recorder's state, read through a reader that agrees below the allocator's ceiling *)
Lemma dpgb_rep_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 (rd' : reader) R1 O1,
AR SEGS B ly1 S1 W1 mem1 md1 -> rec_repA B ly1 S1 (rdW W1 mem1) R1 O1 ->
(forall a, 0 <= a < alloc_ceiling -> rd' a = rdW W1 mem1 a) ->
rec_repA B ly1 S1 rd' R1 O1.
Proof.
intros ly1 S1 W1 mem1 md1 rd' R1 O1 HAR (Q & HA & HQ) HK. exists Q. split; [|exact HQ].
apply (dpgb_arep_kept (ablocks B ly1 S1) (ablocks B ly1 S1) (rdW W1 mem1) rd' R1 Q HA
  (lay_blocks_in _ _ _ _ _ _ HA)).
apply (dpgb_rdkept_of ly1 S1 W1 mem1 md1 rd' Q R1 _ HAR HA). intros a Ha _. exact (HK a Ha).
Qed.

Lemma dpgb_rodata_kept : forall STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (dpgb_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k HAR0 HO HJ HR a Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
rewrite (F3 a Himg Hown Herr); [exact (HR a Hro Hown Herr)|].
apply fp_spares_closed; [exact (dpgb_FP_closed ly S O HO W mem md HAR0)|].
intros HF. destruct (dpgb_inFP O a HF) as [Hg | (p & n & Hpn & Hr)].
- exact (Hpg (dpgb_in_PG a Hg)).
- exact (blk_img SEGS B LAWS ly S W mem md p n a HAR0 (HO _ Hpn) Hr Himg).
Qed.

(* a live block the recorder does not own is still live, and its bytes are kept, at every point of the walk *)
Lemma dpgb_blk_kept : forall STK sp0 ly S (W : world SEGS) mem md O own lyc Sc (Wc : world SEGS) memc mdc k p n,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (dpgb_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
0 < n -> in_blockA (ablocks B ly S) p n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O ->
in_blockA (ablocks B lyc Sc) p n /\
(forall i, 0 <= i < n -> rdW Wc memc (p + i) = rdW W mem (p + i)).
Proof.
intros STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k p n HAR0 HJ HOin HKeep Hn Hblk Hap.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hblk as (pb & pk & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS ly S W mem md pb pk HAR0 Hin) as (_ & Hb4096 & Hbc & _ & _ & _ & Hpk0).
pose proof (req_size_pos pk ltac:(lia)) as [_ Rk].
assert (HnO : ~ In (pb, pk) O).
{ intros HO. rewrite Forall_forall in Hap. pose proof (Hap _ HO) as Hiv. cbn [fst snd] in Hiv.
  unfold iv_apart in Hiv. lia. }
assert (Hinc : In (pb, pk) (ablocks B lyc Sc)) by exact (HKeep _ Hin HnO).
split; [exists pb, pk; split; [exact Hinc | split; [exact Hlo | exact Hhi]]|].
intros i Hi. replace (p + i) with (pb + (p - pb + i)) by lia.
apply (F2 pb pk (p - pb + i) Hin Hinc); [lia|].
intros Hf. destruct (dpgb_inFP O _ Hf) as [Hg | (q & m & Hq & Hr)].
- apply (blk_img SEGS B LAWS ly S W mem md pb pk (pb + (p - pb + i)) HAR0 Hin ltac:(lia)).
  apply cmd_prog_img. exact (dpgb_in_PG _ Hg).
- destruct (recb_pair_dec (pb, pk) (q, m)) as [Heq | Hne].
  + injection Heq as <- <-. exact (HnO Hq).
  + pose proof (sep_blocks SEGS B LAWS ly S W mem md pb pk q m HAR0 Hin (HOin _ Hq) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR0 (HOin _ Hq)) as (_ & _ & _ & _ & _ & _ & Hm0).
    pose proof (req_size_pos m ltac:(lia)) as [_ Rm]. lia.
Qed.

(* the string tail the strlen wrapper reads: the rest of the 8-byte word of a live block's last byte *)
Lemma dpgb_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p n -> p <= e < p + n -> atail_vis SEGS W mem e.
Proof.
intros ly S W mem md p n e HAR (pb & pk & Hin & Hlo & Hhi) He a Ha.
destruct (al_blocks _ _ LAWS ly S W mem md pb pk HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (dpgb_req_ge pk ltac:(lia)) as [_ Rk].
apply (AR_block_word_vis SEGS B ly S W mem md pb pk e a HAR Hin); lia.
Qed.

(* ---------- the blocks of the walk's points and the contract's post ---------- *)

(* how the blocks after record() relate to the entry's: the live ones are entry blocks, an entry block that is
   gone is one of the recorder's (the spill arm's frees), and O1 is what the recorder owns now *)
Definition dpgb_blk ly S (O : list (Z * Z)) lyc Sc (O1 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) /\
(forall pn, In pn O1 -> In pn O) /\
(forall pn, In pn O -> ~ In pn O1 -> ~ In pn (ablocks B lyc Sc)) /\
(exists fr, Permutation (ablocks B ly S) (ablocks B lyc Sc ++ fr)).

(* record_c.v's post gives it *)
Lemma dpgb_blk_of_record : forall ly S (W : world SEGS) mem md O lyc Sc F O1, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) -> dpgb_blk ly S O lyc Sc O1.
Proof.
intros ly S W mem md O lyc Sc F O1 HAR HP HF HO1.
pose proof (Permutation_NoDup HP (dpgb_blocks_nodup ly S W mem md HAR)) as Hnd.
split.
{ intros pn H. apply (Permutation_in pn (Permutation_sym HP)). apply in_or_app. left. exact H. }
split.
{ intros pn H1 H2. apply (Permutation_in pn HP) in H1. apply in_app_or in H1 as [H | H]; [exfalso; exact (H2 H)|].
  exact (HF pn H). }
split.
{ intros pn H. exact (proj1 (proj1 (HO1 pn) H)). }
split.
{ intros pn HO HnO1 Hc. destruct (in_dec recb_pair_dec pn F) as [HinF | HnF].
  - exact (list_nodup_app_disj _ _ pn Hnd Hc HinF).
  - apply HnO1. apply (proj2 (HO1 pn)). split; [exact HO | exact HnF]. }
exists F. exact HP.
Qed.

(* the contract's post (descriptors_panel_get_c.v), verbatim *)
Definition dpgb_postQ (ly : alayout) (S : astate) (R : rstate) (uri : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 descriptors_panel_get_m R uri = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_PANEL_GET R uri /\
 mo_le MT S S' (XM_DESCRIPTORS_PANEL_GET MT R uri).

Definition dpgb_post (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) mem md
(R : rstate) (uri : option (list byte)) (O : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B DESCRIPTORS_PANEL_GET_STK (dpgb_FP O) regs ly S W mem md (EV_DESCRIPTORS_PANEL_GET R)
  (dpgb_postQ ly S R uri O).

Lemma dpgb_post_of : forall ly S R uri O lyc Sc O1 ly2 S2 ly3 S3 (W3 : world SEGS) mem3 md3 ly4 S4 (W4 : world SEGS)
  (regs4 : bvmap 5 word) mem4 md4
  (x : list byte) (p p1 p2 old : Z) (O2 O' : list (Z * Z)) (R' : rstate) (t : list byte),
dpgb_blk ly S O lyc Sc O1 ->
Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length x) + 1) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
AR SEGS B ly3 S3 W3 mem3 md3 -> AR SEGS B ly4 S4 W4 mem4 md4 ->
(forall pn, In pn O2 <-> In pn O1 \/ pn = (p, Z.of_nat (length x) + 1)) ->
(forall pn, In pn O2 -> In pn (ablocks B ly3 S3)) ->
(old = 0 \/ exists m, In (old, m) O2) ->
4096 <= p2 < 2 ^ 64 -> p1 <> p2 ->
(forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old ->
   pn <> (p1, Z.of_nat (length t) + 1) /\ pn <> (p2, Z.of_nat (length t) + 1)) ->
(forall pn, In pn (ablocks B ly4 S4) <-> (In pn (ablocks B ly3 S3) /\ fst pn <> old) \/
   pn = (p1, Z.of_nat (length t) + 1) \/ pn = (p2, Z.of_nat (length t) + 1)) ->
rec_repA B ly4 S4 (rdW W4 mem4) R' O' ->
(forall pn, In pn O' <-> (In pn O2 /\ fst pn <> old) \/ pn = (p1, Z.of_nat (length t) + 1)) ->
astr_atR (rdW W4 mem4) p2 t -> getr regs4 10 = w64 p2 ->
descriptors_panel_get_m R uri = (R', t) ->
blocks_bytes S4 <= blocks_bytes S + LIVE_DESCRIPTORS_PANEL_GET R uri ->
mo_le MT S S4 (XM_DESCRIPTORS_PANEL_GET MT R uri) ->
dpgb_postQ ly S R uri O ly4 S4 W4 regs4 mem4 md4.
Proof.
intros ly S R uri O lyc Sc O1 ly2 S2 ly3 S3 W3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 x p p1 p2 old O2 O' R' t
  Hblk Hp2 HF Hp3 HAR3 HAR4 HO2 HO2in Hold Hq Hp12 Hn12 H4 Hrep HO' Hstr Hreg Hm Hbb Hmo.
destruct Hblk as (B1 & B2 & B3 & B4 & _).
assert (Hc3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3)).
{ intros pn H. apply (Permutation_in pn (Permutation_sym Hp3)). apply (Permutation_in pn (Permutation_sym Hp2)).
  right. exact H. }
assert (H3c : forall pn, In pn (ablocks B ly3 S3) -> pn = (p, Z.of_nat (length x) + 1) \/ In pn (ablocks B lyc Sc)).
{ intros pn H. apply (Permutation_in pn Hp3) in H. apply (Permutation_in pn Hp2) in H.
  destruct H as [<- | H]; [left; reflexivity | right; exact H]. }
assert (Hpc : ~ In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc)).
{ intro H. rewrite Forall_forall in HF. specialize (HF _ H). cbn [fst snd] in HF. unfold iv_apart in HF. lia. }
assert (HO'4 : forall pn, In pn O' -> In pn (ablocks B ly4 S4))
  by exact (dpgb_rec_repA_in B ly4 S4 (rdW W4 mem4) R' O' Hrep).
assert (Hq4 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly4 S4))
  by (apply (proj2 (H4 _)); right; right; reflexivity).
assert (Hnold : forall b m, In (b, m) (ablocks B ly3 S3) -> ~ In (b, m) O2 -> b <> old).
{ intros b m H3 HnO2 E. subst b. destruct Hold as [E | (m' & Hm')].
  - pose proof (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 old m HAR3 H3) as (_ & H4096 & _). lia.
  - pose proof (dpgb_same_start ly3 S3 W3 mem3 md3 old m m' HAR3 H3 (HO2in _ Hm')) as E. subst m'.
    exact (HnO2 Hm'). }
assert (HkeptO2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3) /\ ~ In pn O2).
{ intros pn H1 H2.
  destruct (in_dec recb_pair_dec pn (ablocks B lyc Sc)) as [Hc | Hc]; [|exfalso; exact (H2 (B2 _ H1 Hc))].
  split; [exact (Hc3 _ Hc)|]. intros H. apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
  - exact (H2 (B3 _ H)).
  - exact (Hpc Hc). }
unfold dpgb_postQ.
exists R', t, p2, O'.
split; [exact Hm|]. split; [exact Hreg|]. split; [exact Hq|]. split; [exact Hrep|].
split.
{ intros pn H. apply (proj1 (HO' pn)) in H. destruct H as [(H & _) | ->].
  - apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
    + left. exact (B3 pn H).
    + destruct (in_dec recb_pair_dec (p, Z.of_nat (length x) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
      exact (B2 _ H1 Hpc).
  - destruct (in_dec recb_pair_dec (p1, Z.of_nat (length t) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
    destruct (in_dec recb_pair_dec (p1, Z.of_nat (length t) + 1) O) as [HO | HO]; [exact HO|].
    exfalso. destruct (HkeptO2 _ H1 HO) as [H3 HnO2].
    exact (proj1 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) eq_refl). }
split; [exact Hq4|].
split.
{ intros pn H1 H2 E. destruct (HkeptO2 pn H1 H2) as [H3 HnO2]. destruct pn as [b m].
  exact (proj2 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) E). }
split.
{ intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hbm). cbn [fst] in Eb. subst b.
  assert (Em : m = Z.of_nat (length t) + 1) by exact (dpgb_same_start ly4 S4 W4 mem4 md4 p2 m _ HAR4 (HO'4 _ Hbm) Hq4).
  subst m. apply (proj1 (HO' _)) in Hbm. destruct Hbm as [(Hb & Hbo) | Hb].
  - exact (proj2 (Hn12 _ (HO2in _ Hb) Hbo) eq_refl).
  - apply Hp12. congruence. }
split; [exact Hstr|].
split.
{ intros [b m] H1 H2. destruct (HkeptO2 _ H1 H2) as [H3 HnO2].
  pose proof (Hnold _ _ H3 HnO2) as Hb.
  assert (H4b : In (b, m) (ablocks B ly4 S4)) by (apply (proj2 (H4 _)); left; split; [exact H3 | exact Hb]).
  split; [exact H4b|].
  apply (dpgb_apart ly4 S4 W4 mem4 md4 b m p2 _ HAR4 H4b Hq4).
  exact (proj2 (Hn12 _ H3 Hb)). }
split.
{ intros pn H. apply (proj1 (H4 pn)) in H. destruct H as [(H & Hold') | [-> | ->]].
  - destruct (H3c pn H) as [-> | Hc].
    + right; left. apply (proj2 (HO' _)). left. split; [apply (proj2 (HO2 _)); right; reflexivity | exact Hold'].
    + destruct (in_dec recb_pair_dec pn O) as [HO | HO].
      * right; left. apply (proj2 (HO' _)). left. split; [|exact Hold'].
        apply (proj2 (HO2 _)). left. destruct (in_dec recb_pair_dec pn O1) as [HO1 | HO1]; [exact HO1|].
        exfalso. exact (B4 pn HO HO1 Hc).
      * left. split; [exact (B1 pn Hc) | exact HO].
  - right; left. apply (proj2 (HO' _)). right. reflexivity.
  - right; right. reflexivity. }
split; [exact Hbb | exact Hmo].
Qed.

(* ---------- the statement's premises and the walk's two later segments ---------- *)

(* the contract's premises (descriptors_panel_get_c.v) with uri = Some x *)
Definition dpgb_ctx ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (pu : Z) (x : list byte)
(R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B DESCRIPTORS_PANEL_GET_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pu /\ 0 <= pu < 2 ^ 64 /\
in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
Z.of_nat (length x) + 1 <= LMAX + 1 /\
Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_DESCRIPTORS_PANEL_GET R <= EV_MAX /\
blocks_bytes S + LIVE_DESCRIPTORS_PANEL_GET R (Some x) <= LIVE_MAX /\
mo_ok MT S (XM_DESCRIPTORS_PANEL_GET MT R (Some x)).

(* the segment from the call of rec_shape_of (0x8cd30): record() made the slot rec_slot R hold (24, []) (dpgb_blk,
   O1 the recorder's blocks then), arg_s added the copy p of uri, so the recorder holds (24, [x]) with the blocks
   (p, |x| + 1) :: O1; a0 is the verb "panel_get" (0x21fc0) and a1 its length 9, s1 the slot *)
Definition dpgb_R_stmt : Prop :=
forall ly S W regs mem md ch pu x R O,
dpgb_ctx ly S W regs mem md ch pu x R O ->
forall lyc Sc O1 ly2 S2 W2 (regs2 : bvmap 5 word) mem2 md2 (p : Z),
dpgb_blk ly S O lyc Sc O1 ->
ajournal SEGS B DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2
  (EV_RECORD R + EV_ARG_S) ->
mo_le MT S S2 (XM_RECORD MT R + XM_ARG_S MT (Some x)) ->
blocks_bytes S2 <= blocks_bytes S + LIVE_ARG_S (Some x) ->
Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length x) + 1) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
4096 <= p < 2 ^ 64 ->
rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) ((p, Z.of_nat (length x) + 1) :: O1) ->
spZ regs2 = spZ regs - DPGB_FRAME ->
getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
getr regs2 1 = Z_to_bv 64 (BASE + DPGB_RET_R) ->
getr regs2 9 = w64 (rec_slot R) ->
getr regs2 10 = w64 0x21fc0 -> getr regs2 11 = w64 9 ->
(forall r, 18 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error dpgb_saved j = Some r ->
 aval_mem (rdW W2 mem2) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (SIG CS_rec_shape_of)) mem2 (seg_rom SEGS)) md2)
  (dpgb_post ly S W regs mem md R (Some x) O).

(* the segment from the call of arg_s (0x8cd20): record() returned the slot (a0 = s1 = rec_slot R) holding the
   call (24, []); a1 = s0 = uri, whose block is live and whose bytes are the entry's *)
Definition dpgb_A_stmt : Prop :=
forall ly S W regs mem md ch pu x R O,
dpgb_ctx ly S W regs mem md ch pu x R O ->
forall lyc Sc Wc (regs1 : bvmap 5 word) memc mdc O1,
dpgb_blk ly S O lyc Sc O1 ->
ajournal SEGS B DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] lyc Sc Wc memc mdc (EV_RECORD R) ->
mo_le MT S Sc (XM_RECORD MT R) ->
blocks_bytes Sc <= blocks_bytes S ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_DESCRIPTORS_PANEL_GET []) O1 ->
spZ regs1 = spZ regs - DPGB_FRAME ->
getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 1 = Z_to_bv 64 (BASE + DPGB_RET_ARG) ->
getr regs1 8 = w64 pu -> getr regs1 9 = w64 (rec_slot R) ->
getr regs1 10 = w64 (rec_slot R) -> getr regs1 11 = w64 pu ->
(forall r, 18 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error dpgb_saved j = Some r ->
 aval_mem (rdW Wc memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
in_blockA (ablocks B lyc Sc) pu (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memc) pu x ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (SIG CS_arg_s)) memc (seg_rom SEGS)) mdc)
  (dpgb_post ly S W regs mem md R (Some x) O).

End e.
End f.
End d.
