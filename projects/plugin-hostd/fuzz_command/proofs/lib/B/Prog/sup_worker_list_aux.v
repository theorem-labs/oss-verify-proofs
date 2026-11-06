(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper lemmas of sup_worker_list's walk on plugin-hostd/fuzz_command.asan-ubsan
   (image B), taken from the ASan walk lib/A/Prog/sup_worker_list.v, sup_worker_list_s1.v and sup_worker_list_s2.v
   (a working branch 80a82462f87) and restated at B's addresses and over B's listing (lib/B/Prog, a Theorem Labs lane
   917ca7ac6b1). *)

(* sup_worker_list on image B (recorder.c:390-393; entry BASE + AF_sup_worker_list = 0x8bb2c, 68 bytes,
   17 instructions, measured with capstone from fuzz_command.asan-ubsan's .symtab):
     0x8bb2c addi sp,sp,-16 / sd ra,8(sp) / sd s0,0(sp) / li a0,8
     0x8bb3c jal record                          (record(8): B calls it, A inlined it)
     0x8bb40 mv s0,a0 / auipc+addi a0 = 0x21dc0 "worker_list" (A_OBJ 66, A_HI 159) / li a1,11
     0x8bb50 jal rec_shape_of
     0x8bb54 mv a1,a0 / mv a0,s0 / li a2,0 / ld ra,8(sp) / ld s0,0(sp) / addi sp,sp,16
     0x8bb6c j answer                            (tail jump at the entry's sp)
   No branch, no `jal __asan_report_*`, no UBSan trap site, no shadow access; no load or store through an auipc base.
   This file holds the lemmas of the walk that depend on no callee contract: the walk's offsets, the verb literal and
   rec_shape_of's premise on it, the call targets, record's slot, the entry seed of the symbolic executor, and the
   recorder / block / journal facts of the A walk. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the walk's offsets in B's listing ---------- *)
Definition SWL_FRAME : Z := 16.

Lemma swl_af : AF_sup_worker_list = 0x55fc.
Proof. reflexivity. Qed.

(* ---------- the verb rec_shape_of is handed ---------- *)
(* the 11 bytes of the literal at 0x21dc0 (CmdRo.v's RO_lit_21dc0 less its NUL) *)
Definition swl_verb : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 108; 105; 115; 116].
Lemma swl_verb_lit : swl_verb ++ [Z_to_bv 8 0] = RO_lit_21dc0.
Proof. vm_compute. reflexivity. Qed.
Lemma swl_verb_bstr : bstr "worker_list"%string = swl_verb.
Proof. vm_compute. reflexivity. Qed.
Lemma swl_verb_len : Z.of_nat (length swl_verb) = 11.
Proof. reflexivity. Qed.
Lemma swl_verb_no0 : ~ In (Z_to_bv 8 0) swl_verb.
Proof.
intros Hz. apply (in_map bv_unsigned) in Hz. vm_compute in Hz.
repeat (destruct Hz as [Hz|Hz]; [discriminate Hz|]). exact Hz.
Qed.
Lemma swl_abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity.
Qed.

(* the conjunct of a long conjunction that holds the literal address [a]: drops the leading conjuncts of H in place
   (Wb_sup_lv2_worker_set's slw_projz, a working branch 5c04ebe0308), so no conjunct is unified
   with the goal and no nested proj2 term is retyped *)
Local Ltac swl_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

(* the literal's bytes and their read-only addresses, from cmd_ro_ok and cmd_ro_in *)
Lemma swl_lit_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21dc0 RO_lit_21dc0.
Proof. intros rd [HBY _]. unfold cmd_ro_bytes in HBY. swl_projz HBY 0x21dc0. Qed.
Lemma swl_lit_ro : forall (ro : Z -> Prop), cmd_ro_in ro -> forall i, 0 <= i < 12 -> ro (0x21dc0 + i).
Proof. intros ro HRI. unfold cmd_ro_in in HRI. swl_projz HRI 0x21dc0. Qed.
Lemma swl_verb_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21dc0 swl_verb.
Proof. intros rd H. split; [rewrite swl_verb_lit; exact (swl_lit_bytes rd H) | exact swl_verb_no0]. Qed.

Lemma swl_in_Z : forall (x : Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.

(* the record's checks on the literal's 12 bytes (lib/B/Prog/CmdChk.v) and its end among CmdRo's literal ends:
   closed goals, decided by computation *)
Lemma swl_lit_addr_b : cmd_addr_b 0x21dc0 12 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma swl_lit_hull_b : cmd_hull_b 0x21dc0 12 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma swl_lit_end : In (0x21dc0 + 11) cmd_ro_ends.
Proof. apply swl_in_Z. vm_compute. reflexivity. Qed.

(* the reply shape rec_shape_of returns for the verb fits answer's buffer *)
Lemma swl_fits : fits (shape_of swl_verb).
Proof. unfold fits. vm_compute. intro Hf. discriminate Hf. Qed.

(* the model's step (RecModel.v sup_worker_list_m): record() of the call (8, []), then answer with the verb's shape *)
Lemma swl_model : forall R, sup_worker_list_m R =
rec_answer (rec_record R REC_WORKER_LIST []) (REC_WORKER_LIST, @nil (list byte)) (shape_of swl_verb) false.
Proof. intros R. unfold sup_worker_list_m, rec_stub, daemon_shape. rewrite swl_verb_bstr. reflexivity. Qed.

(* ---------- reader facts ---------- *)
Lemma swl_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma swl_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma swl_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (swl_abytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.

(* ---------- list facts ---------- *)
Lemma swl_nodup_disj : forall {X : Type} (l1 l2 : list X) a, List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 a H H1 H2; [destruct H1|].
cbn in H. apply List.NoDup_cons_iff in H as [Hx H].
destruct H1 as [<- | H1]; [apply Hx, in_app_iff; right; exact H2 | exact (IH l2 a H H1 H2)].
Qed.

Lemma swl_not_in_zr : forall lo hi l, forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) l = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l Hb a Ha Hex. apply Exists_exists in Hex as (r & Hr & Hin). rewrite forallb_forall in Hb.
pose proof (Hb r Hr) as Hr'. apply orb_true_iff in Hr' as [H | H]; apply Z.leb_le in H; unfold in_zr in Hin; lia.
Qed.

Definition swl_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* answer's footprint names the recorder's blocks that start at the old answer (stdpp's filter) *)
Lemma swl_in_filter_old : forall (old : Z) (O : list (Z * Z)) x,
In x (filter (fun pn : Z * Z => fst pn =? old) O) -> In x O /\ fst x = old.
Proof.
intros old O x. induction O as [|y O IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd|Hd] in H.
- destruct H as [-> | H].
  + split; [left; reflexivity|]. revert Hd. destruct (Z.eqb_spec (fst x) old) as [Ex|Ex]; [intros _; exact Ex|].
    intros Hd; exfalso; first [discriminate Hd | exact Hd | inversion Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* ---------- the program's writable statics and record()'s slot ---------- *)
(* g_rec and record.spill are ranges of the record's program statics, lib/B/YF0m.v's TFIB_PROG_STATIC in (start,
   length) form (the list a Theorem Labs lane's CmdRecRest.v cmd_prog_img and cmd_ro_prog_apart are stated over) *)
Lemma swl_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. unfold TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.
Lemma swl_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. unfold TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* the slot record() returns (record_c.v rec_slot): a slot of g_rec's call table or record.spill, its 8 bytes of fn
   and nargs inside g_rec or record.spill *)
Lemma swl_slot_bytes : forall R, (length (r_calls R) <= 16)%nat -> forall a, rec_slot R <= a < rec_slot R + 8 ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros R HL a Ha. unfold rec_slot in Ha. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- right. unfold A_REC_SPILL, SC_SIZE in *. lia.
Qed.
Lemma swl_slot_range : forall R, (length (r_calls R) <= 16)%nat ->
A_G_REC + OFF_CALLS <= rec_slot R <= A_REC_SPILL.
Proof.
intros R HL. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl];
unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *; lia.
Qed.

(* ---------- the recorder's representation ---------- *)
Lemma swl_lay_in_calls : forall Q P pn i, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q P pn i Hi Hpn. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hpn].
Qed.
Lemma swl_lay_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact H. Qed.
Lemma swl_lay_in_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. left. left. reflexivity.
Qed.
Lemma swl_lay_in_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. right. left. reflexivity.
Qed.

(* every block the recorder owns is a live block *)
Lemma swl_arep_in : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q -> forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd R Q HA pn Hpn. unfold lay_blocks in Hpn.
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

Lemma swl_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
pose proof (Nat2Z.is_nonneg (length (snd c))) as Hl0.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (swl_aval_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [apply (swl_aval_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (swl_aval_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (swl_astr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

(* the scalar fields, the answer and the reply survive a write that keeps g_rec's bytes from OFF_ANSWER on and
   the first 8, and every block the recorder owns *)
Lemma swl_arep_tail_kept : forall bl bl2 (rd rd2 : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, A_G_REC <= a < A_G_REC + OFF_NCALLS -> rd2 a = rd a) ->
(forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE -> rd2 a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl2) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd2 (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl2 rd2 A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl2 rd2 A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd2 A_G_REC R.
Proof.
intros bl bl2 rd rd2 R Q HA Hlo Hhi Hbl Hb.
destruct HA as (_ & _ & _ & _ & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & _).
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_NCALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (swl_lay_in_answer Q q Eq) as Hq.
    split; [apply (swl_aval_kept rd); [exact A1 | intros k Hk; apply Hhi; lia]|].
    split; [exact A2|]. split; [apply Hbl; exact Hq|]. split; [exact A4|].
    split; [apply (swl_astr_kept rd); [exact A5 | intros i Hi; apply Hb; [exact Hq | lia]] | exact A6].
  - apply (swl_aval_kept rd); [exact Ha | intros k Hk; apply Hhi; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (swl_lay_in_reply Q q Eq) as Hq.
    split; [apply (swl_aval_kept rd); [exact A1 | intros k Hk; apply Hhi; lia]|].
    split; [apply (swl_aval_kept rd); [exact A2 | intros k Hk; apply Hhi; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply Hbl; exact Hq|]. split; [exact A6|].
    split; [apply (swl_abytes_kept rd); [exact A7 | intros i Hi; apply Hb; [exact Hq | lia]] | exact A8].
  - destruct Hr as [A1 A2]. split; apply (swl_aval_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hhi; lia]. }
split; [apply (swl_aval_kept rd); [exact S1 | intros k Hk; apply Hlo; lia]|].
split; [apply (swl_aval_kept rd); [exact S2 | intros k Hk; apply Hlo; lia]|].
split; [apply (swl_aval_kept rd); [exact S3 | intros k Hk; apply Hhi; lia]|].
split; [apply (swl_aval_kept rd); [exact S4 | intros k Hk; apply Hhi; lia]|].
split; [apply (swl_aval_kept rd); [exact S5 | intros k Hk; apply Hhi; lia]|].
exact S6.
Qed.

(* a write outside g_rec, record.spill and the recorder's own blocks keeps the representation *)
Lemma swl_arep_kept : forall bl bl' (rd rd' : reader) R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hg Hs HbQ.
destruct (swl_arep_tail_kept _ _ rd rd' R Q HA
  ltac:(intros a Ha; apply Hg; unfold OFF_NCALLS, REC_SIZE in *; lia)
  ltac:(intros a Ha; apply Hg; unfold OFF_ANSWER, REC_SIZE in *; lia) HblQ HbQ) as (TA & TR & TS).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact TA|]; split; [exact TR|]; split; [exact TS | exact Hown]].
split; [exact C1|]. split; [exact C2|].
split; [apply (swl_aval_kept rd); [exact C3 | intros k Hk; apply Hg; unfold OFF_NCALLS, REC_SIZE; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
  pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
  pose proof HC as (_ & HL6 & _).
  apply (swl_acall_kept bl _ rd); [exact HC | | |].
  + intros pn Hpn. apply HblQ. exact (swl_lay_in_calls Q P pn i Hp Hpn).
  + intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  + intros pn j Hpn Hj. apply HbQ; [exact (swl_lay_in_calls Q P pn i Hp Hpn) | exact Hj].
- split; [|exact C6].
  pose proof C5 as (_ & HL6 & _).
  apply (swl_acall_kept bl _ rd); [exact C5 | | |].
  + intros pn Hpn. apply HblQ. exact (swl_lay_in_spill Q pn Hpn).
  + intros j Hj. apply Hs. unfold CALL_OFF_ARGS, SC_SIZE in *. lia.
  + intros pn j Hpn Hj. apply HbQ; [exact (swl_lay_in_spill Q pn Hpn) | exact Hj].
Qed.

(* the answer pointer the recorder holds: g_rec.answer is the answer block's address, or 0 when there is none *)
Definition swl_oaddr (q : option (Z * Z)) : Z := match q with Some pn => fst pn | None => 0 end.
Lemma swl_aanswer_ptr : forall bl rd gr t q, aanswer_at bl rd gr t q -> aval_mem rd (gr + OFF_ANSWER) 8 (swl_oaddr q).
Proof. intros bl rd gr t q H. unfold aanswer_at in H. destruct t, q; cbn [swl_oaddr]; try contradiction; [exact (proj1 H) | exact H]. Qed.

Section m.
Variable B : asyms.

Lemma swl_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. apply (swl_arep_in _ rd R Q HA). apply HO. exact Hpn. Qed.

Lemma swl_rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
apply (swl_arep_kept _ _ rd rd' R Q HA); [intros pn Hpn; apply Hbl, HO, Hpn | exact Hg | exact Hs |].
intros [p n] i Hpn Hi. apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi).
Qed.

(* a string argument stays one when its bytes keep their values (both arms of astr_argA are otherwise
   reader-free: in_blockA / iv_apart, or in_roP, unowned, cmd_addr_b, cmd_hull_b, cmd_ro_ends) *)
Lemma swl_astr_argA_rd : forall ly S (rd rd' : reader) ro O p x, astr_argA B ly S rd ro O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly S rd' ro O p (Some x).
Proof.
intros ly S rd rd' ro O p x H Hk. cbv beta iota zeta delta [astr_argA] in H |- *.
destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
apply (swl_astr_kept rd); [exact H2 | exact Hk].
Qed.

(* the verb as a string argument on the read-only arm of astr_argA (lib/B/Prog/CmdRep.v), for any owned-block list:
   its bytes read-only (cmd_ro_in), owned by no runtime entry and not the errno cell (CmdBSyms' ts_owned / ts_errno),
   the record's checks and the literal's end by computation *)
Lemma swl_verb_unowned : CmdBSyms B -> forall i, 0 <= i < 12 ->
~ Exists (in_zr (0x21dc0 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21dc0 + i < as_errno B + 4).
Proof.
intros HB i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split.
- apply (swl_not_in_zr 0x21dc0 (0x21dc0 + 12)); [vm_compute; reflexivity | lia].
- cbv [TFIB_ERRNO]. lia.
Qed.

Lemma swl_verb_arg : CmdBSyms B -> forall ly S (rd : reader) (ro : Z -> Prop) O,
cmd_ro_ok rd -> cmd_ro_in ro -> astr_argA B ly S rd ro O 0x21dc0 (Some swl_verb).
Proof.
intros HB ly S rd ro O HRO HROIN. cbv beta iota zeta delta [astr_argA]. rewrite swl_verb_len.
split; [lia|]. split; [exact (swl_verb_str _ HRO)|]. split; [unfold LMAX; lia|].
right. split; [intros i Hi; split; [exact (swl_lit_ro ro HROIN i Hi) | exact (swl_verb_unowned HB i Hi)]|].
split; [exact swl_lit_addr_b|]. split; [exact swl_lit_hull_b | exact swl_lit_end].
Qed.
End m.

(* ---------- the entry seed of the symbolic executor (one segment: no branch in the function) ---------- *)
(* the atom above the registers: 32 the shadow base, which this function never uses; the token executor's shadow
   list is empty because the function accesses no shadow *)
Definition swl_rs : smem := [stack_region SWL_FRAME].
Definition swl_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_swl : sstate := mkSS AF_sup_worker_list sr_atoms swl_rs None swl_facts.
Definition swl_Bx : sv := SOff 32 0.
Definition swl_SH : list shent := [].
Definition swl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition swl_extra : list word := [Z_to_bv 64 SB].

Lemma swl_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
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
Definition swl_E (regs : bvmap 5 word) : env := Eimg (Ereg regs swl_extra).

Lemma swl_seed : forall STK ly (W : world SEGS) mem (regs : bvmap 5 word),
SWL_FRAME <= STK ->
astk_ok STK ly (spZ regs) ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (swl_E regs) ss_swl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_worker_list)) mem (seg_rom SEGS))) /\
sh_ok SEGS swl_Bx swl_SH (swl_E regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly W mem regs HF Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|unfold sh_ok, swl_SH; apply Forall_nil].
rewrite restrict_mkst_fx.
set (E := swl_E regs).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold swl_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold swl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_swl. apply pa_entry_st_ok_full.
- subst E. unfold swl_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold swl_rs, stack_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U2. unfold SWL_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents.
  unfold swl_rs, stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2.
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [swl_facts f_atoms atoms_ok].
  split; [apply (swl_afact E 2%nat (spZ regs)); [rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | change (2 ^ 4) with 16; exact Hal16 | lia]|].
  split; [apply (swl_afact E 32%nat SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I.
Qed.

Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the literal's object atom and the call targets: from the statement's VOBJS and the walk's cmd_sig_prog_PB *)
Lemma swl_lit_val : cmd_val_objs -> VAL (A_OBJ 66) = 0x21dc0.
Proof. intros VOBJS. rewrite (VOBJS 66%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Local Ltac swl_in_syms := cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]).
Lemma swl_sig_rec : cmd_sig_prog -> SIG CS_record = BASE + AF_record.
Proof. intros SIGP. rewrite (SIGP CS_record) by swl_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma swl_sig_shp : cmd_sig_prog -> SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. intros SIGP. rewrite (SIGP CS_rec_shape_of) by swl_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma swl_sig_ans : cmd_sig_prog -> SIG CS_answer = BASE + AF_answer.
Proof. intros SIGP. rewrite (SIGP CS_answer) by swl_in_syms. f_equal; try (vm_compute; reflexivity). Qed.

(* the program's statics are the record's (CmdBSyms' ts_prog) *)
Lemma swl_prog_static : CmdBSyms B -> as_prog_static B = TFIB_PROG_STATIC.
Proof. intros HB. exact (ts_prog B HB). Qed.

(* rec_shape_of's verb premise (rec_shape_of_c.v, the `Z.of_nat (length v) <= 16 ->` conjunct) at the literal *)
Lemma swl_verb_pre : CmdBSyms B -> forall ly S (rd : reader),
cmd_ro_ok rd -> cmd_ro_in (in_roP SEGS RLO RHI) ->
Z.of_nat (length swl_verb) <= 16 ->
abytes_atR rd 0x21dc0 swl_verb /\
(in_blockA (ablocks B ly S) 0x21dc0 (Z.of_nat (length swl_verb)) \/
 astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21dc0 (Some swl_verb)).
Proof.
intros HB ly S rd HRO HROIN _. split.
- apply (swl_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite swl_verb_lit. exact (swl_lit_bytes _ HRO).
- right. exact (swl_verb_arg B HB ly S rd _ [] HRO HROIN).
Qed.

(* two live blocks that start at the same address are the same block *)
Lemma swl_same_start : forall ly S (W : world SEGS) mem md pn pn', AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In pn' (ablocks B ly S) -> fst pn = fst pn' -> pn = pn'.
Proof.
intros ly S W mem md [p n] [p' n'] HAR H1 H2 E. cbn [fst] in E. subst p'.
destruct (swl_pair_dec (p, n) (p, n')) as [|Hne]; [assumption|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p n' HAR H1 H2 Hne) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n' HAR H2) as (_ & _ & _ & _ & _ & _ & Hn').
pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma swl_blocks_apart : forall ly S (W : world SEGS) mem md pn pn', AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In pn' (ablocks B ly S) -> pn <> pn' -> iv_apart (fst pn) (snd pn) (fst pn') (snd pn').
Proof.
intros ly S W mem md [p n] [p' n'] HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p' n' HAR H1 H2 Hne) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p' n' HAR H2) as (_ & _ & _ & _ & _ & _ & Hn').
pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
unfold zdisjoint in D. unfold iv_apart. cbn [fst snd] in *. lia.
Qed.

(* a byte of a live block: above the null page, below the allocator's ceiling (so below every stack frame), not an
   image byte *)
Lemma swl_blk_byte : forall ly S (W : world SEGS) mem md p n i, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> 0 <= i < n -> 4096 <= p + i /\ p + i < alloc_ceiling /\ ~ in_img SEGS (p + i).
Proof.
intros ly S W mem md p n i HAR Hin Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
split; [lia|]. split; [lia|].
destruct (al_client_img _ _ LAWS _ _ _ _ _ (p + i) HAR) as [_ Hni]; [left; exists p, n; split; [exact Hin | lia] | exact Hni].
Qed.

(* the statement's footprint (lib/B/Prog/sup_worker_list_c.v), and that it lies below the allocator's ceiling *)
Definition swl_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma swl_FP_low : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall a, inFP (swl_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O HAR HREP a Ha. pose proof asan_consts as (C1 & _).
unfold swl_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, REC_SIZE in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hbm & Hba).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (swl_rec_repA_in B ly S _ R O HREP (b, m) Hbm)) as (_ & _ & Hbc & _). lia.
Qed.
End e.
End f.
End d.
