(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the B (fuzz_command.asan-ubsan) twin of the image and model facts of
   lib/A/Prog/descriptors_get_s3.v (a working branch 565c61eeead: dg_verb_lit, dg_shape, dg_fits, dg_verb_val,
   dg_sig_*, dg_not_owned_b, dg_verb_unowned, dg_abytes_prefix, dg_verb_arg) at B's addresses, over a Theorem Labs lane's lib/B/Prog
   kit (a working branch 917ca7ac6b1). *)

(* The facts the walk of descriptors_get on fuzz_command.asan-ubsan takes from the image and the model, none of which
   depends on a callee's statement.

   The B code (MEASURED with capstone over the .symtab of fuzz_command.asan-ubsan, sha256 658cefbe...; the 22 words
   are the listing's slots 6621..6642 of lib/B/Prog/CmdList.v, BASE + AF_descriptors_get with AF = 0x6774):
   descriptors_get at 0x8cca4, 88 bytes, 22 instructions of 4 bytes, a 32-byte frame (ra, s0, s1). It calls record
   (0x8a728) at 0x8ccbc with a0 = 23, then arg_s (0x8a820) at 0x8ccc8 with a0 = the slot record returned (kept in s1)
   and a1 = uri (kept in s0), then rec_shape_of (0x896d4) at 0x8ccd8 with a0 = 0x21fa0 and a1 = 14, and it frees its
   frame and tail-jumps to answer (0x8aa10, `j` at 0x8ccf8) with a0 = the slot, a1 = the shape and a2 = 0. It has no
   `jal __asan_report_*`, no UBSan trap and no branch. Its one auipc pair (0x8cccc / 0x8ccd0, the listing's
   PHi a0 204 / PAddHi a0 a0 204 (A_OBJ 87) 0) makes the address 0x21fa0; no load or store goes through an auipc
   base register.

   - `dgb_model`, `dgb_rec_id`: the model step in the order the code takes it (record, then answer with changes =
     false), and the REC id the code loads (0x8ccb8 `li a0, 23`).
   - `dgb_verb_lit`, `dgb_verb_len`, `dgb_verb_nz`, `dgb_shape`, `dgb_fits`: the verb "descriptor_get" (0x21fa0).
   - `dgb_addrs`: the entry and the four call targets against the listing's base (lib/B/Prog/CmdAddr.v cmd_text).
   - Section v (under a PAImg instance): `dgb_verb_val` (from cmd_val_objs), `dgb_sig_arg_s` .. `dgb_sig_answer`
     (from cmd_sig_prog; record's call target is a Theorem Labs lane's CmdRecAns.rca_sig_record), `dgb_verb_unowned` (from CmdBSyms), `dgb_verb_arg` and `dgb_verb_pre`: the verb as
     rec_shape_of's premise asks it (lib/B/Prog/rec_shape_of_c.v, the `Z.of_nat (length v) <= 16 -> ...` premise).
     The read-only arm's record checks (cmd_addr_b, cmd_hull_b over lib/B/YF0m.v, and the literal's end 0x21fae in
     cmd_ro_ends) hold by computation (`dgb_verb_chk`). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdChk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the verb "descriptor_get" (.str of recorder.c at 0x21fa0, 14 bytes and its NUL) *)
Definition dgb_verb : list byte := bstr "descriptor_get"%string.

Lemma dgb_rec_id : REC_DESCRIPTORS_GET = 23.
Proof. reflexivity. Qed.

Lemma dgb_model : forall R uri, descriptors_get_m R uri =
rec_answer (rec_record R REC_DESCRIPTORS_GET [sarg uri]) (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false.
Proof. intros R uri. unfold descriptors_get_m, rec_stub, daemon_shape, dgb_verb. reflexivity. Qed.

Lemma dgb_verb_lit : dgb_verb ++ [Z_to_bv 8 0] = RO_lit_21fa0.
Proof. vm_compute. reflexivity. Qed.
Lemma dgb_verb_len : length dgb_verb = 14%nat.
Proof. reflexivity. Qed.
Lemma dgb_verb_nz : ~ In (Z_to_bv 8 0) dgb_verb.
Proof. unfold dgb_verb. vm_compute. intros H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.
Lemma dgb_shape : daemon_shape "descriptor_get" = shape_of dgb_verb.
Proof. reflexivity. Qed.
Lemma dgb_fits : fits (shape_of dgb_verb).
Proof. unfold fits. vm_compute. intros H. discriminate H. Qed.

(* the entry and the call targets the capstone walk of the image measured, against the listing's base *)
Lemma dgb_addrs :
cmd_text + AF_descriptors_get = 0x8cca4 /\ cmd_text + AF_record = 0x8a728 /\ cmd_text + AF_arg_s = 0x8a820 /\
cmd_text + AF_rec_shape_of = 0x896d4 /\ cmd_text + AF_answer = 0x8aa10.
Proof.
unfold cmd_text, AF_descriptors_get, AF_record, AF_arg_s, AF_rec_shape_of, AF_answer. repeat split; lia.
Qed.

Lemma dgb_abytes_prefix : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)).
rewrite app_nth1 in H by exact Hi. exact H.
Qed.

Lemma dgb_not_owned_b : forall a (L : list (Z * Z)),
existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) L = false -> ~ Exists (in_zr a) L.
Proof.
intros a L. induction L as [|r L IH]; intros H HE; [inversion HE|].
cbn [existsb] in H. apply Bool.orb_false_iff in H as [H1 H2].
inversion HE as [? ? Hr | ? ? Hr]; subst.
- unfold in_zr in Hr. apply Bool.andb_false_iff in H1 as [H1 | H1]; [apply Z.leb_gt in H1 | apply Z.ltb_ge in H1]; lia.
- exact (IH H2 Hr).
Qed.

(* the program's own writable statics: a Theorem Labs lane's cmd_PG (lib/B/Prog/CmdGlob.v, (lo, hi) pairs under inFP) and the
   allocator record's TFIB_PROG_STATIC (lib/B/YF0m.v, (start, length) pairs under Exists in_zr), which CmdBSyms'
   ts_prog gives as as_prog_static B *)
Lemma dgb_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
Qed.
Lemma dgb_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56).
split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
Qed.
Lemma dgb_PG_range : forall a, inFP cmd_PG a -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG in Hr. cbn [In] in Hr.
unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.
Lemma dgb_static_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in *. lia.
Qed.
Lemma dgb_static_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in *. lia.
Qed.

Definition dgb_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* the reader-only transports: a field, a byte list, a string, a recorded call and the whole recorder state keep
   their meaning over a reader that agrees on the bytes they read (lib/B/Prog/rec_clear's aval_mem_kept /
   rabytes_kept / rastr_kept / acall_at_kept / rc_arep_kept, a working branch dd331f1aac9; the same
   lemmas as lib/A/Prog/descriptors_get_s1.v's) *)
Lemma dgb_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk i Hi. rewrite (Hk i Hi). exact (H i Hi). Qed.
Lemma dgb_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma dgb_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (dgb_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma dgb_acall_blocks : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HlenP & _ & _ & _ & Hargs) pn Hin.
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs;
[|exfalso; apply nth_error_None in Hs;
  assert (Hk' : (k < length P)%nat) by (apply nth_error_Some; rewrite Hk; discriminate); lia].
exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
Qed.
Lemma dgb_acall_at_kept : forall bl (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl rd' a c P.
Proof.
intros bl rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (dgb_aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha;
  apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk;
  pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (dgb_aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha;
  apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk;
  pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (dgb_aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
apply (dgb_rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma dgb_arep_kept : forall bl (rd rd' : reader) R' Q',
arep_at bl rd A_G_REC A_REC_SPILL R' Q' ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) bl -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R' Q'.
Proof.
intros bl rd rd' R' Q' (Hg8 & Hs8 & Hap & (Hle16 & HlenQ & Vnc & HCA & HSP & HSPL) & HANS & HREPL & HSCAL & HOWN)
KG KS KB.
assert (KBpn : forall pn i, In pn bl -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hin Hi; exact (KB p n i Hin Hi)).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ split; [exact Hle16|]. split; [exact HlenQ|].
  split; [apply (dgb_aval_mem_kept rd); [exact Vnc | intros k Hk; apply KG; unfold OFF_NCALLS, A_G_REC, REC_SIZE; lia]|].
  split.
  - intros i c P Hc Hi. destruct (HCA i c P Hc Hi) as (HAC & HFA). split; [|exact HFA].
    assert (Hi2 : (i < length (l_calls Q'))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    apply (dgb_acall_at_kept bl rd); [exact HAC | |
      intros pn ii Hin Hii; apply KBpn; [exact (dgb_acall_blocks bl rd _ c P HAC pn Hin) | exact Hii]].
    intros j Hj. rewrite <- Z.add_assoc. apply KG.
    destruct HAC as (_ & Hle6 & _). unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS, REC_SIZE in *. lia.
  - split; [|exact HSPL]. apply (dgb_acall_at_kept bl rd); [exact HSP | |
      intros pn ii Hin Hii; apply KBpn; [exact (dgb_acall_blocks bl rd _ _ _ HSP pn Hin) | exact Hii]].
    intros j Hj. apply KS. destruct HSP as (_ & Hle6 & _).
    unfold A_REC_SPILL, SC_SIZE, CALL_OFF_ARGS in *. lia. }
split.
{ destruct (r_answer R') as [x|], (l_answer Q') as [pn|]; cbn [aanswer_at] in HANS |- *; try exact HANS.
  - destruct HANS as (V & Hne & Hin & Hsz & Hstr & Hlm).
    split; [apply (dgb_aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_ANSWER, A_G_REC, REC_SIZE; lia]|].
    split; [exact Hne|]. split; [exact Hin|]. split; [exact Hsz|]. split; [|exact Hlm].
    apply (dgb_rastr_kept rd); [exact Hstr | intros i Hi; apply (KB (fst pn) (snd pn) i); [destruct pn; exact Hin | lia]].
  - apply (dgb_aval_mem_kept rd); [exact HANS | intros k Hk; apply KG; unfold OFF_ANSWER, A_G_REC, REC_SIZE; lia]. }
split.
{ destruct (r_reply R') as [x|], (l_reply Q') as [pn|]; cbn [areply_at] in HREPL |- *; try exact HREPL.
  - destruct HREPL as (V & Vs & Hne & Hx & Hin & Hsz & Hbs & Hlm).
    split; [apply (dgb_aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_REPLY, A_G_REC, REC_SIZE; lia]|].
    split; [apply (dgb_aval_mem_kept rd); [exact Vs | intros k Hk; apply KG; unfold OFF_REPLY_SIZE, A_G_REC, REC_SIZE; lia]|].
    split; [exact Hne|]. split; [exact Hx|]. split; [exact Hin|]. split; [exact Hsz|]. split; [|exact Hlm].
    apply (dgb_rabytes_kept rd); [exact Hbs | intros i Hi; apply (KB (fst pn) (snd pn) i); [destruct pn; exact Hin | lia]].
  - destruct HREPL as (V & Vs).
    split; [apply (dgb_aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_REPLY, A_G_REC, REC_SIZE; lia]|].
    apply (dgb_aval_mem_kept rd); [exact Vs | intros k Hk; apply KG; unfold OFF_REPLY_SIZE, A_G_REC, REC_SIZE; lia]. }
split; [|exact HOWN].
destruct HSCAL as (Vrf & Vcd & Vnr & Vst & Vho & Rs).
split; [apply (dgb_aval_mem_kept rd); [exact Vrf | intros k Hk; apply KG; unfold OFF_REFUSE, A_G_REC, REC_SIZE; lia]|].
split; [apply (dgb_aval_mem_kept rd); [exact Vcd | intros k Hk; apply KG; unfold OFF_CODE, A_G_REC, REC_SIZE; lia]|].
split; [apply (dgb_aval_mem_kept rd); [exact Vnr | intros k Hk; apply KG; unfold OFF_NREPLIES, A_G_REC, REC_SIZE; lia]|].
split; [apply (dgb_aval_mem_kept rd); [exact Vst | intros k Hk; apply KG; unfold OFF_STATE, A_G_REC, REC_SIZE; lia]|].
split; [apply (dgb_aval_mem_kept rd); [exact Vho | intros k Hk; apply KG; unfold OFF_HOST, A_G_REC, REC_SIZE; lia]|].
exact Rs.
Qed.
(* the answer the recorder holds: 0, or the start of one of its blocks (A s3's dg_old) *)
Lemma dgb_old : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
exists old, aval_mem rd (gr + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) (lay_blocks Q) /\ 1 <= m).
Proof.
intros bl rd gr sc R Q (_ & _ & _ & _ & HA & _). unfold aanswer_at in HA.
destruct (r_answer R) as [x|], (l_answer Q) as [[qq m]|] eqn:Eq; try contradiction.
- destruct HA as (H1 & _ & _ & Hsz & _). exists qq. split; [exact H1|]. right. exists m.
  cbn [fst snd] in *. split; [|pose proof (Nat2Z.is_nonneg (length x)); lia].
  unfold lay_blocks. rewrite Eq. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- exists 0. split; [exact HA | left; reflexivity].
Qed.

(* every block the representation names is a live block (lib/B/Prog socket_send's lay_blocks_in) *)
Lemma dgb_lay_blocks_in : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _ & _) pn Hpn.
unfold lay_blocks in Hpn.
apply in_app_or in Hpn as [Hc | Hpn]; [|apply in_app_or in Hpn as [Hs | Hpn]; [|apply in_app_or in Hpn as [Ha | Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as (i & Hi).
  destruct HC as (_ & HlenQ & _ & Hcalls & _).
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc'; [|apply nth_error_Some in Hlt; contradiction].
  exact (dgb_acall_blocks _ _ _ _ _ (proj1 (Hcalls i c P Hc' Hi)) pn Hin).
- destruct HC as (_ & _ & _ & _ & Hsp & _). exact (dgb_acall_blocks _ _ _ _ _ Hsp pn Hs).
- unfold aanswer_at in HA. destruct (r_answer R) as [xa|], (l_answer Q) as [pa|]; cbn [oblk In] in Ha; try contradiction.
  destruct Ha as [<- | []]. exact (proj1 (proj2 (proj2 HA))).
- unfold areply_at in HR. destruct (r_reply R) as [xr|], (l_reply Q) as [pr|]; cbn [oblk In] in Hr; try contradiction.
  destruct Hr as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.
Lemma dgb_nodup_app_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
inversion Hnd as [|y' l' Hni Hnd' Heq]; subst. destruct H1 as [<- | H1].
- apply Hni. apply in_or_app. right. exact H2.
- exact (IH l2 x Hnd' H1 H2).
Qed.
Lemma dgb_in_filter : forall (old : Z) (L : list (Z * Z)) pn,
In pn (filter (fun pn : Z * Z => fst pn =? old) L) -> In pn L /\ fst pn = old.
Proof.
intros old L pn. induction L as [|y L IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. apply Z.eqb_eq. destruct (fst y =? old); [reflexivity | first [destruct Hd | discriminate Hd]].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.
(* the block lists of the post (descriptors_get_c.v:105-116), from the lists the walk meets: L0 at the entry, Lc after
   record() (F freed), L3 after xstrdup's copy (p, kx), Lf after answer (the old answer freed, (p1, n) the recorder's
   copy, (p2, n) the caller's) *)
Lemma dgb_post_blocks : forall (L0 Lc L3 Lf F QL OT O O' : list (Z * Z)) (p kx p1 p2 n old : Z),
Permutation L0 (Lc ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn QL -> In pn O) -> (forall pn, In pn QL -> In pn Lc) ->
(forall pn, In pn O -> In pn Lc -> In pn QL) ->
Permutation L3 ((p, kx) :: Lc) -> Forall (fun qk => iv_apart p kx (fst qk) (snd qk)) Lc -> 1 <= kx ->
Permutation OT (QL ++ [(p, kx)]) ->
(old = 0 \/ exists m, In (old, m) QL) ->
(forall b1 b2, In b1 L3 -> In b2 L3 -> fst b1 = fst b2 -> b1 = b2) -> (forall b, In b L3 -> 4096 <= fst b) ->
(forall pn, In pn L3 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn Lf <-> (In pn L3 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn O' <-> (In pn OT /\ fst pn <> old) \/ pn = (p1, n)) ->
(forall b1 b2, In b1 Lf -> In b2 Lf -> fst b1 = fst b2 -> b1 = b2) ->
(forall b1 b2, In b1 Lf -> In b2 Lf -> b1 <> b2 -> iv_apart (fst b1) (snd b1) (fst b2) (snd b2)) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn L0) /\
(forall pn, In pn L0 -> ~ In pn O -> pn <> (p2, n)) /\ ~ In p2 (map fst O') /\
(forall pn, In pn L0 -> ~ In pn O -> In pn Lf /\ iv_apart (fst pn) (snd pn) p2 n) /\
(forall pn, In pn Lf -> (In pn L0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)).
Proof.
intros L0 Lc L3 Lf F QL OT O O' p kx p1 p2 n old HP0 HFO HQO HQc HOQ HP3 HFr Hkx HOT Hold Hst3 H4096 HGf H12 HLf HO' Hstf Hapf.
assert (L3c : forall pn, In pn Lc -> In pn L3) by (intros pn H; apply (Permutation_in _ (Permutation_sym HP3)); right; exact H).
assert (L3p : In (p, kx) L3) by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
assert (L0s : forall pn, In pn L0 -> In pn Lc \/ In pn F)
  by (intros pn H; apply in_app_iff; exact (Permutation_in _ HP0 H)).
assert (Lc0 : forall pn, In pn Lc -> In pn L0)
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HP0)); apply in_app_iff; left; exact H).
assert (OTs : forall pn, In pn OT -> In pn QL \/ pn = (p, kx)).
{ intros pn H. apply (Permutation_in _ HOT) in H. apply in_app_iff in H as [H | [<- | []]]; [left; exact H | right; reflexivity]. }
assert (OT3 : forall pn, In pn OT -> In pn L3) by (intros pn H; destruct (OTs pn H) as [H' | ->]; [exact (L3c pn (HQc pn H')) | exact L3p]).
(* a start that is old belongs to a block of QL only *)
assert (Hold3 : forall pn, In pn L3 -> fst pn = old -> In pn QL).
{ intros pn H He. destruct Hold as [-> | (m & Hm)]; [pose proof (H4096 pn H); lia|].
  rewrite (Hst3 pn (old, m) H (L3c _ (HQc _ Hm)) He). exact Hm. }
(* the copy (p, kx) is no block of Lc *)
assert (Hpc : ~ In (p, kx) Lc).
{ intros H. rewrite Forall_forall in HFr. specialize (HFr _ H). unfold iv_apart in HFr. cbn [fst snd] in HFr. lia. }
split; [|split; [|split; [|split]]].
- intros pn H. apply HO' in H as [(H & _) | ->].
  + destruct (OTs pn H) as [H' | ->]; [left; exact (HQO _ H')|].
    destruct (in_dec dgb_pair_dec (p, kx) L0) as [H0|H0]; [|right; exact H0].
    destruct (L0s _ H0) as [Hc | Hf]; [exfalso; exact (Hpc Hc) | left; exact (HFO _ Hf)].
  + destruct (in_dec dgb_pair_dec (p1, n) L0) as [H0|H0]; [|right; exact H0].
    destruct (L0s _ H0) as [Hc | Hf]; [| left; exact (HFO _ Hf)].
    destruct (Z.eq_dec p1 old) as [Ho | Ho]; [left; exact (HQO _ (Hold3 _ (L3c _ Hc) Ho))|].
    exfalso. exact (proj1 (HGf _ (L3c _ Hc) Ho) eq_refl).
- intros pn H0 HnO Ep. subst pn. destruct (L0s _ H0) as [Hc | Hf]; [| exact (HnO (HFO _ Hf))].
  assert (Hne : p2 <> old) by (intros He; exact (HnO (HQO _ (Hold3 _ (L3c _ Hc) He)))).
  exact (proj2 (HGf _ (L3c _ Hc) Hne) eq_refl).
- intros H. apply in_map_iff in H as (pn & Hpn & H).
  assert (Hf2 : In (p2, n) Lf) by (apply HLf; right; right; reflexivity).
  apply HO' in H as [(H & Hne) | ->].
  + assert (Hf : In pn Lf) by (apply HLf; left; split; [exact (OT3 pn H) | exact Hne]).
    pose proof (Hstf pn (p2, n) Hf Hf2 Hpn) as Ep. subst pn. exact (proj2 (HGf _ (OT3 _ H) Hne) eq_refl).
  + cbn [fst] in Hpn. exact (H12 Hpn).
- intros pn H0 HnO. destruct (L0s _ H0) as [Hc | Hf]; [| exfalso; exact (HnO (HFO _ Hf))].
  assert (Hne : fst pn <> old) by (intros He; exact (HnO (HQO _ (Hold3 _ (L3c _ Hc) He)))).
  assert (Hf : In pn Lf) by (apply HLf; left; split; [exact (L3c _ Hc) | exact Hne]).
  split; [exact Hf|].
  apply (Hapf pn (p2, n) Hf ltac:(apply HLf; right; right; reflexivity)).
  intros Ep. subst pn. exact (proj2 (HGf _ (L3c _ Hc) Hne) eq_refl).
- intros pn H. apply HLf in H as [(H & Hne) | [-> | ->]].
  + apply (Permutation_in _ HP3) in H as [<- | Hc].
    * right; left. apply HO'. left. split; [|exact Hne]. apply (Permutation_in _ (Permutation_sym HOT)).
      apply in_app_iff. right. left. reflexivity.
    * destruct (in_dec dgb_pair_dec pn O) as [HinO | HnO].
      -- right; left. apply HO'. left. split; [|exact Hne]. apply (Permutation_in _ (Permutation_sym HOT)).
         apply in_app_iff. left. exact (HOQ _ HinO Hc).
      -- left. split; [exact (Lc0 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

(* a string argument over a reader that keeps its bytes: the read-only arm's other conditions (cmd_addr_b,
   cmd_hull_b, the literal's end) read no memory on a Theorem Labs lane 917ca7ac6b1, so only the string's bytes have to be kept *)
Lemma dgb_argA_kept : forall Bx ly S (rd rd' : reader) ro O q v,
astr_argA Bx ly S rd ro O q (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (q + i) = rd (q + i)) ->
astr_argA Bx ly S rd' ro O q (Some v).
Proof.
intros Bx ly S rd rd' ro O q v H HK. unfold astr_argA in *. cbv beta iota zeta in *.
destruct H as (H0 & Hs & Hn & Harm).
split; [exact H0|]. split; [|split; [exact Hn | exact Harm]].
apply (dgb_rastr_kept rd); [exact Hs | exact HK].
Qed.

Lemma dgb_bv5 : forall r (b : bv 5), bv_unsigned b = r -> Z_to_bv 5 r = b.
Proof.
intros r b H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. unfold bv_wrap.
pose proof (bv_unsigned_in_range 5 b) as Hb. apply Z.mod_small. exact Hb.
Qed.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Variable B : asyms.
(* the bridge from the listing's object atoms to the image's addresses (the descriptors_get statement's VOBJS) *)
Hypothesis VOBJS : cmd_val_objs.
(* the program functions' call targets (CmdObj.v cmd_sig_prog) and the allocator record (lib/B/YF0m.v), as the
   recorder walks carry them (a Theorem Labs lane's RECB-NAMED-HYPS.md) *)
Hypothesis SIGP : cmd_sig_prog.
Hypothesis HB : CmdBSyms B.

(* the verb's address: 0x8cccc / 0x8ccd0 denote the atom A_OBJ 87 *)
Lemma dgb_verb_val : VAL (A_OBJ 87) = 0x21fa0.
Proof. rewrite (VOBJS 87%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.
Lemma dgb_verb_atom : A_OBJ 87 = 328%nat.
Proof. reflexivity. Qed.

Lemma dgb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dgb_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dgb_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* the verb's 15 bytes lie outside the runtime's owned statics and the errno cell *)
Lemma dgb_verb_unowned : forall i, 0 <= i < 15 ->
~ Exists (in_zr (0x21fa0 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21fa0 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split; [|unfold TFIB_ERRNO; lia].
apply dgb_not_owned_b.
assert (Hc : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] ->
  existsb (fun r => (fst r <=? 0x21fa0 + j) && (0x21fa0 + j <? fst r + snd r)) Tfib_owned_static = false).
{ intros j Hj. repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]). destruct Hj. }
apply Hc. cbn [In]. lia.
Qed.

(* the record's checks of the verb's 15 bytes (lib/B/Prog/CmdChk.v) and its end in cmd_ro_ends (CmdRo.v), by
   computation: the second granule's shadow 7 is one of the record's constant shadow cells *)
Lemma dgb_verb_chk : cmd_addr_b 0x21fa0 15 = true /\ cmd_hull_b 0x21fa0 15 = true /\ In 0x21fae cmd_ro_ends.
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
destruct (proj1 (existsb_exists (Z.eqb 0x21fae) cmd_ro_ends) ltac:(vm_compute; reflexivity)) as (y & Hy & E).
rewrite (proj1 (Z.eqb_eq _ _) E). exact Hy.
Qed.

(* the verb as a read-only string argument: its 14 bytes, and astr_argA's read-only arm (lib/B/Prog/CmdRep.v) *)
Lemma dgb_verb_arg : forall ly S (rd : reader),
cmd_ro_ok rd -> cmd_ro_in (in_roP SEGS RLO RHI) ->
abytes_atR rd 0x21fa0 dgb_verb /\ astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21fa0 (Some dgb_verb).
Proof.
intros ly S rd HRO HRI.
assert (HL : abytes_atR rd 0x21fa0 RO_lit_21fa0).
{ clear - HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x21fa0 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HI : forall i, 0 <= i < 15 -> in_roP SEGS RLO RHI (0x21fa0 + i)).
{ clear - HRI. unfold cmd_ro_in in HRI.
  repeat match type of HRI with
  | (forall i, 0 <= i < _ -> _ (0x21fa0 + i)) /\ _ => exact (proj1 HRI)
  | _ /\ _ => apply proj2 in HRI
  end. }
rewrite <- dgb_verb_lit in HL.
split; [exact (dgb_abytes_prefix _ _ _ _ HL)|].
unfold astr_argA. split; [discriminate|]. split; [exact (conj HL dgb_verb_nz)|].
change (Z.of_nat (length dgb_verb) + 1) with 15. split; [unfold LMAX; lia|].
right. split; [intros i Hi; split; [exact (HI i Hi) | exact (dgb_verb_unowned i Hi)]|].
change (0x21fa0 + Z.of_nat (length dgb_verb)) with 0x21fae. exact dgb_verb_chk.
Qed.

(* rec_shape_of's premise on its verb (lib/B/Prog/rec_shape_of_c.v), for the call at 0x8ccd8 (a0 = 0x21fa0,
   a1 = 14) *)
Lemma dgb_verb_pre : forall ly S (rd : reader),
cmd_ro_ok rd -> cmd_ro_in (in_roP SEGS RLO RHI) ->
Z.of_nat (length dgb_verb) < 2 ^ 64 /\
(Z.of_nat (length dgb_verb) <= 16 ->
 abytes_atR rd 0x21fa0 dgb_verb /\
 (in_blockA (ablocks B ly S) 0x21fa0 (Z.of_nat (length dgb_verb)) \/
  astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21fa0 (Some dgb_verb))).
Proof.
intros ly S rd HRO HRI.
destruct (dgb_verb_arg ly S rd HRO HRI) as [HA HS].
rewrite dgb_verb_len. split; [lia|]. intros _. split; [exact HA | right; exact HS].
Qed.
End v.
