(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from an earlier version of lib/A/Prog/RecBLemmas.v (the frame relocation for fuzz_command) into fuzz_command's program-walk kit, without the Section hypothesis afree_null04_rule: recb_free_any takes the null free rule as its own premise, used only when the freed pointer is NULL, so every other lemma of Section w takes four hypotheses, not five. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/RecBLemmas.v for fuzz_command.asan-ubsan: module paths; the record's zero-shadow range that holds g_rec (0xad560, 0x5e3680 - 0xad560) and the shadow word of g_rec + 896 (2148222664) in that image. *)
(* Modified by Theorem Labs, 2026-10: for fuzz_command.asan-ubsan, lemmas that three B walks proved locally (arg_s, socket_send and pins_set): the allocator's new block given as the cons permutation of xmalloc_c.v's post (recb_fresh_disj_perm, recb_not_new_perm, recb_awr_new_block_perm), a footprint byte of any program static (recb_prog_awr) and what a callee with an empty footprint keeps (recb_call_keeps), each with its minimal form _m. *)
(* Facts about the recorder's representation on the ASan side (lib/B/Prog/CmdRep.v: rec_repA, arep_at) that the
   program walks of plugin-hostd/fuzz_command reuse.

   - `rd_agree rd rd' a n`: the reader rd' gives the same values as rd on [a, a + n). The representation reads only
     g_rec, record.spill and the recorder's own blocks, so it survives any change of memory outside those bytes
     (`*_agree_in`, `acall_at_agree`).
   - `arep_at_set_reply`: replace g_rec.nreplies, g_rec.reply and g_rec.reply_size (offsets 920 .. 943) and the
     reply block, keep every other field. This is the step of socket_send (RecModel.v:54-55 `rec_socket_send`) and
     of every caller that sets the reply.
   - `aval_mem_view` / `val_mem_view`: the n-wide field read over `aview segs H mem` is the symbolic executor's
     `val_mem segs (mrestrict H mem)`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the program's writable statics as (start, length): g_rec, record.spill, g_quitting (CmdGlob.v:13-15) *)
Definition recb_PG : list (Z * Z) := [(A_G_REC, REC_SIZE); (A_REC_SPILL, SC_SIZE); (A_G_QUITTING, 4)].

Definition rd_agree (rd rd' : reader) (a n : Z) : Prop := forall i, 0 <= i < n -> rd' (a + i) = rd (a + i).

Lemma rd_agree_at : forall rd rd' a m x, rd_agree rd rd' a m -> a <= x < a + m -> rd' x = rd x.
Proof. intros rd rd' a m x H Hx. replace x with (a + (x - a)) by lia. apply H. lia. Qed.

Lemma rd_agree_sub : forall rd rd' a m b n, rd_agree rd rd' a m -> a <= b -> b + n <= a + m -> rd_agree rd rd' b n.
Proof. intros rd rd' a m b n H H1 H2 i Hi. apply (rd_agree_at rd rd' a m). exact H. lia. Qed.

Lemma rd_agree_trans : forall rd1 rd2 rd3 a n, rd_agree rd1 rd2 a n -> rd_agree rd2 rd3 a n -> rd_agree rd1 rd3 a n.
Proof. intros rd1 rd2 rd3 a n H1 H2 i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.

Lemma rd_agree_of : forall (rd rd' : reader) a n, (forall x, a <= x < a + n -> rd' x = rd x) -> rd_agree rd rd' a n.
Proof. intros rd rd' a n H i Hi. apply H. lia. Qed.

Lemma aval_mem_agree_in : forall rd rd' a m b n v,
aval_mem rd b n v -> rd_agree rd rd' a m -> a <= b -> b + Z.of_nat n <= a + m -> aval_mem rd' b n v.
Proof. intros rd rd' a m b n v H Hg H1 H2 k Hk. rewrite (rd_agree_at rd rd' a m) by (exact Hg || lia). exact (H k Hk). Qed.

Lemma abytes_atR_agree_in : forall rd rd' a m b l,
abytes_atR rd b l -> rd_agree rd rd' a m -> a <= b -> b + Z.of_nat (length l) <= a + m -> abytes_atR rd' b l.
Proof. intros rd rd' a m b l H Hg H1 H2 i Hi. rewrite (rd_agree_at rd rd' a m) by (exact Hg || lia). exact (H i Hi). Qed.

Lemma astr_atR_agree_in : forall rd rd' a m p s,
astr_atR rd p s -> rd_agree rd rd' a m -> a <= p -> p + Z.of_nat (length s) + 1 <= a + m -> astr_atR rd' p s.
Proof.
intros rd rd' a m p s [H Hn] Hg H1 H2. split; [|exact Hn].
apply (abytes_atR_agree_in rd rd' a m); [exact H | exact Hg | exact H1 |]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma aval_mem_view : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma val_mem_view : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate]. cbn [option_map] in Hb.
injection Hb as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. rewrite Hb. reflexivity.
Qed.

(* the recorder blocks other than the reply *)
Definition lay_rest (Q : rlay) : list (Z * Z) := concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q).

Lemma lay_blocks_rest : forall Q, lay_blocks Q = lay_rest Q ++ oblk (l_reply Q).
Proof. intros Q. unfold lay_blocks, lay_rest. rewrite <- !app_assoc. reflexivity. Qed.

Lemma acall_at_agree : forall bl bl' rd rd' a c P,
acall_at bl rd a c P -> rd_agree rd rd' a CALL_SIZE ->
(forall pn, In pn P -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hg HP.
unfold acall_at. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [apply (aval_mem_agree_in rd rd' a CALL_SIZE); [exact H3 | exact Hg | unfold CALL_OFF_FN; lia | unfold CALL_OFF_FN, CALL_SIZE; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' a CALL_SIZE); [exact H4 | exact Hg | unfold CALL_OFF_NARGS; lia | unfold CALL_OFF_NARGS, CALL_SIZE; cbn; lia]|].
split; [exact H5|].
intros k s pn Hs Hpn. destruct (H6 k s pn Hs Hpn) as (V & Hnz & Hin & Hlen & Hstr).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
assert (HPin : In pn P) by (apply (nth_error_In P k); exact Hpn).
destruct (HP pn HPin) as [Hin' Hgp].
split; [apply (aval_mem_agree_in rd rd' a CALL_SIZE); [exact V | exact Hg | unfold CALL_OFF_ARGS; lia | unfold CALL_OFF_ARGS, CALL_SIZE; cbn; lia]|].
split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|].
apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
Qed.

Lemma In_concat_nth : forall {X} (ll : list (list X)) i (l : list X) x, nth_error ll i = Some l -> In x l -> In x (concat ll).
Proof. intros X ll i l x Hl Hx. apply in_concat. exists l. split; [exact (nth_error_In ll i Hl) | exact Hx]. Qed.

Lemma arep_at_set_reply : forall bl bl' rd rd' R Q n' y q',
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
rd_agree rd rd' A_G_REC OFF_NREPLIES ->
rd_agree rd rd' (A_G_REC + OFF_STATE) 16 ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_rest Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_NREPLIES) 4 n' -> 0 <= n' < 2 ^ 31 ->
areply_at bl' rd' A_G_REC y q' ->
(forall pn, q' = Some pn -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE /\
 ~ In (fst pn) (map fst (lay_rest Q))) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (set_reply R n' y) (RLay (l_calls Q) (l_spill Q) (l_answer Q) q').
Proof.
intros bl bl' rd rd' R Q n' y q' (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) Hgl Hgh Hsp Hrest Hn Hnr Hrep Hnew.
assert (Hrest' : forall pn, In pn (lay_rest Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) by exact Hrest.
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
  unfold ag1_calls. cbn [r_calls r_spill set_reply l_calls l_spill]. split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_NREPLIES); [exact Hnc | exact Hgl | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, OFF_NREPLIES; cbn; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (acall_at_agree bl bl' rd rd'); [exact Hca | |].
    - apply (rd_agree_sub rd rd' A_G_REC OFF_NREPLIES); [exact Hgl | unfold OFF_CALLS, CALL_SIZE; lia |].
      unfold OFF_CALLS, CALL_SIZE, OFF_NREPLIES. lia.
    - intros pn Hpn. apply Hrest'. unfold lay_rest. apply in_or_app. left. exact (In_concat_nth _ i P pn HP Hpn). }
  split; [|exact Hspf].
  apply (acall_at_agree bl bl' rd rd'); [exact Hspill | unfold CALL_SIZE; exact Hsp |].
  intros pn Hpn. apply Hrest'. unfold lay_rest. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
split.
{ cbn [r_answer set_reply l_answer]. unfold aanswer_at in *.
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HA as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    assert (Hpn : In pn (lay_rest Q)) by (unfold lay_rest; apply in_or_app; right; apply in_or_app; right; rewrite EA; left; reflexivity).
    destruct (Hrest' pn Hpn) as [Hin' Hgp].
    split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_NREPLIES); [exact V | exact Hgl | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, OFF_NREPLIES; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
  - apply (aval_mem_agree_in rd rd' A_G_REC OFF_NREPLIES); [exact HA | exact Hgl | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, OFF_NREPLIES; cbn; lia]. }
split; [cbn [r_reply set_reply l_reply]; exact Hrep|].
split.
{ destruct HSC as (Vr & Vc & _ & Vs & Vh & Rr & Rc & _ & Rs & Rh). unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_reply].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_NREPLIES); [exact Vr | exact Hgl | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, OFF_NREPLIES; cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_NREPLIES); [exact Vc | exact Hgl | unfold OFF_CODE; lia | unfold OFF_CODE, OFF_NREPLIES; cbn; lia]|].
  split; [exact Hn|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vs | exact Hgh | lia | cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vh | exact Hgh | unfold OFF_HOST, OFF_STATE; lia | unfold OFF_HOST, OFF_STATE; cbn; lia]|].
  repeat split; lia. }
{ destruct HOWN as [HND Hap2]. unfold ag1_own in *. rewrite lay_blocks_rest in HND, Hap2.
  assert (E' : lay_blocks (RLay (l_calls Q) (l_spill Q) (l_answer Q) q') = lay_rest Q ++ oblk q') by (rewrite lay_blocks_rest; reflexivity).
  rewrite E'.
  assert (Hap' : forall pn, In pn (lay_rest Q) -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
  { intros pn Hpn. apply Hap2. apply in_or_app. left. exact Hpn. }
  split.
  - rewrite map_app in HND |- *. apply NoDup_ListNoDup in HND. apply NoDup_ListNoDup.
    apply List.NoDup_app_remove_r in HND.
    destruct q' as [pn|]; cbn [oblk map]; [|rewrite app_nil_r; exact HND].
    apply List.NoDup_app; [exact HND | constructor; [intros [] | constructor] |].
    intros a Ha Hb. destruct Hb as [<- | []]. destruct (Hnew pn eq_refl) as (_ & _ & Hni). exact (Hni Ha).
  - intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact (Hap' pn Hpn)|].
    destruct q' as [pn'|]; cbn [oblk] in Hpn; [|destruct Hpn]. destruct Hpn as [<- | []].
    destruct (Hnew pn' eq_refl) as (H1 & H2 & _). split; assumption. }
Qed.

(* the reply pointer the recorder holds: g_rec.reply is the reply block's address, or 0 when there is none *)
Definition oaddr (q : option (Z * Z)) : Z := match q with Some pn => fst pn | None => 0 end.

Lemma areply_at_ptr : forall bl rd gr y q,
areply_at bl rd gr y q ->
aval_mem rd (gr + OFF_REPLY) 8 (oaddr q) /\ (forall pn, q = Some pn -> In pn bl /\ fst pn <> 0) /\
(q = None <-> y = None).
Proof.
intros bl rd gr y q H. unfold areply_at in H.
destruct y as [x|], q as [pn|]; try contradiction.
- destruct H as (V & _ & Hnz & _ & Hin & _). split; [exact V|]. split; [|split; discriminate].
  intros pn' Hq. injection Hq as <-. split; [exact Hin | exact Hnz].
- destruct H as [V _]. split; [exact V|]. split; [intros pn' Hq; discriminate | tauto].
Qed.

Lemma list_nodup_app_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
inversion Hnd as [|y' l' Hni Hnd' Heq]; subst. destruct H1 as [<- | H1].
- apply Hni. apply in_or_app. right. exact H2.
- exact (IH l2 x Hnd' H1 H2).
Qed.

Lemma acall_at_in : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H6) pn Hpn.
destruct (In_nth_error P pn Hpn) as (k & Hk).
assert (Hlt : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hlt; contradiction].
exact (proj1 (proj2 (proj2 (H6 k s pn Hs Hk)))).
Qed.

(* every block the representation names is a live block *)
Lemma lay_blocks_in : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _ & _) pn Hpn.
unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hc | Hpn]; [|apply in_app_or in Hpn as [Hs | Hpn]; [|apply in_app_or in Hpn as [Ha | Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as (i & Hi).
  destruct HC as (_ & HlenQ & _ & Hcalls & _).
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc'; [|apply nth_error_Some in Hlt; contradiction].
  exact (acall_at_in _ _ _ _ _ (proj1 (Hcalls i c P Hc' Hi)) pn Hin).
- destruct HC as (_ & _ & _ & _ & Hsp & _). exact (acall_at_in _ _ _ _ _ Hsp pn Hs).
- unfold aanswer_at in HA. destruct (r_answer R) as [xa|], (l_answer Q) as [pa|]; cbn [oblk In] in Ha; try contradiction.
  destruct Ha as [<- | []]. exact (proj1 (proj2 (proj2 HA))).
- unfold areply_at in HR. destruct (r_reply R) as [xr|], (l_reply Q) as [pr|]; cbn [oblk In] in Hr; try contradiction.
  destruct Hr as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.


Section d.
Variable B : asyms.
(* the representation with the reply replaced: the recorder now owns its other blocks and the new reply block *)
Lemma rec_repA_set_reply : forall ly S rd R Q ly' S' rd' n' y q',
arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q ->
rd_agree rd rd' A_G_REC OFF_NREPLIES ->
rd_agree rd rd' (A_G_REC + OFF_STATE) 16 ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_rest Q) -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_NREPLIES) 4 n' -> 0 <= n' < 2 ^ 31 ->
areply_at (ablocks B ly' S') rd' A_G_REC y q' ->
(forall pn, q' = Some pn -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE /\
 ~ In (fst pn) (map fst (lay_rest Q))) ->
rec_repA B ly' S' rd' (set_reply R n' y) (lay_rest Q ++ oblk q').
Proof.
intros ly S rd R Q ly' S' rd' n' y q' HA Hgl Hgh Hsp Hrest Hn Hnr Hrep Hnew.
exists (RLay (l_calls Q) (l_spill Q) (l_answer Q) q'). split.
- exact (arep_at_set_reply _ _ rd rd' R Q n' y q' HA Hgl Hgh Hsp Hrest Hn Hnr Hrep Hnew).
- intros pn. rewrite lay_blocks_rest. unfold lay_rest. cbn [l_calls l_spill l_answer l_reply]. reflexivity.
Qed.
End d.

(* The walks' lemmas over the program statics (recb_PG) and the allocator's blocks, at the hypotheses every
   recorder walk carries: the runtime free rule afree04_rule, the allocator record HB, and the two program-static
   facts cmd_prog_img / cmd_prog_writable (the named Section hypotheses of the recorder walks, without
   afree_null04_rule). Section w states each lemma as recb_x_m at only the hypotheses its proof uses, so a walk part
   that lacks the others can apply it; Section w_full restates each as recb_x at all four (Default Proof Using), so a
   walk binds them once: `Let x := recb_x B MT AFREE4 HB cmd_prog_img cmd_prog_writable.` The null free rule is a
   premise of recb_free_any only, needed when the freed pointer is NULL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
Local Open Scope Z_scope.

Definition recb_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma recb_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) recb_PG.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma recb_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) recb_PG.
Proof. intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md ->
Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* no Default Proof Using: each lemma takes only the section hypotheses its proof uses *)

(* the record's program statics are g_rec, record.spill and g_quitting (CmdBSyms' ts_prog, lib/B/YF0m.v) *)
Lemma recb_ts_prog_m : as_prog_static B = recb_PG.
Proof. rewrite (ts_prog B HB). reflexivity. Qed.

(* CmdRecFacts.v (vi) cmd_prog_unowned, from the record's ts_prog and asyms_ok (YCbq.v's prog_static_sep) *)
Lemma recb_prog_unowned_m : forall a, Exists (in_zr a) recb_PG ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a HP. split; [exact (cmd_prog_img a HP)|].
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite recb_ts_prog_m; exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.

(* a g_rec byte in the footprint is a byte the walk may write: awr_byte's program-static disjunct *)
Lemma recb_grec_awr_m : forall STK sp0 FP bl0 blc fr0 ly own a,
inFP FP a -> A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof.
intros STK sp0 FP bl0 blc fr0 ly own a Hfp Ha. pose proof (recb_grec_in a Ha) as HP.
right; right; right; right; left. split; [exact Hfp|]. split; [rewrite recb_ts_prog_m; exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma recb_grec_writable_m : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k ->
A_G_REC <= a < A_G_REC + REC_SIZE -> writable_at SEGS (mrestrict (w_H Wc) memc) a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a HJ Ha.
exact (cmd_prog_writable _ _ _ _ _ a (proj1 HJ) (recb_grec_in a Ha)).
Qed.

(* the 16 bytes g_rec.reply .. g_rec.reply_size: inside the record's zero-shadow range of the image's
   .bss up to g_rec's end (lib/B/YF0m.v, Tfib_zero_shadow: (0xad560, 0x5e3680 - 0xad560)), so addressable, and every shadow byte of their 8-byte shadow word is present *)
Lemma recb_rep_addressable_m : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (A_G_REC + OFF_REPLY) 16.
Proof.
intros ly S W mem md HAR.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xad560, 0x5e3680 - 0xad560)); [exact HAR | | | | |];
[unfold Tfib_zero_shadow; cbn; tauto | cbn; reflexivity | cbn; reflexivity | | ]; unfold A_G_REC, OFF_REPLY; cbn [fst snd]; lia.
Qed.

Lemma recb_rep_hull_m : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (aview SEGS (w_H W) mem) (A_G_REC + OFF_REPLY) 16.
Proof.
intros ly S W mem md HAR s Hs.
pose proof (cmd_zshadow_sub SEGS B LAWS HB ly S W mem md (0xad560, 0x5e3680 - 0xad560) (A_G_REC + 896) 64 HAR
ltac:(unfold Tfib_zero_shadow; cbn; tauto) ltac:(cbn; reflexivity) ltac:(unfold A_G_REC; cbn; reflexivity)
ltac:(unfold A_G_REC; cbn [fst]; lia) ltac:(unfold A_G_REC; cbn [fst snd]; lia)) as Hz.
assert (Hsh : shadow_of_addr SHADOW_OFF (A_G_REC + 896) = 2148222664) by (unfold shadow_of_addr, SHADOW_OFF, A_G_REC; reflexivity).
assert (E1 : shadow_addr (A_G_REC + OFF_REPLY) / 8 * 8 = 2148222664) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (A_G_REC + OFF_REPLY + 16 - 1) / 8 * 8 + 8 = 2148222672) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
replace s with (shadow_of_addr SHADOW_OFF (A_G_REC + 896) + (s - 2148222664)) by (rewrite Hsh; lia).
rewrite (Hz (s - 2148222664)) by (change (64 / 8) with 8; lia). discriminate.
Qed.

(* the acall_kept of a runtime call keeps every byte of the program's statics (image bytes the runtime does not own) *)
Lemma recb_kept_prog_m : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop) a,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> Exists (in_zr a) recb_PG ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er a (_ & _ & K3 & _) HP. destruct (recb_prog_unowned_m a HP) as (H1 & H2 & H3).
exact (K3 a H1 H2 H3).
Qed.

(* the free of g_rec.reply, NULL or the recorder's reply block, in one form; the free of NULL is the null free rule's,
   which the caller gives only when q = None *)
Definition recb_free_post (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world SEGS) mem md own lyc Sc (W : world SEGS) memT
(k o : Z) (raw : word) (regsT : bvmap 5 word) (q : option (Z * Z)) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B lyc Sc) (oblk q ++ ablocks B ly2 S2) /\
frames S2 = frames Sc /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
(fun a => exists pn, q = Some pn /\ fst pn <= a < fst pn + req_size (snd pn)) /\
mo_le MT Sc S2 (mo_free MT).

Lemma recb_free_any_m : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch q,
(q = None -> afree_null04_rule SEGS B MT) ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
(forall pn, q = Some pn -> In pn (ablocks B lyc Sc) /\
 (In pn (ablocks B ly S) -> forall i, 0 <= i < req_size (snd pn) -> inFP FP (fst pn + i))) ->
getr regsT 10 = w64 (oaddr q) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(recb_free_post STK sp0 FP ly S W0 mem md own lyc Sc W memT k o raw regsT q).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch q HNULL HJ Hq Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch MOK.
destruct q as [[pa n]|].
- destruct (Hq (pa, n) eq_refl) as [Hin Hcov]. cbn [fst snd oaddr] in *.
  eapply SRr_mono.
  { exact (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
    HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch Hcov MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & E1 & E2) & Hfr & HK & MLE & _).
  exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split; [rewrite E1, E2; cbn [oblk app]; apply Permutation_sym; apply Permutation_middle|].
  split; [exact Hfr|]. split; [|exact MLE].
  eapply (acall_kept_mono_E SEGS B); [exact HK|]. intros a Ha. exists (pa, n). split; [reflexivity | exact Ha].
- cbn [oaddr] in Ha0.
  eapply SRr_mono.
  { exact (afree_null04_sub SEGS B LAWS pa_segs_low MT (HNULL eq_refl) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
    HJ Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hperm & Hfr & HK & MLE & _).
  exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split; [cbn [oblk app]; apply Permutation_sym; exact Hperm|].
  split; [exact Hfr|]. split; [|exact MLE].
  eapply (acall_kept_mono_E SEGS B); [exact HK|]. intros a [].
Qed.

Lemma recb_val_mem_frame_m : forall H H' (m m' : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v ->
(forall k, 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply val_mem_view. intros k Hk'. rewrite Hk by lia. exact (aval_mem_view SEGS H m a n v Hv k Hk').
Qed.

Lemma recb_ablocks_nodup_m : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
{ intros [p n] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos n ltac:(lia))). }
revert Hp Hpos. generalize (ablocks B ly S) as l. induction l as [|y l IH]; intros Hp Hpos; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor.
- intros Hin. rewrite Forall_forall in Hf.
  pose proof (Hf (fst y, req_size (snd y)) (in_map (fun b => (fst b, req_size (snd b))) l y Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (Hpos y (or_introl eq_refl)). lia.
- apply IH; [exact Hp | intros b Hb; apply Hpos; right; exact Hb].
Qed.

(* a block the allocator hands out is apart from every block it already holds *)
Lemma recb_fresh_disj_m : forall ly3 S3 (W : world SEGS) mem md L res n b m,
AR SEGS B ly3 S3 W mem md -> ablocks B ly3 S3 = L ++ [(res, n)] -> In (b, m) L ->
zdisjoint (b, req_size m) (res, req_size n).
Proof.
intros ly3 S3 W mem md L res n b m HAR E Hin. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _]. rewrite E in Hp.
destruct (in_split _ _ Hin) as (l1 & l2 & ->).
rewrite !map_app in Hp. cbn [map] in Hp.
exact (pairwise_In2 _ _ _ _ (map (fun b0 => (fst b0, req_size (snd b0))) l1) (map (fun b0 => (fst b0, req_size (snd b0))) l2) [] Hp
ltac:(rewrite <- app_assoc; reflexivity)).
Qed.

Lemma recb_heap_noimg_m : forall ly S (W : world SEGS) mem md b m a,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma recb_heap_apart_m : forall ly S (W : world SEGS) mem md p n lo len,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof.
intros ly S W mem md p n lo len HAR Hin Hn Hlen Himg. unfold iv_apart.
destruct (Z_le_gt_dec (p + n) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos n Hn) as Hq.
apply (recb_heap_noimg_m ly S W mem md p n (Z.max p lo) HAR Hin); [lia | apply Himg; lia].
Qed.

(* the recorder's blocks other than the reply survive the free of the reply *)
Lemma recb_lay_rest_L2_m : forall ly S rd R Q L2,
arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q ->
Permutation (ablocks B ly S) (oblk (l_reply Q) ++ L2) ->
forall pn, In pn (lay_rest Q) -> In pn L2.
Proof.
intros ly S rd R Q L2 HA HP pn Hpn.
assert (Hpl : In pn (lay_blocks Q)) by (rewrite lay_blocks_rest; apply in_or_app; left; exact Hpn).
pose proof (lay_blocks_in _ _ _ _ _ _ HA pn Hpl) as Hin.
apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [Hr | H]; [|exact H]. exfalso.
destruct HA as (_ & _ & _ & _ & _ & _ & _ & HND & _). rewrite lay_blocks_rest in HND.
apply NoDup_ListNoDup in HND. rewrite map_app in HND.
exact (list_nodup_app_disj _ _ (fst pn) HND (in_map fst _ _ Hpn) (in_map fst _ _ Hr)).
Qed.

Lemma recb_run_keeps_m : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hfr Ha Hw. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hw.
Qed.

(* the free of the reply keeps every kept byte *)
Lemma recb_free_keeps_m : forall ly S (W : world SEGS) memc md (W2 : world SEGS) mem2 slo shi q L2 a,
AR SEGS B ly S W memc md -> List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (oblk q ++ L2) ->
acall_kept SEGS B ly S W memc W2 mem2 slo shi (fun a => exists pn, q = Some pn /\ fst pn <= a < fst pn + req_size (snd pn)) ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L2 /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros ly S W memc md W2 mem2 slo shi q L2 a HAR ND HP HK [HPG | (b & m & Hbm & Hab & Hni)].
- exact (recb_kept_prog_m _ _ _ _ _ _ _ _ _ a HK HPG).
- destruct HK as (_ & K2 & _).
  assert (Hin : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hbm).
  replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin ltac:(lia)).
  intros (pn & Hq & Hpa). subst q.
  assert (Hpn : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; left; reflexivity).
  destruct (recb_pair_dec (b, m) pn) as [Heq | Hne].
  + subst pn. apply (Permutation_NoDup HP) in ND.
    exact (list_nodup_app_disj _ _ (b, m) ND (or_introl eq_refl) Hbm).
  + destruct pn as [p n]. pose proof (sep_blocks SEGS B LAWS ly S W memc md b m p n HAR Hin Hpn Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd, Hpa. lia.
Qed.

(* the malloc keeps every kept byte: the new block is apart from every block that was live *)
Lemma recb_malloc_keeps_m : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi ly4 S4 mem4 md4 res n a,
AR SEGS B ly4 S4 W2 mem4 md4 -> ablocks B ly4 S4 = ablocks B lyc Sc ++ [(res, n)] ->
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun a => res <= a < res + req_size n) ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi ly4 S4 mem4 md4 res n a HAR4 E4 HK [HPG | (b & m & Hbm & Hab & Hni)].
- exact (recb_kept_prog_m _ _ _ _ _ _ _ _ _ a HK HPG).
- destruct HK as (_ & K2 & _).
  replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hbm ltac:(lia)).
  pose proof (recb_fresh_disj_m ly4 S4 W2 mem4 md4 (ablocks B lyc Sc) res n b m HAR4 E4 Hbm) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a kept byte is not a byte of a block the allocator hands out later *)
Lemma recb_not_new_m : forall ly4 S4 (W4 : world SEGS) mem4 md4 L res n a,
AR SEGS B ly4 S4 W4 mem4 md4 -> ablocks B ly4 S4 = L ++ [(res, n)] -> 0 <= n ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
~ (res <= a < res + n).
Proof.
intros ly4 S4 W4 mem4 md4 L res n a HAR E Hn [HPG | (b & m & Hbm & Hab & Hni)] Ha.
- assert (Hin : In (res, n) (ablocks B ly4 S4)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (req_size_pos n Hn) as Hq.
  exact (recb_heap_noimg_m ly4 S4 W4 mem4 md4 res n a HAR Hin ltac:(lia) (cmd_prog_img a HPG)).
- pose proof (recb_fresh_disj_m ly4 S4 W4 mem4 md4 L res n b m HAR E Hbm) as Hd. pose proof (req_size_pos n Hn) as Hq.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* The allocator's new block as xmalloc_c.v's post gives it, a cons permutation
   `Permutation (ablocks B ly' S') ((p, LIVE_XMALLOC n) :: ablocks B ly S)`, where recb_fresh_disj_m / recb_not_new_m
   above and the core's awr_new_block take an equation `ablocks = L ++ [(res, n)]` (the B walks' arg_s as_fresh_disj /
   as_awr_new and socket_send ssk_fresh_disj / ssk_not_new / ssk_awr_new_block proved these locally). *)
Lemma recb_fresh_disj_perm_m : forall ly3 S3 (W : world SEGS) mem md L res n b m,
AR SEGS B ly3 S3 W mem md -> Permutation (ablocks B ly3 S3) ((res, n) :: L) -> In (b, m) L ->
zdisjoint (b, req_size m) (res, req_size n).
Proof.
intros ly3 S3 W mem md L res n b m HAR HP Hin.
pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m ly3 S3 W mem md HAR)) as ND.
inversion ND as [|x l Hni Hnd]; subst.
assert (Hne : (b, m) <> (res, n)) by (intros E; rewrite E in Hin; exact (Hni Hin)).
assert (Hb : In (b, m) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact Hin).
assert (Hr : In (res, n) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
exact (sep_blocks SEGS B LAWS ly3 S3 W mem md b m res n HAR Hb Hr Hne).
Qed.

Lemma recb_not_new_perm_m : forall ly4 S4 (W4 : world SEGS) mem4 md4 L res n a,
AR SEGS B ly4 S4 W4 mem4 md4 -> Permutation (ablocks B ly4 S4) ((res, n) :: L) -> 0 <= n ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
~ (res <= a < res + n).
Proof.
intros ly4 S4 W4 mem4 md4 L res n a HAR HP Hn [HPG | (b & m & Hbm & Hab & Hni)] Ha.
- assert (Hin : In (res, n) (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  pose proof (req_size_pos n Hn) as Hq.
  exact (recb_heap_noimg_m ly4 S4 W4 mem4 md4 res n a HAR Hin ltac:(lia) (cmd_prog_img a HPG)).
- pose proof (recb_fresh_disj_perm_m ly4 S4 W4 mem4 md4 L res n b m HAR HP Hbm) as Hd. pose proof (req_size_pos n Hn) as Hq.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a byte of the block a callee handed out is a byte the walk may write (the core's awr_new_block) *)
Lemma recb_awr_new_block_perm_m : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR SEGS B ly2 S2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B lyc Sc) ->
In (res, n) blc -> 0 <= i < req_size n ->
awr_byte SEGS B STK sp0 FP (ablocks B ly S) blc (frames S) lyq own (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq HJ HAR2 HP Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec recb_pair_dec (res, n) (ablocks B ly S)) as [H0 | H0].
- assert (Hc : ~ In (res, n) (ablocks B lyc Sc)).
  { intros Hc. pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m ly2 S2 W2 mem2 md2 HAR2)) as ND.
    inversion ND as [|x l Hni Hnd]; subst. exact (Hni Hc). }
  right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | lia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | lia].
Qed.

(* a footprint byte of any program static is a byte the walk may write: awr_byte's program-static disjunct
   (recb_grec_awr_m for every program static: record's slot may be in record.spill; pins_set's recb_prog_awr) *)
Lemma recb_prog_awr_m : forall STK sp0 FP bl0 blc fr0 ly own a,
inFP FP a -> Exists (in_zr a) recb_PG -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof.
intros STK sp0 FP bl0 blc fr0 ly own a Hfp HP.
right; right; right; right; left. split; [exact Hfp|].
split; [rewrite recb_ts_prog_m; exact HP | exact (cmd_prog_img a HP)].
Qed.

(* a program callee whose footprint is empty keeps every program-static byte and every byte of a block live before
   and after it (pins_set's recb_call_keeps, socket_send's ssk_call_keeps) *)
Lemma recb_call_keeps_m : forall STK1 sp1 lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(Exists (in_zr a) recb_PG \/
 exists b m, In (b, m) (ablocks B lyc Sc) /\ In (b, m) (ablocks B ly2 S2) /\ b <= a < b + req_size m) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros STK1 sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 a HJ [HPG | (b & m & Hb & Hb2 & Hab)].
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  destruct (recb_prog_unowned_m a HPG) as (Hi & Ho & He).
  exact (F3 a Hi Ho He (fp_spares_closed [] a ltac:(intros (r & Hr & _); destruct Hr) ltac:(intros (r & Hr & _); destruct Hr))).
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace a with (b + (a - b)) by lia. apply (F2 b m (a - b) Hb Hb2 ltac:(lia)). intros (r & Hr & _). destruct Hr.
Qed.

End w.

(* The same lemmas at the four hypotheses every recorder walk binds (Default Proof Using), under their first
   names, so the walks that bind them once keep compiling; each is its minimal form _m above. *)
Section w_full.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md ->
Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
#[local] Set Default Proof Using "AFREE4 HB cmd_prog_img cmd_prog_writable".

Lemma recb_ts_prog : as_prog_static B = recb_PG.
Proof. exact (recb_ts_prog_m B HB). Qed.
Lemma recb_prog_unowned : forall a, Exists (in_zr a) recb_PG ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. exact (recb_prog_unowned_m B HB cmd_prog_img). Qed.
Lemma recb_grec_awr : forall STK sp0 FP bl0 blc fr0 ly own a,
inFP FP a -> A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof. exact (recb_grec_awr_m B HB cmd_prog_img). Qed.
Lemma recb_grec_writable : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k ->
A_G_REC <= a < A_G_REC + REC_SIZE -> writable_at SEGS (mrestrict (w_H Wc) memc) a.
Proof. exact (recb_grec_writable_m B cmd_prog_writable). Qed.
Lemma recb_rep_addressable : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (A_G_REC + OFF_REPLY) 16.
Proof. exact (recb_rep_addressable_m B HB). Qed.
Lemma recb_rep_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (aview SEGS (w_H W) mem) (A_G_REC + OFF_REPLY) 16.
Proof. exact (recb_rep_hull_m B HB). Qed.
Lemma recb_kept_prog : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop) a,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> Exists (in_zr a) recb_PG ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof. exact (recb_kept_prog_m B HB cmd_prog_img). Qed.
Lemma recb_free_any : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch q,
(q = None -> afree_null04_rule SEGS B MT) ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
(forall pn, q = Some pn -> In pn (ablocks B lyc Sc) /\
 (In pn (ablocks B ly S) -> forall i, 0 <= i < req_size (snd pn) -> inFP FP (fst pn + i))) ->
getr regsT 10 = w64 (oaddr q) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(recb_free_post B MT STK sp0 FP ly S W0 mem md own lyc Sc W memT k o raw regsT q).
Proof. exact (recb_free_any_m B MT AFREE4). Qed.
Lemma recb_val_mem_frame : forall H H' (m m' : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v ->
(forall k, 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
val_mem SEGS (mrestrict H' m') a n v.
Proof. exact (recb_val_mem_frame_m). Qed.
Lemma recb_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof. exact (recb_ablocks_nodup_m B). Qed.
Lemma recb_fresh_disj : forall ly3 S3 (W : world SEGS) mem md L res n b m,
AR SEGS B ly3 S3 W mem md -> ablocks B ly3 S3 = L ++ [(res, n)] -> In (b, m) L ->
zdisjoint (b, req_size m) (res, req_size n).
Proof. exact (recb_fresh_disj_m B). Qed.
Lemma recb_heap_noimg : forall ly S (W : world SEGS) mem md b m a,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof. exact (recb_heap_noimg_m B). Qed.
Lemma recb_heap_apart : forall ly S (W : world SEGS) mem md p n lo len,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof. exact (recb_heap_apart_m B). Qed.
Lemma recb_lay_rest_L2 : forall ly S rd R Q L2,
arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q ->
Permutation (ablocks B ly S) (oblk (l_reply Q) ++ L2) ->
forall pn, In pn (lay_rest Q) -> In pn L2.
Proof. exact (recb_lay_rest_L2_m B). Qed.
Lemma recb_run_keeps : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof. exact (recb_run_keeps_m). Qed.
Lemma recb_free_keeps : forall ly S (W : world SEGS) memc md (W2 : world SEGS) mem2 slo shi q L2 a,
AR SEGS B ly S W memc md -> List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (oblk q ++ L2) ->
acall_kept SEGS B ly S W memc W2 mem2 slo shi (fun a => exists pn, q = Some pn /\ fst pn <= a < fst pn + req_size (snd pn)) ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L2 /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof. exact (recb_free_keeps_m B HB cmd_prog_img). Qed.
Lemma recb_malloc_keeps : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi ly4 S4 mem4 md4 res n a,
AR SEGS B ly4 S4 W2 mem4 md4 -> ablocks B ly4 S4 = ablocks B lyc Sc ++ [(res, n)] ->
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun a => res <= a < res + req_size n) ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof. exact (recb_malloc_keeps_m B HB cmd_prog_img). Qed.
Lemma recb_not_new : forall ly4 S4 (W4 : world SEGS) mem4 md4 L res n a,
AR SEGS B ly4 S4 W4 mem4 md4 -> ablocks B ly4 S4 = L ++ [(res, n)] -> 0 <= n ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
~ (res <= a < res + n).
Proof. exact (recb_not_new_m B cmd_prog_img). Qed.
Lemma recb_fresh_disj_perm : forall ly3 S3 (W : world SEGS) mem md L res n b m,
AR SEGS B ly3 S3 W mem md -> Permutation (ablocks B ly3 S3) ((res, n) :: L) -> In (b, m) L ->
zdisjoint (b, req_size m) (res, req_size n).
Proof. exact (recb_fresh_disj_perm_m B). Qed.
Lemma recb_not_new_perm : forall ly4 S4 (W4 : world SEGS) mem4 md4 L res n a,
AR SEGS B ly4 S4 W4 mem4 md4 -> Permutation (ablocks B ly4 S4) ((res, n) :: L) -> 0 <= n ->
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L /\ b <= a < b + req_size m /\ ~ in_img SEGS a) ->
~ (res <= a < res + n).
Proof. exact (recb_not_new_perm_m B cmd_prog_img). Qed.
Lemma recb_awr_new_block_perm : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR SEGS B ly2 S2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B lyc Sc) ->
In (res, n) blc -> 0 <= i < req_size n ->
awr_byte SEGS B STK sp0 FP (ablocks B ly S) blc (frames S) lyq own (res + i).
Proof. exact (recb_awr_new_block_perm_m B). Qed.
Lemma recb_prog_awr : forall STK sp0 FP bl0 blc fr0 ly own a,
inFP FP a -> Exists (in_zr a) recb_PG -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof. exact (recb_prog_awr_m B HB cmd_prog_img). Qed.
Lemma recb_call_keeps : forall STK1 sp1 lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(Exists (in_zr a) recb_PG \/
 exists b m, In (b, m) (ablocks B lyc Sc) /\ In (b, m) (ablocks B ly2 S2) /\ b <= a < b + req_size m) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof. exact (recb_call_keeps_m B HB cmd_prog_img). Qed.
End w_full.
