(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder-state steps of pins_clear's ASan walk on
   plugin-hostd/fuzz_command, after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the object-state lemmas of the
   cgif_close walk) over fuzz_command's recorder representation. *)

(* What the inlined record(REC_PINS_CLEAR) and the inlined arg_s of pins_clear (recorder.c:205-227, :524-533) do
   to the recorder's representation (lib/A/Prog/CmdRep.v arep_at):

   - `pcl_arep_slot`: the table arm (fewer than 16 calls recorded). g_rec.ncalls becomes ncalls + 1 and the slot
     g_rec.calls[ncalls] holds the new call: fn = 21, one argument, the copy the xstrdup call made.
   - `pcl_arep_spill`: the spill arm (16 calls recorded). record.spill holds the new call; the arguments it held
     are gone, because record() frees them through rec_calls_free before it fills the slot.
   - `pcl_arep_state`: the write of g_rec.state that the mixing arm does with mix_call's result.

   Each is stated over two readers, the one before the step and the one after, which agree outside the bytes the
   step writes. These are the same steps the plain proof takes over its own representation
   (lib/Prog/RecStep.v rec_rep_record_lt, rep_at_record_full, rec_rep_arg, rec_rep_set_state); the list lemmas of
   that file are reused here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the recorder's blocks other than the spill's arguments, which record() frees on the spill arm *)
Definition lay_nospill (Q : rlay) : list (Z * Z) :=
concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q).

Lemma lay_blocks_perm_nospill : forall Q, Permutation (lay_blocks Q) (l_spill Q ++ lay_nospill Q).
Proof.
intros Q. unfold lay_blocks, lay_nospill.
exact (Permutation_app_swap_app (concat (l_calls Q)) (l_spill Q) (oblk (l_answer Q) ++ oblk (l_reply Q))).
Qed.


Lemma In_lay_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hpn. unfold lay_blocks. apply in_or_app. left. exact (In_concat_nth _ i P pn Hi Hpn).
Qed.

Lemma In_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma In_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
rewrite H. left. reflexivity.
Qed.

Lemma In_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
rewrite H. left. reflexivity.
Qed.

Lemma In_lay_nospill : forall Q pn, In pn (lay_nospill Q) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_nospill in H. unfold lay_blocks.
apply in_app_or in H as [H | H]; [apply in_or_app; left; exact H|].
apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

Lemma In_nospill_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_nospill Q).
Proof. intros Q i P pn Hi Hpn. unfold lay_nospill. apply in_or_app. left. exact (In_concat_nth _ i P pn Hi Hpn). Qed.

Lemma In_nospill_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_nospill Q).
Proof.
intros Q pn H. unfold lay_nospill. apply in_or_app. right. apply in_or_app. left. rewrite H. left. reflexivity.
Qed.

Lemma In_nospill_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_nospill Q).
Proof.
intros Q pn H. unfold lay_nospill. apply in_or_app. right. apply in_or_app. right. rewrite H. left. reflexivity.
Qed.

(* the recorder's blocks after the table arm recorded one argument *)
Lemma pcl_lay_perm : forall lc S ans rep pk,
Permutation (lay_blocks (RLay (lc ++ [[pk]]) S ans rep)) (lay_blocks (RLay lc S ans rep) ++ [pk]).
Proof.
intros lc S ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite concat_app. cbn [concat app].
exact (perm_snoc_mid [] (concat lc) (S ++ oblk ans ++ oblk rep) pk).
Qed.

(* the same after the spill arm filled record.spill *)
Lemma pcl_lay_perm_spill : forall lc ans rep pk,
Permutation (lay_blocks (RLay lc [pk] ans rep)) (pk :: lay_nospill (RLay lc [pk] ans rep)).
Proof.
intros lc ans rep pk. unfold lay_blocks, lay_nospill. cbn [l_calls l_spill l_answer l_reply].
exact (Permutation_sym (Permutation_middle (concat lc) (oblk ans ++ oblk rep) pk)).
Qed.

(* the new call's own facts, shared by the two arms *)
Definition pcl_new_call (bl' : list (Z * Z)) (rd' : reader) (c p : Z) (s : list byte) : Prop :=
aval_mem rd' (c + CALL_OFF_FN) 4 REC_PINS_CLEAR /\
aval_mem rd' (c + CALL_OFF_NARGS) 4 1 /\
aval_mem rd' (c + CALL_OFF_ARGS) 8 p /\
astr_atR rd' p s /\ p <> 0 /\ In (p, Z.of_nat (length s) + 1) bl' /\ Z.of_nat (length s) <= LMAX.

Lemma pcl_acall_new : forall bl' rd' c p s,
pcl_new_call bl' rd' c p s ->
acall_at bl' rd' c (REC_PINS_CLEAR, [s]) [(p, Z.of_nat (length s) + 1)].
Proof.
intros bl' rd' c p s (Hfn & Hna & Harg & Hstr & Hnz & Hin & Hlen).
unfold acall_at. cbn [fst snd map length].
split; [unfold REC_PINS_CLEAR, REC_FN_COUNT; lia|].
split; [lia|].
split; [reflexivity|].
split; [exact Hfn|].
split; [exact Hna|].
split.
{ constructor; [intros HH; inversion HH | constructor]. }
intros k y pn Hy Hpn. destruct k as [|k]; cbn [nth_error] in Hy, Hpn; [|destruct k; discriminate].
injection Hy as <-. injection Hpn as <-. cbn [fst snd].
split; [rewrite Z.mul_0_r, Z.add_0_r; exact Harg|].
split; [exact Hnz|]. split; [exact Hin|]. split; [unfold LMAX in *; lia | exact Hstr].
Qed.

(* the recorder's addresses as numbers, so every range side condition is plain arithmetic *)
Ltac pcl_consts :=
assert (CST : A_G_REC = 6174528 /\ A_REC_SPILL = 6175712 /\ REC_SIZE = 960 /\ SC_SIZE = 56 /\ CALL_SIZE = 56 /\
  OFF_REFUSE = 0 /\ OFF_CODE = 4 /\ OFF_NCALLS = 8 /\ OFF_CALLS = 16 /\ OFF_ANSWER = 912 /\ OFF_NREPLIES = 920 /\
  OFF_REPLY = 928 /\ OFF_REPLY_SIZE = 936 /\ OFF_STATE = 944 /\ OFF_HOST = 952)
  by (repeat split; reflexivity);
destruct CST as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).

(* --- the table arm of record(): the call goes into g_rec.calls[ncalls] ------------------------------------ *)

Lemma pcl_arep_slot : forall bl bl' rd rd' R Q c p s,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (r_calls R) < 16)%nat ->
c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
(* the bytes of g_rec outside its call count and the new slot, and record.spill, are kept *)
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
   ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) -> rd' a = rd a) ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
pcl_new_call bl' rd' c p s ->
iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_blocks Q)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R REC_PINS_CLEAR [s])
  (RLay (l_calls Q ++ [[(p, Z.of_nat (length s) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q c p s HA Hlt Hc HKEEP HSP HBL HNC HNEW Hap1 Hap2 Hnew.
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAns & HRpl & HSC & HOWN).
pose proof HC as (Hlen16 & HlenQ & HncM & HCALLS & HSPILL & HSPMAX).
set (n := length (r_calls R)) in *.
set (ns := Z.of_nat (length s) + 1) in *.
pcl_consts.
assert (Hcb : A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER) by (subst c; lia).
(* every byte outside the two written ranges is kept, in the rd_agree form *)
assert (KEEPsub : forall a m, A_G_REC <= a -> a + m <= A_G_REC + REC_SIZE ->
  (a + m <= A_G_REC + OFF_NCALLS \/ A_G_REC + OFF_NCALLS + 4 <= a) ->
  (a + m <= c \/ c + CALL_SIZE <= a) -> rd_agree rd rd' a m).
{ intros a m H1 H2 H3 H4. apply rd_agree_of. intros x Hx. apply HKEEP; lia. }
rewrite (rec_record_lt R REC_PINS_CLEAR [s] Hlt).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ (* the calls *)
  unfold ag1_calls. cbn [l_calls l_spill set_calls r_calls r_spill].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app; cbn [length]; lia|].
  split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; cbn [Z.of_nat]; exact HNC|].
  split.
  { intros i e P Hi HP.
    destruct (Nat.lt_ge_cases i n) as [Hin | Hge].
    - rewrite nth_error_app1 in Hi by lia. rewrite nth_error_app1 in HP by lia.
      destruct (HCALLS i e P Hi HP) as [Hca Hfa]. split; [|exact Hfa].
      apply (acall_at_agree bl bl' rd rd'); [exact Hca | |].
      + apply KEEPsub; subst c; lia.
      + intros pn Hpn. apply HBL. exact (In_lay_calls Q i P pn HP Hpn).
    - assert (Hi16 : (i < length (r_calls R ++ [(REC_PINS_CLEAR, [s])]))%nat)
        by (apply nth_error_Some; rewrite Hi; discriminate).
      rewrite length_app in Hi16. cbn [length] in Hi16.
      assert (Hieq : i = n) by lia. subst i.
      assert (Ei : nth_error (r_calls R ++ [(REC_PINS_CLEAR, [s])]) n = Some (REC_PINS_CLEAR, [s]))
        by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
      assert (EP : nth_error (l_calls Q ++ [[(p, ns)]]) n = Some [(p, ns)])
        by (rewrite nth_error_app2 by lia; rewrite HlenQ, Nat.sub_diag; reflexivity).
      rewrite Ei in Hi. rewrite EP in HP. injection Hi as <-. injection HP as <-.
      split.
      + rewrite <- Hc. exact (pcl_acall_new bl' rd' c p s HNEW).
      + cbn [snd]. constructor; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HNEW))))))|constructor]. }
  split; [|exact HSPMAX].
  apply (acall_at_agree bl bl' rd rd'); [exact HSPILL | unfold CALL_SIZE; exact HSP |].
  intros pn Hpn. apply HBL. exact (In_lay_spill Q pn Hpn). }
split.
{ (* the answer *)
  cbn [l_answer r_answer set_calls]. unfold aanswer_at in *.
  destruct (r_answer R) as [x|] eqn:Ex, (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HAns as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    destruct (HBL pn (In_lay_answer Q pn EA)) as [Hin' Hgp].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact V | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
  - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact HAns | | lia | cbn; lia].
    apply KEEPsub; lia. }
split.
{ (* the reply *)
  cbn [l_reply r_reply set_calls]. unfold areply_at in *.
  destruct (r_reply R) as [x|] eqn:Ex, (l_reply Q) as [pn|] eqn:ER; try contradiction.
  - destruct HRpl as (V1 & V2 & Hnz & Hne & Hin & Hlen & Hby & Hlx).
    destruct (HBL pn (In_lay_reply Q pn ER)) as [Hin' Hgp].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (abytes_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hby | exact Hgp | lia | lia].
  - destruct HRpl as [V1 V2].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | lia | cbn; lia].
    apply KEEPsub; lia. }
split.
{ (* the scalars *)
  destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
  cbn [r_refuse r_code r_nreplies r_state r_host set_calls].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vr | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vc | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NREPLIES) 4); [exact Vn | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vs | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vh | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [exact Rr|]. split; [exact Rc|]. split; [exact Rn|]. split; [exact Rs|]. exact Rh. }
{ (* the ownership list *)
  destruct HOWN as [HND HAP].
  pose proof (pcl_lay_perm (l_calls Q) (l_spill Q) (l_answer Q) (l_reply Q) (p, ns)) as PERM.
  split.
  - apply (nodup_fst_perm (lay_blocks (RLay (l_calls Q) (l_spill Q) (l_answer Q) (l_reply Q)) ++ [(p, ns)]));
      [apply Permutation_sym; exact PERM|].
    apply nodup_fst_snoc; [exact HND | exact Hnew].
  - intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn | [Hpn | []]].
    + exact (HAP pn Hpn).
    + subst pn. cbn [fst snd]. split; assumption. }
Qed.

(* --- the spill arm of record(): the table is full, so the call goes into record.spill --------------------- *)

Lemma pcl_arep_spill : forall bl bl' rd rd' R Q p s,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
length (r_calls R) = 16%nat ->
(* g_rec is untouched; record.spill holds the new call *)
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall pn, In pn (lay_nospill Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
pcl_new_call bl' rd' A_REC_SPILL p s ->
iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_nospill Q)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R REC_PINS_CLEAR [s])
  (RLay (l_calls Q) [(p, Z.of_nat (length s) + 1)] (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q p s HA H16 HKEEP HBL HNEW Hap1 Hap2 Hnew.
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAns & HRpl & HSC & HOWN).
pose proof HC as (Hlen16 & HlenQ & HncM & HCALLS & HSPILL & HSPMAX).
set (ns := Z.of_nat (length s) + 1) in *.
pcl_consts.
assert (KEEPsub : forall a m, A_G_REC <= a -> a + m <= A_G_REC + REC_SIZE -> rd_agree rd rd' a m).
{ intros a m H1 H2. apply rd_agree_of. intros x Hx. apply HKEEP. lia. }
rewrite (rec_record_full R REC_PINS_CLEAR [s] H16).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ (* the calls *)
  unfold ag1_calls. cbn [l_calls l_spill set_spill r_calls r_spill].
  split; [lia|]. split; [exact HlenQ|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NCALLS) 4); [exact HncM | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split.
  { intros i e P Hi HP. destruct (HCALLS i e P Hi HP) as [Hca Hfa]. split; [|exact Hfa].
    assert (Hi16 : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    apply (acall_at_agree bl bl' rd rd'); [exact Hca | |].
    - apply KEEPsub; lia.
    - intros pn Hpn. apply HBL. exact (In_nospill_calls Q i P pn HP Hpn). }
  split.
  - exact (pcl_acall_new bl' rd' A_REC_SPILL p s HNEW).
  - cbn [snd]. constructor; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HNEW))))))|constructor]. }
split.
{ (* the answer *)
  cbn [l_answer r_answer set_spill]. unfold aanswer_at in *.
  destruct (r_answer R) as [x|] eqn:Ex, (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HAns as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    destruct (HBL pn (In_nospill_answer Q pn EA)) as [Hin' Hgp].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact V | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
  - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact HAns | | lia | cbn; lia].
    apply KEEPsub; lia. }
split.
{ (* the reply *)
  cbn [l_reply r_reply set_spill]. unfold areply_at in *.
  destruct (r_reply R) as [x|] eqn:Ex, (l_reply Q) as [pn|] eqn:ER; try contradiction.
  - destruct HRpl as (V1 & V2 & Hnz & Hne & Hin & Hlen & Hby & Hlx).
    destruct (HBL pn (In_nospill_reply Q pn ER)) as [Hin' Hgp].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (abytes_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hby | exact Hgp | lia | lia].
  - destruct HRpl as [V1 V2].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
    { apply KEEPsub; lia. }
    apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | lia | cbn; lia].
    apply KEEPsub; lia. }
split.
{ (* the scalars *)
  destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
  cbn [r_refuse r_code r_nreplies r_state r_host set_spill].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vr | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vc | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NREPLIES) 4); [exact Vn | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vs | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_STATE) 16); [exact Vh | | lia | cbn; lia]|].
  { apply KEEPsub; lia. }
  split; [exact Rr|]. split; [exact Rc|]. split; [exact Rn|]. split; [exact Rs|]. exact Rh. }
{ (* the ownership list *)
  destruct HOWN as [HND HAP].
  assert (NDrest : NoDup (map fst (lay_nospill Q))).
  { pose proof (nodup_fst_perm _ _ (lay_blocks_perm_nospill Q) HND) as H.
    rewrite map_app in H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
    exact (NoDup_app_remove_l _ _ H). }
  pose proof (pcl_lay_perm_spill (l_calls Q) (l_answer Q) (l_reply Q) (p, ns)) as PERM.
  assert (ENS : lay_nospill (RLay (l_calls Q) [(p, ns)] (l_answer Q) (l_reply Q)) = lay_nospill Q)
    by reflexivity.
  rewrite ENS in PERM.
  split.
  - apply (nodup_fst_perm ((p, ns) :: lay_nospill Q)); [apply Permutation_sym; exact PERM|].
    cbn [map fst]. apply NoDup_ListNoDup. constructor; [exact Hnew | apply NoDup_ListNoDup; exact NDrest].
  - intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. destruct Hpn as [<- | Hpn].
    + cbn [fst snd]. split; assumption.
    + exact (HAP pn (In_lay_nospill Q pn Hpn)). }
Qed.

(* --- the write of g_rec.state that the mixing arm does ---------------------------------------------------- *)

Lemma pcl_arep_state : forall bl rd rd' R Q h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_state R h) Q.
Proof.
intros bl rd rd' R Q h HA HKEEP HST Hh.
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAns & HRpl & HSC & HOWN).
pose proof HC as (Hlen16 & HlenQ & HncM & HCALLS & HSPILL & HSPMAX).
pcl_consts.
assert (KEEPsub : forall a m, (a + m <= A_G_REC + OFF_STATE \/ A_G_REC + OFF_STATE + 8 <= a) ->
  rd_agree rd rd' a m).
{ intros a m H. apply rd_agree_of. intros x Hx. apply HKEEP. lia. }
(* every block of the recorder lies outside g_rec, so the state word is not one of its bytes *)
assert (KEEPblk : forall pn, In pn (lay_blocks Q) -> rd_agree rd rd' (fst pn) (snd pn)).
{ intros pn Hpn. destruct (proj2 HOWN pn Hpn) as [Hiv _]. apply KEEPsub. unfold iv_apart in Hiv. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ unfold ag1_calls. cbn [r_calls r_spill set_state].
  split; [exact Hlen16|]. split; [exact HlenQ|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NCALLS) 4); [exact HncM | apply KEEPsub; lia | lia | cbn; lia]|].
  split.
  { intros i e P Hi HP. destruct (HCALLS i e P Hi HP) as [Hca Hfa]. split; [|exact Hfa].
    assert (Hi16 : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    apply (acall_at_agree bl bl rd rd'); [exact Hca | apply KEEPsub; lia |].
    intros pn Hpn. split; [|exact (KEEPblk pn (In_lay_calls Q i P pn HP Hpn))].
    destruct (HCALLS i e P Hi HP) as [(_ & _ & Hlp & _ & _ & _ & Hk) _].
    destruct (In_nth_error P pn Hpn) as [k Ek].
    assert (Hk2 : (k < length (snd e))%nat) by (rewrite <- Hlp; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd e) k) as [x|] eqn:Ex; [|apply nth_error_Some in Hk2; contradiction].
    exact (proj1 (proj2 (proj2 (Hk k x pn Ex Ek)))). }
  split; [|exact HSPMAX].
  apply (acall_at_agree bl bl rd rd'); [exact HSPILL | apply KEEPsub; lia |].
  intros pn Hpn. split; [|exact (KEEPblk pn (In_lay_spill Q pn Hpn))].
  destruct HSPILL as (_ & _ & Hlp & _ & _ & _ & Hk).
  destruct (In_nth_error (l_spill Q) pn Hpn) as [k Ek].
  assert (Hk2 : (k < length (snd (r_spill R)))%nat)
    by (rewrite <- Hlp; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd (r_spill R)) k) as [x|] eqn:Ex; [|apply nth_error_Some in Hk2; contradiction].
  exact (proj1 (proj2 (proj2 (Hk k x pn Ex Ek)))). }
split.
{ cbn [r_answer set_state]. unfold aanswer_at in *.
  destruct (r_answer R) as [x|] eqn:Ex, (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HAns as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact V | apply KEEPsub; lia | lia | cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn));
      [exact Hstr | exact (KEEPblk pn (In_lay_answer Q pn EA)) | lia | lia].
  - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact HAns | apply KEEPsub; lia | lia | cbn; lia]. }
split.
{ cbn [r_reply set_state]. unfold areply_at in *.
  destruct (r_reply R) as [x|] eqn:Ex, (l_reply Q) as [pn|] eqn:ER; try contradiction.
  - destruct HRpl as (V1 & V2 & Hnz & Hne & Hin & Hlen & Hby & Hlx).
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | apply KEEPsub; lia | lia | cbn; lia]|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | apply KEEPsub; lia | lia | cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (abytes_atR_agree_in rd rd' (fst pn) (snd pn));
      [exact Hby | exact (KEEPblk pn (In_lay_reply Q pn ER)) | lia | lia].
  - destruct HRpl as [V1 V2].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | apply KEEPsub; lia | lia | cbn; lia]|].
    apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | apply KEEPsub; lia | lia | cbn; lia]. }
split.
{ destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
  cbn [r_refuse r_code r_nreplies r_state r_host set_state].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vr | apply KEEPsub; lia | lia | cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vc | apply KEEPsub; lia | lia | cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NREPLIES) 4); [exact Vn | apply KEEPsub; lia | lia | cbn; lia]|].
  split; [exact HST|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_HOST) 8); [exact Vh | apply KEEPsub; lia | lia | cbn; lia]|].
  split; [exact Rr|]. split; [exact Rc|]. split; [exact Rn|]. split; [exact Hh|]. exact Rh. }
exact HOWN.
Qed.
