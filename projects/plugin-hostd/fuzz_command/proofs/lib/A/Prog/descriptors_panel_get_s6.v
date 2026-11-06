(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_info (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8bb70, 122 instructions), after lib/A/Prog/answer_code.v (a working branch
   2ba4488ce71: a side-stack frame taken by __asan_stack_malloc_N, its header and shadow, the snprintf call and the
   release by the flag store) and lib/A/Prog/sup_instance_info.v (a working branch 0de7ca03d26: the
   recorder's chain through record, arg_s, rec_shape_of and answer and the post), re-derived on B's code, against
   a Theorem Labs lane's statement (a working branch f490061c104). The snprintf step through the shared contract and the change of FP
   state after it follow a working branch 07b554c4785 (lib/B/Prog/answer_code.v:943-1070), the release
   by the flag store answer_code.v's end, the post's block algebra a working branch b5e1a22725a
   (descriptors_panel_get_aux.v dpgb_post_of), the calls after record a working branch c79a9f2daf7. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_info.v, with its module paths and module names changed; 141 of its 266 lines of code are new or changed and 1697 lines of the source are left out. *)
(* The model and block-list steps of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan).

   record()'s two arms as the recorder's state sees them (dpg_nargs0, dpg_hrec_slot, dpg_hrec_spill: the slot
   `dpg_c R` holds the new call (fn, [])), arg_s's step that adds the copy of uri to that call (dpg_arg_step, from
   descriptors_panel_get_s2.v's arep_arg_slot / arep_arg_spill), and the assembly of the contract's post in the
   form `dpg_post_g1` states from the block lists of the walk's points (dpg_post_of). The allocator facts are
   YG0d's al_blocks and YCbq's sep_blocks through AR_laws_ok. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c descriptors_panel_get_s1 descriptors_panel_get_s3 descriptors_panel_get_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Ltac dpg6_lia := cbv beta in *;
unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, CALL_SIZE, CALL_OFF_FN,
CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.

Lemma dpg_pdec : forall a b : Z * Z, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Qed.

Lemma dpg_req_ge : forall x, 0 <= x -> 1 <= req_size x /\ x <= req_size x.
Proof. intros x Hx. unfold req_size. destruct (Z.eqb_spec x 0); lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* ---------- record()'s two arms and arg_s, over the recorder's state ---------- *)

Lemma dpg_nargs0 : forall bl rd R Q fn, arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn []) Q ->
(length (r_calls R) <= 16)%nat -> aval_mem rd (dpg_c R + CALL_OFF_NARGS) 4 0.
Proof.
intros bl rd R Q fn HA Hn.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- assert (Hc : dpg_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold dpg_c; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  assert (Hr : rec_record R fn [] = set_calls R (r_calls R ++ [(fn, [])]))
    by (unfold rec_record; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  rewrite Hc. rewrite Hr in HA.
  destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
  cbn [set_calls r_calls] in C2, C4.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP.
  + assert (Ec : nth_error (r_calls R ++ [(fn, [])]) (length (r_calls R)) = Some (fn, []))
      by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (C4 _ _ _ Ec EP) as ((_ & _ & _ & _ & H5 & _) & _). exact H5.
  + exfalso. apply nth_error_None in EP. rewrite length_app in C2. cbn [length] in C2. lia.
- assert (E16 : length (r_calls R) = 16%nat) by lia.
  assert (Hc : dpg_c R = A_REC_SPILL) by (unfold dpg_c; rewrite E16; reflexivity).
  assert (Hr : rec_record R fn [] = set_spill R (fn, [])) by (unfold rec_record; rewrite E16; reflexivity).
  rewrite Hc. rewrite Hr in HA.
  destruct HA as (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
  cbn [set_spill r_spill] in C5. destruct C5 as (_ & _ & _ & _ & H5 & _). exact H5.
Qed.

Lemma dpg_arg_step : forall bl bl' rd rd' R Q1 fn p x,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn []) Q1 -> (length (r_calls R) <= 16)%nat ->
(forall pn, In pn bl -> In pn bl') -> In (p, Z.of_nat (length x) + 1) bl' -> p <> 0 ->
~ In p (map fst (lay_blocks Q1)) ->
iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE ->
Z.of_nat (length x) <= LMAX -> astr_atR rd' p x ->
aval_mem rd' (dpg_c R + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (dpg_c R + CALL_OFF_ARGS) 8 p ->
rec_rd_kept Q1 rd rd' (fun a => dpg_c R + CALL_OFF_NARGS <= a < dpg_c R + CALL_OFF_ARGS + 8) ->
exists Q2, arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn [x]) Q2 /\
  (forall pn, In pn (lay_blocks Q2) <-> In pn (lay_blocks Q1) \/ pn = (p, Z.of_nat (length x) + 1)).
Proof.
intros bl bl' rd rd' R Q1 fn p x HA Hn Hbl Hpb Hp0 Hpn Hiv1 Hiv2 HLx Hstr Hna Har Hk.
assert (Hperm_iff : forall Q2, Permutation (lay_blocks Q2) ((p, Z.of_nat (length x) + 1) :: lay_blocks Q1) ->
  forall pn, In pn (lay_blocks Q2) <-> In pn (lay_blocks Q1) \/ pn = (p, Z.of_nat (length x) + 1)).
{ intros Q2 HP pn. split; intros H.
  - apply (Permutation_in pn HP) in H. destruct H as [<- | H]; [right; reflexivity | left; exact H].
  - apply (Permutation_in pn (Permutation_sym HP)). destruct H as [H | ->]; [right; exact H | left; reflexivity]. }
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- assert (Hc : dpg_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold dpg_c; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  assert (Hr : forall A, rec_record R fn A = set_calls R (r_calls R ++ [(fn, A)]))
    by (intros A; unfold rec_record; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  rewrite Hc in Hna, Har, Hk. rewrite Hr in HA. rewrite Hr.
  destruct (arep_arg_slot bl bl' rd rd' (set_calls R (r_calls R ++ [(fn, [])])) Q1 (r_calls R) fn p x
    HA eq_refl Hbl Hpb Hp0 Hpn Hiv1 Hiv2 HLx Hstr Hna Har Hk) as (Ps & HQ & HA2).
  exists (RLay (Ps ++ [[(p, Z.of_nat (length x) + 1)]]) (l_spill Q1) (l_answer Q1) (l_reply Q1)).
  split; [exact HA2 | exact (Hperm_iff _ (dpg_lay_arg_call Q1 Ps _ HQ))].
- assert (E16 : length (r_calls R) = 16%nat) by lia.
  assert (Hc : dpg_c R = A_REC_SPILL) by (unfold dpg_c; rewrite E16; reflexivity).
  assert (Hr : forall A, rec_record R fn A = set_spill R (fn, A))
    by (intros A; unfold rec_record; rewrite E16; reflexivity).
  rewrite Hc in Hna, Har, Hk. rewrite Hr in HA. rewrite Hr.
  destruct (arep_arg_spill bl bl' rd rd' (set_spill R (fn, [])) Q1 fn p x
    HA eq_refl Hbl Hpb Hp0 Hpn Hiv1 Hiv2 HLx Hstr Hna Har Hk) as (Hl0 & HA2).
  exists (RLay (l_calls Q1) [(p, Z.of_nat (length x) + 1)] (l_answer Q1) (l_reply Q1)).
  split; [exact HA2 | exact (Hperm_iff _ (dpg_lay_arg_spill Q1 _ Hl0))].
Qed.

Lemma dpg_lay_slot : forall Q pn,
In pn (lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q))) <-> In pn (lay_blocks Q).
Proof. intros Q pn. rewrite dpg_lay_nil. apply iff_refl. Qed.

Lemma dpg_hrec_slot : forall bl rd rdj R Q fn, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
aval_mem rdj (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
rec_rd_kept Q rd rdj (fun a => A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
forall rd', aval_mem rd' (dpg_c R + CALL_OFF_FN) 4 fn -> aval_mem rd' (dpg_c R + CALL_OFF_NARGS) 4 0 ->
(forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
            (exists pn, In pn (lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q))) /\
                        fst pn <= a < fst pn + snd pn)) ->
   ~ (dpg_c R <= a < dpg_c R + 8) -> rd' a = rdj a) ->
arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R fn []) (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl rd rdj R Q fn HA Hn Hfn Hnc Hk rd' Hf Hna Hj.
assert (Hc : dpg_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
  by (unfold dpg_c; apply Nat.ltb_lt in Hn; rewrite Hn; reflexivity).
assert (Hr : rec_record R fn [] = set_calls R (r_calls R ++ [(fn, [])]))
  by (unfold rec_record; apply Nat.ltb_lt in Hn; rewrite Hn; reflexivity).
rewrite Hc in Hf, Hna, Hj. rewrite Hr.
unfold rec_rd_kept in Hk.
assert (Hnc' : aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)).
{ apply (aval_mem_kept rdj); [exact Hnc | intros k Hk'; apply Hj; [left; dpg6_lia | intro Hw; dpg6_lia]]. }
assert (Hk' : rec_rd_kept Q rd rd' (fun a => (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) \/
  (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= a <
   A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 8))).
{ unfold rec_rd_kept. intros a Ha Hw. transitivity (rdj a).
  - apply Hj; [| intro Hw'; apply Hw; right; exact Hw'].
    destruct Ha as [Ha | [Ha | (pn & Hpn & Ha)]]; [left; exact Ha | right; left; exact Ha |].
    right; right. exists pn. split; [apply (proj2 (dpg_lay_slot Q pn)); exact Hpn | exact Ha].
  - apply Hk; [exact Ha | intro Hw'; apply Hw; left; exact Hw']. }
exact (arep_record_slot bl rd rd' R Q fn HA Hn Hfn Hnc' Hf Hna Hk').
Qed.

Lemma dpg_hrec_spill : forall bl rdj R Q fn,
arep_at bl rdj A_G_REC A_REC_SPILL (set_spill R (fst (r_spill R), [])) Q ->
length (r_calls R) = 16%nat -> 0 <= fn < REC_FN_COUNT ->
forall rd', aval_mem rd' (dpg_c R + CALL_OFF_FN) 4 fn -> aval_mem rd' (dpg_c R + CALL_OFF_NARGS) 4 0 ->
(forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
            (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn)) ->
   ~ (dpg_c R <= a < dpg_c R + 8) -> rd' a = rdj a) ->
arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R fn []) Q.
Proof.
intros bl rdj R Q fn HA Hn Hfn rd' Hf Hna Hj.
assert (Hc : dpg_c R = A_REC_SPILL) by (unfold dpg_c; rewrite Hn; reflexivity).
assert (Hr : rec_record R fn [] = set_spill R (fn, [])) by (unfold rec_record; rewrite Hn; reflexivity).
rewrite Hc in Hf, Hna, Hj. rewrite Hr.
exact (arep_record_spill bl rdj rd' (set_spill R (fst (r_spill R), [])) Q fn HA eq_refl Hfn Hf Hna Hj).
Qed.

(* ---------- the blocks of the walk's points and the contract's post ---------- *)

(* two live blocks with one start are one block *)
Lemma dpg_same_start : forall ly S (W : world SEGS) mem md p m n, AR SEGS B ly S W mem md ->
In (p, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> m = n.
Proof.
intros ly S W mem md p m n HAR H1 H2.
destruct (Z.eq_dec m n) as [E | E]; [exact E|]. exfalso.
pose proof (al_blocks _ _ LAWS ly S W mem md p m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
assert (Hne : (p, m) <> (p, n)) by congruence.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p m p n HAR H1 H2 Hne) as Hd.
pose proof (dpg_req_ge m ltac:(lia)) as Rm. pose proof (dpg_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* two distinct live blocks are apart *)
Lemma dpg_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) -> iv_apart b m p n.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (al_blocks _ _ LAWS ly S W mem md b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as Hd.
pose proof (dpg_req_ge m ltac:(lia)) as Rm. pose proof (dpg_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
Qed.

Lemma dpg_post_of : forall ly S R uri O lyc Sc O1 ly2 S2 ly3 S3 (W3 : world SEGS) mem3 md3 ly4 S4 (W4 : world SEGS)
  (regs4 : bvmap 5 word) mem4 md4
  (x : list byte) (p p1 p2 old : Z) (O2 O' : list (Z * Z)) (R' : rstate) (t : list byte),
dpg_blk B ly S R O lyc Sc O1 ->
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
dpg_postQ B MT ly S R uri O ly4 S4 W4 regs4 mem4 md4.
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
assert (Hent : forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B ly3 S3) -> In pn O).
{ intros pn H1 H2. destruct (in_dec dpg_pdec pn (ablocks B lyc Sc)) as [H3 | H3].
  - exfalso. exact (H2 (Hc3 pn H3)).
  - exact (proj1 (B2 pn H1 H3)). }
assert (HO'4 : forall pn, In pn O' -> In pn (ablocks B ly4 S4))
  by exact (rec_repA_in B ly4 S4 (rdW W4 mem4) R' O' Hrep).
assert (Hq4 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly4 S4))
  by (apply (proj2 (H4 _)); right; right; reflexivity).
(* a block of ly3 S3 that is a block of the recorder's O2 or one that was live and not in O has a start other
   than old's: old is 0 or the start of an O2 block *)
assert (Hnold : forall b m, In (b, m) (ablocks B ly3 S3) -> ~ In (b, m) O2 -> b <> old).
{ intros b m H3 HnO2 E. subst b. destruct Hold as [E | (m' & Hm')].
  - pose proof (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 old m HAR3 H3) as (_ & H4096 & _). lia.
  - pose proof (dpg_same_start ly3 S3 W3 mem3 md3 old m m' HAR3 H3 (HO2in _ Hm')) as E. subst m'.
    exact (HnO2 Hm'). }
assert (HkeptO2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3) /\ ~ In pn O2).
{ intros pn H1 H2.
  destruct (in_dec dpg_pdec pn (ablocks B lyc Sc)) as [Hc | Hc]; [|exfalso; exact (H2 (proj1 (B2 _ H1 Hc)))].
  split; [exact (Hc3 _ Hc)|]. intros H. apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
  - exact (H2 (B3 _ H)).
  - exact (Hpc Hc). }
unfold dpg_postQ.
exists R', t, p2, O'.
split; [exact Hm|]. split; [exact Hreg|]. split; [exact Hq|]. split; [exact Hrep|].
split.
{ intros pn H. apply (proj1 (HO' pn)) in H. destruct H as [(H & _) | ->].
  - apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
    + left. exact (B3 pn H).
    + destruct (in_dec dpg_pdec (p, Z.of_nat (length x) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
      exact (proj1 (B2 _ H1 Hpc)).
  - destruct (in_dec dpg_pdec (p1, Z.of_nat (length t) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
    destruct (in_dec dpg_pdec (p1, Z.of_nat (length t) + 1) O) as [HO | HO]; [exact HO|].
    exfalso. destruct (HkeptO2 _ H1 HO) as [H3 HnO2].
    exact (proj1 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) eq_refl). }
split; [exact Hq4|].
split.
{ intros pn H1 H2 E. destruct (HkeptO2 pn H1 H2) as [H3 HnO2]. destruct pn as [b m].
  exact (proj2 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) E). }
split.
{ intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hbm). cbn [fst] in Eb. subst b.
  assert (Em : m = Z.of_nat (length t) + 1) by exact (dpg_same_start ly4 S4 W4 mem4 md4 p2 m _ HAR4 (HO'4 _ Hbm) Hq4).
  subst m. apply (proj1 (HO' _)) in Hbm. destruct Hbm as [(Hb & Hbo) | Hb].
  - exact (proj2 (Hn12 _ (HO2in _ Hb) Hbo) eq_refl).
  - apply Hp12. congruence. }
split; [exact Hstr|].
split.
{ intros [b m] H1 H2. destruct (HkeptO2 _ H1 H2) as [H3 HnO2].
  pose proof (Hnold _ _ H3 HnO2) as Hb.
  assert (H4b : In (b, m) (ablocks B ly4 S4)) by (apply (proj2 (H4 _)); left; split; [exact H3 | exact Hb]).
  split; [exact H4b|].
  apply (dpg_apart ly4 S4 W4 mem4 md4 b m p2 _ HAR4 H4b Hq4).
  exact (proj2 (Hn12 _ H3 Hb)). }
split.
{ intros pn H. apply (proj1 (H4 pn)) in H. destruct H as [(H & Hold') | [-> | ->]].
  - destruct (H3c pn H) as [-> | Hc].
    + right; left. apply (proj2 (HO' _)). left. split; [apply (proj2 (HO2 _)); right; reflexivity | exact Hold'].
    + destruct (in_dec dpg_pdec pn O) as [HO | HO].
      * right; left. apply (proj2 (HO' _)). left. split; [|exact Hold'].
        apply (proj2 (HO2 _)). left. destruct (in_dec dpg_pdec pn O1) as [HO1 | HO1]; [exact HO1|].
        exfalso. exact (B4 pn HO HO1 Hc).
      * left. split; [exact (B1 pn Hc) | exact HO].
  - right; left. apply (proj2 (HO' _)). right. reflexivity.
  - right; right. reflexivity. }
split; [exact Hbb | exact Hmo].
Qed.

End e.
End f.
End d.
