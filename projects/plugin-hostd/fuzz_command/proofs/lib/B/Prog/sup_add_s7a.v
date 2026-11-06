(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from an earlier version of lib/A/Prog/send_message_l.v (ported there from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v, ACke.v at c8557374ad2e) for fuzz_command's program walk: the call rule for a callee whose footprint holds the program's statics (g_rec, record.spill), built on PaNoChain.v's cl_callS_wide, with its statement (send_message_k.v's cl_callS_pg_stmt) stated in the lemma and over any PAImg listing; and the transport lemmas the callers of such a callee need (readers that agree on the bytes read, a journal's footprint widened, the recorder's representation kept). send_message's own lemmas (sm_achain, ev_vr_nonneg, rec_spill_frees_nonneg) are left in its walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaCallPg.v, with its module paths and module names changed; 586 of its 650 lines of code are new or changed and 143 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, the M6 stage's shared lemmas (lane
   SaBranch: sup_add_s7.v and sup_add_s7b.v / sup_add_s7c.v).

   The stage runs from M6 (0x8a5bc) over the range check on id to M7 (0x8a628) on three arms: id out of range
   (0x8a5c8, v = -1), id in range and the input refused (0x8a5f0: `jal answer` 0x8a5fc, then `j 0x8a634` to M9),
   and id in range and accepted (0x8a604: `jal mix_call` 0x8ad54, the store into g_rec.state, then M7 with v = id).
   This file holds what the three arms share: the arithmetic of the check (sab_srliw, sab_in_range), the model on
   the refused arm (sab_m_refused), the transport lemmas of the mid-state (sab_core_kept), the recorder's fields
   and the state store (sab_rep_fields, sab_rep_set_state), the premises a callee asks at this point
   (sab_aro_kept, sab_pres_at), the footprint arithmetic of answer's call (sab_ansFP_*, sab_ans_blocks) and the
   last step of the refused arm (sab_m9_jmp: `j 0x8a634` at EVERY FP state, used at the fx1 answer returns).

   The A walk's file for the same stage is lib/A/Prog/sup_add_s5.v on a working branch 87f17ee4716; the
   lemmas keep its shapes, re-derived on B's code, B's mid-states (lib/B/Prog/sup_add_s0.v) and B's kit. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCallPg PaFx PaArt PaArtOwn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the symbolic seeds of the stage *)
(* At M6 the registers are atoms 0..31 and atom 32 is g_rec.refuse (as 32 bits); the field the stage loads is a
   read-only region on the atom of g_rec (A_OBJ 44, the object `s5` holds from 0x8a5e4). At the accepted arm's
   return from mix_call the state field is a writable window with no chunk, which the store `sd a0,944(s5)` fills. *)
Definition sab_SB : Z := 0x7fff8000.
Definition sab_Bx : sv := SLit sab_SB.
Definition sab_Bspan : Z * Z := (sab_SB, sab_SB + 2 ^ 44 - 1).
Definition sab_rg_refuse : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 44)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition sab_rg_state : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 44)) 944 952 944 944 [YP09.mkChunk 944 (CVal 8 (SOff 33 0))].
Definition sab_rg_store : YP09.region := YP09.mkRegion (Some (A_OBJ 44)) 944 952 944 952 [].
Definition sab_facts : facts := mkFacts [] [] [].
Definition sab_extra (rf st : Z) : list word := map (Z_to_bv 64) [rf; st].

(* ---------------------------------------------------------------- the arithmetic of the range check *)
Lemma sab_s1_cases : forall x, x mod 16 = 0 ->
x - 128 - (x - 128) mod 32 = x - 128 \/ x - 128 - (x - 128) mod 32 = x - 144.
Proof.
intros x Hx. pose proof (Z.mod_pos_bound (x - 128) 32 ltac:(lia)) as Hb.
Z.div_mod_to_equations. lia.
Qed.
Lemma sab_div16 : forall x, 625 <= x / 16 -> 0 <= x -> 10000 <= x.
Proof. intros x H H0. Z.div_mod_to_equations. lia. Qed.
Lemma sab_div16_lt : forall x, 0 <= x -> x / 16 < 625 -> x < 10000.
Proof. intros x H0 H. Z.div_mod_to_equations. lia. Qed.
Lemma sab_in_range : forall id, - 2 ^ 31 <= id < 2 ^ 31 -> (id mod 2 ^ 32) / 16 < 625 -> 0 <= id < 10000.
Proof.
intros id Hid Hlt.
assert (Hb : 0 <= id mod 2 ^ 32) by (apply Z.mod_pos_bound; lia).
pose proof (sab_div16_lt (id mod 2 ^ 32) Hb Hlt) as H1.
destruct (Z_lt_le_dec id 0) as [Hneg|Hpos].
- exfalso.
  assert (E0 : (id + 1 * 2 ^ 32) mod 2 ^ 32 = id mod 2 ^ 32) by (apply Z.mod_add; lia).
  assert (E1 : (id + 1 * 2 ^ 32) mod 2 ^ 32 = id + 1 * 2 ^ 32) by (apply Z.mod_small; lia).
  lia.
- rewrite (Z.mod_small id (2 ^ 32)) in H1 by lia. lia.
Qed.
(* the model on the refused arm: an id in range and a refusal give answer's own hand_back *)
Lemma sab_m_refused : forall R uri id placement client e x chg,
0 <= id < 10000 -> r_refuse (rec_record R REC_ADD (sa_A uri id placement client)) <> 0 ->
sup_add_m R uri id placement client = rec_answer (rec_record R REC_ADD (sa_A uri id placement client)) e x chg.
Proof.
intros R uri id placement client e x chg Hid Href.
unfold sup_add_m, rec_answer, sa_A in *. cbv zeta in *.
replace ((id <? 0) || (10000 <=? id))%bool with false
  by (symmetry; apply Bool.orb_false_intro; [apply Z.ltb_ge; lia | apply Z.leb_gt; lia]).
replace (r_refuse (rec_record R REC_ADD [sarg uri; dec id; darg placement (bstr "-"%string);
  darg client (bstr "-"%string)]) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Href).
reflexivity.
Qed.
(* the model on the accepted arm *)
Lemma sab_m_accepted : forall R uri id placement client,
0 <= id < 10000 -> r_refuse (rec_record R REC_ADD (sa_A uri id placement client)) = 0 ->
sup_add_m R uri id placement client =
hand_back (rec_mix (rec_record R REC_ADD (sa_A uri id placement client))
  (REC_ADD, sa_A uri id placement client)) (resp id).
Proof.
intros R uri id placement client Hid Href.
unfold sup_add_m, sa_A in *. cbv zeta in *.
replace ((id <? 0) || (10000 <=? id))%bool with false
  by (symmetry; apply Bool.orb_false_intro; [apply Z.ltb_ge; lia | apply Z.leb_gt; lia]).
replace (negb (r_refuse (rec_record R REC_ADD [sarg uri; dec id; darg placement (bstr "-"%string);
  darg client (bstr "-"%string)]) =? 0)) with false
  by (symmetry; rewrite Href; reflexivity).
reflexivity.
Qed.

(* ---------------------------------------------------------------- small reader and list facts *)
Lemma sab_inFP_ablocks_fp : forall bl a, inFP (ablocks_fp bl) a ->
exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
intros bl a (r & Hin & Hr). unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([p n] & <- & Hin).
cbn [fst snd] in Hr. exists p, n. split; [exact Hin | exact Hr].
Qed.
Lemma sab_filter_in : forall (f : Z * Z -> bool) (l : list (Z * Z)) x, In x (filter f l) -> In x l.
Proof.
intros f l x. induction l as [|q l IH].
- cbn. exact (fun H => H).
- cbn. destruct (decide (f q)) as [Hq|Hq].
  + cbn [In]. intros [H|H]; [left; exact H | right; exact (IH H)].
  + intros H. right. exact (IH H).
Qed.
Lemma sab_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
Lemma sab_rdword_eq : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma sab_astr_kept : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] K. split; [|exact H2]. intros i Hi.
pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite K by lia. exact (H1 i Hi).
Qed.
Lemma sab_req_ge : forall n, 0 <= n -> n <= req_size n.
Proof. intros n H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* the blocks of the post on the refusal arm, from answer's post and the accounting at M6 (A's s5_ans_blocks) *)
Lemma sab_ans_blocks : forall (bl0 blc bl2 O O6 O' : list (Z * Z)) old p1 p2 n,
(forall pn, In pn O6 -> In pn O \/ ~ In pn bl0) ->
(forall pn, In pn blc -> (In pn bl0 /\ ~ In pn O) \/ In pn O6) ->
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn O6 -> In pn blc) ->
(old = 0 \/ exists m, In (old, m) O6) ->
(forall pn, In pn blc -> 4096 <= fst pn) ->
(forall p m m', In (p, m) blc -> In (p, m') blc -> m = m') ->
(forall p m m', In (p, m) bl2 -> In (p, m') bl2 -> m = m') ->
p1 <> p2 -> (forall pn, In pn blc -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
(forall pn, In pn bl2 <-> (In pn blc /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn O' <-> (In pn O6 /\ fst pn <> old) \/ pn = (p1, n)) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
(forall pn, In pn bl2 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl2) /\
In (p2, n) bl2 /\ (forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
~ In p2 (map fst O').
Proof.
intros bl0 blc bl2 O O6 O' old p1 p2 n A1 A2 A3 HO6 Hold H4096 Uc U2 Hp12 HF HB2 HO'.
assert (DEC : forall (x : Z * Z) l, {In x l} + {~ In x l})
  by (intros x l; apply in_dec; intros u v; decide equality; apply Z.eq_dec).
(* a block of the entry outside the recorder's O that is live at M6 is none of answer's two fresh blocks *)
assert (FR : forall p, In (p, n) bl0 -> ~ In (p, n) O -> In (p, n) blc -> fst (p, n) = old -> False).
{ intros p H0 HnO Hc Ep. cbn [fst] in Ep. subst p. destruct Hold as [Eo | (m0 & Hm0)].
  - pose proof (H4096 _ Hc) as X. cbn [fst] in X. lia.
  - pose proof (Uc old n m0 Hc (HO6 _ Hm0)) as ->.
    destruct (A1 _ Hm0) as [X | X]; [exact (HnO X) | exact (X H0)]. }
split.
{ intros pn Hpn. apply HO' in Hpn as [[H1 _] | ->]; [exact (A1 pn H1)|].
  destruct (DEC (p1, n) O) as [Hin|Hnin]; [left; exact Hin|].
  right. intros H0. pose proof (A3 _ H0 Hnin) as Hc.
  destruct (Z.eq_dec (fst (p1, n)) old) as [Ep|Np]; [exact (FR p1 H0 Hnin Hc Ep)|].
  exact (proj1 (HF _ Hc Np) eq_refl). }
split.
{ intros pn Hpn. apply HB2 in Hpn as [[H1 H2] | [-> | ->]].
  - destruct (A2 pn H1) as [H3 | H3]; [left; exact H3|]. right; left. apply HO'. left. split; assumption.
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ intros [p m] H0 HnO. apply HB2. left. split; [exact (A3 _ H0 HnO)|]. cbn [fst]. intros ->.
  destruct Hold as [-> | (m0 & Hm0)].
  - pose proof (H4096 _ (A3 _ H0 HnO)) as X. cbn [fst] in X. lia.
  - pose proof (Uc old m m0 (A3 _ H0 HnO) (HO6 _ Hm0)) as ->.
    destruct (A1 _ Hm0) as [X | X]; [exact (HnO X) | exact (X H0)]. }
split; [apply HB2; right; right; reflexivity|].
split.
{ intros pn H0 HnO ->. pose proof (A3 _ H0 HnO) as Hc.
  destruct (Z.eq_dec (fst (p2, n)) old) as [Ep|Np]; [exact (FR p2 H0 HnO Hc Ep)|].
  exact (proj2 (HF _ Hc Np) eq_refl). }
intros Hq. apply in_map_iff in Hq as ([p m] & Ep & Hin). cbn [fst] in Ep. subst p.
apply HO' in Hin as [[H1 H2] | E].
- assert (Hb2 : In (p2, m) bl2) by (apply HB2; left; split; [exact (HO6 _ H1) | exact H2]).
  assert (Hb2' : In (p2, n) bl2) by (apply HB2; right; right; reflexivity).
  pose proof (U2 p2 m n Hb2 Hb2') as ->. exact (proj2 (HF _ (HO6 _ H1) H2) eq_refl).
- injection E as E1 _. exact (Hp12 (eq_sym E1)).
Qed.

(* the frame hypotheses of a run: a read-only region list keeps every byte. The tactics read the instance's
   segment list off the goal, since they are used outside the section that names it. *)
Ltac sab_clear_frames :=
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac sab_memeq Wx MEQ :=
lazymatch goal with
| |- SRr ?SEGSx _ _ _ =>
lazymatch goal with
| HX : frame_of ?Ex ?rs (mrestrict (w_H Wx) ?m0) (mrestrict (w_H Wx) ?m1) |- _ =>
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGSx (w_H Wx) m1 a = aview SEGSx (w_H Wx) m0 a) by
  (let a := fresh "a" in let Ha := fresh "Ha" in
   intros a Ha; apply (kept_of_frame Ex rs (w_H Wx) m0 m1 (fun _ => False) HX);
   [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
     let a' := fresh "a'" in let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
     intros b wlo whi a' Hin Hrr; vm_compute in Hin;
     repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
       [ injection Hq as <- <- <-; cbn [base_val] in Hrr; exfalso; clear - Hrr; lia |]);
     destruct Hin
   | exact Ha | let X := fresh "X" in intros X; exact X ])
end end.
(* the run after mix_call writes only g_rec.state (the store region, base the g_rec atom by U44) *)
Ltac sab_memeq_st Wx U44 MEQ :=
lazymatch goal with
| |- SRr ?SEGSx _ _ _ =>
lazymatch goal with
| HX : frame_of ?Ex ?rs (mrestrict (w_H Wx) ?m0) (mrestrict (w_H Wx) ?m1) |- _ =>
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    aview SEGSx (w_H Wx) m1 a = aview SEGSx (w_H Wx) m0 a) by
  (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
   intros a Ha Hn; apply (kept_of_frame Ex rs (w_H Wx) m0 m1 (fun x => A_G_REC + 944 <= x < A_G_REC + 952) HX);
   [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
     let a' := fresh "a'" in let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
     intros b wlo whi a' Hin Hrr; vm_compute in Hin;
     repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
       [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U44 in Hrr; lia |]);
     destruct Hin
   | exact Ha | exact Hn ])
end end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* srliw a0,s3,4 on a signed 32-bit id *)
Lemma sab_srliw : forall E id, ew E 19 = w64 id -> - 2 ^ 31 <= id < 2 ^ 31 ->
U E (SAluw ALU_SRL (SOff 19 0) (SLit 4)) = (id mod 2 ^ 32) / 16.
Proof.
intros E id H19 Hid.
rewrite U_of_S, S_SAluw, U_SOff, U_SLit, H19. cbn [zalu_raw].
change (Z.land (zcanon 4 mod 2 ^ 32) 31) with 4.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_swrap.
change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
Z.div_mod_to_equations. lia.
Qed.
(* lw a0,0(s5); beqz a0: the loaded refusal is 0 exactly when g_rec.refuse is *)
Lemma sab_refuse_eq : forall E r, ew E 32 = Z_to_bv 64 (r mod 2 ^ 32) -> - 2 ^ 31 <= r < 2 ^ 31 ->
(U E (SExt true 32 (SOff 32 0)) =? U E (SLit 0)) = (r =? 0).
Proof.
intros E r H32 Hr.
rewrite U_SExt, U_SOff, U_SLit, H32, Z_to_bv_unsigned. cbv iota beta.
change (2 ^ Z.of_N 32) with (2 ^ 32).
unfold zcanon, M64, bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec r 0) as [->|Hn]; [vm_compute; reflexivity|].
apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a word the run stored, read back from the post-state's region chunk *)
Lemma sab_chunk_aval : forall E ss (ms : machine_state) H i r j off (w : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  aval_mem (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
intros E ss ms H i r j off w e v HS Hi Hj He Hv Hw. apply aval_mem_view.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i r HS Hi) as (_ & _ & _ & Hcs). cbn [ms_mem restrict] in Hcs.
eapply val_of_chunk_ok; [| exact He | exact Hv | exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.

(* ---------------------------------------------------------------- the mid-state's transport *)
(* the common mid facts at a later state of the walk: the journal is given, the memory of the saved registers and
   of the frame's flag word is kept, and the registers sa_core names are the same *)
Lemma sab_core_kept : forall ly S W (regs : bvmap 5 word) mem md O lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word)
memc mdc k pos lyc' Sc' (Wc' : world SEGS) (regs1' : bvmap 5 word) memc' mdc' k',
sa_core B ly S W regs mem md O lyc Sc Wc regs1 memc mdc k pos ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc' Sc' Wc' memc' mdc' k' ->
ly_F lyc' = ly_F lyc ->
(forall a, spZ regs - 104 <= a < spZ regs \/
   frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> rdW Wc' memc' a = rdW Wc memc a) ->
(getr regs1' 2 = getr regs1 2 /\ getr regs1' 3 = getr regs1 3 /\ getr regs1' 4 = getr regs1 4 /\
 getr regs1' 8 = getr regs1 8 /\ getr regs1' 9 = getr regs1 9 /\ getr regs1' 18 = getr regs1 18 /\
 getr regs1' 19 = getr regs1 19 /\ getr regs1' 23 = getr regs1 23 /\ getr regs1' 25 = getr regs1 25 /\
 getr regs1' 26 = getr regs1 26 /\ getr regs1' 27 = getr regs1 27) ->
sa_core B ly S W regs mem md O lyc' Sc' Wc' regs1' memc' mdc' k' pos.
Proof using Type.
intros ly S W regs mem md O lyc Sc Wc regs1 memc mdc k pos lyc' Sc' Wc' regs1' memc' mdc' k'
HCORE HJ HLF HM HQ.
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ0 & HFRM & HFL & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P23 & P25 & P26 & P27).
destruct HQ as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27).
assert (HFA : frame_addr lyc' 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HLF; reflexivity).
assert (HFL' : flag_addr lyc' 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HLF; reflexivity).
unfold sa_core. cbv zeta. split; [exact HJ|].
split.
{ intros j r Hj. apply (sab_aval_kept (rdW Wc memc)); [exact (HFRM j r Hj)|].
  assert (Hjle : (j < length sa_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length sa_saved] in Hjle.
  intros x Hx. apply HM. left. lia. }
split.
{ rewrite HFA, HFL'. rewrite (sab_rdword_eq (rdW Wc memc) (rdW Wc' memc')); [exact HFL|].
  change (fs_frame_bytes 1) with 128. intros i Hi. apply HM. right. lia. }
rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q23, Q25, Q26, Q27, HFA.
repeat (split; [assumption|]). assumption.
Qed.

(* ---------------------------------------------------------------- the recorder's fields and the state store *)
(* the scalar fields and the answer word of the recorder's representation *)
Lemma sab_rep_fields : forall ly S (rd : reader) R O,
rec_repA B ly S rd R O ->
aval_mem rd (A_G_REC + OFF_REFUSE) 4 (r_refuse R) /\ -2 ^ 31 <= r_refuse R < 2 ^ 31 /\
aval_mem rd (A_G_REC + OFF_STATE) 8 (r_state R) /\ 0 <= r_state R < 2 ^ 64 /\
(exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) O)) /\
(forall pn, In pn O -> In pn (ablocks B ly S)).
Proof using Type.
intros ly S rd R O (Q & HA & HO).
pose proof HA as (_ & _ & _ & _ & HAn & _ & HSc & _).
destruct HSc as (Vr & _ & _ & Vs & _ & Rr & _ & _ & Rs & _).
split; [exact Vr|]. split; [exact Rr|]. split; [exact Vs|]. split; [exact Rs|].
split.
{ unfold aanswer_at in HAn.
  destruct (r_answer R) as [x|], (l_answer Q) as [[p m]|] eqn:EA; try contradiction.
  - destruct HAn as (V & _ & Hin & Hlen & _). cbn [fst snd] in V, Hlen.
    exists p. split; [exact V|]. right. exists m. apply HO.
    unfold lay_blocks. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    rewrite EA. unfold oblk. apply in_eq.
  - exists 0. split; [exact HAn | left; reflexivity]. }
intros pn Hpn. exact (lay_blocks_in _ rd _ _ _ _ HA pn (proj1 (HO pn) Hpn)).
Qed.

(* g_rec.state := h, every other byte of g_rec, record.spill and the recorder's blocks kept *)
Lemma sab_rep_set_state : forall ly S rd ly' S' (rd' : reader) R O h,
rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/ inFP (ablocks_fp O) a ->
 ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
rec_repA B ly' S' rd' (set_state R h) O.
Proof using Type.
intros ly S rd ly' S' rd' R O h (Q & HA & HO) HBl HK Hst Hh.
exists Q. split; [|exact HO].
assert (HBQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hp; apply HBl, HO, Hp).
assert (HKg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  rd' a = rd a) by (intros a Ha Hn; apply HK; [left; exact Ha | exact Hn]).
assert (HKs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a).
{ intros a Ha. apply HK; [right; left; exact Ha|]. unfold A_G_REC, OFF_STATE, A_REC_SPILL, SC_SIZE in *. lia. }
assert (HKb : forall pn a, In pn (lay_blocks Q) -> fst pn <= a < fst pn + snd pn -> rd' a = rd a).
{ intros [p m] a Hp Ha.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & (_ & HOwn)).
  destruct (HOwn (p, m) Hp) as (Hap & _). unfold iv_apart in Hap. cbn [fst snd] in Hap, Ha.
  apply HK; [|unfold A_G_REC, OFF_STATE, REC_SIZE in *; lia].
  right; right. apply HO in Hp. exists (p, p + req_size m). split.
  - unfold ablocks_fp. exact (in_map (fun b => (fst b, fst b + req_size (snd b))) O (p, m) Hp).
  - cbn [fst snd]. pose proof (sab_req_ge m). unfold req_size in *. destruct (Z.eqb_spec m 0); lia. }
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRe & HSc & HOwn).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). cbn [r_calls r_spill set_state] in *.
  split; [exact C1|]. split; [exact C2|].
  split; [apply (aval_mem_kept_r rd); [intros x Hx; apply HKg; unfold OFF_NCALLS, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact C3]|].
  split.
  { intros i c P Hc HP. destruct (C4 i c P Hc HP) as (D1 & D2). split; [|exact D2].
    cbn [r_calls r_spill set_state] in Hc.
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    assert (HPin : forall pn, In pn P -> In pn (lay_blocks Q)).
    { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
      split; [eapply nth_error_In; exact HP | exact Hpn]. }
    apply (acall_at_kept (ablocks B ly S) _ rd); [intros pn Hpn; apply HBQ, HPin, Hpn | | | exact D1].
    - intros x Hx. apply HKg; unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, OFF_STATE, REC_SIZE in *;
      assert (Hi' : Z.of_nat i < 16) by lia; lia.
    - intros pn x Hpn Hx. exact (HKb pn x (HPin pn Hpn) Hx). }
  split; [|exact C6].
  assert (HPin : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q))
  by (intros pn Hpn; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hpn).
  apply (acall_at_kept (ablocks B ly S) _ rd); [intros pn Hpn; apply HBQ, HPin, Hpn | | | exact C5].
  - intros x Hx. apply HKs. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros pn x Hpn Hx. exact (HKb pn x (HPin pn Hpn) Hx). }
split.
{ unfold aanswer_at in *. cbn [r_answer set_state] in *.
  assert (HPin : forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
  { intros pn Hq. unfold lay_blocks. rewrite Hq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn. left. reflexivity. }
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|]; try contradiction.
  - destruct HAn as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (HPin pn eq_refl) as Hpn.
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_ANSWER, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    split; [exact A2|]. split; [exact (HBQ pn Hpn)|]. split; [exact A4|].
    split; [apply (astr_atR_kept_r rd); [intros y Hy; apply (HKb pn y Hpn); lia | exact A5] | exact A6].
  - apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_ANSWER, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact HAn]. }
split.
{ unfold areply_at in *. cbn [r_reply set_state] in *.
  assert (HPin : forall pn, l_reply Q = Some pn -> In pn (lay_blocks Q)).
  { intros pn Hq. unfold lay_blocks. rewrite Hq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
    cbn. left. reflexivity. }
  destruct (r_reply R) as [x|], (l_reply Q) as [pn|]; try contradiction.
  - destruct HRe as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (HPin pn eq_refl) as Hpn.
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY_SIZE, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HBQ pn Hpn)|]. split; [exact A6|].
    split; [apply (abytes_atR_kept_r rd); [intros y Hy; apply (HKb pn y Hpn); lia | exact A7] | exact A8].
  - destruct HRe as (A1 & A2).
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY_SIZE, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A2]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_state].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REFUSE, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S1]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_CODE, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S2]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_NREPLIES, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S3]|].
split; [exact Hst|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_HOST, OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S5]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|]. split; [exact Hh | exact S10].
Qed.

(* the mid-state M6 after a run that keeps every byte and the registers sa_M6m names (the three arms of the stage
   start from it, at the state the dispatch run left) *)
Lemma sab_m6_kept : forall ly S W (regs : bvmap 5 word) mem md O uri id placement client R
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos
(Wc' : world SEGS) (regs1' : bvmap 5 word) memc' mdc',
sa_M6m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc' memc' mdc' (sa_ev6 R) ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc' memc' a = rdW Wc memc a) ->
(getr regs1' 2 = getr regs1 2 /\ getr regs1' 3 = getr regs1 3 /\ getr regs1' 4 = getr regs1 4 /\
 getr regs1' 8 = getr regs1 8 /\ getr regs1' 9 = getr regs1 9 /\ getr regs1' 18 = getr regs1 18 /\
 getr regs1' 19 = getr regs1 19 /\ getr regs1' 20 = getr regs1 20 /\ getr regs1' 23 = getr regs1 23 /\
 getr regs1' 24 = getr regs1 24 /\ getr regs1' 25 = getr regs1 25 /\ getr regs1' 26 = getr regs1 26 /\
 getr regs1' 27 = getr regs1 27) ->
sa_M6m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc' regs1' memc' mdc' pos.
Proof using LAWS.
intros ly S W regs mem md O uri id placement client R lyc Sc Wc regs1 memc mdc pos Wc' regs1' memc' mdc'
HM HJ MEQ HQ.
pose proof HM as (HCORE & R20 & R24 & HBUF & O6 & HREP6 & HACCT & HMO6).
destruct HQ as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q23 & Q24 & Q25 & Q26 & Q27).
pose proof HCORE as (HJ0 & _).
pose proof (proj1 HJ0) as HARo.
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HARo Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (sab_rep_fields lyc Sc (rdW Wc memc) (rec_record R REC_ADD (sa_A uri id placement client)) O6 HREP6)
  as (_ & _ & _ & _ & _ & HO6b).
assert (HF8 : 0 <= frame_addr lyc 1 pos / 8 <= frame_addr lyc 1 pos)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
split.
{ eapply sab_core_kept; [exact HCORE | exact HJ | reflexivity | |].
  - intros a Ha. apply MEQ. destruct Ha as [Ha | Ha]; lia.
  - repeat (split; [assumption|]). assumption. }
split; [rewrite Q20; exact R20|].
split; [rewrite Q24; exact R24|].
split.
{ intros i Hi. rewrite MEQ by (unfold SHADOW_OFF; lia). exact (HBUF i Hi). }
exists O6.
split.
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc' memc') _ O6 HREP6).
  - intros pn Hpn. exact (HO6b pn Hpn).
  - intros a Ha. apply MEQ.
    destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia
    | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (sab_inFP_ablocks_fp _ _ Ha) as (p & n & Hpn & Hr).
    pose proof (HO6b (p, n) Hpn) as Hbl.
    destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARo Hbl) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn1).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia. }
split; [exact HACCT | exact HMO6].
Qed.

(* ---------------------------------------------------------------- the program's statics *)
Lemma sab_prog_static : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof using HB.
intros a Ha. rewrite (ts_prog B HB).
destruct Ha as (r & Hr & Hb). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. unfold TFIB_PROG_STATIC.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hb;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.

Section e2.
Hypothesis IMG : cmd_img_facts SEGS B.
#[local] Notation cif_prog_img := (CmdRecBase.cif_prog_img _ _ IMG).
#[local] Notation cif_prog_not_ro := (CmdRecBase.cif_prog_not_ro _ _ IMG).

(* a byte of a live block is off the image *)
Lemma sab_blk_off : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> a < 0x10000 \/ 0x606000 <= a.
Proof using LAWS.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha)))))
  as [Hz _].
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [C1 C2].
unfold in_zr in Hz. lia.
Qed.

(* the read-only bytes of the image, kept across the journal of this call (A's sa_aro_kept) *)
Lemma sab_aro_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
rec_repA B ly S (rdW W mem) R O ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof using LAWS HB IMG.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O HAR HJ HREP HR a Hro Ho He.
pose proof (sab_rep_fields ly S (rdW W mem) R O HREP) as (_ & _ & _ & _ & _ & HOb).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs|exact Hr]
     | exact (CmdRecBase.cif_relro_img _ _ IMG a Hr)]).
pose proof (pa_img_range a Himg) as Hrng.
rewrite (F3 a Himg Ho He); [exact (HR a Hro Ho He)|].
apply fp_spares_closed.
- unfold sa_FP.
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_NCALLS; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_STATE; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_REC_SPILL; lia|].
  apply sink_closed_ablocks_fp. apply Forall_forall. intros [q m] Hqm.
  pose proof (HOb (q, m) Hqm) as Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4 & _). cbn [fst]. lia.
- unfold sa_FP. intros H.
  apply inFP_cons in H as [H|H];
    [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_NCALLS in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H];
    [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H];
    [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_STATE in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H];
    [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold A_REC_SPILL, SC_SIZE in *; lia|exact Hro]|].
  destruct H as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
  cbn [fst snd] in Hr1, Hr2. pose proof (HOb (q, m) Hqm) as Hin.
  pose proof (sab_blk_off ly S W mem md q m a HAR Hin ltac:(lia)) as Hoff. lia.
Qed.

(* ---------------------------------------------------------------- the last step of the refused arm *)
(* `j 0x8a634` at 0x8a600, the instruction answer returns to: it writes nothing, so the mid-state M9 at 0x8a600 is
   the mid-state M9 at its label. The lemma is proved for the AMBIENT FP state, so the arm applies it at the fx1
   answer returned (with SA_M9_at taken at that fx1). *)
Let RUNTO := paj_run_to B LAWS.
Lemma sab_m9_jmp :
@SA_M9_at fx rc SK PI B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch pu id pp pc uri placement client R O
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M9m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_sup_add + 0x200))) memc (seg_rom SEGS)) mdc)
(sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS.
intros HM9 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HFRM0 HM.
pose proof HCX as (HPRE & Hfr7 & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP & HEV & HLIVE & HMO).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSPB : 0x7fff7f800000 <= spZ regs <= 2 ^ 47) by lia.
pose proof HM as (HCORE & HPOST).
pose proof HCORE as (HJ & HFRMs & HFLG & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & R25 & R26 & R27).
assert (HARc : AR SEGS B lyc Sc Wc memc mdc) by exact (proj1 HJ).
assert (Hfin : In (1, pos) (frames Sc)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left; reflexivity. }
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HARc Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
(* the seed at 0x8a600: no region, no shadow entry *)
set (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_sup_add + 0x200) sr_atoms [] None sab_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (AF_sup_add + 0x200))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS sab_Bx [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
paj_run_to_tok RUNTO HS HJ SHOK sab_Bspan L_M9.
{ apply awr_ok_nil. }
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
sab_memeq Wc MEQ. sab_clear_frames.
pmkst HS.
prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (23%bv : bv 5) T23.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
rewrite (ew_Eimg_Ereg_nat regs1 [] 2%nat (2%bv : bv 5) eq_refl) in T2.
rewrite (ew_Eimg_Ereg_nat regs1 [] 3%nat (3%bv : bv 5) eq_refl) in T3.
rewrite (ew_Eimg_Ereg_nat regs1 [] 4%nat (4%bv : bv 5) eq_refl) in T4.
rewrite (ew_Eimg_Ereg_nat regs1 [] 8%nat (8%bv : bv 5) eq_refl) in T8.
rewrite (ew_Eimg_Ereg_nat regs1 [] 9%nat (9%bv : bv 5) eq_refl) in T9.
rewrite (ew_Eimg_Ereg_nat regs1 [] 10%nat (10%bv : bv 5) eq_refl) in T10.
rewrite (ew_Eimg_Ereg_nat regs1 [] 18%nat (18%bv : bv 5) eq_refl) in T18.
rewrite (ew_Eimg_Ereg_nat regs1 [] 19%nat (19%bv : bv 5) eq_refl) in T19.
rewrite (ew_Eimg_Ereg_nat regs1 [] 23%nat (23%bv : bv 5) eq_refl) in T23.
rewrite (ew_Eimg_Ereg_nat regs1 [] 25%nat (25%bv : bv 5) eq_refl) in T25.
rewrite (ew_Eimg_Ereg_nat regs1 [] 26%nat (26%bv : bv 5) eq_refl) in T26.
rewrite (ew_Eimg_Ereg_nat regs1 [] 27%nat (27%bv : bv 5) eq_refl) in T27.
(* the recorder's blocks after the call are live, so their bytes are addresses MEQ speaks of *)
destruct HPOST as (R' & O' & q & HQm & HQ10 & HQ4096 & HQrep & HQO1 & HQbl1 & HQbl2 & HQin & HQne & HQnm & HQstr
  & HQbytes & HQmo).
pose proof (sab_rep_fields lyc Sc (rdW Wc memc) R' O' HQrep) as (_ & _ & _ & _ & _ & HO'b).
apply (HM9 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc _ _ _ pos HCX HFRM0).
unfold sa_M9m. cbv zeta. split.
{ eapply sab_core_kept; [exact HCORE | exact HJ | reflexivity | |].
  - intros a Ha. apply MEQ. lia.
  - rewrite T2, T3, T4, T8, T9, T18, T19, T23, T25, T26, T27.
    repeat (split; [reflexivity|]). reflexivity. }
unfold sa_postQ. cbv zeta.
exists R', O', q.
split; [exact HQm|].
split; [rewrite T10; exact HQ10|].
split; [exact HQ4096|].
split.
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc (ms_mem ms)) R' O' HQrep).
  - intros pn Hpn. exact (HO'b pn Hpn).
  - intros a Ha. apply MEQ.
    destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia
    | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (sab_inFP_ablocks_fp _ _ Ha) as (p & n & Hpn & Hr).
    pose proof (HO'b (p, n) Hpn) as Hbl.
    destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc Hbl) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn1).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia. }
split; [exact HQO1|]. split; [exact HQbl1|]. split; [exact HQbl2|]. split; [exact HQin|].
split; [exact HQne|]. split; [exact HQnm|].
split.
{ apply (sab_astr_kept (rdW Wc memc)); [exact HQstr|].
  intros i Hi. apply MEQ.
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc q _ HARc HQin) as (_ & Hq4096 & Hqceil & _).
  pose proof (req_size_pos (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1) ltac:(lia))
    as [_ Hrq]. lia. }
split; [exact HQbytes | exact HQmo].
Qed.

(* ---------------------------------------------------------------- the footprint of answer's call *)
(* the footprint of answer's call (answer_c.v:136-137) *)
Definition sab_ansFP (old : Z) (Ox : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
ablocks_fp (filter (fun pn => fst pn =? old) Ox).
Lemma sab_ansFP_cases : forall lyx Sx (Wx : world SEGS) memx mdx (Ox : list (Z * Z)) old a,
AR SEGS B lyx Sx Wx memx mdx -> (forall pn, In pn Ox -> In pn (ablocks B lyx Sx)) ->
inFP (sab_ansFP old Ox) a ->
a < alloc_ceiling /\ (inFP cmd_PG a \/ exists p n, In (p, n) Ox /\ p <= a < p + req_size n).
Proof using LAWS.
intros lyx Sx Wx memx mdx Ox old a HAR HOx HFP.
pose proof asan_consts as (C1 & _).
unfold sab_ansFP in HFP. apply inFP_cons in HFP as [Ha | HFP].
{ unfold OFF_ANSWER, A_G_REC in Ha. split; [lia|]. left. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
apply inFP_cons in HFP as [Ha | HFP].
{ unfold OFF_STATE, A_G_REC in Ha. split; [lia|]. left. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
destruct (sab_inFP_ablocks_fp _ _ HFP) as (p & n & Hin & Hr).
apply sab_filter_in in Hin.
destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p n HAR (HOx _ Hin)) as (_ & _ & Hceil & _).
split; [lia|]. right. exists p, n. split; [exact Hin | exact Hr].
Qed.
Lemma sab_ansFP_not_frame : forall lyx Sx (Wx : world SEGS) memx mdx Ox old a cid posx,
AR SEGS B lyx Sx Wx memx mdx -> (forall pn, In pn Ox -> In pn (ablocks B lyx Sx)) ->
In (cid, posx) (frames Sx) ->
frame_addr lyx cid posx <= a < frame_addr lyx cid posx + fs_frame_bytes cid ->
~ inFP (sab_ansFP old Ox) a.
Proof using LAWS HB IMG.
intros lyx Sx Wx memx mdx Ox old a cid posx HAR HOx Hfr Ha HFP.
destruct (sab_ansFP_cases lyx Sx Wx memx mdx Ox old a HAR HOx HFP) as (_ & [HPG | (p & n & Hin & Hr)]).
- apply (al_client_img SEGS B LAWS lyx Sx Wx memx mdx a HAR).
  + right; left. exists cid, posx. split; [exact Hfr | exact Ha].
  + exact (cif_prog_img a HPG).
- pose proof (sep_block_frame SEGS B LAWS lyx Sx Wx memx mdx p n cid posx HAR (HOx _ Hin) Hfr) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* two live blocks with the same start have the same size *)
Lemma sab_uniq : forall lyx Sx (Wx : world SEGS) memx mdx, AR SEGS B lyx Sx Wx memx mdx -> forall p m m',
In (p, m) (ablocks B lyx Sx) -> In (p, m') (ablocks B lyx Sx) -> m = m'.
Proof using LAWS.
intros lyx Sx Wx memx mdx HARx p m m' H1 H2. destruct (Z.eq_dec m m') as [Em|Hne]; [exact Em|exfalso].
pose proof (sep_blocks SEGS B LAWS lyx Sx Wx memx mdx p m p m' HARx H1 H2
  ltac:(intros EE'; apply Hne; congruence)) as Hd.
destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p m HARx H1) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p m' HARx H2) as (_ & _ & _ & _ & _ & _ & Hm').
pose proof (req_size_pos m ltac:(lia)) as [Hq _]. pose proof (req_size_pos m' ltac:(lia)) as [Hq' _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
End e2.
End e.
End f.
End d.
