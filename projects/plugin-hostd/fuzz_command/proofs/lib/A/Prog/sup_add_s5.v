(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   memchr call 0x86ef8 to the return of sup_reply_code 0x86f18, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS, the state
   after the return) at c8557374ad2e.

   The pieces: 0x86ef8 jal memchr (the reply holds no NUL, so the wrapper returns 0: the not-found contract
   through PaArt.v's aj_art_at); 0x86efc bnez a0 (not taken); 0x86f00 mv a0,s3; 0x86f04 jal check_reply_answer
   (cl_callS); 0x86f08 the inline check of &g_rec.reply (a shadow entry of g_rec makes it a literal 0); 0x86f10
   ld a0,928(s9); 0x86f14 jal sup_reply_code (cl_callS), whose return point 0x86f18 is CR_CODE_stmt's.
   After each call the mid-walk invariant cr_mid and the registers cr_regs_at are rebuilt from the callee's journal
   (the frame (1, pos) is among the caller's frames, the saved registers lie above the callee's stack pointer, g_rec
   is a program static), and the walk is seeded again with check_reply_sd.v's cr_seed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s2.v, with its module paths and module names changed; 923 of its 964 lines of code are new or changed and 544 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage M3 (0x8a050) to M3b / M4: the range check
   on id, the refusal branch (answer by `jal` at 0x8a08c, then M4) and the mix of the call into g_rec.state
   (mix_call at 0x8a09c, then M3b). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at M3: the registers are atoms 0..31, atom 32 is g_rec.refuse (as 32 bits) and atom 33
   g_rec.state; the two fields the stage loads are read-only regions on s5 = g_rec (atom 21) *)
Definition s5_SB : Z := 0x7fff8000.
Definition s5_Bx : sv := SLit s5_SB.
Definition s5_Bspan : Z * Z := (s5_SB, s5_SB + 2 ^ 44 - 1).
Definition s5_regions : smem :=
[ YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some 21%nat) 944 952 944 944 [YP09.mkChunk 944 (CVal 8 (SOff 33 0))] ].
Definition s5_facts : facts := mkFacts [] [] [].
Definition ss_s5 : sstate := mkSS L_M3 sr_atoms s5_regions None s5_facts.
Definition s5_extra (rf st : Z) : list word := map (Z_to_bv 64) [rf; st].
(* after mix_call (0x8a0a0): a fresh state with one region, g_rec.state as a writable window with no chunk; the
   store `sd a0,944(s5)` fills it *)
Definition s5_rg_st : YP09.region := YP09.mkRegion (Some 21%nat) 944 952 944 952 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma s5_val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite <- Hb. symmetry.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma s5_s1_cases : forall x, x mod 16 = 0 ->
x - 160 - (x - 160) mod 32 = x - 160 \/ x - 160 - (x - 160) mod 32 = x - 176.
Proof.
intros x Hx. pose proof (Z.mod_pos_bound (x - 160) 32 ltac:(lia)) as Hb.
Z.div_mod_to_equations. lia.
Qed.
Lemma s5_div16 : forall x, 625 <= x / 16 -> 0 <= x -> 10000 <= x.
Proof. intros x H H0. Z.div_mod_to_equations. lia. Qed.
Lemma s5_div16_lt : forall x, 0 <= x -> x / 16 < 625 -> x < 10000.
Proof. intros x H0 H. Z.div_mod_to_equations. lia. Qed.
Lemma s5_in_range : forall id, - 2 ^ 31 <= id < 2 ^ 31 -> (id mod 2 ^ 32) / 16 < 625 -> 0 <= id < 10000.
Proof.
intros id Hid Hlt.
assert (Hb : 0 <= id mod 2 ^ 32) by (apply Z.mod_pos_bound; lia).
pose proof (s5_div16_lt (id mod 2 ^ 32) Hb Hlt) as H1.
destruct (Z_lt_le_dec id 0) as [Hneg|Hpos].
- exfalso.
  assert (E0 : (id + 1 * 2 ^ 32) mod 2 ^ 32 = id mod 2 ^ 32) by (apply Z.mod_add; lia).
  assert (E1 : (id + 1 * 2 ^ 32) mod 2 ^ 32 = id + 1 * 2 ^ 32) by (apply Z.mod_small; lia).
  lia.
- rewrite (Z.mod_small id (2 ^ 32)) in H1 by lia. lia.
Qed.
(* the model on the refused arm: an id in range and a refusal give answer's own hand_back *)
Lemma s5_m_refused : forall R uri id placement client e x chg,
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
(* a byte of the blocks of a footprint list *)
Lemma s5_inFP_ablocks_fp : forall bl a, inFP (ablocks_fp bl) a ->
exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
intros bl a (r & Hin & Hr). unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([p n] & <- & Hin).
cbn [fst snd] in Hr. exists p, n. split; [exact Hin | exact Hr].
Qed.
(* the footprint of answer's call: g_rec.answer, g_rec.state and the old answer's block *)
Definition s5_ansFP (old : Z) (Ox : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
ablocks_fp (filter (fun pn => fst pn =? old) Ox).
Lemma s5_filter_in : forall (f : Z * Z -> bool) (l : list (Z * Z)) x, In x (filter f l) -> In x l.
Proof.
intros f l x. induction l as [|q l IH].
- cbn. exact (fun H => H).
- cbn. destruct (decide (f q)) as [Hq|Hq].
  + cbn [In]. intros [H|H]; [left; exact H | right; exact (IH H)].
  + intros H. right. exact (IH H).
Qed.
Lemma s5_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma s5_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
Lemma s5_rdword_eq : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma s5_astr_kept : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] K. split; [|exact H2]. intros i Hi.
pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite K by lia. exact (H1 i Hi).
Qed.
(* srliw a0,s3,4 on a signed 32-bit id *)
Lemma s5_srliw : forall E id, ew E 19 = w64 id -> - 2 ^ 31 <= id < 2 ^ 31 ->
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
Lemma s5_refuse_eq : forall E r, ew E 32 = Z_to_bv 64 (r mod 2 ^ 32) -> - 2 ^ 31 <= r < 2 ^ 31 ->
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
(* the blocks of the post on the refusal arm, from answer's post and the accounting at M3 *)
Lemma s5_ans_blocks : forall (bl0 blc bl2 O O3 O' : list (Z * Z)) old p1 p2 n,
(forall pn, In pn O3 -> In pn O \/ ~ In pn bl0) ->
(forall pn, In pn blc -> (In pn bl0 /\ ~ In pn O) \/ In pn O3) ->
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn O3 -> In pn blc) ->
(old = 0 \/ exists m, In (old, m) O3) ->
(forall pn, In pn blc -> 4096 <= fst pn) ->
(forall p m m', In (p, m) blc -> In (p, m') blc -> m = m') ->
(forall p m m', In (p, m) bl2 -> In (p, m') bl2 -> m = m') ->
p1 <> p2 -> (forall pn, In pn blc -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
(forall pn, In pn bl2 <-> (In pn blc /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn O' <-> (In pn O3 /\ fst pn <> old) \/ pn = (p1, n)) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
(forall pn, In pn bl2 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl2) /\
In (p2, n) bl2 /\ (forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
~ In p2 (map fst O').
Proof.
intros bl0 blc bl2 O O3 O' old p1 p2 n A1 A2 A3 HO3 Hold H4096 Uc U2 Hp12 HF HB2 HO'.
assert (DEC : forall (x : Z * Z) l, {In x l} + {~ In x l})
  by (intros x l; apply in_dec; intros u v; decide equality; apply Z.eq_dec).
(* a block of the entry outside the recorder's O that is live at M3 is none of answer's two fresh blocks *)
assert (FR : forall p, In (p, n) bl0 -> ~ In (p, n) O -> In (p, n) blc -> fst (p, n) = old -> False).
{ intros p H0 HnO Hc Ep. cbn [fst] in Ep. subst p. destruct Hold as [Eo | (m0 & Hm0)].
  - pose proof (H4096 _ Hc) as X. cbn [fst] in X. lia.
  - pose proof (Uc old n m0 Hc (HO3 _ Hm0)) as ->.
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
  - pose proof (Uc old m m0 (A3 _ H0 HnO) (HO3 _ Hm0)) as ->.
    destruct (A1 _ Hm0) as [X | X]; [exact (HnO X) | exact (X H0)]. }
split; [apply HB2; right; right; reflexivity|].
split.
{ intros pn H0 HnO ->. pose proof (A3 _ H0 HnO) as Hc.
  destruct (Z.eq_dec (fst (p2, n)) old) as [Ep|Np]; [exact (FR p2 H0 HnO Hc Ep)|].
  exact (proj2 (HF _ Hc Np) eq_refl). }
intros Hq. apply in_map_iff in Hq as ([p m] & Ep & Hin). cbn [fst] in Ep. subst p.
apply HO' in Hin as [[H1 H2] | E].
- assert (Hb2 : In (p2, m) bl2) by (apply HB2; left; split; [exact (HO3 _ H1) | exact H2]).
  assert (Hb2' : In (p2, n) bl2) by (apply HB2; right; right; reflexivity).
  pose proof (U2 p2 m n Hb2 Hb2') as ->. exact (proj2 (HF _ (HO3 _ H1) H2) eq_refl).
- injection E as E1 _. exact (Hp12 (eq_sym E1)).
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the frame hypotheses of a run: the walk's regions have an empty writable window, so the run keeps every byte *)
Ltac s5_clear_frames :=
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac s5_memeq Wx MEQ :=
lazymatch goal with
| HX : frame_of ?Ex ?rs (mrestrict (w_H Wx) ?m0) (mrestrict (w_H Wx) ?m1) |- _ =>
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) m0 a) by
  (let a := fresh "a" in let Ha := fresh "Ha" in
   intros a Ha; apply (kept_of_frame Ex rs (w_H Wx) m0 m1 (fun _ => False) HX);
   [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
     let a' := fresh "a'" in let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
     intros b wlo whi a' Hin Hrr; vm_compute in Hin;
     repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
       [ injection Hq as <- <- <-; cbn [base_val] in Hrr; exfalso; clear - Hrr; lia |]);
     destruct Hin
   | exact Ha | let X := fresh "X" in intros X; exact X ])
end.
(* the run after mix_call writes only g_rec.state (s5_rg_st, base s5 = g_rec by U21) *)
Ltac s5_memeq_st Wx U21 MEQ :=
lazymatch goal with
| HX : frame_of ?Ex ?rs (mrestrict (w_H Wx) ?m0) (mrestrict (w_H Wx) ?m1) |- _ =>
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) m0 a) by
  (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
   intros a Ha Hn; apply (kept_of_frame Ex rs (w_H Wx) m0 m1 (fun x => A_G_REC + 944 <= x < A_G_REC + 952) HX);
   [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
     let a' := fresh "a'" in let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
     intros b wlo whi a' Hin Hrr; vm_compute in Hin;
     repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
       [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U21 in Hrr; lia |]);
     destruct Hin
   | exact Ha | exact Hn ])
end.
(* a word the run stored, read back from the post-state's region chunk *)
Lemma s5_chunk_aval : forall E ss (ms : machine_state) H i r j off (w : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  aval_mem (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
intros E ss ms H i r j off w e v HS Hi Hj He Hv Hw. apply s5_aval_of_val_mem.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i r HS Hi) as (_ & _ & _ & Hcs). cbn [ms_mem restrict] in Hcs.
eapply val_of_chunk_ok; [| exact He | exact Hv | exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

(* the seed of the stage at M3 *)
Lemma s5_seed : forall (Wc : world SEGS) (regs1 : bvmap 5 word) memc rf st,
getr regs1 21 = w64 A_G_REC ->
aval_mem (rdW Wc memc) (A_G_REC + 0) 4 rf -> 0 <= rf < 2 ^ 32 ->
aval_mem (rdW Wc memc) (A_G_REC + 944) 8 st -> 0 <= st < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (s5_extra rf st))) ss_s5
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + L_M3)) memc (seg_rom SEGS)))
/\ sh_ok SEGS s5_Bx [] (Eimg (Ereg regs1 (s5_extra rf st))) (mrestrict (w_H Wc) memc).
Proof.
intros Wc regs1 memc rf st H21 Hrf Hrf0 Hst Hst0.
set (E := Eimg (Ereg regs1 (s5_extra rf st))).
assert (E21 : ew E 21 = getr regs1 21) by (subst E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 rf)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 st)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (B21 : base_val E (Some 21%nat) = A_G_REC).
{ cbn [base_val]. rewrite E21, H21. unfold w64. rewrite unsigned_lit_small by (unfold A_G_REC; lia). reflexivity. }
split.
- rewrite restrict_mkst_fx. unfold ss_s5. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s5_regions. constructor; [|constructor; [|constructor]].
    * unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B21.
      split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC 0 4 (SOff 32 0) rf);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
      exact (s5_val_mem_of_aval SEGS (w_H Wc) memc _ 4 rf Hrf).
    * unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B21.
      split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC 944 8 (SOff 33 0) st);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      exact (s5_val_mem_of_aval SEGS (w_H Wc) memc _ 8 st Hst).
  + cbn [pairwise_disjoint all_disjoint s5_regions]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B21.
    split; [split; [left; lia | exact I] | split; exact I].
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
(* the rounding mode at this stage's FP state: answer's premise *)
Hypothesis FXR : frm0 fx.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the common mid facts at a later state of the walk: the journal is given, the memory of the frame and of the
   three spills is kept, and the ten registers sa_core names are the same *)
Lemma s5_core_kept : forall ly S W (regs : bvmap 5 word) mem md O lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word)
memc mdc k pos lyc' Sc' (Wc' : world SEGS) (regs1' : bvmap 5 word) memc' mdc' k',
sa_core B ly S W regs mem md O lyc Sc Wc regs1 memc mdc k pos ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc' Sc' Wc' memc' mdc' k' ->
ly_F lyc' = ly_F lyc ->
(forall a, spZ regs - 104 <= a < spZ regs \/ sa_s1 (spZ regs) + 16 <= a < sa_s1 (spZ regs) + 56 \/
   frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> rdW Wc' memc' a = rdW Wc memc a) ->
(getr regs1' 2 = getr regs1 2 /\ getr regs1' 3 = getr regs1 3 /\ getr regs1' 4 = getr regs1 4 /\
 getr regs1' 8 = getr regs1 8 /\ getr regs1' 9 = getr regs1 9 /\ getr regs1' 18 = getr regs1 18 /\
 getr regs1' 19 = getr regs1 19 /\ getr regs1' 21 = getr regs1 21 /\ getr regs1' 25 = getr regs1 25 /\
 getr regs1' 26 = getr regs1 26) ->
sa_core B ly S W regs mem md O lyc' Sc' Wc' regs1' memc' mdc' k' pos.
Proof.
intros ly S W regs mem md O lyc Sc Wc regs1 memc mdc k pos lyc' Sc' Wc' regs1' memc' mdc' k'
(HJ0 & HFRM & H16 & H24 & H48 & HFL & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P25 & P26)
HJ HLF HM (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q21 & Q25 & Q26).
assert (HFA : frame_addr lyc' 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HLF; reflexivity).
assert (HFL' : flag_addr lyc' 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HLF; reflexivity).
unfold sa_core. split; [exact HJ|].
split.
{ intros j r Hj. apply (s5_aval_kept (rdW Wc memc)); [exact (HFRM j r Hj)|].
  assert (Hjle : (j < length sa_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length sa_saved] in Hjle.
  intros x Hx. apply HM. left. lia. }
split; [apply (s5_aval_kept (rdW Wc memc)); [exact H16 | intros x Hx; apply HM; right; left; lia]|].
split; [apply (s5_aval_kept (rdW Wc memc)); [exact H24 | intros x Hx; apply HM; right; left; lia]|].
split.
{ rewrite HFA. apply (s5_aval_kept (rdW Wc memc)); [exact H48 | intros x Hx; apply HM; right; left; lia]. }
split.
{ rewrite HFA, HFL'. rewrite (s5_rdword_eq (rdW Wc memc) (rdW Wc' memc')); [exact HFL|].
  change (fs_frame_bytes 1) with 128. intros i Hi. apply HM. right; right; lia. }
rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q21, Q25, Q26, HFA.
repeat (split; [assumption|]). assumption.
Qed.

(* the footprint of the call of answer (answer_c.v:111-112) *)
Lemma s5_ansFP_cases : forall lyx Sx (Wx : world SEGS) memx mdx (Ox : list (Z * Z)) old a,
AR SEGS B lyx Sx Wx memx mdx -> (forall pn, In pn Ox -> In pn (ablocks B lyx Sx)) ->
inFP (s5_ansFP old Ox) a ->
a < alloc_ceiling /\ (inFP cmd_PG a \/ exists p n, In (p, n) Ox /\ p <= a < p + req_size n).
Proof.
intros lyx Sx Wx memx mdx Ox old a HAR HOx HFP.
pose proof asan_consts as (C1 & _).
unfold s5_ansFP in HFP. apply inFP_cons in HFP as [Ha | HFP].
{ unfold OFF_ANSWER, A_G_REC in Ha. split; [lia|]. left. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
apply inFP_cons in HFP as [Ha | HFP].
{ unfold OFF_STATE, A_G_REC in Ha. split; [lia|]. left. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
destruct (s5_inFP_ablocks_fp _ _ HFP) as (p & n & Hin & Hr).
apply s5_filter_in in Hin.
destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p n HAR (HOx _ Hin)) as (_ & _ & Hceil & _).
split; [lia|]. right. exists p, n. split; [exact Hin | exact Hr].
Qed.
Lemma s5_ansFP_not_frame : forall lyx Sx (Wx : world SEGS) memx mdx Ox old a cid posx,
AR SEGS B lyx Sx Wx memx mdx -> (forall pn, In pn Ox -> In pn (ablocks B lyx Sx)) ->
In (cid, posx) (frames Sx) ->
frame_addr lyx cid posx <= a < frame_addr lyx cid posx + fs_frame_bytes cid ->
~ inFP (s5_ansFP old Ox) a.
Proof.
intros lyx Sx Wx memx mdx Ox old a cid posx HAR HOx Hfr Ha HFP.
destruct (s5_ansFP_cases lyx Sx Wx memx mdx Ox old a HAR HOx HFP) as (_ & [HPG | (p & n & Hin & Hr)]).
- apply (al_client_img SEGS B LAWS lyx Sx Wx memx mdx a HAR).
  + right; left. exists cid, posx. split; [exact Hfr | exact Ha].
  + exact (cif_prog_img a HPG).
- pose proof (sep_block_frame SEGS B LAWS lyx Sx Wx memx mdx p n cid posx HAR (HOx _ Hin) Hfr) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the refused arm calls answer, which returns at some FP state fx1 (PaFx.v's cl_callS_wideF), and reaches M4 at fx1:
   this stage takes M4's statement at every FP state with rounding mode 0 *)
Lemma sa_m3_ok : SA_M3b_stmt B MT -> (forall fx1 : YK11.FPState, frm0 fx1 -> SA_M4_stmt (fx := fx1) B MT) ->
  SA_M3_stmt B MT.
Proof.
intros HM3b HM4. unfold SA_M3_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HM3.
pose proof HCX as (HPRE & Hfr7 & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP & HEV & HLIVE & HMO).
destruct HM3 as (HCORE & H22 & HBUF & O3 & HREP3 & HACCT & HMO3).
pose proof HCORE as (HJ & HFRM & HS16 & HS24 & HS48 & HFLG & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R25 & R26).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSPB : 0x7fff7f800000 <= spZ regs <= 2 ^ 47) by lia.
assert (HSTK176 : 176 <= SUP_ADD_STK) by (vm_compute; discriminate).
assert (Hs1 : sa_s1 (spZ regs) = spZ regs - 160 \/ sa_s1 (spZ regs) = spZ regs - 176)
  by (unfold sa_s1; apply s5_s1_cases; exact Hal16).
assert (HARc : AR SEGS B lyc Sc Wc memc mdc) by exact (proj1 HJ).
assert (Hfin : In (1, pos) (frames Sc)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left; reflexivity. }
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HARc Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
assert (HF8 : 0 <= frame_addr lyc 1 pos / 8 <= frame_addr lyc 1 pos)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
set (R1 := rec_record R REC_ADD (sa_A uri id placement client)) in *.
pose proof (rec_repA_fields B HB LAWS _ _ _ _ _ HREP3) as FLD.
destruct FLD as (Hrf & Hrfr & Hst & Hstr & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSIGA : SIG CS_answer = BASE + AF_answer).
{ rewrite (SIGP CS_answer ltac:(cbv [cmd_prog_syms]; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
assert (HSIGM : SIG CS_mix_call = BASE + AF_mix_call).
{ rewrite (SIGP CS_mix_call ltac:(cbv [cmd_prog_syms]; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
assert (Hrf' : aval_mem (rdW Wc memc) (A_G_REC + 0) 4 (r_refuse R1 mod 2 ^ 32)).
{ intros k Hk. pose proof (Hrf k Hk) as Hk'. unfold OFF_REFUSE in Hk'. rewrite Hk'. f_equal.
  cbv [YO0f.le_byte YG0f.le_byte]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. }
destruct (s5_seed Wc regs1 memc (r_refuse R1 mod 2 ^ 32) (r_state R1) R21 Hrf'
  ltac:(apply Z.mod_pos_bound; lia) Hst Hstr) as [HS SHOK].
remember (Eimg (Ereg regs1 (s5_extra (r_refuse R1 mod 2 ^ 32) (r_state R1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (r_refuse R1 mod 2 ^ 32))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (r_state R1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
(* 0x8a050 .. 0x8a058: a0 := (id mod 2^32) >> 4, a1 := 625, s4 := F + 32 *)
paj_run_tok RUN HS HJ SHOK s5_Bspan.
{ awr_ok_tac. }
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
s5_memeq Wc MEQ1. s5_clear_frames.
(* 0x8a05c: bltu a0,a1 -- the range check on id *)
psrr_branch_tok RUN BR HS SHOK s5_Bspan.
- (* 0 <= id < 10000 *)
  paj_run_tok RUN HS HJ SHOK s5_Bspan.
  { awr_ok_tac. }
  lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv2 := with_vm_backing x y z) in *; clearbody mdv2 end.
  s5_memeq Wc MEQ2a. s5_clear_frames.
  psrr_branch_tok RUN BR HS SHOK s5_Bspan.
  + (* g_rec.refuse = 0: 0x8a094 a0 := g_rec.state, a1 := c, the call of mix_call at 0x8a09c *)
    assert (HREF0 : r_refuse R1 = 0).
    { rewrite branch_eq_U, (s5_refuse_eq E (r_refuse R1) E32 Hrfr) in Hc0. apply Z.eqb_eq. exact Hc0. }
    assert (HIN : 0 <= id < 10000).
    { rewrite branch_ltu_U in Hc.
      rewrite (s5_srliw E id ltac:(rewrite (EE 19%nat (19%bv : bv 5) eq_refl), R19; exact H11) Hid), U_SLit in Hc.
      change (zcanon 625) with 625 in Hc. apply Z.ltb_lt in Hc. exact (s5_in_range id Hid Hc). }
    paj_run_tok RUN HS HJ SHOK s5_Bspan.
    { awr_ok_tac. }
    lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv3 := with_vm_backing x y z) in *; clearbody mdv3 end.
    s5_memeq Wc MEQ3. pose proof (fun a Ha => eq_trans (MEQ3 a Ha) (eq_trans (MEQ2a a Ha) (MEQ1 a Ha))) as MEQ.
    clear MEQ3. s5_clear_frames.
    pmkst HS. rewrite HSIGM.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
    rewrite (EE 2%nat (2%bv : bv 5) eq_refl) in P2. rewrite (EE 3%nat (3%bv : bv 5) eq_refl) in P3.
    rewrite (EE 4%nat (4%bv : bv 5) eq_refl) in P4. rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in P8.
    rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in P9. rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in P18.
    rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in P19. rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in P21.
    rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in P25. rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in P26.
    rewrite (EE 22%nat (22%bv : bv 5) eq_refl) in P11. rewrite E33 in P10.
    assert (P2' : getr (ms_regs ms1) 2 = w64 (sa_s1 (spZ regs))) by (rewrite P2; exact R2).
    assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3; exact R3).
    assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4; exact R4).
    assert (P10' : getr (ms_regs ms1) 10 = w64 (r_state R1)) by exact P10.
    assert (P11' : getr (ms_regs ms1) 11 = w64 (sa_c R)) by (rewrite P11; exact H22).
    (* the state at the call *)
    pose proof HACCT as (HA1 & HA2 & HA3 & HO3live & HA5).
    assert (HARC : AR SEGS B lyc Sc Wc (ms_mem ms1) mdv3) by exact (proj1 HJ).
    assert (HAROc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
      by exact (sa_aro_kept B HB LAWS IMG
        SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] lyc Sc Wc (ms_mem ms1) mdv3 (sa_ev3 R) R O HAR HJ HREP HROD).
    assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms1)))
      by exact (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem ms1) mdv3 HARC HAROc).
    assert (HREPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms1)) R1 O3).
    { apply (rec_repA_kept B HB LAWS lyc Sc (rdW Wc memc) lyc Sc (rdW Wc (ms_mem ms1)) R1 O3 HREP3).
      - intros a Hin. apply MEQ. unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hin. lia.
      - intros p n i Hpn Hi. apply MEQ.
        destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc (HO3live _ Hpn)) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia.
      - exact HO3live. }
    pose proof (rec_repA_fields B HB LAWS _ _ _ _ _ HREPc) as FLDc.
    destruct FLDc as (_ & _ & _ & _ & _ & _ & _ & _ & HO3fact).
    assert (HCOREc : sa_core B ly S W regs mem md O lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv3 (sa_ev3 R) pos).
    { eapply s5_core_kept; [exact HCORE | exact HJ | reflexivity | |].
      - intros a Ha. apply MEQ. destruct Hs1 as [Es1|Es1]; rewrite Es1 in Ha; lia.
      - repeat (split; [assumption|]). assumption. }
    destruct (rec_repA_last_call B HB LAWS lyc Sc (rdW Wc (ms_mem ms1)) R
      (sa_A uri id placement client) O3 HREPc) as (Pc & HACALL & _).
    assert (HSLOT : (exists i, 0 <= i < REC_CALLS_MAX /\ sa_c R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/
      sa_c R = A_REC_SPILL).
    { unfold sa_c. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; [apply Nat.ltb_lt in Elt|].
      - left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
      - right. reflexivity. }
    assert (HNEVm : st_nev Sc + EV_MIX_CALL <= EV_MAX).
    { pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
      unfold EV_SUP_ADD in HEV. unfold sa_ev3, sa_ev2, sa_ev1 in Hnev.
      unfold EV_MIX_CALL, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
    (* 0x8a09c: jal mix_call *)
    eapply SRr_bind.
    { eapply (cl_callS_na B LAWS Wc (ms_regs ms1) (ms_mem ms1) _ SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md
        [(1, pos)] lyc Sc mdv3 (sa_ev3 R) MIX_CALL_STK [] EV_MIX_CALL (sa_s1 (spZ regs) - spZ regs) _ _ HJ).
      - unfold spZ at 1. rewrite P2'. unfold w64. rewrite unsigned_lit_small by lia. lia.
      - destruct Hs1 as [Es1|Es1]; rewrite Es1;
        [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia];
        vm_compute; reflexivity.
      - destruct Hs1 as [Es1|Es1]; lia.
      - vm_compute; discriminate.
      - destruct Hs1 as [Es1|Es1]; rewrite Es1;
        [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia];
        vm_compute; discriminate.
      - exact P3'.
      - exact P4'.
      - reflexivity.
      - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite P1. rewrite unsigned_lit_small by lia. lia.
      - intros HFN.
        exact (TMIX_CALL fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv3 (r_state R1) (sa_c R)
          (REC_ADD, sa_A uri id placement client) Pc HFN HAROc P10' Hstr P11' HSLOT HACALL HROc HNEVm).
      - intros a (r & Hr & _). destruct Hr. }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP2 & HQ10 & _ & -> & ->).
    (* what the call kept: it writes only its own stack window (FP = []) *)
    pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & Fi1 & Fi2 & Fi3 & Fi4 & _).
    assert (NOFP : forall a, ~ inFP [] a) by (intros a (r & Hr & _); destruct Hr).
    assert (KEEPc : forall a, spZ regs - 104 <= a < spZ regs \/
      sa_s1 (spZ regs) + 16 <= a < sa_s1 (spZ regs) + 56 \/
      frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> rdW W2 mem2 a = rdW Wc (ms_mem ms1) a).
    { intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
      - apply Fi1; [destruct Hs1 as [Es1|Es1]; lia | destruct Hs1 as [Es1|Es1]; lia | exact (NOFP a)].
      - apply Fi1; [destruct Hs1 as [Es1|Es1]; lia | destruct Hs1 as [Es1|Es1]; lia | exact (NOFP a)].
      - apply (Fi4 1 pos a Hfin); [|exact (NOFP a)].
        left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia. }
    assert (KEEPsh : forall i, 0 <= i < 4 -> rdW W2 mem2 (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 + i) =
      rdW Wc (ms_mem ms1) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 + i)).
    { intros i Hi. apply (Fi4 1 pos _ Hfin); [|exact (NOFP _)].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
    assert (KEEPrec : forall a, in_rec a -> rdW W2 mem2 a = rdW Wc (ms_mem ms1) a).
    { intros a Hin.
      assert (HPGa : inFP cmd_PG a).
      { unfold in_rec, REC_SIZE, SC_SIZE in Hin. destruct Hin as [Hin | Hin].
        - exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
        - exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
      destruct (sa_prog_unowned B HB LAWS a HPGa) as [Hown Herr].
      apply Fi3; [exact (cif_prog_img a HPGa) | exact Hown | exact Herr |].
      apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | exact (NOFP a)]. }
    assert (KEEPblk : forall p n i, In (p, n) O3 -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc (ms_mem ms1) (p + i)).
    { intros p n i Hpn Hi. destruct (HO3fact (p, n) Hpn) as (Hbl & H1n & _). cbn [fst snd] in H1n.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
      apply (Fi2 p n i Hbl Hbl); [lia | exact (NOFP _)]. }
    (* back at 0x8a0a0: a fresh state with g_rec.state writable *)
    rewrite P1.
    jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
    specialize (HS2 (Forall_nil _)).
    clear HS. rewrite <- restrict_mkst_fx in HS2.
    pose proof (img_env_havoc E 40%nat (map (getr regs2) CLOB) HEI ltac:(vm_compute; lia)) as HEIhv.
    assert (U21h : bv_unsigned (ew (havoc E 40 (map (getr regs2) CLOB)) 21) = A_G_REC).
    { rewrite ew_havoc_old by (cbv; lia). rewrite (EE 21%nat (21%bv : bv 5) eq_refl), R21.
      unfold w64. apply unsigned_lit_small. unfold A_G_REC. lia. }
    assert (ROK : forall m, region_ok SEGS (havoc E 40 (map (getr regs2) CLOB)) m s5_rg_st).
    { intros m. unfold region_ok, s5_rg_st.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U21h. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [|constructor].
      intros o Ho. apply PRW. apply (sa_HPROG B HB LAWS).
      exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. }
    pose proof (st_ok_pi_add_region _ _ _ s5_rg_st HS2 eq_refl (ROK _) I) as HS3.
    clear HS2 ROK.
    (* s5 = g_rec exactly (the window's disjointness from the shadow span is decided on this fact) *)
    assert (AF21 : afact_ok (havoc E 40 (map (getr regs2) CLOB)) 21 (mkAF A_G_REC A_G_REC 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21h, Z.pow_0_r, Z.mod_1_r. lia. }
    pose proof (st_ok_pi_add_fact _ _ _ 21%nat (mkAF A_G_REC A_G_REC 0) HS3 AF21) as HS. clear HS3.
    lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?s ?m =>
      let s' := eval vm_compute in s in change (st_ok_pi sg vl Ex s' m) in HS end.
    assert (SHOK2 : sh_ok SEGS s5_Bx [] (havoc E 40 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2))
      by (unfold sh_ok; apply Forall_nil).
    (* 0x8a0a0 .. 0x8a0b4: sd a0,944(s5); a2 := "resp %d"; a1 := 32; a0 := s4 = F + 32; a3 := s3 = id *)
    paj_run_to_tok RUNTO HS HJo SHOK2 s5_Bspan L_M3b.
    { cbn [ss_mem]. eapply awr_ok_cons_gen; [reflexivity | exact U21h | | apply awr_ok_nil].
      intros a Ha. cbn [s5_rg_st YP09.r_wlo YP09.r_whi] in Ha.
      assert (HPGa : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
      unfold awr_byte, awr_prog_or_caller. right; right; right; right; left.
      split; [|split; [exact (sa_HPROG B HB LAWS a HPGa) | exact (cif_prog_img a HPGa)]].
      unfold sa_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. unfold OFF_STATE. lia. }
    lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv4 := with_vm_backing x y z) in *; clearbody mdv4 end.
    s5_memeq_st W2 U21h MEQ5. s5_clear_frames.
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (21%bv : bv 5) T21. prreg HS (25%bv : bv 5) T25.
    prreg HS (26%bv : bv 5) T26.
    prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
    prreg HS (13%bv : bv 5) T13. prreg HS (20%bv : bv 5) T20.
    rewrite (EE 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EE 3%nat (3%bv : bv 5) eq_refl) in T3.
    rewrite (EE 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in T8.
    rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in T18.
    rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in T21.
    rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in T26.
    rewrite (EE 26%nat (26%bv : bv 5) eq_refl), R26 in T10, T20.
    rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in T13.
    (* the stored state, read back from the region *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) => rename msx into ms4;
      assert (D44 : sv_denot Ex (SOff 44 0) = Z_to_bv 64 (mixcall (r_state R1) (fst (REC_ADD, sa_A uri id placement client))
        (snd (REC_ADD, sa_A uri id placement client))))
        by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HQ10);
      assert (U21x : bv_unsigned (ew Ex 21) = A_G_REC) by exact U21h;
      pose proof (s5_chunk_aval Ex _ ms4 (w_H W2) 0 _ 0 944 8 (SOff 44 0) _ HS eq_refl eq_refl D44
        ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply mixcall_range; exact Hstr) ltac:(cbn; lia)) as AST;
      cbn [YP09.r_base base_val] in AST; rewrite U21x in AST
    end.
    change (N.to_nat 8) with 8%nat in AST.
    assert (HREP2 : rec_repA B lyc Sc (rdW W2 (ms_mem ms4)) (rec_mix R1 (REC_ADD, sa_A uri id placement client)) O3).
    { unfold rec_mix.
      apply (rec_repA_set_state B HB LAWS lyc Sc (rdW Wc (ms_mem ms1)) (rdW W2 (ms_mem ms4)) R1 O3 _
        HREPc).
      - intros a Hin Hns. rewrite MEQ5; [exact (KEEPrec a Hin) | |].
        + unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hin. lia.
        + unfold OFF_STATE in Hns. exact Hns.
      - intros p n i Hpn Hi. destruct (HO3fact (p, n) Hpn) as (Hbl & H1n & _). cbn [fst snd] in H1n.
        pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
        destruct (al_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms1) mdv3 p n HARC Hbl) as (_ & Hp4096 & Hpceil & _).
        pose proof (lem_blk_off B HB LAWS lyc Sc Wc (ms_mem ms1) mdv3 p n (p + i) HARC Hbl
          ltac:(lia)) as Hoff.
        rewrite MEQ5; [exact (KEEPblk p n i Hpn Hi) | lia | unfold A_G_REC; lia].
      - unfold OFF_STATE. exact AST.
      - apply mixcall_range. exact Hstr. }
    pose proof (frm_off_imgP B lyc Sc Wc memc mdc 1 pos HARc Hfin) as HFimg.
    assert (HFoff : frame_addr lyc 1 pos + 128 <= 0x10000 \/ 0x606000 <= frame_addr lyc 1 pos)
      by (destruct HFimg as [X|X]; [left|right]; exact X).
    (* M3b at 0x8a0b8, v = id and the recorder mixed *)
    apply (HM3b ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc W2 _ _ _ pos HCX).
    unfold sa_M3bm. cbv zeta.
    split.
    { eapply s5_core_kept; [exact HCOREc | | reflexivity | |].
      - eapply ajournal_mono_k; [exact HJo | unfold EV_MIX_CALL; lia].
      - intros a Ha. rewrite MEQ5 by (destruct Hs1 as [Es1|Es1]; unfold A_G_REC; lia). exact (KEEPc a Ha).
      - rewrite T2, T3, T4, T8, T9, T18, T19, T21, T25, T26, P2, P3, P4, P8, P9, P18, P19, P21, P25, P26.
        repeat (split; [reflexivity|]). reflexivity. }
    split; [rewrite T10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
    split; [rewrite T11; reflexivity|].
    split.
    { cbn [map CLOB nth] in T12. rewrite T12.
      lazymatch goal with |- ew ?Ev _ = _ =>
        lazymatch goal with HX : img_env _ _ Ev |- _ =>
          pose proof (HX 288%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H288 end end.
      change (VAL 288%nat) with (VAL (A_OBJ 47)) in H288.
      rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in H288.
      apply bv_eq. rewrite H288. unfold w64. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
    split; [rewrite T20; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
    split.
    { intros i Hi. rewrite MEQ5 by (unfold SHADOW_OFF, A_G_REC; lia).
      rewrite (KEEPsh i Hi). rewrite MEQ by (unfold SHADOW_OFF; lia). exact (HBUF i Hi). }
    exists id, (rec_mix R1 (REC_ADD, sa_A uri id placement client)), O3.
    split.
    { right. split; [reflexivity|]. split; [exact HIN|]. split; [exact HREF0|]. split; [reflexivity|].
      rewrite T13. exact R19. }
    split; [exact HREP2|].
    split; [exact HACCT | exact HMO3].
  + (* refused: a0 := c, a1 := 0, a2 := 0, the call of answer at 0x8a08c, then j 0x8a0c4 *)
    assert (HREF : r_refuse R1 <> 0).
    { rewrite branch_eq_U, (s5_refuse_eq E (r_refuse R1) E32 Hrfr) in Hc0. apply Z.eqb_neq. exact Hc0. }
    assert (HIN : 0 <= id < 10000).
    { rewrite branch_ltu_U in Hc.
      rewrite (s5_srliw E id ltac:(rewrite (EE 19%nat (19%bv : bv 5) eq_refl), R19; exact H11) Hid), U_SLit in Hc.
      change (zcanon 625) with 625 in Hc. apply Z.ltb_lt in Hc. exact (s5_in_range id Hid Hc). }
    paj_run_tok RUN HS HJ SHOK s5_Bspan.
    { awr_ok_tac. }
    lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv3 := with_vm_backing x y z) in *; clearbody mdv3 end.
    s5_memeq Wc MEQ3. pose proof (fun a Ha => eq_trans (MEQ3 a Ha) (eq_trans (MEQ2a a Ha) (MEQ1 a Ha))) as MEQ.
    clear MEQ3. s5_clear_frames.
    pmkst HS. rewrite HSIGA.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
    rewrite (EE 2%nat (2%bv : bv 5) eq_refl) in P2. rewrite (EE 3%nat (3%bv : bv 5) eq_refl) in P3.
    rewrite (EE 4%nat (4%bv : bv 5) eq_refl) in P4. rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in P8.
    rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in P9. rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in P18.
    rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in P19. rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in P21.
    rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in P25. rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in P26.
    rewrite (EE 22%nat (22%bv : bv 5) eq_refl) in P10.
    assert (P2' : getr (ms_regs ms1) 2 = w64 (sa_s1 (spZ regs))) by (rewrite P2; exact R2).
    assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3; exact R3).
    assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4; exact R4).
    assert (P8' : getr (ms_regs ms1) 8 = w64 (spZ regs)) by (rewrite P8; exact R8).
    assert (P10' : getr (ms_regs ms1) 10 = w64 (sa_c R)) by (rewrite P10; exact H22).
    (* the state at the call *)
    pose proof HACCT as (HA1 & HA2 & HA3 & HO3live & HA5).
    assert (HARC : AR SEGS B lyc Sc Wc (ms_mem ms1) mdv3) by exact (proj1 HJ).
    assert (HAROc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
      by exact (sa_aro_kept B HB LAWS IMG
        SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] lyc Sc Wc (ms_mem ms1) mdv3 (sa_ev3 R) R O HAR HJ HREP HROD).
    assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms1)))
      by exact (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem ms1) mdv3 HARC HAROc).
    assert (HREPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms1)) R1 O3).
    { apply (rec_repA_kept B HB LAWS lyc Sc (rdW Wc memc) lyc Sc (rdW Wc (ms_mem ms1)) R1 O3 HREP3).
      - intros a Hin. apply MEQ. unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hin. lia.
      - intros p n i Hpn Hi. apply MEQ.
        destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc (HO3live _ Hpn)) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia.
      - exact HO3live. }
    pose proof (rec_repA_fields B HB LAWS _ _ _ _ _ HREPc) as FLDc.
    destruct FLDc as (_ & _ & _ & _ & _ & _ & (old & Hold & Holdcase) & Huniq3 & HO3fact).
    assert (Hold64 : 0 <= old < 2 ^ 64).
    { destruct Holdcase as [-> | (m & Hm)]; [lia|].
      destruct (HO3fact (old, m) Hm) as (Hbl & H1m & _). cbn [fst snd] in H1m.
      destruct (al_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms1) mdv3 old m HARC Hbl) as (_ & H4 & Hcl & _).
      pose proof (req_size_pos m ltac:(lia)) as [Hr1 _]. lia. }
    assert (Hc64 : 0 <= sa_c R < 2 ^ 64).
    { unfold sa_c. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; [apply Nat.ltb_lt in Elt|];
      unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL; lia. }
    assert (HCHG : false = negb (bv_unsigned (getr (ms_regs ms1) 12) =? 0)) by (rewrite P12; vm_compute; reflexivity).
    assert (HCOREc : sa_core B ly S W regs mem md O lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv3 (sa_ev3 R) pos).
    { eapply s5_core_kept; [exact HCORE | exact HJ | reflexivity | |].
      - intros a Ha. apply MEQ. destruct Hs1 as [Es1|Es1]; rewrite Es1 in Ha; lia.
      - repeat (split; [assumption|]). assumption. }
    pose proof (proj1 (proj2 HCOREc)) as HFRMc.
    assert (HCHx : exists ch1, achain lyc (rdW Wc (ms_mem ms1)) (sa_s1 (spZ regs)) (spZ regs) ch1)
      by exact (sa_achain B HB LAWS ly S W regs mem md ch R O [(1, pos)] lyc Sc Wc (ms_mem ms1) mdv3
        (sa_ev3 R) HPRE HREP HJ HFRMc).
    destruct HCHx as (ch1 & HCH).
    assert (HMEQm : rec_answer R1 (REC_ADD, sa_A uri id placement client) [] false
                    = sup_add_m R uri id placement client)
      by (symmetry; apply s5_m_refused; assumption).
    assert (HFR8 : Z.of_nat (length (frames Sc)) <= 8).
    { pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app length]. lia. }
    assert (HNEVc : st_nev Sc + EV_ANSWER <= EV_MAX).
    { pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
      unfold EV_SUP_ADD in HEV. unfold sa_ev3, sa_ev2, sa_ev1 in Hnev.
      unfold EV_ANSWER in *. lia. }
    assert (HLIVEc : blocks_bytes Sc + LIVE_ANSWER (snd (sup_add_m R uri id placement client)) <= LIVE_MAX).
    { unfold LIVE_SUP_ADD in HLIVE. unfold sa_live3, sa_live2 in HA5. lia. }
    assert (HMOc : mo_ok MT Sc (XM_ANSWER MT (snd (sup_add_m R uri id placement client)))).
    { eapply (mok_station MT S Sc _ (sa_acc3 MT R uri id placement client) _ MTL HMO HMO3).
      - unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
        pose proof (mo_free_nonneg MT MTL).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1)
          ltac:(lia)). lia.
      - unfold XM_SUP_ADD, sa_acc3, sa_acc2, sa_acc1. lia. }
    (* 0x8a08c: jal answer; answer returns at some FP state fx1 with fxrel fx fx1 *)
    unfold sa_final.
    eapply srr_after_callF.
    { eapply (cl_callS_wideF B LAWS Wc (ms_regs ms1) (ms_mem ms1) _ SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md
        [(1, pos)] lyc Sc mdv3 (sa_ev3 R) ANSWER_STK (s5_ansFP old O3) EV_ANSWER
        (sa_s1 (spZ regs) - spZ regs) _ ch1 _ HJ).
      - unfold spZ at 1. rewrite P2'. unfold w64. rewrite unsigned_lit_small by lia. lia.
      - destruct Hs1 as [Es1|Es1]; rewrite Es1;
        [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia];
        vm_compute; reflexivity.
      - destruct Hs1 as [Es1|Es1]; lia.
      - vm_compute; discriminate.
      - destruct Hs1 as [Es1|Es1]; rewrite Es1;
        [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia];
        vm_compute; discriminate.
      - exact P3'.
      - exact P4'.
      - reflexivity.
      - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite P1. rewrite unsigned_lit_small by lia. lia.
      - replace (spZ regs + (sa_s1 (spZ regs) - spZ regs)) with (sa_s1 (spZ regs)) by lia.
        unfold s0Z. rewrite P8'. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
      - intros HFN.
        refine (TANSWER fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv3 ch1 (sa_c R) 0 old
                  (REC_ADD, sa_A uri id placement client) [] false R1 O3
                  HFN FXR HFR8 HAROc HROc P10' Hc64 P11 ltac:(lia) HCHG HREPc Hold Hold64 _ _ _ _ _).
        + intros HZ. exfalso. exact (HREF HZ).
        + intros HZ. exfalso. exact (HREF HZ).
        + exact HNEVc.
        + rewrite HMEQm. exact HLIVEc.
        + rewrite HMEQm. exact HMOc.
      - intros a Hfp.
        assert (HPGcase : (inFP cmd_PG a /\ inFP (sa_FP O) a) \/
                          (exists p n, In (p, n) O3 /\ p <= a < p + req_size n)).
        { unfold s5_ansFP in Hfp. apply inFP_cons in Hfp as [Ha | Hfp].
          - left. split.
            + exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
              cbn [fst snd]. unfold OFF_ANSWER in *. lia.
            + exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [right; left; reflexivity|].
              cbn [fst snd]. unfold OFF_CALLS, OFF_ANSWER in *. lia.
          - apply inFP_cons in Hfp as [Ha | Hfp].
            + left. split.
              * exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
                cbn [fst snd]. unfold OFF_STATE in *. lia.
              * exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8). split; [right; right; left; reflexivity|].
                cbn [fst snd]. lia.
            + right. destruct (s5_inFP_ablocks_fp _ _ Hfp) as (p & n & Hin & Hr).
              apply s5_filter_in in Hin. exists p, n. split; [exact Hin | exact Hr]. }
        destruct HPGcase as [(HPGa & HFPa) | (p & n & Hin & Hr)].
        + right; right; right; right. left. split; [exact HFPa | split].
          * exact (sa_HPROG B HB LAWS a HPGa).
          * exact (cif_prog_img a HPGa).
        + destruct (HA1 _ Hin) as [HinO | HnotS].
          * right; left. split.
            -- exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
               unfold sa_FP. right; right; right; right.
               unfold ablocks_fp. apply in_map_iff. exists (p, n). split; [reflexivity | exact HinO].
            -- exists p, n. split; [exact (HO3live _ Hin) | exact Hr].
          * right; right; left. exists p, n. split; [exact (HO3live _ Hin)|]. split; [exact HnotS | exact Hr].
      - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _.
        exfalso.
        destruct (s5_ansFP_cases lyc Sc Wc (ms_mem ms1) mdv3 O3 old a HARC HO3live Hfp) as (Hlow & _). lia. }
    cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 Hwle2 Hfx1 (HJo & HJi & HP2 & HK2).
    rewrite HMEQm in HK2.
    (* what the call kept of the frame and of the real-stack slots *)
    assert (KEEPc : forall a, spZ regs - 104 <= a < spZ regs \/
      sa_s1 (spZ regs) + 16 <= a < sa_s1 (spZ regs) + 56 \/
      frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> rdW W2 mem2 a = rdW Wc (ms_mem ms1) a).
    { pose proof HJi as (HARi & Hlyi & _ & _ & _ & _ & _ & _ & Fi1 & _ & _ & Fi4 & _).
      intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
      - apply Fi1; [destruct Hs1 as [Es1|Es1]; lia | destruct Hs1 as [Es1|Es1]; lia |].
        intros Hfp. destruct (s5_ansFP_cases lyc Sc Wc (ms_mem ms1) mdv3 O3 old a HARC HO3live Hfp) as (Hlow & _). lia.
      - apply Fi1; [destruct Hs1 as [Es1|Es1]; lia | destruct Hs1 as [Es1|Es1]; lia |].
        intros Hfp. destruct (s5_ansFP_cases lyc Sc Wc (ms_mem ms1) mdv3 O3 old a HARC HO3live Hfp) as (Hlow & _). lia.
      - apply (Fi4 1 pos a Hfin).
        + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
        + exact (s5_ansFP_not_frame lyc Sc Wc (ms_mem ms1) mdv3 O3 old a 1 pos HARC HO3live Hfin
            ltac:(change (fs_frame_bytes 1) with 128; lia)). }
    pose proof HJi as (HARi & Hlyi & _).
    destruct (al_layout SEGS B LAWS lyc Sc Wc (ms_mem ms1) mdv3 ly2 HARC Hlyi) as (_ & HFEQ2 & _).
    assert (HLF2 : ly_F ly2 = ly_F lyc)
      by (pose proof Hlyi as (_ & _ & _ & _ & _ & EF & _); exact EF).
    (* back at 0x8a090, then j 0x8a0c4, at the FP state fx1 answer returned (in place:
       the symbolic state carried to fx1 by PaFx.v's st_ok_restrict_xfx, the executor taken at fx1) *)
    rewrite P1.
    pose proof (st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
    jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
    specialize (HS2 (Forall_nil _)).
    clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
    pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
    pose proof (img_env_havoc E 40%nat (map (getr regs2) CLOB) HEI ltac:(vm_compute; lia)) as HEIhv.
    assert (SHOK2 : sh_ok SEGS s5_Bx [] (havoc E 40 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2))
      by (unfold sh_ok; apply Forall_nil).
    paj_run_to_tok RUNTO1 HS HJo SHOK2 s5_Bspan L_M4.
    { apply awr_ok_nil. }
    lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv4 := with_vm_backing x y z) in *; clearbody mdv4 end.
    s5_memeq W2 MEQ5. s5_clear_frames.
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (19%bv : bv 5) T19. prreg HS (21%bv : bv 5) T21. prreg HS (25%bv : bv 5) T25.
    prreg HS (26%bv : bv 5) T26. prreg HS (10%bv : bv 5) T10.
    rewrite (EE 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EE 3%nat (3%bv : bv 5) eq_refl) in T3.
    rewrite (EE 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in T8.
    rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in T18.
    rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in T21.
    rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in T26.
    assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
    try rewrite A44 in T10.
    (* the blocks of the post *)
    destruct HK2 as (p1 & p2 & O' & HQ10 & HQ4096 & HQne & HQfresh & HQbl & HQrep & HQO' & HQstr & HQbytes & HQmo).
    assert (HUNIQ : forall lyx Sx (Wx : world SEGS) memx mdx, AR SEGS B lyx Sx Wx memx mdx -> forall p m m',
      In (p, m) (ablocks B lyx Sx) -> In (p, m') (ablocks B lyx Sx) -> m = m').
    { intros lyx Sx Wx memx mdx HARx p m m' H1 H2. destruct (Z.eq_dec m m') as [Em|Hne]; [exact Em|exfalso].
      pose proof (sep_blocks SEGS B LAWS lyx Sx Wx memx mdx p m p m' HARx H1 H2
        ltac:(intros EE'; apply Hne; congruence)) as Hd.
      destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p m HARx H1) as (_ & _ & _ & _ & _ & _ & Hm).
      destruct (al_blocks SEGS B LAWS lyx Sx Wx memx mdx p m' HARx H2) as (_ & _ & _ & _ & _ & _ & Hm').
      pose proof (req_size_pos m ltac:(lia)) as [Hq _]. pose proof (req_size_pos m' ltac:(lia)) as [Hq' _].
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    assert (H4096c : forall pn, In pn (ablocks B lyc Sc) -> 4096 <= fst pn).
    { intros [p n] Hin. exact (proj1 (proj2 (al_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms1) mdv3 p n HARC Hin))). }
    destruct (s5_ans_blocks (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly2 S2) O O3 O' old p1 p2
      (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1)
      HA1 HA2 HA3 HO3live Holdcase H4096c
      (HUNIQ lyc Sc Wc (ms_mem ms1) mdv3 HARC) (HUNIQ ly2 S2 W2 mem2 md2 HARi)
      HQne HQfresh HQbl HQO') as (G1 & G2 & G3 & G4 & G5 & G6).
    assert (HO'live : forall pn, In pn O' -> In pn (ablocks B ly2 S2)).
    { intros pn Hpn. apply HQbl. apply HQO' in Hpn as [[H1 H2] | ->]; [left; split; [exact (HO3live _ H1) | exact H2]|].
      right; left; reflexivity. }
    destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p2 _ HARi G4) as (_ & _ & Hp2ceil & _).
    (* M4 *)
    apply (HM4 fx1 (fxrel_frm0 fx fx1 FXR Hfx1) ly S W regs mem md ch pu id pp pc uri placement client R O ly2 S2 W2
      _ _ _ pos HCX).
    unfold sa_M4m. cbv zeta.
    split.
    { eapply s5_core_kept; [exact HCOREc | | exact HLF2 | |].
      - eapply ajournal_mono_k; [exact HJo|].
        unfold EV_SUP_ADD, sa_ev3, sa_ev2, sa_ev1, EV_ANSWER. lia.
      - intros a Ha. rewrite MEQ5 by (destruct Hs1 as [Es1|Es1]; lia). exact (KEEPc a Ha).
      - rewrite T2, T3, T4, T8, T9, T18, T19, T21, T25, T26, P2, P3, P4, P8, P9, P18, P19, P21, P25, P26.
        repeat (split; [reflexivity|]). reflexivity. }
    unfold sa_postQ. cbv zeta.
    exists (fst (sup_add_m R uri id placement client)), O', p2.
    split; [apply surjective_pairing|].
    split; [rewrite T10; exact HQ10|].
    split; [exact HQ4096|].
    split.
    { eapply rec_repA_kept; try eassumption.
      - intros a Hin. apply MEQ5. unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hin. lia.
      - intros p n i Hpn Hi. apply MEQ5.
        destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p n HARi (HO'live _ Hpn)) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia. }
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G5|]. split; [exact G6|].
    split.
    { eapply s5_astr_kept; [exact HQstr|]. intros i Hi. apply MEQ5.
      pose proof (req_size_pos (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1) ltac:(lia)) as [_ Hrq].
      lia. }
    split.
    { unfold LIVE_SUP_ADD. unfold sa_live3, sa_live2 in HA5. lia. }
    eapply mle_weaken; [exact MTL | eapply (mle_station MT S Sc S2); [exact MTL | exact HMO3 | exact HQmo] |].
    unfold XM_SUP_ADD, sa_acc3, sa_acc2, sa_acc1. lia.
- (* id outside [0, 10000): 0x8a060 .. 0x8a074 set a0 = F + 32, a1 = 32, a2 = "resp %d", a3 = -1, j 0x8a0b8 *)
  assert (HOUT : ((id <? 0) || (10000 <=? id))%bool = true).
  { rewrite branch_ltu_U in Hc.
    rewrite (s5_srliw E id ltac:(rewrite (EE 19%nat (19%bv : bv 5) eq_refl), R19; exact H11) Hid), U_SLit in Hc.
    change (zcanon 625) with 625 in Hc. apply Z.ltb_ge in Hc.
    apply Bool.orb_true_intro.
    destruct (Z_lt_le_dec id 0) as [Hlt|Hge]; [left; apply Z.ltb_lt; exact Hlt|].
    right. apply Z.leb_le. rewrite (Z.mod_small id (2 ^ 32)) in Hc by lia. exact (s5_div16 id Hc Hge). }
  paj_run_to_tok RUNTO HS HJ SHOK s5_Bspan L_M3b.
  { awr_ok_tac. }
  lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv2 := with_vm_backing x y z) in *; clearbody mdv2 end.
  s5_memeq Wc MEQ2. pose proof (fun a Ha => eq_trans (MEQ2 a Ha) (MEQ1 a Ha)) as MEQ.
  clear MEQ2. s5_clear_frames.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20.
  rewrite (EE 2%nat (2%bv : bv 5) eq_refl) in Q2. rewrite (EE 3%nat (3%bv : bv 5) eq_refl) in Q3.
  rewrite (EE 4%nat (4%bv : bv 5) eq_refl) in Q4. rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in Q8.
  rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in Q9. rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in Q18.
  rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in Q19. rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in Q21.
  rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in Q25. rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in Q26.
  rewrite (EE 26%nat (26%bv : bv 5) eq_refl), R26 in Q10, Q20.
  apply (HM3b ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc _ _ _ pos HCX).
  unfold sa_M3bm. cbv zeta.
  split.
  { eapply s5_core_kept; [exact HCORE | exact HJ | reflexivity | |].
    - intros a Ha. apply MEQ. destruct Hs1 as [Es1|Es1]; rewrite Es1 in Ha; lia.
    - repeat (split; [assumption|]). assumption. }
  split; [rewrite Q10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite Q11; reflexivity|].
  split.
  { rewrite Q12.
    lazymatch goal with |- ew ?Ev _ = _ =>
      lazymatch goal with HX : img_env _ _ Ev |- _ =>
        pose proof (HX 288%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H288 end end.
    change (VAL 288%nat) with (VAL (A_OBJ 47)) in H288.
    rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in H288.
    apply bv_eq. rewrite H288. unfold w64. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
  split; [rewrite Q20; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split.
  { intros i Hi. rewrite MEQ by (unfold SHADOW_OFF; lia). exact (HBUF i Hi). }
  exists (-1), (rec_record R REC_ADD (sa_A uri id placement client)), O3.
  split.
  { left. split; [reflexivity|]. split; [exact HOUT|]. split; [reflexivity|].
    rewrite Q13. apply bv_eq. vm_compute. reflexivity. }
  split.
  { pose proof HACCT as (_ & _ & _ & HO3live & _).
    eapply rec_repA_kept; try eassumption.
    - intros a Hin. apply MEQ. unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hin. lia.
    - intros p n i Hpn Hi. apply MEQ.
      destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc (HO3live _ Hpn)) as (_ & Hp4096 & Hpceil & _).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia. }
  split; [exact HACCT | exact HMO3].
Qed.
End e.
End f.
End d.
